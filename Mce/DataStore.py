# Copyright(C) 2011,2012,2013,2014 by Abe developers.

# DataStore.py: back end database access for Abe.

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Affero General Public License for more details.
# 
# You should have received a copy of the GNU Affero General Public
# License along with this program.  If not, see
# <http://www.gnu.org/licenses/agpl.html>.

# This module combines three functions that might be better split up:
# 1. Abe's schema
# 2. Abstraction over the schema for importing blocks, etc.
# 3. Code to load data by scanning blockfiles or using JSON-RPC.

import os
import re
import time
import errno
import logging
import redis

import SqlAbstraction

import Chain

# bitcointools -- modified deserialize.py to return raw transaction
import BCDataStream
import deserialize
import util
import base58

# MULTICHAIN START
import binascii
import struct
# MULTICHAIN END

SCHEMA_TYPE = "Abe"
SCHEMA_VERSION = SCHEMA_TYPE + "40"

CONFIG_DEFAULTS = {
    "dbtype":             None,
    "connect_args":       None,
    "binary_type":        None,
    "int_type":           None,
    "upgrade":            None,
    "rescan":             None,
    "commit_bytes":       None,
    "log_sql":            None,
    "log_rpc":            None,
    "default_chain":      "Bitcoin",
    "datadir":            None,
    "ignore_bit8_chains": None,
    "use_firstbits":      False,
    "keep_scriptsig":     True,
    "import_tx":          [],
    "default_loader":     "default",
    "rpc_load_mempool":   False,
# MULTICHAIN START
    "home_refresh_interval_secs": 60,
    "recent_tx_interval_ms": 5000,
    "catch_up_tx_interval_secs": 60
# MULTICHAIN END
}

WORK_BITS = 304  # XXX more than necessary.

CHAIN_CONFIG = [
#    {"chain":"Bitcoin"},
#    {"chain":"Testnet"},
    #{"chain":"",
    # "code3":"", "address_version":"\x", "magic":""},
# MULTICHAIN START
#    {"chain":"MultiChain"}
# MULTICHAIN END
    ]

NULL_PUBKEY_HASH = "\0" * Chain.PUBKEY_HASH_LENGTH
NULL_PUBKEY_ID = 0
PUBKEY_ID_NETWORK_FEE = NULL_PUBKEY_ID

# MULTICHAIN START
PUBKEY_FLAGS_P2SH = 1<<0
# MULTICHAIN END

# Size of the script and pubkey columns in bytes.
MAX_SCRIPT = 1000000
MAX_PUBKEY = 65

NO_CLOB = 'BUG_NO_CLOB'

# XXX This belongs in another module.
class InvalidBlock(Exception):
    pass
class MerkleRootMismatch(InvalidBlock):
    def __init__(ex, block_hash, tx_hashes):
        ex.block_hash = block_hash
        ex.tx_hashes = tx_hashes
    def __str__(ex):
        return 'Block header Merkle root does not match its transactions. ' \
            'block hash=%s' % (ex.block_hash[::-1].encode('hex'),)

class MalformedHash(ValueError):
    pass

class MalformedAddress(ValueError):
    pass

class DataStore(object):

    """
    Bitcoin data storage class based on DB-API 2 and standard SQL with
    workarounds to support SQLite3, PostgreSQL/psycopg2, MySQL,
    Oracle, ODBC, and IBM DB2.
    """

    def __init__(store, args):
        """
        Open and store a connection to the SQL database.

        args.dbtype should name a DB-API 2 driver module, e.g.,
        "sqlite3".

        args.connect_args should be an argument to the module's
        connect() method, or None for no argument, or a list of
        arguments, or a dictionary of named arguments.

        args.datadir names Bitcoin data directories containing
        blk0001.dat to scan for new blocks.
        """
        if args.datadir is None:
            args.datadir = util.determine_db_dir()
        if isinstance(args.datadir, str):
            args.datadir = [args.datadir]

        store.args = args
        store.log = logging.getLogger(__name__)

        store.rpclog = logging.getLogger(__name__ + ".rpc")
        if not args.log_rpc:
            store.rpclog.setLevel(logging.ERROR)

        if args.dbtype is None:
            store.log.warn("dbtype not configured, see abe.conf for examples");
            store.dbmodule = None
            store.config = CONFIG_DEFAULTS.copy()
            store.datadirs = []
            store.use_firstbits = CONFIG_DEFAULTS['use_firstbits']
            store._sql = None
            return
        store.dbmodule = __import__(args.dbtype)

        if args.redisPort is not None and args.redisHost is not None and args.redisDb is not None:
            store.redis = redis.Redis(host = args.redisHost, port = args.redisPort, db = args.redisDb)

        sql_args = lambda: 1
        sql_args.module = store.dbmodule
        sql_args.connect_args = args.connect_args
        sql_args.binary_type = args.binary_type
        sql_args.int_type = args.int_type
        sql_args.log_sql = args.log_sql
        sql_args.prefix = "abe_"
        sql_args.config = {}
        store.sql_args = sql_args
        store.set_db(None)
        store.init_sql()

        store._blocks = {}

        # Read the CONFIG and CONFIGVAR tables if present.
        store.config = store._read_config()

        if store.config is None:
            store.keep_scriptsig = args.keep_scriptsig
        elif 'keep_scriptsig' in store.config:
            store.keep_scriptsig = store.config.get('keep_scriptsig') == "true"
        else:
            store.keep_scriptsig = CONFIG_DEFAULTS['keep_scriptsig']

        store.refresh_ddl()

        if store.config is None:
            store.initialize()
        else:
            store.init_sql()

            if store.config['schema_version'] == SCHEMA_VERSION:
                pass
            elif args.upgrade:
                import upgrade
                upgrade.upgrade_schema(store)
            else:
                raise Exception(
                    "Database schema version (%s) does not match software"
                    " (%s).  Please run with --upgrade to convert database."
                    % (store.config['schema_version'], SCHEMA_VERSION))
        store._sql.auto_reconnect = True

        if args.rescan:
            store.sql("UPDATE datadir SET blkfile_number=1, blkfile_offset=0")

        store._init_datadirs()
        store.init_chains()

        store.commit_bytes = args.commit_bytes
        if store.commit_bytes is None:
            store.commit_bytes = 0  # Commit whenever possible.
        else:
            store.commit_bytes = int(store.commit_bytes)
        store.bytes_since_commit = 0

        store.use_firstbits = (store.config['use_firstbits'] == "true")

        for hex_tx in args.import_tx:
            chain_name = None
            if isinstance(hex_tx, dict):
                chain_name = hex_tx.get("chain")
                hex_tx = hex_tx.get("tx")
            store.maybe_import_binary_tx(chain_name, str(hex_tx).decode('hex'))

        store.default_loader = args.default_loader

        store.rpc_load_mempool = args.rpc_load_mempool

        store.default_chain = args.default_chain;

# MULTICHAIN START
        store.home_refresh_interval_secs = args.home_refresh_interval_secs
        store.recent_tx_interval_ms = args.recent_tx_interval_ms
        store.catch_up_tx_interval_secs = args.catch_up_tx_interval_secs
# MULTICHAIN END

        store.commit()

    def set_db(store, db):
        store._sql = db

    def get_db(store):
        return store._sql

    def connect(store):
        return store._sql.connect()

    def reconnect(store):
        return store._sql.reconnect()

    def close(store):
        store._sql.close()

    def commit(store):
        store._sql.commit()

    def rollback(store):
        if store._sql is not None:
            store._sql.rollback()

    def sql(store, stmt, params=()):
        store._sql.sql(stmt, params)

    def ddl(store, stmt):
        store._sql.ddl(stmt)

    def selectrow(store, stmt, params=()):
        return store._sql.selectrow(stmt, params)

    def selectall(store, stmt, params=()):
        return store._sql.selectall(stmt, params)

    def rowcount(store):
        return store._sql.rowcount()

    def create_sequence(store, key):
        store._sql.create_sequence(key)

    def drop_sequence(store, key):
        store._sql.drop_sequence(key)

    def new_id(store, key):
        return store._sql.new_id(key)

    def init_sql(store):
        sql_args = store.sql_args
        if hasattr(store, 'config'):
            for name in store.config.keys():
                if name.startswith('sql.'):
                    sql_args.config[name[len('sql.'):]] = store.config[name]
        if store._sql:
            store._sql.close()  # XXX Could just set_flavour.
        store.set_db(SqlAbstraction.SqlAbstraction(sql_args))
        store.init_binfuncs()

    def init_binfuncs(store):
        store.binin       = store._sql.binin
        store.binin_hex   = store._sql.binin_hex
        store.binin_int   = store._sql.binin_int
        store.binout      = store._sql.binout
        store.binout_hex  = store._sql.binout_hex
        store.binout_int  = store._sql.binout_int
        store.intin       = store._sql.intin
        store.hashin      = store._sql.revin
        store.hashin_hex  = store._sql.revin_hex
        store.hashout     = store._sql.revout
        store.hashout_hex = store._sql.revout_hex

    def _read_config(store):
        # Read table CONFIGVAR if it exists.
        config = {}
        try:
            for name, value in store.selectall("""
                SELECT configvar_name, configvar_value
                  FROM configvar"""):
                config[name] = '' if value is None else value
            if config:
                return config

        except store.dbmodule.DatabaseError:
            try:
                store.rollback()
            except Exception:
                pass

        # Read legacy table CONFIG if it exists.
        try:
            row = store.selectrow("""
                SELECT schema_version, binary_type
                  FROM config
                 WHERE config_id = 1""")
            sv, btype = row
            return { 'schema_version': sv, 'binary_type': btype }
        except Exception:
            try:
                store.rollback()
            except Exception:
                pass

        # Return None to indicate no schema found.
        return None

    def _init_datadirs(store):
        """Parse store.args.datadir, create store.datadirs."""
        if store.args.datadir == []:
            store.datadirs = []
            return

        datadirs = {}
        for row in store.selectall("""
            SELECT datadir_id, dirname, blkfile_number, blkfile_offset,
                   chain_id
              FROM datadir"""):
            id, dir, num, offs, chain_id = row
            datadirs[dir] = {
                "id": id,
                "dirname": dir,
                "blkfile_number": int(num),
                "blkfile_offset": int(offs),
                "chain_id": None if chain_id is None else int(chain_id),
                "loader": None}

        #print("datadirs: %r" % datadirs)

        # By default, scan every dir we know.  This doesn't happen in
        # practise, because abe.py sets ~/.bitcoin as default datadir.
        if store.args.datadir is None:
            store.datadirs = datadirs.values()
            return

        def lookup_chain_id(name):
            row = store.selectrow(
                "SELECT chain_id FROM chain WHERE chain_name = ?",
                (name,))
            return None if row is None else int(row[0])

        store.datadirs = []
        for dircfg in store.args.datadir:
            loader = None
            conf = None

            if isinstance(dircfg, dict):
                #print("dircfg is dict: %r" % dircfg)  # XXX
                dirname = dircfg.get('dirname')
                if dirname is None:
                    raise ValueError(
                        'Missing dirname in datadir configuration: '
                        + str(dircfg))
                if dirname in datadirs:
                    d = datadirs[dirname]
                    d['loader'] = dircfg.get('loader')
                    d['conf'] = dircfg.get('conf')
                    if d['chain_id'] is None and 'chain' in dircfg:
                        d['chain_id'] = lookup_chain_id(dircfg['chain'])
                    store.datadirs.append(d)
                    continue

                loader = dircfg.get('loader')
                conf = dircfg.get('conf')
                chain_id = dircfg.get('chain_id')
                if chain_id is None:
                    chain_name = dircfg.get('chain')
                    chain_id = lookup_chain_id(chain_name)

                    if chain_id is None and chain_name is not None:
                        chain_id = store.new_id('chain')

                        code3 = dircfg.get('code3')
                        if code3 is None:
                            # XXX Should default via policy.
                            code3 = '000' if chain_id > 999 else "%03d" % (
                                chain_id,)
# MULTICHAIN START
                        paramsdat_broken = False
                        paramsfile = os.path.join(os.path.expanduser(dirname), "params.dat")
                        try:
                            params = {}
                            for line in open(paramsfile):
                                if "=" not in line:
                                    continue
                                x = line.partition('#')[0].split("=", 1)
                                if len(x) != 2:
                                    continue
                                params[x[0].strip()]=x[1].strip()
                        except Exception, e:
                            store.log.error("failed to load %s: %s", paramsfile, e)
                            paramsdat_broken = True

                        if paramsdat_broken is False:
                            x = params.get("address-pubkeyhash-version","00").strip()
                            addr_vers = binascii.unhexlify(x)
                            x = params.get("address-scripthash-version","05").strip()
                            script_addr_vers = binascii.unhexlify(x)
                            x = params.get("address-checksum-value","00000000").strip()
                            address_checksum = binascii.unhexlify(x)
                            x = params.get("network-message-start","f9beb4d9").strip()
                            chain_magic = binascii.unhexlify(x)
                            protocol_version = params.get("protocol-version",10007)
                        else:
                            protocol_version = 10007
                            chain_magic = '\xf9\xbe\xb4\xd9'
                            address_checksum = "\0\0\0\0"
                            addr_vers = dircfg.get('address_version')
                            if addr_vers is None:
                                addr_vers = "\0"
                            elif isinstance(addr_vers, unicode):
                                addr_vers = addr_vers.encode('latin_1')

                            script_addr_vers = dircfg.get('script_addr_vers')
                            if script_addr_vers is None:
                                script_addr_vers = "\x05"
                            elif isinstance(script_addr_vers, unicode):
                                script_addr_vers = script_addr_vers.encode('latin_1')
# MULTICHAIN END
                        decimals = dircfg.get('decimals')
                        if decimals is not None:
                            decimals = int(decimals)

                        # XXX Could do chain_magic, but this datadir won't
                        # use it, because it knows its chain.
# MULTICHAIN START
                        store.sql("""
                            INSERT INTO chain (
                                chain_id, chain_name, chain_code3,
                                chain_magic, chain_address_checksum, chain_address_version, chain_script_addr_vers, chain_policy,
                                chain_decimals, chain_protocol_version
                            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                                  (chain_id, chain_name, code3,
                                   store.binin(chain_magic), store.binin(address_checksum), store.binin(addr_vers), store.binin(script_addr_vers),
# MULTICHAIN END
                                   dircfg.get('policy', chain_name), decimals, protocol_version))
                        store.commit()
                        store.log.warning("Assigned chain_id %d to %s",
                                          chain_id, chain_name)

            elif dircfg in datadirs:
                store.datadirs.append(datadirs[dircfg])
                continue
            else:
                # Not a dict.  A string naming a directory holding
                # standard chains.
                dirname = dircfg
                chain_id = None

            d = {
                "id": store.new_id("datadir"),
                "dirname": dirname,
                "blkfile_number": 1,
                "blkfile_offset": 0,
                "chain_id": chain_id,
                "loader": loader,
                "conf": conf,
                }
            store.datadirs.append(d)

    def init_chains(store):
        store.chains_by = lambda: 0
        store.chains_by.id = {}
        store.chains_by.name = {}
        store.chains_by.magic = {}

        # Legacy config option.
        no_bit8_chains = store.args.ignore_bit8_chains or []
        if isinstance(no_bit8_chains, str):
            no_bit8_chains = [no_bit8_chains]
# MULTICHAIN START
        for chain_id, magic, chain_name, chain_code3, address_checksum, address_version, script_addr_vers, \
                chain_policy, chain_decimals, chain_protocol_version in \
                store.selectall("""
                    SELECT chain_id, chain_magic, chain_name, chain_code3,
                           chain_address_checksum, chain_address_version, chain_script_addr_vers, chain_policy, chain_decimals,
                           chain_protocol_version
                      FROM chain
                """):
# MULTICHAIN END
            chain = Chain.create(
                id              = int(chain_id),
                magic           = store.binout(magic),
                name            = unicode(chain_name),
                code3           = chain_code3 and unicode(chain_code3),
# MULTICHAIN START
                address_checksum = store.binout(address_checksum),
                protocol_version = int(chain_protocol_version),
# MULTICHAIN END
                address_version = store.binout(address_version),
                script_addr_vers = store.binout(script_addr_vers),
                policy          = unicode(chain_policy),
                decimals        = None if chain_decimals is None else \
                    int(chain_decimals))

            # Legacy config option.
            if chain.name in no_bit8_chains and \
                    chain.has_feature('block_version_bit8_merge_mine'):
                chain = Chain.create(src=chain, policy="LegacyNoBit8")

            store.chains_by.id[chain.id] = chain
            store.chains_by.name[chain.name] = chain
            store.chains_by.magic[bytes(chain.magic)] = chain

    def get_chain_by_id(store, chain_id):
        return store.chains_by.id[int(chain_id)]

    def get_chain_by_name(store, name):
        return store.chains_by.name.get(name, None)

    def get_default_chain(store):
        store.log.debug("Falling back to default (Bitcoin) policy.")
        return Chain.create(store.default_chain)

# MULTICHAIN START
    def get_url_by_chain(store, chain):
        dirname = store.get_dirname_by_id(chain.id)
        conffile = chain.datadir_conf_file_name
        conffile = os.path.join(dirname, conffile)
        try:
            conf = dict([line.strip().split("=", 1)
                         if "=" in line
                         else (line.strip(), True)
                         for line in open(conffile)
                         if line != "" and line[0] not in "#\r\n"])
        except Exception, e:
            store.log.error("failed to load %s: %s", conffile, e)
            return None

        rpcuser     = conf.get("rpcuser", "")
        rpcpassword = conf["rpcpassword"]
        rpcconnect  = conf.get("rpcconnect", "127.0.0.1")
        rpcport     = conf.get("rpcport", chain.datadir_rpcport)
        url = "http://" + rpcuser + ":" + rpcpassword + "@" + rpcconnect \
            + ":" + str(rpcport)
        return url

    def get_multichain_name_by_id(store, chain_id):
        dirname = store.get_dirname_by_id( chain_id)
        if dirname is None:
            return None
        return os.path.basename(dirname)

    def get_dirname_by_id(store, chain_id):
        """
        Get the chain name of a multichain network, given the chain id.
        :param store:
        :param chain_id:
        :return:
        """
        chain_id = int(chain_id)
        row = store.selectrow("""
                SELECT dirname
                  FROM datadir
                 WHERE chain_id = ?""", (chain_id,))
        if row is None:
            return None
        dirname, = row
        return dirname


# MULTICHAIN END


    def get_ddl(store, key):
        return store._ddl[key]

    def refresh_ddl(store):
        store._ddl = {
            "chain_summary":
# XXX I could do a lot with MATERIALIZED views.
"""CREATE VIEW chain_summary AS SELECT
    cc.chain_id,
    cc.in_longest,
    b.block_id,
    b.block_hash,
    b.block_version,
    b.block_hashMerkleRoot,
    b.block_nTime,
    b.block_nBits,
    b.block_nNonce,
    cc.block_height,
    b.prev_block_id,
    prev.block_hash prev_block_hash,
    b.block_chain_work,
    b.block_num_tx,
    b.block_value_in,
    b.block_value_out,
    b.block_total_satoshis,
    b.block_total_seconds,
    b.block_satoshi_seconds,
    b.block_total_ss,
    b.block_ss_destroyed
FROM chain_candidate cc
JOIN block b ON (cc.block_id = b.block_id)
LEFT JOIN block prev ON (b.prev_block_id = prev.block_id)""",

            "txout_detail":
"""CREATE VIEW txout_detail AS SELECT
    cc.chain_id,
    cc.in_longest,
    cc.block_id,
    b.block_hash,
    b.block_height,
    block_tx.tx_pos,
    tx.tx_id,
    tx.tx_hash,
    tx.tx_lockTime,
    tx.tx_version,
    tx.tx_size,
    txout.txout_id,
    txout.txout_pos,
    txout.txout_value,
    txout.txout_scriptPubKey,
    pubkey.pubkey_id,
    pubkey.pubkey_hash,
    pubkey.pubkey
  FROM chain_candidate cc
  JOIN block b ON (cc.block_id = b.block_id)
  JOIN block_tx ON (b.block_id = block_tx.block_id)
  JOIN tx    ON (tx.tx_id = block_tx.tx_id)
  JOIN txout ON (tx.tx_id = txout.tx_id)
  LEFT JOIN pubkey ON (txout.pubkey_id = pubkey.pubkey_id)""",

            "txin_detail":
"""CREATE VIEW txin_detail AS SELECT
    cc.chain_id,
    cc.in_longest,
    cc.block_id,
    b.block_hash,
    b.block_height,
    block_tx.tx_pos,
    tx.tx_id,
    tx.tx_hash,
    tx.tx_lockTime,
    tx.tx_version,
    tx.tx_size,
    txin.txin_id,
    txin.txin_pos,
    txin.txout_id prevout_id""" + (""",
    txin.txin_scriptSig,
    txin.txin_sequence""" if store.keep_scriptsig else """,
    NULL txin_scriptSig,
    NULL txin_sequence""") + """,
    prevout.txout_value txin_value,
    prevout.txout_scriptPubKey txin_scriptPubKey,
    pubkey.pubkey_id,
    pubkey.pubkey_hash,
    pubkey.pubkey
  FROM chain_candidate cc
  JOIN block b ON (cc.block_id = b.block_id)
  JOIN block_tx ON (b.block_id = block_tx.block_id)
  JOIN tx    ON (tx.tx_id = block_tx.tx_id)
  JOIN txin  ON (tx.tx_id = txin.tx_id)
  LEFT JOIN txout prevout ON (txin.txout_id = prevout.txout_id)
  LEFT JOIN pubkey
      ON (prevout.pubkey_id = pubkey.pubkey_id)""",

            "txout_approx":
# View of txout for drivers like sqlite3 that can not handle large
# integer arithmetic.  For them, we transform the definition of
# txout_approx_value to DOUBLE PRECISION (approximate) by a CAST.
"""CREATE VIEW txout_approx AS SELECT
    txout_id,
    tx_id,
    txout_value txout_approx_value
  FROM txout""",

            "configvar":
# ABE accounting.  This table is read without knowledge of the
# database's SQL quirks, so it must use only the most widely supported
# features.
"""CREATE TABLE configvar (
    configvar_name  VARCHAR(100) NOT NULL PRIMARY KEY,
    configvar_value VARCHAR(255)
)""",

            "abe_sequences":
"""CREATE TABLE abe_sequences (
    sequence_key VARCHAR(100) NOT NULL PRIMARY KEY,
    nextid NUMERIC(30)
)""",
            }

    def initialize(store):
        """
        Create the database schema.
        """
        store.config = {}
        store.configure()

        for stmt in (

store._ddl['configvar'],

"""CREATE TABLE datadir (
    datadir_id  NUMERIC(10) NOT NULL PRIMARY KEY,
    dirname     VARCHAR(2000) NOT NULL,
    blkfile_number NUMERIC(8) NULL,
    blkfile_offset NUMERIC(20) NULL,
    chain_id    NUMERIC(10) NULL
)""",

# A block of the type used by Bitcoin.
"""CREATE TABLE block (
    block_id      NUMERIC(14) NOT NULL PRIMARY KEY,
    block_hash    BINARY(32)  UNIQUE NOT NULL,
    block_hash_string   VARCHAR(64) UNIQUE NOT NULL,
    block_version NUMERIC(10),
    block_hashMerkleRoot BINARY(32),
    block_nTime   NUMERIC(20),
    block_datetime DATETIME,
    block_nBits   NUMERIC(10),
    block_nNonce  NUMERIC(10),
    block_height  NUMERIC(14) NULL,
    prev_block_id NUMERIC(14) NULL,
    search_block_id NUMERIC(14) NULL,
    block_chain_work BINARY(""" + str(WORK_BITS / 8) + """),
    block_value_in NUMERIC(30) NULL,
    block_value_out NUMERIC(30),
    block_total_satoshis NUMERIC(26) NULL,
    block_total_seconds NUMERIC(20) NULL,
    block_satoshi_seconds NUMERIC(28) NULL,
    block_total_ss NUMERIC(28) NULL,
    block_num_tx  NUMERIC(10) NOT NULL,
    block_ss_destroyed NUMERIC(28) NULL,
    FOREIGN KEY (prev_block_id)
        REFERENCES block (block_id),
    FOREIGN KEY (search_block_id)
        REFERENCES block (block_id)
)""",

# CHAIN comprises a magic number, a policy, and (indirectly via
# CHAIN_LAST_BLOCK_ID and the referenced block's ancestors) a genesis
# block, possibly null.  A chain may have a currency code.
"""CREATE TABLE chain (
    chain_id    NUMERIC(10) NOT NULL PRIMARY KEY,
    chain_name  VARCHAR(100) UNIQUE NOT NULL,
    chain_code3 VARCHAR(5)  NULL,
    chain_address_version VARBINARY(100) NOT NULL,
    chain_script_addr_vers VARBINARY(100) NULL,
    chain_address_checksum VARBINARY(100) NULL,
    chain_magic BINARY(4)     NULL,
    chain_policy VARCHAR(255) NOT NULL,
    chain_decimals NUMERIC(2) NULL,
    chain_last_block_id NUMERIC(14) NULL,
    chain_protocol_version NUMERIC(10) NOT NULL,
    FOREIGN KEY (chain_last_block_id)
        REFERENCES block (block_id)
)""",

# CHAIN_CANDIDATE lists blocks that are, or might become, part of the
# given chain.  IN_LONGEST is 1 when the block is in the chain, else 0.
# IN_LONGEST denormalizes information stored canonically in
# CHAIN.CHAIN_LAST_BLOCK_ID and BLOCK.PREV_BLOCK_ID.
"""CREATE TABLE chain_candidate (
    chain_id      NUMERIC(10) NOT NULL,
    block_id      NUMERIC(14) NOT NULL,
    in_longest    NUMERIC(1),
    block_height  NUMERIC(14),
    PRIMARY KEY (chain_id, block_id),
    FOREIGN KEY (block_id) REFERENCES block (block_id)
)""",
"""CREATE INDEX x_cc_block ON chain_candidate (block_id)""",
"""CREATE INDEX x_cc_chain_block_height
    ON chain_candidate (chain_id, block_height)""",
"""CREATE INDEX x_cc_block_height ON chain_candidate (block_height)""",

# An orphan block must remember its hashPrev.
"""CREATE TABLE orphan_block (
    block_id      NUMERIC(14) NOT NULL PRIMARY KEY,
    block_hashPrev BINARY(32) NOT NULL,
    FOREIGN KEY (block_id) REFERENCES block (block_id)
)""",
"""CREATE INDEX x_orphan_block_hashPrev ON orphan_block (block_hashPrev)""",

# Denormalize the relationship inverse to BLOCK.PREV_BLOCK_ID.
"""CREATE TABLE block_next (
    block_id      NUMERIC(14) NOT NULL,
    next_block_id NUMERIC(14) NOT NULL,
    PRIMARY KEY (block_id, next_block_id),
    FOREIGN KEY (block_id) REFERENCES block (block_id),
    FOREIGN KEY (next_block_id) REFERENCES block (block_id)
)""",

# A transaction of the type used by Bitcoin.
"""CREATE TABLE tx (
    tx_id         NUMERIC(26) NOT NULL PRIMARY KEY,
    tx_hash       BINARY(32)  UNIQUE NOT NULL,
    tx_version    NUMERIC(10),
    tx_lockTime   NUMERIC(10),
    tx_size       NUMERIC(10)
)""",

# Presence of transactions in blocks is many-to-many.
"""CREATE TABLE block_tx (
    block_id      NUMERIC(14) NOT NULL,
    tx_id         NUMERIC(26) NOT NULL,
    tx_pos        NUMERIC(10) NOT NULL,
    PRIMARY KEY (block_id, tx_id),
    UNIQUE (block_id, tx_pos),
    FOREIGN KEY (block_id)
        REFERENCES block (block_id),
    FOREIGN KEY (tx_id)
        REFERENCES tx (tx_id)
)""",
"""CREATE INDEX x_block_tx_tx ON block_tx (tx_id)""",

# A public key for sending bitcoins.  PUBKEY_HASH is derivable from a
# Bitcoin or Testnet address.
"""CREATE TABLE pubkey (
    pubkey_id     NUMERIC(26) NOT NULL PRIMARY KEY,
    pubkey_hash   BINARY(20)  UNIQUE NOT NULL,
    pubkey        VARBINARY(""" + str(MAX_PUBKEY) + """) NULL,
    pubkey_flags  NUMERIC(32) NULL
)""",

"""CREATE TABLE multisig_pubkey (
    multisig_id   NUMERIC(26) NOT NULL,
    pubkey_id     NUMERIC(26) NOT NULL,
    PRIMARY KEY (multisig_id, pubkey_id),
    FOREIGN KEY (multisig_id) REFERENCES pubkey (pubkey_id),
    FOREIGN KEY (pubkey_id) REFERENCES pubkey (pubkey_id)
)""",
"""CREATE INDEX x_multisig_pubkey_pubkey ON multisig_pubkey (pubkey_id)""",

# A transaction out-point.
"""CREATE TABLE txout (
    txout_id      NUMERIC(26) NOT NULL PRIMARY KEY,
    tx_id         NUMERIC(26) NOT NULL,
    txout_pos     NUMERIC(10) NOT NULL,
    txout_value   NUMERIC(30) NOT NULL,
    txout_scriptPubKey VARBINARY(""" + str(MAX_SCRIPT) + """),
    pubkey_id     NUMERIC(26),
    UNIQUE (tx_id, txout_pos),
    FOREIGN KEY (pubkey_id)
        REFERENCES pubkey (pubkey_id)
)""",
"""CREATE INDEX x_txout_pubkey ON txout (pubkey_id)""",

# A transaction in-point.
"""CREATE TABLE txin (
    txin_id       NUMERIC(26) NOT NULL PRIMARY KEY,
    tx_id         NUMERIC(26) NOT NULL,
    txin_pos      NUMERIC(10) NOT NULL,
    txout_id      NUMERIC(26)""" + (""",
    txin_scriptSig VARBINARY(""" + str(MAX_SCRIPT) + """),
    txin_sequence NUMERIC(10)""" if store.keep_scriptsig else "") + """,
    UNIQUE (tx_id, txin_pos),
    FOREIGN KEY (tx_id)
        REFERENCES tx (tx_id)
)""",
"""CREATE INDEX x_txin_txout ON txin (txout_id)""",

# While TXIN.TXOUT_ID can not be found, we must remember TXOUT_POS,
# a.k.a. PREVOUT_N.
"""CREATE TABLE unlinked_txin (
    txin_id       NUMERIC(26) NOT NULL PRIMARY KEY,
    txout_tx_hash BINARY(32)  NOT NULL,
    txout_pos     NUMERIC(10) NOT NULL,
    FOREIGN KEY (txin_id) REFERENCES txin (txin_id)
)""",
"""CREATE INDEX x_unlinked_txin_outpoint
    ON unlinked_txin (txout_tx_hash, txout_pos)""",

"""CREATE TABLE block_txin (
    block_id      NUMERIC(14) NOT NULL,
    txin_id       NUMERIC(26) NOT NULL,
    out_block_id  NUMERIC(14) NOT NULL,
    PRIMARY KEY (block_id, txin_id),
    FOREIGN KEY (block_id) REFERENCES block (block_id),
    FOREIGN KEY (txin_id) REFERENCES txin (txin_id),
    FOREIGN KEY (out_block_id) REFERENCES block (block_id)
)""",

store._ddl['chain_summary'],
store._ddl['txout_detail'],
store._ddl['txin_detail'],
store._ddl['txout_approx'],

"""CREATE TABLE abe_lock (
    lock_id       NUMERIC(10) NOT NULL PRIMARY KEY,
    pid           VARCHAR(255) NULL
)""",
# MULTICHAIN START

# issued assets are stored here
# op_drop has issue qty
# op_return of issue asset has: name, multiplier
# 2 steps to get all data.
"""CREATE TABLE asset (
    asset_id      NUMERIC(10) NOT NULL PRIMARY KEY,
    tx_id         NUMERIC(26) NOT NULL,
    chain_id      NUMERIC(10) NOT NULL,
    name          VARCHAR(255) NOT NULL,
    multiplier    NUMERIC(10) NOT NULL,
    issue_qty     NUMERIC(30) NOT NULL,
    prefix        NUMERIC(10) NOT NULL,
    UNIQUE      (tx_id),
    FOREIGN KEY (tx_id) REFERENCES tx (tx_id),
    FOREIGN KEY (chain_id) REFERENCES chain (chain_id)
)""",

"""CREATE TABLE asset_txid (
    asset_id      NUMERIC(10) NOT NULL,
    tx_id         NUMERIC(26) NOT NULL,
    txout_pos     NUMERIC(10) NOT NULL,
    UNIQUE (asset_id, tx_id, txout_pos),
    FOREIGN KEY (tx_id) REFERENCES tx (tx_id),
    FOREIGN KEY (asset_id) REFERENCES asset (asset_id)
)""",

# raw units
"""CREATE TABLE asset_address_balance (
    asset_id      NUMERIC(10) NOT NULL,
    pubkey_id     NUMERIC(26) NOT NULL,
    balance       NUMERIC(30) NOT NULL,
    PRIMARY KEY (asset_id, pubkey_id),
    FOREIGN KEY (asset_id) REFERENCES asset (asset_id),
    FOREIGN KEY (pubkey_id) REFERENCES pubkey (pubkey_id)
)""",

##########################################
######## SDEC Business Tables ############
##########################################

# Emissor Table
"""
/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;


# Dump of table estado
# ------------------------------------------------------------

LOCK TABLES `estado` WRITE;
/*!40000 ALTER TABLE `estado` DISABLE KEYS */;

INSERT INTO `estado` (`sigla`, `nome`)
VALUES
	('AC','Acre'),
	('AL','Alagoas'),
	('AP','Amapá'),
	('AM','Amazonas'),
	('BA','Bahia'),
	('CE','Ceará'),
	('DF','Distrito Federal'),
	('ES','Espírito Santo'),
	('GO','Goiás'),
	('MA','Maranhão'),
	('MT','Mato Grosso'),
	('MS','Mato Grosso do Sul'),
	('MG','Minas Gerais'),
	('PA','Pará'),
	('PB','Paraíba'),
	('PR','Paraná'),
	('PE','Pernambuco'),
	('PI','Piauí'),
	('RJ','Rio de Janeiro'),
	('RN','Rio Grande do Norte'),
	('RS','Rio Grande do Sul'),
	('RO','Rondônia'),
	('RR','Roraima'),
	('SC','Santa Catarina'),
	('SP','São Paulo'),
	('SE','Sergipe'),
	('TO','Tocantins');

/*!40000 ALTER TABLE `estado` ENABLE KEYS */;
UNLOCK TABLES;


# Dump of table municipio
# ------------------------------------------------------------

LOCK TABLES `municipio` WRITE;
/*!40000 ALTER TABLE `municipio` DISABLE KEYS */;

INSERT INTO `municipio` (`codigoIbge`, `nome`, `uf`, `nomeRegiao`)
VALUES
	('1100015','Alta Floresta D\'Oeste','RO','Leste Rondoniense'),
	('1100023','Ariquemes','RO','Leste Rondoniense'),
	('1100031','Cabixi','RO','Leste Rondoniense'),
	('1100049','Cacoal','RO','Leste Rondoniense'),
	('1100056','Cerejeiras','RO','Leste Rondoniense'),
	('1100064','Colorado do Oeste','RO','Leste Rondoniense'),
	('1100072','Corumbiara','RO','Leste Rondoniense'),
	('1100080','Costa Marques','RO','Madeira-Guaporé'),
	('1100098','Espigão D\'Oeste','RO','Leste Rondoniense'),
	('1100106','Guajará-Mirim','RO','Madeira-Guaporé'),
	('1100114','Jaru','RO','Leste Rondoniense'),
	('1100122','Ji-Paraná','RO','Leste Rondoniense'),
	('1100130','Machadinho D\'Oeste','RO','Leste Rondoniense'),
	('1100148','Nova Brasilândia D\'Oeste','RO','Leste Rondoniense'),
	('1100155','Ouro Preto do Oeste','RO','Leste Rondoniense'),
	('1100189','Pimenta Bueno','RO','Leste Rondoniense'),
	('1100205','Porto Velho','RO','Madeira-Guaporé'),
	('1100254','Presidente Médici','RO','Leste Rondoniense'),
	('1100262','Rio Crespo','RO','Leste Rondoniense'),
	('1100288','Rolim de Moura','RO','Leste Rondoniense'),
	('1100296','Santa Luzia D\'Oeste','RO','Leste Rondoniense'),
	('1100304','Vilhena','RO','Leste Rondoniense'),
	('1100320','São Miguel do Guaporé','RO','Leste Rondoniense'),
	('1100338','Nova Mamoré','RO','Madeira-Guaporé'),
	('1100346','Alvorada D\'Oeste','RO','Leste Rondoniense'),
	('1100379','Alto Alegre dos Parecis','RO','Leste Rondoniense'),
	('1100403','Alto Paraíso','RO','Leste Rondoniense'),
	('1100452','Buritis','RO','Madeira-Guaporé'),
	('1100502','Novo Horizonte do Oeste','RO','Leste Rondoniense'),
	('1100601','Cacaulândia','RO','Leste Rondoniense'),
	('1100700','Campo Novo de Rondônia','RO','Madeira-Guaporé'),
	('1100809','Candeias do Jamari','RO','Madeira-Guaporé'),
	('1100908','Castanheiras','RO','Leste Rondoniense'),
	('1100924','Chupinguaia','RO','Leste Rondoniense'),
	('1100940','Cujubim','RO','Madeira-Guaporé'),
	('1101005','Governador Jorge Teixeira','RO','Leste Rondoniense'),
	('1101104','Itapuã do Oeste','RO','Madeira-Guaporé'),
	('1101203','Ministro Andreazza','RO','Leste Rondoniense'),
	('1101302','Mirante da Serra','RO','Leste Rondoniense'),
	('1101401','Monte Negro','RO','Leste Rondoniense'),
	('1101435','Nova União','RO','Leste Rondoniense'),
	('1101450','Parecis','RO','Leste Rondoniense'),
	('1101468','Pimenteiras do Oeste','RO','Leste Rondoniense'),
	('1101476','Primavera de Rondônia','RO','Leste Rondoniense'),
	('1101484','São Felipe D\'Oeste','RO','Leste Rondoniense'),
	('1101492','São Francisco do Guaporé','RO','Madeira-Guaporé'),
	('1101500','Seringueiras','RO','Leste Rondoniense'),
	('1101559','Teixeirópolis','RO','Leste Rondoniense'),
	('1101609','Theobroma','RO','Leste Rondoniense'),
	('1101708','Urupá','RO','Leste Rondoniense'),
	('1101757','Vale do Anari','RO','Leste Rondoniense'),
	('1101807','Vale do Paraíso','RO','Leste Rondoniense'),
	('1200013','Acrelândia','AC','Vale do Acre'),
	('1200054','Assis Brasil','AC','Vale do Acre'),
	('1200104','Brasiléia','AC','Vale do Acre'),
	('1200138','Bujari','AC','Vale do Acre'),
	('1200179','Capixaba','AC','Vale do Acre'),
	('1200203','Cruzeiro do Sul','AC','Vale do Juruá'),
	('1200252','Epitaciolândia','AC','Vale do Acre'),
	('1200302','Feijó','AC','Vale do Juruá'),
	('1200328','Jordão','AC','Vale do Juruá'),
	('1200336','Mâncio Lima','AC','Vale do Juruá'),
	('1200344','Manoel Urbano','AC','Vale do Acre'),
	('1200351','Marechal Thaumaturgo','AC','Vale do Juruá'),
	('1200385','Plácido de Castro','AC','Vale do Acre'),
	('1200393','Porto Walter','AC','Vale do Juruá'),
	('1200401','Rio Branco','AC','Vale do Acre'),
	('1200427','Rodrigues Alves','AC','Vale do Juruá'),
	('1200435','Santa Rosa do Purus','AC','Vale do Acre'),
	('1200450','Senador Guiomard','AC','Vale do Acre'),
	('1200500','Sena Madureira','AC','Vale do Acre'),
	('1200609','Tarauacá','AC','Vale do Juruá'),
	('1200708','Xapuri','AC','Vale do Acre'),
	('1200807','Porto Acre','AC','Vale do Acre'),
	('1300029','Alvarães','AM','Centro Amazonense'),
	('1300060','Amaturá','AM','Sudoeste Amazonense'),
	('1300086','Anamã','AM','Centro Amazonense'),
	('1300102','Anori','AM','Centro Amazonense'),
	('1300144','Apuí','AM','Sul Amazonense'),
	('1300201','Atalaia do Norte','AM','Sudoeste Amazonense'),
	('1300300','Autazes','AM','Centro Amazonense'),
	('1300409','Barcelos','AM','Norte Amazonense'),
	('1300508','Barreirinha','AM','Centro Amazonense'),
	('1300607','Benjamin Constant','AM','Sudoeste Amazonense'),
	('1300631','Beruri','AM','Centro Amazonense'),
	('1300680','Boa Vista do Ramos','AM','Centro Amazonense'),
	('1300706','Boca do Acre','AM','Sul Amazonense'),
	('1300805','Borba','AM','Sul Amazonense'),
	('1300839','Caapiranga','AM','Centro Amazonense'),
	('1300904','Canutama','AM','Sul Amazonense'),
	('1301001','Carauari','AM','Sudoeste Amazonense'),
	('1301100','Careiro','AM','Centro Amazonense'),
	('1301159','Careiro da Várzea','AM','Centro Amazonense'),
	('1301209','Coari','AM','Centro Amazonense'),
	('1301308','Codajás','AM','Centro Amazonense'),
	('1301407','Eirunepé','AM','Sudoeste Amazonense'),
	('1301506','Envira','AM','Sudoeste Amazonense'),
	('1301605','Fonte Boa','AM','Sudoeste Amazonense'),
	('1301654','Guajará','AM','Sudoeste Amazonense'),
	('1301704','Humaitá','AM','Sul Amazonense'),
	('1301803','Ipixuna','AM','Sudoeste Amazonense'),
	('1301852','Iranduba','AM','Centro Amazonense'),
	('1301902','Itacoatiara','AM','Centro Amazonense'),
	('1301951','Itamarati','AM','Sudoeste Amazonense'),
	('1302009','Itapiranga','AM','Centro Amazonense'),
	('1302108','Japurá','AM','Norte Amazonense'),
	('1302207','Juruá','AM','Sudoeste Amazonense'),
	('1302306','Jutaí','AM','Sudoeste Amazonense'),
	('1302405','Lábrea','AM','Sul Amazonense'),
	('1302504','Manacapuru','AM','Centro Amazonense'),
	('1302553','Manaquiri','AM','Centro Amazonense'),
	('1302603','Manaus','AM','Centro Amazonense'),
	('1302702','Manicoré','AM','Sul Amazonense'),
	('1302801','Maraã','AM','Norte Amazonense'),
	('1302900','Maués','AM','Centro Amazonense'),
	('1303007','Nhamundá','AM','Centro Amazonense'),
	('1303106','Nova Olinda do Norte','AM','Centro Amazonense'),
	('1303205','Novo Airão','AM','Norte Amazonense'),
	('1303304','Novo Aripuanã','AM','Sul Amazonense'),
	('1303403','Parintins','AM','Centro Amazonense'),
	('1303502','Pauini','AM','Sul Amazonense'),
	('1303536','Presidente Figueiredo','AM','Centro Amazonense'),
	('1303569','Rio Preto da Eva','AM','Centro Amazonense'),
	('1303601','Santa Isabel do Rio Negro','AM','Norte Amazonense'),
	('1303700','Santo Antônio do Içá','AM','Sudoeste Amazonense'),
	('1303809','São Gabriel da Cachoeira','AM','Norte Amazonense'),
	('1303908','São Paulo de Olivença','AM','Sudoeste Amazonense'),
	('1303957','São Sebastião do Uatumã','AM','Centro Amazonense'),
	('1304005','Silves','AM','Centro Amazonense'),
	('1304062','Tabatinga','AM','Sudoeste Amazonense'),
	('1304104','Tapauá','AM','Sul Amazonense'),
	('1304203','Tefé','AM','Centro Amazonense'),
	('1304237','Tonantins','AM','Sudoeste Amazonense'),
	('1304260','Uarini','AM','Centro Amazonense'),
	('1304302','Urucará','AM','Centro Amazonense'),
	('1304401','Urucurituba','AM','Centro Amazonense'),
	('1400027','Amajari','RR','Norte de Roraima'),
	('1400050','Alto Alegre','RR','Norte de Roraima'),
	('1400100','Boa Vista','RR','Norte de Roraima'),
	('1400159','Bonfim','RR','Norte de Roraima'),
	('1400175','Cantá','RR','Norte de Roraima'),
	('1400209','Caracaraí','RR','Sul de Roraima'),
	('1400233','Caroebe','RR','Sul de Roraima'),
	('1400282','Iracema','RR','Sul de Roraima'),
	('1400308','Mucajaí','RR','Sul de Roraima'),
	('1400407','Normandia','RR','Norte de Roraima'),
	('1400456','Pacaraima','RR','Norte de Roraima'),
	('1400472','Rorainópolis','RR','Sul de Roraima'),
	('1400506','São João da Baliza','RR','Sul de Roraima'),
	('1400605','São Luiz','RR','Sul de Roraima'),
	('1400704','Uiramutã','RR','Norte de Roraima'),
	('1500107','Abaetetuba','PA','Nordeste Paraense'),
	('1500131','Abel Figueiredo','PA','Sudeste Paraense'),
	('1500206','Acará','PA','Nordeste Paraense'),
	('1500305','Afuá','PA','Marajó'),
	('1500347','Água Azul do Norte','PA','Sudeste Paraense'),
	('1500404','Alenquer','PA','Baixo Amazonas'),
	('1500503','Almeirim','PA','Baixo Amazonas'),
	('1500602','Altamira','PA','Sudoeste Paraense'),
	('1500701','Anajás','PA','Marajó'),
	('1500800','Ananindeua','PA','Metropolitana de Belém'),
	('1500859','Anapu','PA','Sudoeste Paraense'),
	('1500909','Augusto Corrêa','PA','Nordeste Paraense'),
	('1500958','Aurora do Pará','PA','Nordeste Paraense'),
	('1501006','Aveiro','PA','Sudoeste Paraense'),
	('1501105','Bagre','PA','Marajó'),
	('1501204','Baião','PA','Nordeste Paraense'),
	('1501253','Bannach','PA','Sudeste Paraense'),
	('1501303','Barcarena','PA','Metropolitana de Belém'),
	('1501402','Belém','PA','Metropolitana de Belém'),
	('1501451','Belterra','PA','Baixo Amazonas'),
	('1501501','Benevides','PA','Metropolitana de Belém'),
	('1501576','Bom Jesus do Tocantins','PA','Sudeste Paraense'),
	('1501600','Bonito','PA','Nordeste Paraense'),
	('1501709','Bragança','PA','Nordeste Paraense'),
	('1501725','Brasil Novo','PA','Sudoeste Paraense'),
	('1501758','Brejo Grande do Araguaia','PA','Sudeste Paraense'),
	('1501782','Breu Branco','PA','Sudeste Paraense'),
	('1501808','Breves','PA','Marajó'),
	('1501907','Bujaru','PA','Metropolitana de Belém'),
	('1501956','Cachoeira do Piriá','PA','Nordeste Paraense'),
	('1502004','Cachoeira do Arari','PA','Marajó'),
	('1502103','Cametá','PA','Nordeste Paraense'),
	('1502152','Canaã dos Carajás','PA','Sudeste Paraense'),
	('1502202','Capanema','PA','Nordeste Paraense'),
	('1502301','Capitão Poço','PA','Nordeste Paraense'),
	('1502400','Castanhal','PA','Metropolitana de Belém'),
	('1502509','Chaves','PA','Marajó'),
	('1502608','Colares','PA','Nordeste Paraense'),
	('1502707','Conceição do Araguaia','PA','Sudeste Paraense'),
	('1502756','Concórdia do Pará','PA','Nordeste Paraense'),
	('1502764','Cumaru do Norte','PA','Sudeste Paraense'),
	('1502772','Curionópolis','PA','Sudeste Paraense'),
	('1502806','Curralinho','PA','Marajó'),
	('1502855','Curuá','PA','Baixo Amazonas'),
	('1502905','Curuçá','PA','Nordeste Paraense'),
	('1502939','Dom Eliseu','PA','Sudeste Paraense'),
	('1502954','Eldorado do Carajás','PA','Sudeste Paraense'),
	('1503002','Faro','PA','Baixo Amazonas'),
	('1503044','Floresta do Araguaia','PA','Sudeste Paraense'),
	('1503077','Garrafão do Norte','PA','Nordeste Paraense'),
	('1503093','Goianésia do Pará','PA','Sudeste Paraense'),
	('1503101','Gurupá','PA','Marajó'),
	('1503200','Igarapé-Açu','PA','Nordeste Paraense'),
	('1503309','Igarapé-Miri','PA','Nordeste Paraense'),
	('1503408','Inhangapi','PA','Metropolitana de Belém'),
	('1503457','Ipixuna do Pará','PA','Nordeste Paraense'),
	('1503507','Irituia','PA','Nordeste Paraense'),
	('1503606','Itaituba','PA','Sudoeste Paraense'),
	('1503705','Itupiranga','PA','Sudeste Paraense'),
	('1503754','Jacareacanga','PA','Sudoeste Paraense'),
	('1503804','Jacundá','PA','Sudeste Paraense'),
	('1503903','Juruti','PA','Baixo Amazonas'),
	('1504000','Limoeiro do Ajuru','PA','Nordeste Paraense'),
	('1504059','Mãe do Rio','PA','Nordeste Paraense'),
	('1504109','Magalhães Barata','PA','Nordeste Paraense'),
	('1504208','Marabá','PA','Sudeste Paraense'),
	('1504307','Maracanã','PA','Nordeste Paraense'),
	('1504406','Marapanim','PA','Nordeste Paraense'),
	('1504422','Marituba','PA','Metropolitana de Belém'),
	('1504455','Medicilândia','PA','Sudoeste Paraense'),
	('1504505','Melgaço','PA','Marajó'),
	('1504604','Mocajuba','PA','Nordeste Paraense'),
	('1504703','Moju','PA','Nordeste Paraense'),
	('1504752','Mojuí dos Campos','PA','Baixo Amazonas'),
	('1504802','Monte Alegre','PA','Baixo Amazonas'),
	('1504901','Muaná','PA','Marajó'),
	('1504950','Nova Esperança do Piriá','PA','Nordeste Paraense'),
	('1504976','Nova Ipixuna','PA','Sudeste Paraense'),
	('1505007','Nova Timboteua','PA','Nordeste Paraense'),
	('1505031','Novo Progresso','PA','Sudoeste Paraense'),
	('1505064','Novo Repartimento','PA','Sudeste Paraense'),
	('1505106','Óbidos','PA','Baixo Amazonas'),
	('1505205','Oeiras do Pará','PA','Nordeste Paraense'),
	('1505304','Oriximiná','PA','Baixo Amazonas'),
	('1505403','Ourém','PA','Nordeste Paraense'),
	('1505437','Ourilândia do Norte','PA','Sudeste Paraense'),
	('1505486','Pacajá','PA','Sudoeste Paraense'),
	('1505494','Palestina do Pará','PA','Sudeste Paraense'),
	('1505502','Paragominas','PA','Sudeste Paraense'),
	('1505536','Parauapebas','PA','Sudeste Paraense'),
	('1505551','Pau D\'Arco','PA','Sudeste Paraense'),
	('1505601','Peixe-Boi','PA','Nordeste Paraense'),
	('1505635','Piçarra','PA','Sudeste Paraense'),
	('1505650','Placas','PA','Baixo Amazonas'),
	('1505700','Ponta de Pedras','PA','Marajó'),
	('1505809','Portel','PA','Marajó'),
	('1505908','Porto de Moz','PA','Baixo Amazonas'),
	('1506005','Prainha','PA','Baixo Amazonas'),
	('1506104','Primavera','PA','Nordeste Paraense'),
	('1506112','Quatipuru','PA','Nordeste Paraense'),
	('1506138','Redenção','PA','Sudeste Paraense'),
	('1506161','Rio Maria','PA','Sudeste Paraense'),
	('1506187','Rondon do Pará','PA','Sudeste Paraense'),
	('1506195','Rurópolis','PA','Sudoeste Paraense'),
	('1506203','Salinópolis','PA','Nordeste Paraense'),
	('1506302','Salvaterra','PA','Marajó'),
	('1506351','Santa Bárbara do Pará','PA','Metropolitana de Belém'),
	('1506401','Santa Cruz do Arari','PA','Marajó'),
	('1506500','Santa Izabel do Pará','PA','Metropolitana de Belém'),
	('1506559','Santa Luzia do Pará','PA','Nordeste Paraense'),
	('1506583','Santa Maria das Barreiras','PA','Sudeste Paraense'),
	('1506609','Santa Maria do Pará','PA','Nordeste Paraense'),
	('1506708','Santana do Araguaia','PA','Sudeste Paraense'),
	('1506807','Santarém','PA','Baixo Amazonas'),
	('1506906','Santarém Novo','PA','Nordeste Paraense'),
	('1507003','Santo Antônio do Tauá','PA','Metropolitana de Belém'),
	('1507102','São Caetano de Odivelas','PA','Nordeste Paraense'),
	('1507151','São Domingos do Araguaia','PA','Sudeste Paraense'),
	('1507201','São Domingos do Capim','PA','Nordeste Paraense'),
	('1507300','São Félix do Xingu','PA','Sudeste Paraense'),
	('1507409','São Francisco do Pará','PA','Nordeste Paraense'),
	('1507458','São Geraldo do Araguaia','PA','Sudeste Paraense'),
	('1507466','São João da Ponta','PA','Nordeste Paraense'),
	('1507474','São João de Pirabas','PA','Nordeste Paraense'),
	('1507508','São João do Araguaia','PA','Sudeste Paraense'),
	('1507607','São Miguel do Guamá','PA','Nordeste Paraense'),
	('1507706','São Sebastião da Boa Vista','PA','Marajó'),
	('1507755','Sapucaia','PA','Sudeste Paraense'),
	('1507805','Senador José Porfírio','PA','Sudoeste Paraense'),
	('1507904','Soure','PA','Marajó'),
	('1507953','Tailândia','PA','Nordeste Paraense'),
	('1507961','Terra Alta','PA','Nordeste Paraense'),
	('1507979','Terra Santa','PA','Baixo Amazonas'),
	('1508001','Tomé-Açu','PA','Nordeste Paraense'),
	('1508035','Tracuateua','PA','Nordeste Paraense'),
	('1508050','Trairão','PA','Sudoeste Paraense'),
	('1508084','Tucumã','PA','Sudeste Paraense'),
	('1508100','Tucuruí','PA','Sudeste Paraense'),
	('1508126','Ulianópolis','PA','Sudeste Paraense'),
	('1508159','Uruará','PA','Sudoeste Paraense'),
	('1508209','Vigia','PA','Nordeste Paraense'),
	('1508308','Viseu','PA','Nordeste Paraense'),
	('1508357','Vitória do Xingu','PA','Sudoeste Paraense'),
	('1508407','Xinguara','PA','Sudeste Paraense'),
	('1600055','Serra do Navio','AP','Sul do Amapá'),
	('1600105','Amapá','AP','Norte do Amapá'),
	('1600154','Pedra Branca do Amapari','AP','Sul do Amapá'),
	('1600204','Calçoene','AP','Norte do Amapá'),
	('1600212','Cutias','AP','Sul do Amapá'),
	('1600238','Ferreira Gomes','AP','Sul do Amapá'),
	('1600253','Itaubal','AP','Sul do Amapá'),
	('1600279','Laranjal do Jari','AP','Sul do Amapá'),
	('1600303','Macapá','AP','Sul do Amapá'),
	('1600402','Mazagão','AP','Sul do Amapá'),
	('1600501','Oiapoque','AP','Norte do Amapá'),
	('1600535','Porto Grande','AP','Sul do Amapá'),
	('1600550','Pracuúba','AP','Norte do Amapá'),
	('1600600','Santana','AP','Sul do Amapá'),
	('1600709','Tartarugalzinho','AP','Norte do Amapá'),
	('1600808','Vitória do Jari','AP','Sul do Amapá'),
	('1700251','Abreulândia','TO','Ocidental do Tocantins'),
	('1700301','Aguiarnópolis','TO','Ocidental do Tocantins'),
	('1700350','Aliança do Tocantins','TO','Ocidental do Tocantins'),
	('1700400','Almas','TO','Oriental do Tocantins'),
	('1700707','Alvorada','TO','Ocidental do Tocantins'),
	('1701002','Ananás','TO','Ocidental do Tocantins'),
	('1701051','Angico','TO','Ocidental do Tocantins'),
	('1701101','Aparecida do Rio Negro','TO','Oriental do Tocantins'),
	('1701309','Aragominas','TO','Ocidental do Tocantins'),
	('1701903','Araguacema','TO','Ocidental do Tocantins'),
	('1702000','Araguaçu','TO','Ocidental do Tocantins'),
	('1702109','Araguaína','TO','Ocidental do Tocantins'),
	('1702158','Araguanã','TO','Ocidental do Tocantins'),
	('1702208','Araguatins','TO','Ocidental do Tocantins'),
	('1702307','Arapoema','TO','Ocidental do Tocantins'),
	('1702406','Arraias','TO','Oriental do Tocantins'),
	('1702554','Augustinópolis','TO','Ocidental do Tocantins'),
	('1702703','Aurora do Tocantins','TO','Oriental do Tocantins'),
	('1702901','Axixá do Tocantins','TO','Ocidental do Tocantins'),
	('1703008','Babaçulândia','TO','Ocidental do Tocantins'),
	('1703057','Bandeirantes do Tocantins','TO','Ocidental do Tocantins'),
	('1703073','Barra do Ouro','TO','Oriental do Tocantins'),
	('1703107','Barrolândia','TO','Ocidental do Tocantins'),
	('1703206','Bernardo Sayão','TO','Ocidental do Tocantins'),
	('1703305','Bom Jesus do Tocantins','TO','Oriental do Tocantins'),
	('1703602','Brasilândia do Tocantins','TO','Ocidental do Tocantins'),
	('1703701','Brejinho de Nazaré','TO','Ocidental do Tocantins'),
	('1703800','Buriti do Tocantins','TO','Ocidental do Tocantins'),
	('1703826','Cachoeirinha','TO','Ocidental do Tocantins'),
	('1703842','Campos Lindos','TO','Oriental do Tocantins'),
	('1703867','Cariri do Tocantins','TO','Ocidental do Tocantins'),
	('1703883','Carmolândia','TO','Ocidental do Tocantins'),
	('1703891','Carrasco Bonito','TO','Ocidental do Tocantins'),
	('1703909','Caseara','TO','Ocidental do Tocantins'),
	('1704105','Centenário','TO','Oriental do Tocantins'),
	('1704600','Chapada de Areia','TO','Ocidental do Tocantins'),
	('1705102','Chapada da Natividade','TO','Oriental do Tocantins'),
	('1705508','Colinas do Tocantins','TO','Ocidental do Tocantins'),
	('1705557','Combinado','TO','Oriental do Tocantins'),
	('1705607','Conceição do Tocantins','TO','Oriental do Tocantins'),
	('1706001','Couto Magalhães','TO','Ocidental do Tocantins'),
	('1706100','Cristalândia','TO','Ocidental do Tocantins'),
	('1706258','Crixás do Tocantins','TO','Ocidental do Tocantins'),
	('1706506','Darcinópolis','TO','Ocidental do Tocantins'),
	('1707009','Dianópolis','TO','Oriental do Tocantins'),
	('1707108','Divinópolis do Tocantins','TO','Ocidental do Tocantins'),
	('1707207','Dois Irmãos do Tocantins','TO','Ocidental do Tocantins'),
	('1707306','Dueré','TO','Ocidental do Tocantins'),
	('1707405','Esperantina','TO','Ocidental do Tocantins'),
	('1707553','Fátima','TO','Ocidental do Tocantins'),
	('1707652','Figueirópolis','TO','Ocidental do Tocantins'),
	('1707702','Filadélfia','TO','Ocidental do Tocantins'),
	('1708205','Formoso do Araguaia','TO','Ocidental do Tocantins'),
	('1708254','Fortaleza do Tabocão','TO','Ocidental do Tocantins'),
	('1708304','Goianorte','TO','Ocidental do Tocantins'),
	('1709005','Goiatins','TO','Oriental do Tocantins'),
	('1709302','Guaraí','TO','Ocidental do Tocantins'),
	('1709500','Gurupi','TO','Ocidental do Tocantins'),
	('1709807','Ipueiras','TO','Oriental do Tocantins'),
	('1710508','Itacajá','TO','Oriental do Tocantins'),
	('1710706','Itaguatins','TO','Ocidental do Tocantins'),
	('1710904','Itapiratins','TO','Oriental do Tocantins'),
	('1711100','Itaporã do Tocantins','TO','Ocidental do Tocantins'),
	('1711506','Jaú do Tocantins','TO','Ocidental do Tocantins'),
	('1711803','Juarina','TO','Ocidental do Tocantins'),
	('1711902','Lagoa da Confusão','TO','Ocidental do Tocantins'),
	('1711951','Lagoa do Tocantins','TO','Oriental do Tocantins'),
	('1712009','Lajeado','TO','Oriental do Tocantins'),
	('1712157','Lavandeira','TO','Oriental do Tocantins'),
	('1712405','Lizarda','TO','Oriental do Tocantins'),
	('1712454','Luzinópolis','TO','Ocidental do Tocantins'),
	('1712504','Marianópolis do Tocantins','TO','Ocidental do Tocantins'),
	('1712702','Mateiros','TO','Oriental do Tocantins'),
	('1712801','Maurilândia do Tocantins','TO','Ocidental do Tocantins'),
	('1713205','Miracema do Tocantins','TO','Ocidental do Tocantins'),
	('1713304','Miranorte','TO','Ocidental do Tocantins'),
	('1713601','Monte do Carmo','TO','Oriental do Tocantins'),
	('1713700','Monte Santo do Tocantins','TO','Ocidental do Tocantins'),
	('1713809','Palmeiras do Tocantins','TO','Ocidental do Tocantins'),
	('1713957','Muricilândia','TO','Ocidental do Tocantins'),
	('1714203','Natividade','TO','Oriental do Tocantins'),
	('1714302','Nazaré','TO','Ocidental do Tocantins'),
	('1714880','Nova Olinda','TO','Ocidental do Tocantins'),
	('1715002','Nova Rosalândia','TO','Ocidental do Tocantins'),
	('1715101','Novo Acordo','TO','Oriental do Tocantins'),
	('1715150','Novo Alegre','TO','Oriental do Tocantins'),
	('1715259','Novo Jardim','TO','Oriental do Tocantins'),
	('1715507','Oliveira de Fátima','TO','Ocidental do Tocantins'),
	('1715705','Palmeirante','TO','Ocidental do Tocantins'),
	('1715754','Palmeirópolis','TO','Ocidental do Tocantins'),
	('1716109','Paraíso do Tocantins','TO','Ocidental do Tocantins'),
	('1716208','Paranã','TO','Oriental do Tocantins'),
	('1716307','Pau D\'Arco','TO','Ocidental do Tocantins'),
	('1716505','Pedro Afonso','TO','Oriental do Tocantins'),
	('1716604','Peixe','TO','Ocidental do Tocantins'),
	('1716653','Pequizeiro','TO','Ocidental do Tocantins'),
	('1716703','Colméia','TO','Ocidental do Tocantins'),
	('1717008','Pindorama do Tocantins','TO','Oriental do Tocantins'),
	('1717206','Piraquê','TO','Ocidental do Tocantins'),
	('1717503','Pium','TO','Ocidental do Tocantins'),
	('1717800','Ponte Alta do Bom Jesus','TO','Oriental do Tocantins'),
	('1717909','Ponte Alta do Tocantins','TO','Oriental do Tocantins'),
	('1718006','Porto Alegre do Tocantins','TO','Oriental do Tocantins'),
	('1718204','Porto Nacional','TO','Oriental do Tocantins'),
	('1718303','Praia Norte','TO','Ocidental do Tocantins'),
	('1718402','Presidente Kennedy','TO','Ocidental do Tocantins'),
	('1718451','Pugmil','TO','Ocidental do Tocantins'),
	('1718501','Recursolândia','TO','Oriental do Tocantins'),
	('1718550','Riachinho','TO','Ocidental do Tocantins'),
	('1718659','Rio da Conceição','TO','Oriental do Tocantins'),
	('1718709','Rio dos Bois','TO','Ocidental do Tocantins'),
	('1718758','Rio Sono','TO','Oriental do Tocantins'),
	('1718808','Sampaio','TO','Ocidental do Tocantins'),
	('1718840','Sandolândia','TO','Ocidental do Tocantins'),
	('1718865','Santa Fé do Araguaia','TO','Ocidental do Tocantins'),
	('1718881','Santa Maria do Tocantins','TO','Oriental do Tocantins'),
	('1718899','Santa Rita do Tocantins','TO','Ocidental do Tocantins'),
	('1718907','Santa Rosa do Tocantins','TO','Oriental do Tocantins'),
	('1719004','Santa Tereza do Tocantins','TO','Oriental do Tocantins'),
	('1720002','Santa Terezinha do Tocantins','TO','Ocidental do Tocantins'),
	('1720101','São Bento do Tocantins','TO','Ocidental do Tocantins'),
	('1720150','São Félix do Tocantins','TO','Oriental do Tocantins'),
	('1720200','São Miguel do Tocantins','TO','Ocidental do Tocantins'),
	('1720259','São Salvador do Tocantins','TO','Ocidental do Tocantins'),
	('1720309','São Sebastião do Tocantins','TO','Ocidental do Tocantins'),
	('1720499','São Valério','TO','Oriental do Tocantins'),
	('1720655','Silvanópolis','TO','Oriental do Tocantins'),
	('1720804','Sítio Novo do Tocantins','TO','Ocidental do Tocantins'),
	('1720853','Sucupira','TO','Ocidental do Tocantins'),
	('1720903','Taguatinga','TO','Oriental do Tocantins'),
	('1720937','Taipas do Tocantins','TO','Oriental do Tocantins'),
	('1720978','Talismã','TO','Ocidental do Tocantins'),
	('1721000','Palmas','TO','Oriental do Tocantins'),
	('1721109','Tocantínia','TO','Oriental do Tocantins'),
	('1721208','Tocantinópolis','TO','Ocidental do Tocantins'),
	('1721257','Tupirama','TO','Ocidental do Tocantins'),
	('1721307','Tupiratins','TO','Ocidental do Tocantins'),
	('1722081','Wanderlândia','TO','Ocidental do Tocantins'),
	('1722107','Xambioá','TO','Ocidental do Tocantins'),
	('2100055','Açailândia','MA','Oeste Maranhense'),
	('2100105','Afonso Cunha','MA','Leste Maranhense'),
	('2100154','Água Doce do Maranhão','MA','Leste Maranhense'),
	('2100204','Alcântara','MA','Norte Maranhense'),
	('2100303','Aldeias Altas','MA','Leste Maranhense'),
	('2100402','Altamira do Maranhão','MA','Oeste Maranhense'),
	('2100436','Alto Alegre do Maranhão','MA','Leste Maranhense'),
	('2100477','Alto Alegre do Pindaré','MA','Oeste Maranhense'),
	('2100501','Alto Parnaíba','MA','Sul Maranhense'),
	('2100550','Amapá do Maranhão','MA','Oeste Maranhense'),
	('2100600','Amarante do Maranhão','MA','Oeste Maranhense'),
	('2100709','Anajatuba','MA','Norte Maranhense'),
	('2100808','Anapurus','MA','Leste Maranhense'),
	('2100832','Apicum-Açu','MA','Norte Maranhense'),
	('2100873','Araguanã','MA','Oeste Maranhense'),
	('2100907','Araioses','MA','Leste Maranhense'),
	('2100956','Arame','MA','Centro Maranhense'),
	('2101004','Arari','MA','Norte Maranhense'),
	('2101103','Axixá','MA','Norte Maranhense'),
	('2101202','Bacabal','MA','Centro Maranhense'),
	('2101251','Bacabeira','MA','Norte Maranhense'),
	('2101301','Bacuri','MA','Norte Maranhense'),
	('2101350','Bacurituba','MA','Norte Maranhense'),
	('2101400','Balsas','MA','Sul Maranhense'),
	('2101509','Barão de Grajaú','MA','Leste Maranhense'),
	('2101608','Barra do Corda','MA','Centro Maranhense'),
	('2101707','Barreirinhas','MA','Norte Maranhense'),
	('2101731','Belágua','MA','Leste Maranhense'),
	('2101772','Bela Vista do Maranhão','MA','Norte Maranhense'),
	('2101806','Benedito Leite','MA','Sul Maranhense'),
	('2101905','Bequimão','MA','Norte Maranhense'),
	('2101939','Bernardo do Mearim','MA','Centro Maranhense'),
	('2101970','Boa Vista do Gurupi','MA','Oeste Maranhense'),
	('2102002','Bom Jardim','MA','Oeste Maranhense'),
	('2102036','Bom Jesus das Selvas','MA','Oeste Maranhense'),
	('2102077','Bom Lugar','MA','Centro Maranhense'),
	('2102101','Brejo','MA','Leste Maranhense'),
	('2102150','Brejo de Areia','MA','Oeste Maranhense'),
	('2102200','Buriti','MA','Leste Maranhense'),
	('2102309','Buriti Bravo','MA','Leste Maranhense'),
	('2102325','Buriticupu','MA','Oeste Maranhense'),
	('2102358','Buritirana','MA','Oeste Maranhense'),
	('2102374','Cachoeira Grande','MA','Norte Maranhense'),
	('2102408','Cajapió','MA','Norte Maranhense'),
	('2102507','Cajari','MA','Norte Maranhense'),
	('2102556','Campestre do Maranhão','MA','Sul Maranhense'),
	('2102606','Cândido Mendes','MA','Oeste Maranhense'),
	('2102705','Cantanhede','MA','Norte Maranhense'),
	('2102754','Capinzal do Norte','MA','Leste Maranhense'),
	('2102804','Carolina','MA','Sul Maranhense'),
	('2102903','Carutapera','MA','Oeste Maranhense'),
	('2103000','Caxias','MA','Leste Maranhense'),
	('2103109','Cedral','MA','Norte Maranhense'),
	('2103125','Central do Maranhão','MA','Norte Maranhense'),
	('2103158','Centro do Guilherme','MA','Oeste Maranhense'),
	('2103174','Centro Novo do Maranhão','MA','Oeste Maranhense'),
	('2103208','Chapadinha','MA','Leste Maranhense'),
	('2103257','Cidelândia','MA','Oeste Maranhense'),
	('2103307','Codó','MA','Leste Maranhense'),
	('2103406','Coelho Neto','MA','Leste Maranhense'),
	('2103505','Colinas','MA','Leste Maranhense'),
	('2103554','Conceição do Lago-Açu','MA','Norte Maranhense'),
	('2103604','Coroatá','MA','Leste Maranhense'),
	('2103703','Cururupu','MA','Norte Maranhense'),
	('2103752','Davinópolis','MA','Oeste Maranhense'),
	('2103802','Dom Pedro','MA','Centro Maranhense'),
	('2103901','Duque Bacelar','MA','Leste Maranhense'),
	('2104008','Esperantinópolis','MA','Centro Maranhense'),
	('2104057','Estreito','MA','Sul Maranhense'),
	('2104073','Feira Nova do Maranhão','MA','Sul Maranhense'),
	('2104081','Fernando Falcão','MA','Centro Maranhense'),
	('2104099','Formosa da Serra Negra','MA','Centro Maranhense'),
	('2104107','Fortaleza dos Nogueiras','MA','Sul Maranhense'),
	('2104206','Fortuna','MA','Centro Maranhense'),
	('2104305','Godofredo Viana','MA','Oeste Maranhense'),
	('2104404','Gonçalves Dias','MA','Centro Maranhense'),
	('2104503','Governador Archer','MA','Centro Maranhense'),
	('2104552','Governador Edison Lobão','MA','Oeste Maranhense'),
	('2104602','Governador Eugênio Barros','MA','Centro Maranhense'),
	('2104628','Governador Luiz Rocha','MA','Centro Maranhense'),
	('2104651','Governador Newton Bello','MA','Oeste Maranhense'),
	('2104677','Governador Nunes Freire','MA','Oeste Maranhense'),
	('2104701','Graça Aranha','MA','Centro Maranhense'),
	('2104800','Grajaú','MA','Centro Maranhense'),
	('2104909','Guimarães','MA','Norte Maranhense'),
	('2105005','Humberto de Campos','MA','Norte Maranhense'),
	('2105104','Icatu','MA','Norte Maranhense'),
	('2105153','Igarapé do Meio','MA','Norte Maranhense'),
	('2105203','Igarapé Grande','MA','Centro Maranhense'),
	('2105302','Imperatriz','MA','Oeste Maranhense'),
	('2105351','Itaipava do Grajaú','MA','Centro Maranhense'),
	('2105401','Itapecuru Mirim','MA','Norte Maranhense'),
	('2105427','Itinga do Maranhão','MA','Oeste Maranhense'),
	('2105450','Jatobá','MA','Leste Maranhense'),
	('2105476','Jenipapo dos Vieiras','MA','Centro Maranhense'),
	('2105500','João Lisboa','MA','Oeste Maranhense'),
	('2105609','Joselândia','MA','Centro Maranhense'),
	('2105658','Junco do Maranhão','MA','Oeste Maranhense'),
	('2105708','Lago da Pedra','MA','Oeste Maranhense'),
	('2105807','Lago do Junco','MA','Centro Maranhense'),
	('2105906','Lago Verde','MA','Centro Maranhense'),
	('2105922','Lagoa do Mato','MA','Leste Maranhense'),
	('2105948','Lago dos Rodrigues','MA','Centro Maranhense'),
	('2105963','Lagoa Grande do Maranhão','MA','Oeste Maranhense'),
	('2105989','Lajeado Novo','MA','Oeste Maranhense'),
	('2106003','Lima Campos','MA','Centro Maranhense'),
	('2106102','Loreto','MA','Sul Maranhense'),
	('2106201','Luís Domingues','MA','Oeste Maranhense'),
	('2106300','Magalhães de Almeida','MA','Leste Maranhense'),
	('2106326','Maracaçumé','MA','Oeste Maranhense'),
	('2106359','Marajá do Sena','MA','Oeste Maranhense'),
	('2106375','Maranhãozinho','MA','Oeste Maranhense'),
	('2106409','Mata Roma','MA','Leste Maranhense'),
	('2106508','Matinha','MA','Norte Maranhense'),
	('2106607','Matões','MA','Leste Maranhense'),
	('2106631','Matões do Norte','MA','Norte Maranhense'),
	('2106672','Milagres do Maranhão','MA','Leste Maranhense'),
	('2106706','Mirador','MA','Leste Maranhense'),
	('2106755','Miranda do Norte','MA','Norte Maranhense'),
	('2106805','Mirinzal','MA','Norte Maranhense'),
	('2106904','Monção','MA','Norte Maranhense'),
	('2107001','Montes Altos','MA','Oeste Maranhense'),
	('2107100','Morros','MA','Norte Maranhense'),
	('2107209','Nina Rodrigues','MA','Norte Maranhense'),
	('2107258','Nova Colinas','MA','Sul Maranhense'),
	('2107308','Nova Iorque','MA','Leste Maranhense'),
	('2107357','Nova Olinda do Maranhão','MA','Oeste Maranhense'),
	('2107407','Olho d\'Água das Cunhãs','MA','Centro Maranhense'),
	('2107456','Olinda Nova do Maranhão','MA','Norte Maranhense'),
	('2107506','Paço do Lumiar','MA','Norte Maranhense'),
	('2107605','Palmeirândia','MA','Norte Maranhense'),
	('2107704','Paraibano','MA','Leste Maranhense'),
	('2107803','Parnarama','MA','Leste Maranhense'),
	('2107902','Passagem Franca','MA','Leste Maranhense'),
	('2108009','Pastos Bons','MA','Leste Maranhense'),
	('2108058','Paulino Neves','MA','Norte Maranhense'),
	('2108108','Paulo Ramos','MA','Oeste Maranhense'),
	('2108207','Pedreiras','MA','Centro Maranhense'),
	('2108256','Pedro do Rosário','MA','Norte Maranhense'),
	('2108306','Penalva','MA','Norte Maranhense'),
	('2108405','Peri Mirim','MA','Norte Maranhense'),
	('2108454','Peritoró','MA','Leste Maranhense'),
	('2108504','Pindaré-Mirim','MA','Oeste Maranhense'),
	('2108603','Pinheiro','MA','Norte Maranhense'),
	('2108702','Pio XII','MA','Centro Maranhense'),
	('2108801','Pirapemas','MA','Norte Maranhense'),
	('2108900','Poção de Pedras','MA','Centro Maranhense'),
	('2109007','Porto Franco','MA','Sul Maranhense'),
	('2109056','Porto Rico do Maranhão','MA','Norte Maranhense'),
	('2109106','Presidente Dutra','MA','Centro Maranhense'),
	('2109205','Presidente Juscelino','MA','Norte Maranhense'),
	('2109239','Presidente Médici','MA','Oeste Maranhense'),
	('2109270','Presidente Sarney','MA','Norte Maranhense'),
	('2109304','Presidente Vargas','MA','Norte Maranhense'),
	('2109403','Primeira Cruz','MA','Norte Maranhense'),
	('2109452','Raposa','MA','Norte Maranhense'),
	('2109502','Riachão','MA','Sul Maranhense'),
	('2109551','Ribamar Fiquene','MA','Oeste Maranhense'),
	('2109601','Rosário','MA','Norte Maranhense'),
	('2109700','Sambaíba','MA','Sul Maranhense'),
	('2109759','Santa Filomena do Maranhão','MA','Centro Maranhense'),
	('2109809','Santa Helena','MA','Norte Maranhense'),
	('2109908','Santa Inês','MA','Oeste Maranhense'),
	('2110005','Santa Luzia','MA','Oeste Maranhense'),
	('2110039','Santa Luzia do Paruá','MA','Oeste Maranhense'),
	('2110104','Santa Quitéria do Maranhão','MA','Leste Maranhense'),
	('2110203','Santa Rita','MA','Norte Maranhense'),
	('2110237','Santana do Maranhão','MA','Leste Maranhense'),
	('2110278','Santo Amaro do Maranhão','MA','Norte Maranhense'),
	('2110302','Santo Antônio dos Lopes','MA','Centro Maranhense'),
	('2110401','São Benedito do Rio Preto','MA','Leste Maranhense'),
	('2110500','São Bento','MA','Norte Maranhense'),
	('2110609','São Bernardo','MA','Leste Maranhense'),
	('2110658','São Domingos do Azeitão','MA','Sul Maranhense'),
	('2110708','São Domingos do Maranhão','MA','Centro Maranhense'),
	('2110807','São Félix de Balsas','MA','Sul Maranhense'),
	('2110856','São Francisco do Brejão','MA','Oeste Maranhense'),
	('2110906','São Francisco do Maranhão','MA','Leste Maranhense'),
	('2111003','São João Batista','MA','Norte Maranhense'),
	('2111029','São João do Carú','MA','Oeste Maranhense'),
	('2111052','São João do Paraíso','MA','Sul Maranhense'),
	('2111078','São João do Soter','MA','Leste Maranhense'),
	('2111102','São João dos Patos','MA','Leste Maranhense'),
	('2111201','São José de Ribamar','MA','Norte Maranhense'),
	('2111250','São José dos Basílios','MA','Centro Maranhense'),
	('2111300','São Luís','MA','Norte Maranhense'),
	('2111409','São Luís Gonzaga do Maranhão','MA','Centro Maranhense'),
	('2111508','São Mateus do Maranhão','MA','Centro Maranhense'),
	('2111532','São Pedro da Água Branca','MA','Oeste Maranhense'),
	('2111573','São Pedro dos Crentes','MA','Sul Maranhense'),
	('2111607','São Raimundo das Mangabeiras','MA','Sul Maranhense'),
	('2111631','São Raimundo do Doca Bezerra','MA','Centro Maranhense'),
	('2111672','São Roberto','MA','Centro Maranhense'),
	('2111706','São Vicente Ferrer','MA','Norte Maranhense'),
	('2111722','Satubinha','MA','Centro Maranhense'),
	('2111748','Senador Alexandre Costa','MA','Centro Maranhense'),
	('2111763','Senador La Rocque','MA','Oeste Maranhense'),
	('2111789','Serrano do Maranhão','MA','Norte Maranhense'),
	('2111805','Sítio Novo','MA','Centro Maranhense'),
	('2111904','Sucupira do Norte','MA','Leste Maranhense'),
	('2111953','Sucupira do Riachão','MA','Leste Maranhense'),
	('2112001','Tasso Fragoso','MA','Sul Maranhense'),
	('2112100','Timbiras','MA','Leste Maranhense'),
	('2112209','Timon','MA','Leste Maranhense'),
	('2112233','Trizidela do Vale','MA','Centro Maranhense'),
	('2112274','Tufilândia','MA','Oeste Maranhense'),
	('2112308','Tuntum','MA','Centro Maranhense'),
	('2112407','Turiaçu','MA','Oeste Maranhense'),
	('2112456','Turilândia','MA','Oeste Maranhense'),
	('2112506','Tutóia','MA','Norte Maranhense'),
	('2112605','Urbano Santos','MA','Leste Maranhense'),
	('2112704','Vargem Grande','MA','Norte Maranhense'),
	('2112803','Viana','MA','Norte Maranhense'),
	('2112852','Vila Nova dos Martírios','MA','Oeste Maranhense'),
	('2112902','Vitória do Mearim','MA','Norte Maranhense'),
	('2113009','Vitorino Freire','MA','Oeste Maranhense'),
	('2114007','Zé Doca','MA','Oeste Maranhense'),
	('2200053','Acauã','PI','Sudeste Piauiense'),
	('2200103','Agricolândia','PI','Centro-Norte Piauiense'),
	('2200202','Água Branca','PI','Centro-Norte Piauiense'),
	('2200251','Alagoinha do Piauí','PI','Sudeste Piauiense'),
	('2200277','Alegrete do Piauí','PI','Sudeste Piauiense'),
	('2200301','Alto Longá','PI','Centro-Norte Piauiense'),
	('2200400','Altos','PI','Centro-Norte Piauiense'),
	('2200459','Alvorada do Gurguéia','PI','Sudoeste Piauiense'),
	('2200509','Amarante','PI','Centro-Norte Piauiense'),
	('2200608','Angical do Piauí','PI','Centro-Norte Piauiense'),
	('2200707','Anísio de Abreu','PI','Sudoeste Piauiense'),
	('2200806','Antônio Almeida','PI','Sudoeste Piauiense'),
	('2200905','Aroazes','PI','Centro-Norte Piauiense'),
	('2200954','Aroeiras do Itaim','PI','Sudeste Piauiense'),
	('2201002','Arraial','PI','Centro-Norte Piauiense'),
	('2201051','Assunção do Piauí','PI','Centro-Norte Piauiense'),
	('2201101','Avelino Lopes','PI','Sudoeste Piauiense'),
	('2201150','Baixa Grande do Ribeiro','PI','Sudoeste Piauiense'),
	('2201176','Barra D\'Alcântara','PI','Centro-Norte Piauiense'),
	('2201200','Barras','PI','Norte Piauiense'),
	('2201309','Barreiras do Piauí','PI','Sudoeste Piauiense'),
	('2201408','Barro Duro','PI','Centro-Norte Piauiense'),
	('2201507','Batalha','PI','Norte Piauiense'),
	('2201556','Bela Vista do Piauí','PI','Sudeste Piauiense'),
	('2201572','Belém do Piauí','PI','Sudeste Piauiense'),
	('2201606','Beneditinos','PI','Centro-Norte Piauiense'),
	('2201705','Bertolínia','PI','Sudoeste Piauiense'),
	('2201739','Betânia do Piauí','PI','Sudeste Piauiense'),
	('2201770','Boa Hora','PI','Norte Piauiense'),
	('2201804','Bocaina','PI','Sudeste Piauiense'),
	('2201903','Bom Jesus','PI','Sudoeste Piauiense'),
	('2201919','Bom Princípio do Piauí','PI','Norte Piauiense'),
	('2201929','Bonfim do Piauí','PI','Sudoeste Piauiense'),
	('2201945','Boqueirão do Piauí','PI','Centro-Norte Piauiense'),
	('2201960','Brasileira','PI','Norte Piauiense'),
	('2201988','Brejo do Piauí','PI','Sudoeste Piauiense'),
	('2202000','Buriti dos Lopes','PI','Norte Piauiense'),
	('2202026','Buriti dos Montes','PI','Centro-Norte Piauiense'),
	('2202059','Cabeceiras do Piauí','PI','Norte Piauiense'),
	('2202075','Cajazeiras do Piauí','PI','Sudeste Piauiense'),
	('2202083','Cajueiro da Praia','PI','Norte Piauiense'),
	('2202091','Caldeirão Grande do Piauí','PI','Sudeste Piauiense'),
	('2202109','Campinas do Piauí','PI','Sudeste Piauiense'),
	('2202117','Campo Alegre do Fidalgo','PI','Sudeste Piauiense'),
	('2202133','Campo Grande do Piauí','PI','Sudeste Piauiense'),
	('2202174','Campo Largo do Piauí','PI','Norte Piauiense'),
	('2202208','Campo Maior','PI','Centro-Norte Piauiense'),
	('2202251','Canavieira','PI','Sudoeste Piauiense'),
	('2202307','Canto do Buriti','PI','Sudoeste Piauiense'),
	('2202406','Capitão de Campos','PI','Centro-Norte Piauiense'),
	('2202455','Capitão Gervásio Oliveira','PI','Sudeste Piauiense'),
	('2202505','Caracol','PI','Sudoeste Piauiense'),
	('2202539','Caraúbas do Piauí','PI','Norte Piauiense'),
	('2202554','Caridade do Piauí','PI','Sudeste Piauiense'),
	('2202604','Castelo do Piauí','PI','Centro-Norte Piauiense'),
	('2202653','Caxingó','PI','Norte Piauiense'),
	('2202703','Cocal','PI','Norte Piauiense'),
	('2202711','Cocal de Telha','PI','Centro-Norte Piauiense'),
	('2202729','Cocal dos Alves','PI','Norte Piauiense'),
	('2202737','Coivaras','PI','Centro-Norte Piauiense'),
	('2202752','Colônia do Gurguéia','PI','Sudoeste Piauiense'),
	('2202778','Colônia do Piauí','PI','Sudeste Piauiense'),
	('2202802','Conceição do Canindé','PI','Sudeste Piauiense'),
	('2202851','Coronel José Dias','PI','Sudoeste Piauiense'),
	('2202901','Corrente','PI','Sudoeste Piauiense'),
	('2203008','Cristalândia do Piauí','PI','Sudoeste Piauiense'),
	('2203107','Cristino Castro','PI','Sudoeste Piauiense'),
	('2203206','Curimatá','PI','Sudoeste Piauiense'),
	('2203230','Currais','PI','Sudoeste Piauiense'),
	('2203255','Curralinhos','PI','Centro-Norte Piauiense'),
	('2203271','Curral Novo do Piauí','PI','Sudeste Piauiense'),
	('2203305','Demerval Lobão','PI','Centro-Norte Piauiense'),
	('2203354','Dirceu Arcoverde','PI','Sudoeste Piauiense'),
	('2203404','Dom Expedito Lopes','PI','Sudeste Piauiense'),
	('2203420','Domingos Mourão','PI','Centro-Norte Piauiense'),
	('2203453','Dom Inocêncio','PI','Sudoeste Piauiense'),
	('2203503','Elesbão Veloso','PI','Centro-Norte Piauiense'),
	('2203602','Eliseu Martins','PI','Sudoeste Piauiense'),
	('2203701','Esperantina','PI','Norte Piauiense'),
	('2203750','Fartura do Piauí','PI','Sudoeste Piauiense'),
	('2203800','Flores do Piauí','PI','Sudoeste Piauiense'),
	('2203859','Floresta do Piauí','PI','Sudeste Piauiense'),
	('2203909','Floriano','PI','Sudoeste Piauiense'),
	('2204006','Francinópolis','PI','Centro-Norte Piauiense'),
	('2204105','Francisco Ayres','PI','Centro-Norte Piauiense'),
	('2204154','Francisco Macedo','PI','Sudeste Piauiense'),
	('2204204','Francisco Santos','PI','Sudeste Piauiense'),
	('2204303','Fronteiras','PI','Sudeste Piauiense'),
	('2204352','Geminiano','PI','Sudeste Piauiense'),
	('2204402','Gilbués','PI','Sudoeste Piauiense'),
	('2204501','Guadalupe','PI','Sudoeste Piauiense'),
	('2204550','Guaribas','PI','Sudoeste Piauiense'),
	('2204600','Hugo Napoleão','PI','Centro-Norte Piauiense'),
	('2204659','Ilha Grande','PI','Norte Piauiense'),
	('2204709','Inhuma','PI','Centro-Norte Piauiense'),
	('2204808','Ipiranga do Piauí','PI','Sudeste Piauiense'),
	('2204907','Isaías Coelho','PI','Sudeste Piauiense'),
	('2205003','Itainópolis','PI','Sudeste Piauiense'),
	('2205102','Itaueira','PI','Sudoeste Piauiense'),
	('2205151','Jacobina do Piauí','PI','Sudeste Piauiense'),
	('2205201','Jaicós','PI','Sudeste Piauiense'),
	('2205250','Jardim do Mulato','PI','Centro-Norte Piauiense'),
	('2205276','Jatobá do Piauí','PI','Centro-Norte Piauiense'),
	('2205300','Jerumenha','PI','Sudoeste Piauiense'),
	('2205359','João Costa','PI','Sudeste Piauiense'),
	('2205409','Joaquim Pires','PI','Norte Piauiense'),
	('2205458','Joca Marques','PI','Norte Piauiense'),
	('2205508','José de Freitas','PI','Centro-Norte Piauiense'),
	('2205516','Juazeiro do Piauí','PI','Centro-Norte Piauiense'),
	('2205524','Júlio Borges','PI','Sudoeste Piauiense'),
	('2205532','Jurema','PI','Sudoeste Piauiense'),
	('2205540','Lagoinha do Piauí','PI','Centro-Norte Piauiense'),
	('2205557','Lagoa Alegre','PI','Centro-Norte Piauiense'),
	('2205565','Lagoa do Barro do Piauí','PI','Sudeste Piauiense'),
	('2205573','Lagoa de São Francisco','PI','Centro-Norte Piauiense'),
	('2205581','Lagoa do Piauí','PI','Centro-Norte Piauiense'),
	('2205599','Lagoa do Sítio','PI','Centro-Norte Piauiense'),
	('2205607','Landri Sales','PI','Sudoeste Piauiense'),
	('2205706','Luís Correia','PI','Norte Piauiense'),
	('2205805','Luzilândia','PI','Norte Piauiense'),
	('2205854','Madeiro','PI','Norte Piauiense'),
	('2205904','Manoel Emídio','PI','Sudoeste Piauiense'),
	('2205953','Marcolândia','PI','Sudeste Piauiense'),
	('2206001','Marcos Parente','PI','Sudoeste Piauiense'),
	('2206050','Massapê do Piauí','PI','Sudeste Piauiense'),
	('2206100','Matias Olímpio','PI','Norte Piauiense'),
	('2206209','Miguel Alves','PI','Norte Piauiense'),
	('2206308','Miguel Leão','PI','Centro-Norte Piauiense'),
	('2206357','Milton Brandão','PI','Centro-Norte Piauiense'),
	('2206407','Monsenhor Gil','PI','Centro-Norte Piauiense'),
	('2206506','Monsenhor Hipólito','PI','Sudeste Piauiense'),
	('2206605','Monte Alegre do Piauí','PI','Sudoeste Piauiense'),
	('2206654','Morro Cabeça no Tempo','PI','Sudoeste Piauiense'),
	('2206670','Morro do Chapéu do Piauí','PI','Norte Piauiense'),
	('2206696','Murici dos Portelas','PI','Norte Piauiense'),
	('2206704','Nazaré do Piauí','PI','Sudoeste Piauiense'),
	('2206720','Nazária','PI','Centro-Norte Piauiense'),
	('2206753','Nossa Senhora de Nazaré','PI','Centro-Norte Piauiense'),
	('2206803','Nossa Senhora dos Remédios','PI','Norte Piauiense'),
	('2206902','Novo Oriente do Piauí','PI','Centro-Norte Piauiense'),
	('2206951','Novo Santo Antônio','PI','Centro-Norte Piauiense'),
	('2207009','Oeiras','PI','Sudeste Piauiense'),
	('2207108','Olho D\'Água do Piauí','PI','Centro-Norte Piauiense'),
	('2207207','Padre Marcos','PI','Sudeste Piauiense'),
	('2207306','Paes Landim','PI','Sudeste Piauiense'),
	('2207355','Pajeú do Piauí','PI','Sudoeste Piauiense'),
	('2207405','Palmeira do Piauí','PI','Sudoeste Piauiense'),
	('2207504','Palmeirais','PI','Centro-Norte Piauiense'),
	('2207553','Paquetá','PI','Sudeste Piauiense'),
	('2207603','Parnaguá','PI','Sudoeste Piauiense'),
	('2207702','Parnaíba','PI','Norte Piauiense'),
	('2207751','Passagem Franca do Piauí','PI','Centro-Norte Piauiense'),
	('2207777','Patos do Piauí','PI','Sudeste Piauiense'),
	('2207793','Pau D\'Arco do Piauí','PI','Centro-Norte Piauiense'),
	('2207801','Paulistana','PI','Sudeste Piauiense'),
	('2207850','Pavussu','PI','Sudoeste Piauiense'),
	('2207900','Pedro II','PI','Centro-Norte Piauiense'),
	('2207934','Pedro Laurentino','PI','Sudeste Piauiense'),
	('2207959','Nova Santa Rita','PI','Sudeste Piauiense'),
	('2208007','Picos','PI','Sudeste Piauiense'),
	('2208106','Pimenteiras','PI','Centro-Norte Piauiense'),
	('2208205','Pio IX','PI','Sudeste Piauiense'),
	('2208304','Piracuruca','PI','Norte Piauiense'),
	('2208403','Piripiri','PI','Norte Piauiense'),
	('2208502','Porto','PI','Norte Piauiense'),
	('2208551','Porto Alegre do Piauí','PI','Sudoeste Piauiense'),
	('2208601','Prata do Piauí','PI','Centro-Norte Piauiense'),
	('2208650','Queimada Nova','PI','Sudeste Piauiense'),
	('2208700','Redenção do Gurguéia','PI','Sudoeste Piauiense'),
	('2208809','Regeneração','PI','Centro-Norte Piauiense'),
	('2208858','Riacho Frio','PI','Sudoeste Piauiense'),
	('2208874','Ribeira do Piauí','PI','Sudeste Piauiense'),
	('2208908','Ribeiro Gonçalves','PI','Sudoeste Piauiense'),
	('2209005','Rio Grande do Piauí','PI','Sudoeste Piauiense'),
	('2209104','Santa Cruz do Piauí','PI','Sudeste Piauiense'),
	('2209153','Santa Cruz dos Milagres','PI','Centro-Norte Piauiense'),
	('2209203','Santa Filomena','PI','Sudoeste Piauiense'),
	('2209302','Santa Luz','PI','Sudoeste Piauiense'),
	('2209351','Santana do Piauí','PI','Sudeste Piauiense'),
	('2209377','Santa Rosa do Piauí','PI','Sudeste Piauiense'),
	('2209401','Santo Antônio de Lisboa','PI','Sudeste Piauiense'),
	('2209450','Santo Antônio dos Milagres','PI','Centro-Norte Piauiense'),
	('2209500','Santo Inácio do Piauí','PI','Sudeste Piauiense'),
	('2209559','São Braz do Piauí','PI','Sudoeste Piauiense'),
	('2209609','São Félix do Piauí','PI','Centro-Norte Piauiense'),
	('2209658','São Francisco de Assis do Piauí','PI','Sudeste Piauiense'),
	('2209708','São Francisco do Piauí','PI','Sudoeste Piauiense'),
	('2209757','São Gonçalo do Gurguéia','PI','Sudoeste Piauiense'),
	('2209807','São Gonçalo do Piauí','PI','Centro-Norte Piauiense'),
	('2209856','São João da Canabrava','PI','Sudeste Piauiense'),
	('2209872','São João da Fronteira','PI','Norte Piauiense'),
	('2209906','São João da Serra','PI','Centro-Norte Piauiense'),
	('2209955','São João da Varjota','PI','Sudeste Piauiense'),
	('2209971','São João do Arraial','PI','Norte Piauiense'),
	('2210003','São João do Piauí','PI','Sudeste Piauiense'),
	('2210052','São José do Divino','PI','Norte Piauiense'),
	('2210102','São José do Peixe','PI','Sudoeste Piauiense'),
	('2210201','São José do Piauí','PI','Sudeste Piauiense'),
	('2210300','São Julião','PI','Sudeste Piauiense'),
	('2210359','São Lourenço do Piauí','PI','Sudoeste Piauiense'),
	('2210375','São Luis do Piauí','PI','Sudeste Piauiense'),
	('2210383','São Miguel da Baixa Grande','PI','Centro-Norte Piauiense'),
	('2210391','São Miguel do Fidalgo','PI','Sudoeste Piauiense'),
	('2210409','São Miguel do Tapuio','PI','Centro-Norte Piauiense'),
	('2210508','São Pedro do Piauí','PI','Centro-Norte Piauiense'),
	('2210607','São Raimundo Nonato','PI','Sudoeste Piauiense'),
	('2210623','Sebastião Barros','PI','Sudoeste Piauiense'),
	('2210631','Sebastião Leal','PI','Sudoeste Piauiense'),
	('2210656','Sigefredo Pacheco','PI','Centro-Norte Piauiense'),
	('2210706','Simões','PI','Sudeste Piauiense'),
	('2210805','Simplício Mendes','PI','Sudeste Piauiense'),
	('2210904','Socorro do Piauí','PI','Sudeste Piauiense'),
	('2210938','Sussuapara','PI','Sudeste Piauiense'),
	('2210953','Tamboril do Piauí','PI','Sudoeste Piauiense'),
	('2210979','Tanque do Piauí','PI','Sudeste Piauiense'),
	('2211001','Teresina','PI','Centro-Norte Piauiense'),
	('2211100','União','PI','Centro-Norte Piauiense'),
	('2211209','Uruçuí','PI','Sudoeste Piauiense'),
	('2211308','Valença do Piauí','PI','Centro-Norte Piauiense'),
	('2211357','Várzea Branca','PI','Sudoeste Piauiense'),
	('2211407','Várzea Grande','PI','Centro-Norte Piauiense'),
	('2211506','Vera Mendes','PI','Sudeste Piauiense'),
	('2211605','Vila Nova do Piauí','PI','Sudeste Piauiense'),
	('2211704','Wall Ferraz','PI','Sudeste Piauiense'),
	('2300101','Abaiara','CE','Sul Cearense'),
	('2300150','Acarape','CE','Norte Cearense'),
	('2300200','Acaraú','CE','Noroeste Cearense'),
	('2300309','Acopiara','CE','Sertões Cearenses'),
	('2300408','Aiuaba','CE','Sertões Cearenses'),
	('2300507','Alcântaras','CE','Noroeste Cearense'),
	('2300606','Altaneira','CE','Sul Cearense'),
	('2300705','Alto Santo','CE','Jaguaribe'),
	('2300754','Amontada','CE','Norte Cearense'),
	('2300804','Antonina do Norte','CE','Centro-Sul Cearense'),
	('2300903','Apuiarés','CE','Norte Cearense'),
	('2301000','Aquiraz','CE','Metropolitana de Fortaleza'),
	('2301109','Aracati','CE','Jaguaribe'),
	('2301208','Aracoiaba','CE','Norte Cearense'),
	('2301257','Ararendá','CE','Sertões Cearenses'),
	('2301307','Araripe','CE','Sul Cearense'),
	('2301406','Aratuba','CE','Norte Cearense'),
	('2301505','Arneiroz','CE','Sertões Cearenses'),
	('2301604','Assaré','CE','Sul Cearense'),
	('2301703','Aurora','CE','Sul Cearense'),
	('2301802','Baixio','CE','Centro-Sul Cearense'),
	('2301851','Banabuiú','CE','Sertões Cearenses'),
	('2301901','Barbalha','CE','Sul Cearense'),
	('2301950','Barreira','CE','Norte Cearense'),
	('2302008','Barro','CE','Sul Cearense'),
	('2302057','Barroquinha','CE','Noroeste Cearense'),
	('2302107','Baturité','CE','Norte Cearense'),
	('2302206','Beberibe','CE','Norte Cearense'),
	('2302305','Bela Cruz','CE','Noroeste Cearense'),
	('2302404','Boa Viagem','CE','Sertões Cearenses'),
	('2302503','Brejo Santo','CE','Sul Cearense'),
	('2302602','Camocim','CE','Noroeste Cearense'),
	('2302701','Campos Sales','CE','Sul Cearense'),
	('2302800','Canindé','CE','Norte Cearense'),
	('2302909','Capistrano','CE','Norte Cearense'),
	('2303006','Caridade','CE','Norte Cearense'),
	('2303105','Cariré','CE','Noroeste Cearense'),
	('2303204','Caririaçu','CE','Sul Cearense'),
	('2303303','Cariús','CE','Centro-Sul Cearense'),
	('2303402','Carnaubal','CE','Noroeste Cearense'),
	('2303501','Cascavel','CE','Norte Cearense'),
	('2303600','Catarina','CE','Sertões Cearenses'),
	('2303659','Catunda','CE','Noroeste Cearense'),
	('2303709','Caucaia','CE','Metropolitana de Fortaleza'),
	('2303808','Cedro','CE','Centro-Sul Cearense'),
	('2303907','Chaval','CE','Noroeste Cearense'),
	('2303931','Choró','CE','Sertões Cearenses'),
	('2303956','Chorozinho','CE','Norte Cearense'),
	('2304004','Coreaú','CE','Noroeste Cearense'),
	('2304103','Crateús','CE','Sertões Cearenses'),
	('2304202','Crato','CE','Sul Cearense'),
	('2304236','Croatá','CE','Noroeste Cearense'),
	('2304251','Cruz','CE','Noroeste Cearense'),
	('2304269','Deputado Irapuan Pinheiro','CE','Sertões Cearenses'),
	('2304277','Ererê','CE','Jaguaribe'),
	('2304285','Eusébio','CE','Metropolitana de Fortaleza'),
	('2304301','Farias Brito','CE','Sul Cearense'),
	('2304350','Forquilha','CE','Noroeste Cearense'),
	('2304400','Fortaleza','CE','Metropolitana de Fortaleza'),
	('2304459','Fortim','CE','Jaguaribe'),
	('2304509','Frecheirinha','CE','Noroeste Cearense'),
	('2304608','General Sampaio','CE','Norte Cearense'),
	('2304657','Graça','CE','Noroeste Cearense'),
	('2304707','Granja','CE','Noroeste Cearense'),
	('2304806','Granjeiro','CE','Sul Cearense'),
	('2304905','Groaíras','CE','Noroeste Cearense'),
	('2304954','Guaiúba','CE','Metropolitana de Fortaleza'),
	('2305001','Guaraciaba do Norte','CE','Noroeste Cearense'),
	('2305100','Guaramiranga','CE','Norte Cearense'),
	('2305209','Hidrolândia','CE','Noroeste Cearense'),
	('2305233','Horizonte','CE','Metropolitana de Fortaleza'),
	('2305266','Ibaretama','CE','Sertões Cearenses'),
	('2305308','Ibiapina','CE','Noroeste Cearense'),
	('2305332','Ibicuitinga','CE','Jaguaribe'),
	('2305357','Icapuí','CE','Jaguaribe'),
	('2305407','Icó','CE','Centro-Sul Cearense'),
	('2305506','Iguatu','CE','Centro-Sul Cearense'),
	('2305605','Independência','CE','Sertões Cearenses'),
	('2305654','Ipaporanga','CE','Sertões Cearenses'),
	('2305704','Ipaumirim','CE','Centro-Sul Cearense'),
	('2305803','Ipu','CE','Noroeste Cearense'),
	('2305902','Ipueiras','CE','Noroeste Cearense'),
	('2306009','Iracema','CE','Jaguaribe'),
	('2306108','Irauçuba','CE','Noroeste Cearense'),
	('2306207','Itaiçaba','CE','Jaguaribe'),
	('2306256','Itaitinga','CE','Metropolitana de Fortaleza'),
	('2306306','Itapajé','CE','Norte Cearense'),
	('2306405','Itapipoca','CE','Norte Cearense'),
	('2306504','Itapiúna','CE','Norte Cearense'),
	('2306553','Itarema','CE','Noroeste Cearense'),
	('2306603','Itatira','CE','Norte Cearense'),
	('2306702','Jaguaretama','CE','Jaguaribe'),
	('2306801','Jaguaribara','CE','Jaguaribe'),
	('2306900','Jaguaribe','CE','Jaguaribe'),
	('2307007','Jaguaruana','CE','Jaguaribe'),
	('2307106','Jardim','CE','Sul Cearense'),
	('2307205','Jati','CE','Sul Cearense'),
	('2307254','Jijoca de Jericoacoara','CE','Noroeste Cearense'),
	('2307304','Juazeiro do Norte','CE','Sul Cearense'),
	('2307403','Jucás','CE','Centro-Sul Cearense'),
	('2307502','Lavras da Mangabeira','CE','Centro-Sul Cearense'),
	('2307601','Limoeiro do Norte','CE','Jaguaribe'),
	('2307635','Madalena','CE','Sertões Cearenses'),
	('2307650','Maracanaú','CE','Metropolitana de Fortaleza'),
	('2307700','Maranguape','CE','Metropolitana de Fortaleza'),
	('2307809','Marco','CE','Noroeste Cearense'),
	('2307908','Martinópole','CE','Noroeste Cearense'),
	('2308005','Massapê','CE','Noroeste Cearense'),
	('2308104','Mauriti','CE','Sul Cearense'),
	('2308203','Meruoca','CE','Noroeste Cearense'),
	('2308302','Milagres','CE','Sul Cearense'),
	('2308351','Milhã','CE','Sertões Cearenses'),
	('2308377','Miraíma','CE','Noroeste Cearense'),
	('2308401','Missão Velha','CE','Sul Cearense'),
	('2308500','Mombaça','CE','Sertões Cearenses'),
	('2308609','Monsenhor Tabosa','CE','Sertões Cearenses'),
	('2308708','Morada Nova','CE','Jaguaribe'),
	('2308807','Moraújo','CE','Noroeste Cearense'),
	('2308906','Morrinhos','CE','Noroeste Cearense'),
	('2309003','Mucambo','CE','Noroeste Cearense'),
	('2309102','Mulungu','CE','Norte Cearense'),
	('2309201','Nova Olinda','CE','Sul Cearense'),
	('2309300','Nova Russas','CE','Sertões Cearenses'),
	('2309409','Novo Oriente','CE','Sertões Cearenses'),
	('2309458','Ocara','CE','Norte Cearense'),
	('2309508','Orós','CE','Centro-Sul Cearense'),
	('2309607','Pacajus','CE','Metropolitana de Fortaleza'),
	('2309706','Pacatuba','CE','Metropolitana de Fortaleza'),
	('2309805','Pacoti','CE','Norte Cearense'),
	('2309904','Pacujá','CE','Noroeste Cearense'),
	('2310001','Palhano','CE','Jaguaribe'),
	('2310100','Palmácia','CE','Norte Cearense'),
	('2310209','Paracuru','CE','Norte Cearense'),
	('2310258','Paraipaba','CE','Norte Cearense'),
	('2310308','Parambu','CE','Sertões Cearenses'),
	('2310407','Paramoti','CE','Norte Cearense'),
	('2310506','Pedra Branca','CE','Sertões Cearenses'),
	('2310605','Penaforte','CE','Sul Cearense'),
	('2310704','Pentecoste','CE','Norte Cearense'),
	('2310803','Pereiro','CE','Jaguaribe'),
	('2310852','Pindoretama','CE','Norte Cearense'),
	('2310902','Piquet Carneiro','CE','Sertões Cearenses'),
	('2310951','Pires Ferreira','CE','Noroeste Cearense'),
	('2311009','Poranga','CE','Noroeste Cearense'),
	('2311108','Porteiras','CE','Sul Cearense'),
	('2311207','Potengi','CE','Sul Cearense'),
	('2311231','Potiretama','CE','Jaguaribe'),
	('2311264','Quiterianópolis','CE','Sertões Cearenses'),
	('2311306','Quixadá','CE','Sertões Cearenses'),
	('2311355','Quixelô','CE','Centro-Sul Cearense'),
	('2311405','Quixeramobim','CE','Sertões Cearenses'),
	('2311504','Quixeré','CE','Jaguaribe'),
	('2311603','Redenção','CE','Norte Cearense'),
	('2311702','Reriutaba','CE','Noroeste Cearense'),
	('2311801','Russas','CE','Jaguaribe'),
	('2311900','Saboeiro','CE','Sertões Cearenses'),
	('2311959','Salitre','CE','Sul Cearense'),
	('2312007','Santana do Acaraú','CE','Noroeste Cearense'),
	('2312106','Santana do Cariri','CE','Sul Cearense'),
	('2312205','Santa Quitéria','CE','Noroeste Cearense'),
	('2312304','São Benedito','CE','Noroeste Cearense'),
	('2312403','São Gonçalo do Amarante','CE','Norte Cearense'),
	('2312502','São João do Jaguaribe','CE','Jaguaribe'),
	('2312601','São Luís do Curu','CE','Norte Cearense'),
	('2312700','Senador Pompeu','CE','Sertões Cearenses'),
	('2312809','Senador Sá','CE','Noroeste Cearense'),
	('2312908','Sobral','CE','Noroeste Cearense'),
	('2313005','Solonópole','CE','Sertões Cearenses'),
	('2313104','Tabuleiro do Norte','CE','Jaguaribe'),
	('2313203','Tamboril','CE','Sertões Cearenses'),
	('2313252','Tarrafas','CE','Centro-Sul Cearense'),
	('2313302','Tauá','CE','Sertões Cearenses'),
	('2313351','Tejuçuoca','CE','Norte Cearense'),
	('2313401','Tianguá','CE','Noroeste Cearense'),
	('2313500','Trairi','CE','Norte Cearense'),
	('2313559','Tururu','CE','Norte Cearense'),
	('2313609','Ubajara','CE','Noroeste Cearense'),
	('2313708','Umari','CE','Centro-Sul Cearense'),
	('2313757','Umirim','CE','Norte Cearense'),
	('2313807','Uruburetama','CE','Norte Cearense'),
	('2313906','Uruoca','CE','Noroeste Cearense'),
	('2313955','Varjota','CE','Noroeste Cearense'),
	('2314003','Várzea Alegre','CE','Centro-Sul Cearense'),
	('2314102','Viçosa do Ceará','CE','Noroeste Cearense'),
	('2400109','Acari','RN','Central Potiguar'),
	('2400208','Açu','RN','Oeste Potiguar'),
	('2400307','Afonso Bezerra','RN','Central Potiguar'),
	('2400406','Água Nova','RN','Oeste Potiguar'),
	('2400505','Alexandria','RN','Oeste Potiguar'),
	('2400604','Almino Afonso','RN','Oeste Potiguar'),
	('2400703','Alto do Rodrigues','RN','Oeste Potiguar'),
	('2400802','Angicos','RN','Central Potiguar'),
	('2400901','Antônio Martins','RN','Oeste Potiguar'),
	('2401008','Apodi','RN','Oeste Potiguar'),
	('2401107','Areia Branca','RN','Oeste Potiguar'),
	('2401206','Arês','RN','Leste Potiguar'),
	('2401305','Augusto Severo','RN','Oeste Potiguar'),
	('2401404','Baía Formosa','RN','Leste Potiguar'),
	('2401453','Baraúna','RN','Oeste Potiguar'),
	('2401503','Barcelona','RN','Agreste Potiguar'),
	('2401602','Bento Fernandes','RN','Agreste Potiguar'),
	('2401651','Bodó','RN','Central Potiguar'),
	('2401701','Bom Jesus','RN','Agreste Potiguar'),
	('2401800','Brejinho','RN','Agreste Potiguar'),
	('2401859','Caiçara do Norte','RN','Central Potiguar'),
	('2401909','Caiçara do Rio do Vento','RN','Central Potiguar'),
	('2402006','Caicó','RN','Central Potiguar'),
	('2402105','Campo Redondo','RN','Agreste Potiguar'),
	('2402204','Canguaretama','RN','Leste Potiguar'),
	('2402303','Caraúbas','RN','Oeste Potiguar'),
	('2402402','Carnaúba dos Dantas','RN','Central Potiguar'),
	('2402501','Carnaubais','RN','Oeste Potiguar'),
	('2402600','Ceará-Mirim','RN','Leste Potiguar'),
	('2402709','Cerro Corá','RN','Central Potiguar'),
	('2402808','Coronel Ezequiel','RN','Agreste Potiguar'),
	('2402907','Coronel João Pessoa','RN','Oeste Potiguar'),
	('2403004','Cruzeta','RN','Central Potiguar'),
	('2403103','Currais Novos','RN','Central Potiguar'),
	('2403202','Doutor Severiano','RN','Oeste Potiguar'),
	('2403251','Parnamirim','RN','Leste Potiguar'),
	('2403301','Encanto','RN','Oeste Potiguar'),
	('2403400','Equador','RN','Central Potiguar'),
	('2403509','Espírito Santo','RN','Leste Potiguar'),
	('2403608','Extremoz','RN','Leste Potiguar'),
	('2403707','Felipe Guerra','RN','Oeste Potiguar'),
	('2403756','Fernando Pedroza','RN','Central Potiguar'),
	('2403806','Florânia','RN','Central Potiguar'),
	('2403905','Francisco Dantas','RN','Oeste Potiguar'),
	('2404002','Frutuoso Gomes','RN','Oeste Potiguar'),
	('2404101','Galinhos','RN','Central Potiguar'),
	('2404200','Goianinha','RN','Leste Potiguar'),
	('2404309','Governador Dix-Sept Rosado','RN','Oeste Potiguar'),
	('2404408','Grossos','RN','Oeste Potiguar'),
	('2404507','Guamaré','RN','Central Potiguar'),
	('2404606','Ielmo Marinho','RN','Agreste Potiguar'),
	('2404705','Ipanguaçu','RN','Oeste Potiguar'),
	('2404804','Ipueira','RN','Central Potiguar'),
	('2404853','Itajá','RN','Oeste Potiguar'),
	('2404903','Itaú','RN','Oeste Potiguar'),
	('2405009','Jaçanã','RN','Agreste Potiguar'),
	('2405108','Jandaíra','RN','Agreste Potiguar'),
	('2405207','Janduís','RN','Oeste Potiguar'),
	('2405306','Januário Cicco','RN','Agreste Potiguar'),
	('2405405','Japi','RN','Agreste Potiguar'),
	('2405504','Jardim de Angicos','RN','Central Potiguar'),
	('2405603','Jardim de Piranhas','RN','Central Potiguar'),
	('2405702','Jardim do Seridó','RN','Central Potiguar'),
	('2405801','João Câmara','RN','Agreste Potiguar'),
	('2405900','João Dias','RN','Oeste Potiguar'),
	('2406007','José da Penha','RN','Oeste Potiguar'),
	('2406106','Jucurutu','RN','Oeste Potiguar'),
	('2406155','Jundiá','RN','Agreste Potiguar'),
	('2406205','Lagoa d\'Anta','RN','Agreste Potiguar'),
	('2406304','Lagoa de Pedras','RN','Agreste Potiguar'),
	('2406403','Lagoa de Velhos','RN','Agreste Potiguar'),
	('2406502','Lagoa Nova','RN','Central Potiguar'),
	('2406601','Lagoa Salgada','RN','Agreste Potiguar'),
	('2406700','Lajes','RN','Central Potiguar'),
	('2406809','Lajes Pintadas','RN','Agreste Potiguar'),
	('2406908','Lucrécia','RN','Oeste Potiguar'),
	('2407005','Luís Gomes','RN','Oeste Potiguar'),
	('2407104','Macaíba','RN','Leste Potiguar'),
	('2407203','Macau','RN','Central Potiguar'),
	('2407252','Major Sales','RN','Oeste Potiguar'),
	('2407302','Marcelino Vieira','RN','Oeste Potiguar'),
	('2407401','Martins','RN','Oeste Potiguar'),
	('2407500','Maxaranguape','RN','Leste Potiguar'),
	('2407609','Messias Targino','RN','Oeste Potiguar'),
	('2407708','Montanhas','RN','Leste Potiguar'),
	('2407807','Monte Alegre','RN','Agreste Potiguar'),
	('2407906','Monte das Gameleiras','RN','Agreste Potiguar'),
	('2408003','Mossoró','RN','Oeste Potiguar'),
	('2408102','Natal','RN','Leste Potiguar'),
	('2408201','Nísia Floresta','RN','Leste Potiguar'),
	('2408300','Nova Cruz','RN','Agreste Potiguar'),
	('2408409','Olho d\'Água do Borges','RN','Oeste Potiguar'),
	('2408508','Ouro Branco','RN','Central Potiguar'),
	('2408607','Paraná','RN','Oeste Potiguar'),
	('2408706','Paraú','RN','Oeste Potiguar'),
	('2408805','Parazinho','RN','Agreste Potiguar'),
	('2408904','Parelhas','RN','Central Potiguar'),
	('2408953','Rio do Fogo','RN','Leste Potiguar'),
	('2409100','Passa e Fica','RN','Agreste Potiguar'),
	('2409209','Passagem','RN','Agreste Potiguar'),
	('2409308','Patu','RN','Oeste Potiguar'),
	('2409332','Santa Maria','RN','Agreste Potiguar'),
	('2409407','Pau dos Ferros','RN','Oeste Potiguar'),
	('2409506','Pedra Grande','RN','Leste Potiguar'),
	('2409605','Pedra Preta','RN','Central Potiguar'),
	('2409704','Pedro Avelino','RN','Central Potiguar'),
	('2409803','Pedro Velho','RN','Leste Potiguar'),
	('2409902','Pendências','RN','Oeste Potiguar'),
	('2410009','Pilões','RN','Oeste Potiguar'),
	('2410108','Poço Branco','RN','Agreste Potiguar'),
	('2410207','Portalegre','RN','Oeste Potiguar'),
	('2410256','Porto do Mangue','RN','Oeste Potiguar'),
	('2410306','Serra Caiada','RN','Agreste Potiguar'),
	('2410405','Pureza','RN','Leste Potiguar'),
	('2410504','Rafael Fernandes','RN','Oeste Potiguar'),
	('2410603','Rafael Godeiro','RN','Oeste Potiguar'),
	('2410702','Riacho da Cruz','RN','Oeste Potiguar'),
	('2410801','Riacho de Santana','RN','Oeste Potiguar'),
	('2410900','Riachuelo','RN','Agreste Potiguar'),
	('2411007','Rodolfo Fernandes','RN','Oeste Potiguar'),
	('2411056','Tibau','RN','Oeste Potiguar'),
	('2411106','Ruy Barbosa','RN','Agreste Potiguar'),
	('2411205','Santa Cruz','RN','Agreste Potiguar'),
	('2411403','Santana do Matos','RN','Central Potiguar'),
	('2411429','Santana do Seridó','RN','Central Potiguar'),
	('2411502','Santo Antônio','RN','Agreste Potiguar'),
	('2411601','São Bento do Norte','RN','Central Potiguar'),
	('2411700','São Bento do Trairí','RN','Agreste Potiguar'),
	('2411809','São Fernando','RN','Central Potiguar'),
	('2411908','São Francisco do Oeste','RN','Oeste Potiguar'),
	('2412005','São Gonçalo do Amarante','RN','Leste Potiguar'),
	('2412104','São João do Sabugi','RN','Central Potiguar'),
	('2412203','São José de Mipibu','RN','Leste Potiguar'),
	('2412302','São José do Campestre','RN','Agreste Potiguar'),
	('2412401','São José do Seridó','RN','Central Potiguar'),
	('2412500','São Miguel','RN','Oeste Potiguar'),
	('2412559','São Miguel do Gostoso','RN','Leste Potiguar'),
	('2412609','São Paulo do Potengi','RN','Agreste Potiguar'),
	('2412708','São Pedro','RN','Agreste Potiguar'),
	('2412807','São Rafael','RN','Oeste Potiguar'),
	('2412906','São Tomé','RN','Agreste Potiguar'),
	('2413003','São Vicente','RN','Central Potiguar'),
	('2413102','Senador Elói de Souza','RN','Agreste Potiguar'),
	('2413201','Senador Georgino Avelino','RN','Leste Potiguar'),
	('2413300','Serra de São Bento','RN','Agreste Potiguar'),
	('2413359','Serra do Mel','RN','Oeste Potiguar'),
	('2413409','Serra Negra do Norte','RN','Central Potiguar'),
	('2413508','Serrinha','RN','Agreste Potiguar'),
	('2413557','Serrinha dos Pintos','RN','Oeste Potiguar'),
	('2413607','Severiano Melo','RN','Oeste Potiguar'),
	('2413706','Sítio Novo','RN','Agreste Potiguar'),
	('2413805','Taboleiro Grande','RN','Oeste Potiguar'),
	('2413904','Taipu','RN','Leste Potiguar'),
	('2414001','Tangará','RN','Agreste Potiguar'),
	('2414100','Tenente Ananias','RN','Oeste Potiguar'),
	('2414159','Tenente Laurentino Cruz','RN','Central Potiguar'),
	('2414209','Tibau do Sul','RN','Leste Potiguar'),
	('2414308','Timbaúba dos Batistas','RN','Central Potiguar'),
	('2414407','Touros','RN','Leste Potiguar'),
	('2414456','Triunfo Potiguar','RN','Oeste Potiguar'),
	('2414506','Umarizal','RN','Oeste Potiguar'),
	('2414605','Upanema','RN','Oeste Potiguar'),
	('2414704','Várzea','RN','Agreste Potiguar'),
	('2414753','Venha-Ver','RN','Oeste Potiguar'),
	('2414803','Vera Cruz','RN','Agreste Potiguar'),
	('2414902','Viçosa','RN','Oeste Potiguar'),
	('2415008','Vila Flor','RN','Leste Potiguar'),
	('2500106','Água Branca','PB','Sertão Paraibano'),
	('2500205','Aguiar','PB','Sertão Paraibano'),
	('2500304','Alagoa Grande','PB','Agreste Paraibano'),
	('2500403','Alagoa Nova','PB','Agreste Paraibano'),
	('2500502','Alagoinha','PB','Agreste Paraibano'),
	('2500536','Alcantil','PB','Borborema'),
	('2500577','Algodão de Jandaíra','PB','Agreste Paraibano'),
	('2500601','Alhandra','PB','Mata Paraibana'),
	('2500700','São João do Rio do Peixe','PB','Sertão Paraibano'),
	('2500734','Amparo','PB','Borborema'),
	('2500775','Aparecida','PB','Sertão Paraibano'),
	('2500809','Araçagi','PB','Agreste Paraibano'),
	('2500908','Arara','PB','Agreste Paraibano'),
	('2501005','Araruna','PB','Agreste Paraibano'),
	('2501104','Areia','PB','Agreste Paraibano'),
	('2501153','Areia de Baraúnas','PB','Sertão Paraibano'),
	('2501203','Areial','PB','Agreste Paraibano'),
	('2501302','Aroeiras','PB','Agreste Paraibano'),
	('2501351','Assunção','PB','Borborema'),
	('2501401','Baía da Traição','PB','Mata Paraibana'),
	('2501500','Bananeiras','PB','Agreste Paraibano'),
	('2501534','Baraúna','PB','Borborema'),
	('2501575','Barra de Santana','PB','Borborema'),
	('2501609','Barra de Santa Rosa','PB','Agreste Paraibano'),
	('2501708','Barra de São Miguel','PB','Borborema'),
	('2501807','Bayeux','PB','Mata Paraibana'),
	('2501906','Belém','PB','Agreste Paraibano'),
	('2502003','Belém do Brejo do Cruz','PB','Sertão Paraibano'),
	('2502052','Bernardino Batista','PB','Sertão Paraibano'),
	('2502102','Boa Ventura','PB','Sertão Paraibano'),
	('2502151','Boa Vista','PB','Agreste Paraibano'),
	('2502201','Bom Jesus','PB','Sertão Paraibano'),
	('2502300','Bom Sucesso','PB','Sertão Paraibano'),
	('2502409','Bonito de Santa Fé','PB','Sertão Paraibano'),
	('2502508','Boqueirão','PB','Borborema'),
	('2502607','Igaracy','PB','Sertão Paraibano'),
	('2502706','Borborema','PB','Agreste Paraibano'),
	('2502805','Brejo do Cruz','PB','Sertão Paraibano'),
	('2502904','Brejo dos Santos','PB','Sertão Paraibano'),
	('2503001','Caaporã','PB','Mata Paraibana'),
	('2503100','Cabaceiras','PB','Borborema'),
	('2503209','Cabedelo','PB','Mata Paraibana'),
	('2503308','Cachoeira dos Índios','PB','Sertão Paraibano'),
	('2503407','Cacimba de Areia','PB','Sertão Paraibano'),
	('2503506','Cacimba de Dentro','PB','Agreste Paraibano'),
	('2503555','Cacimbas','PB','Sertão Paraibano'),
	('2503605','Caiçara','PB','Agreste Paraibano'),
	('2503704','Cajazeiras','PB','Sertão Paraibano'),
	('2503753','Cajazeirinhas','PB','Sertão Paraibano'),
	('2503803','Caldas Brandão','PB','Agreste Paraibano'),
	('2503902','Camalaú','PB','Borborema'),
	('2504009','Campina Grande','PB','Agreste Paraibano'),
	('2504033','Capim','PB','Mata Paraibana'),
	('2504074','Caraúbas','PB','Borborema'),
	('2504108','Carrapateira','PB','Sertão Paraibano'),
	('2504157','Casserengue','PB','Agreste Paraibano'),
	('2504207','Catingueira','PB','Sertão Paraibano'),
	('2504306','Catolé do Rocha','PB','Sertão Paraibano'),
	('2504355','Caturité','PB','Borborema'),
	('2504405','Conceição','PB','Sertão Paraibano'),
	('2504504','Condado','PB','Sertão Paraibano'),
	('2504603','Conde','PB','Mata Paraibana'),
	('2504702','Congo','PB','Borborema'),
	('2504801','Coremas','PB','Sertão Paraibano'),
	('2504850','Coxixola','PB','Borborema'),
	('2504900','Cruz do Espírito Santo','PB','Mata Paraibana'),
	('2505006','Cubati','PB','Borborema'),
	('2505105','Cuité','PB','Agreste Paraibano'),
	('2505204','Cuitegi','PB','Agreste Paraibano'),
	('2505238','Cuité de Mamanguape','PB','Mata Paraibana'),
	('2505279','Curral de Cima','PB','Mata Paraibana'),
	('2505303','Curral Velho','PB','Sertão Paraibano'),
	('2505352','Damião','PB','Agreste Paraibano'),
	('2505402','Desterro','PB','Sertão Paraibano'),
	('2505501','Vista Serrana','PB','Sertão Paraibano'),
	('2505600','Diamante','PB','Sertão Paraibano'),
	('2505709','Dona Inês','PB','Agreste Paraibano'),
	('2505808','Duas Estradas','PB','Agreste Paraibano'),
	('2505907','Emas','PB','Sertão Paraibano'),
	('2506004','Esperança','PB','Agreste Paraibano'),
	('2506103','Fagundes','PB','Agreste Paraibano'),
	('2506202','Frei Martinho','PB','Borborema'),
	('2506251','Gado Bravo','PB','Agreste Paraibano'),
	('2506301','Guarabira','PB','Agreste Paraibano'),
	('2506400','Gurinhém','PB','Agreste Paraibano'),
	('2506509','Gurjão','PB','Borborema'),
	('2506608','Ibiara','PB','Sertão Paraibano'),
	('2506707','Imaculada','PB','Sertão Paraibano'),
	('2506806','Ingá','PB','Agreste Paraibano'),
	('2506905','Itabaiana','PB','Agreste Paraibano'),
	('2507002','Itaporanga','PB','Sertão Paraibano'),
	('2507101','Itapororoca','PB','Mata Paraibana'),
	('2507200','Itatuba','PB','Agreste Paraibano'),
	('2507309','Jacaraú','PB','Mata Paraibana'),
	('2507408','Jericó','PB','Sertão Paraibano'),
	('2507507','João Pessoa','PB','Mata Paraibana'),
	('2507606','Juarez Távora','PB','Agreste Paraibano'),
	('2507705','Juazeirinho','PB','Borborema'),
	('2507804','Junco do Seridó','PB','Borborema'),
	('2507903','Juripiranga','PB','Mata Paraibana'),
	('2508000','Juru','PB','Sertão Paraibano'),
	('2508109','Lagoa','PB','Sertão Paraibano'),
	('2508208','Lagoa de Dentro','PB','Agreste Paraibano'),
	('2508307','Lagoa Seca','PB','Agreste Paraibano'),
	('2508406','Lastro','PB','Sertão Paraibano'),
	('2508505','Livramento','PB','Borborema'),
	('2508554','Logradouro','PB','Agreste Paraibano'),
	('2508604','Lucena','PB','Mata Paraibana'),
	('2508703','Mãe d\'Água','PB','Sertão Paraibano'),
	('2508802','Malta','PB','Sertão Paraibano'),
	('2508901','Mamanguape','PB','Mata Paraibana'),
	('2509008','Manaíra','PB','Sertão Paraibano'),
	('2509057','Marcação','PB','Mata Paraibana'),
	('2509107','Mari','PB','Mata Paraibana'),
	('2509156','Marizópolis','PB','Sertão Paraibano'),
	('2509206','Massaranduba','PB','Agreste Paraibano'),
	('2509305','Mataraca','PB','Mata Paraibana'),
	('2509339','Matinhas','PB','Agreste Paraibano'),
	('2509370','Mato Grosso','PB','Sertão Paraibano'),
	('2509396','Maturéia','PB','Sertão Paraibano'),
	('2509404','Mogeiro','PB','Agreste Paraibano'),
	('2509503','Montadas','PB','Agreste Paraibano'),
	('2509602','Monte Horebe','PB','Sertão Paraibano'),
	('2509701','Monteiro','PB','Borborema'),
	('2509800','Mulungu','PB','Agreste Paraibano'),
	('2509909','Natuba','PB','Agreste Paraibano'),
	('2510006','Nazarezinho','PB','Sertão Paraibano'),
	('2510105','Nova Floresta','PB','Agreste Paraibano'),
	('2510204','Nova Olinda','PB','Sertão Paraibano'),
	('2510303','Nova Palmeira','PB','Borborema'),
	('2510402','Olho d\'Água','PB','Sertão Paraibano'),
	('2510501','Olivedos','PB','Agreste Paraibano'),
	('2510600','Ouro Velho','PB','Borborema'),
	('2510659','Parari','PB','Borborema'),
	('2510709','Passagem','PB','Sertão Paraibano'),
	('2510808','Patos','PB','Sertão Paraibano'),
	('2510907','Paulista','PB','Sertão Paraibano'),
	('2511004','Pedra Branca','PB','Sertão Paraibano'),
	('2511103','Pedra Lavrada','PB','Borborema'),
	('2511202','Pedras de Fogo','PB','Mata Paraibana'),
	('2511301','Piancó','PB','Sertão Paraibano'),
	('2511400','Picuí','PB','Borborema'),
	('2511509','Pilar','PB','Mata Paraibana'),
	('2511608','Pilões','PB','Agreste Paraibano'),
	('2511707','Pilõezinhos','PB','Agreste Paraibano'),
	('2511806','Pirpirituba','PB','Agreste Paraibano'),
	('2511905','Pitimbu','PB','Mata Paraibana'),
	('2512002','Pocinhos','PB','Agreste Paraibano'),
	('2512036','Poço Dantas','PB','Sertão Paraibano'),
	('2512077','Poço de José de Moura','PB','Sertão Paraibano'),
	('2512101','Pombal','PB','Sertão Paraibano'),
	('2512200','Prata','PB','Borborema'),
	('2512309','Princesa Isabel','PB','Sertão Paraibano'),
	('2512408','Puxinanã','PB','Agreste Paraibano'),
	('2512507','Queimadas','PB','Agreste Paraibano'),
	('2512606','Quixaba','PB','Sertão Paraibano'),
	('2512705','Remígio','PB','Agreste Paraibano'),
	('2512721','Pedro Régis','PB','Mata Paraibana'),
	('2512747','Riachão','PB','Agreste Paraibano'),
	('2512754','Riachão do Bacamarte','PB','Agreste Paraibano'),
	('2512762','Riachão do Poço','PB','Mata Paraibana'),
	('2512788','Riacho de Santo Antônio','PB','Borborema'),
	('2512804','Riacho dos Cavalos','PB','Sertão Paraibano'),
	('2512903','Rio Tinto','PB','Mata Paraibana'),
	('2513000','Salgadinho','PB','Borborema'),
	('2513109','Salgado de São Félix','PB','Agreste Paraibano'),
	('2513158','Santa Cecília','PB','Agreste Paraibano'),
	('2513208','Santa Cruz','PB','Sertão Paraibano'),
	('2513307','Santa Helena','PB','Sertão Paraibano'),
	('2513356','Santa Inês','PB','Sertão Paraibano'),
	('2513406','Santa Luzia','PB','Borborema'),
	('2513505','Santana de Mangueira','PB','Sertão Paraibano'),
	('2513604','Santana dos Garrotes','PB','Sertão Paraibano'),
	('2513653','Joca Claudino','PB','Sertão Paraibano'),
	('2513703','Santa Rita','PB','Mata Paraibana'),
	('2513802','Santa Teresinha','PB','Sertão Paraibano'),
	('2513851','Santo André','PB','Borborema'),
	('2513901','São Bento','PB','Sertão Paraibano'),
	('2513927','São Bentinho','PB','Sertão Paraibano'),
	('2513943','São Domingos do Cariri','PB','Borborema'),
	('2513968','São Domingos','PB','Sertão Paraibano'),
	('2513984','São Francisco','PB','Sertão Paraibano'),
	('2514008','São João do Cariri','PB','Borborema'),
	('2514107','São João do Tigre','PB','Borborema'),
	('2514206','São José da Lagoa Tapada','PB','Sertão Paraibano'),
	('2514305','São José de Caiana','PB','Sertão Paraibano'),
	('2514404','São José de Espinharas','PB','Sertão Paraibano'),
	('2514453','São José dos Ramos','PB','Mata Paraibana'),
	('2514503','São José de Piranhas','PB','Sertão Paraibano'),
	('2514552','São José de Princesa','PB','Sertão Paraibano'),
	('2514602','São José do Bonfim','PB','Sertão Paraibano'),
	('2514651','São José do Brejo do Cruz','PB','Sertão Paraibano'),
	('2514701','São José do Sabugi','PB','Borborema'),
	('2514800','São José dos Cordeiros','PB','Borborema'),
	('2514909','São Mamede','PB','Borborema'),
	('2515005','São Miguel de Taipu','PB','Mata Paraibana'),
	('2515104','São Sebastião de Lagoa de Roça','PB','Agreste Paraibano'),
	('2515203','São Sebastião do Umbuzeiro','PB','Borborema'),
	('2515302','Sapé','PB','Mata Paraibana'),
	('2515401','São Vicente do Seridó','PB','Borborema'),
	('2515500','Serra Branca','PB','Borborema'),
	('2515609','Serra da Raiz','PB','Agreste Paraibano'),
	('2515708','Serra Grande','PB','Sertão Paraibano'),
	('2515807','Serra Redonda','PB','Agreste Paraibano'),
	('2515906','Serraria','PB','Agreste Paraibano'),
	('2515930','Sertãozinho','PB','Agreste Paraibano'),
	('2515971','Sobrado','PB','Mata Paraibana'),
	('2516003','Solânea','PB','Agreste Paraibano'),
	('2516102','Soledade','PB','Agreste Paraibano'),
	('2516151','Sossêgo','PB','Agreste Paraibano'),
	('2516201','Sousa','PB','Sertão Paraibano'),
	('2516300','Sumé','PB','Borborema'),
	('2516409','Tacima','PB','Agreste Paraibano'),
	('2516508','Taperoá','PB','Borborema'),
	('2516607','Tavares','PB','Sertão Paraibano'),
	('2516706','Teixeira','PB','Sertão Paraibano'),
	('2516755','Tenório','PB','Borborema'),
	('2516805','Triunfo','PB','Sertão Paraibano'),
	('2516904','Uiraúna','PB','Sertão Paraibano'),
	('2517001','Umbuzeiro','PB','Agreste Paraibano'),
	('2517100','Várzea','PB','Borborema'),
	('2517209','Vieirópolis','PB','Sertão Paraibano'),
	('2517407','Zabelê','PB','Borborema'),
	('2600054','Abreu e Lima','PE','Metropolitana de Recife'),
	('2600104','Afogados da Ingazeira','PE','Sertão Pernambucano'),
	('2600203','Afrânio','PE','São Francisco Pernambucano'),
	('2600302','Agrestina','PE','Agreste Pernambucano'),
	('2600401','Água Preta','PE','Mata Pernambucana'),
	('2600500','Águas Belas','PE','Agreste Pernambucano'),
	('2600609','Alagoinha','PE','Agreste Pernambucano'),
	('2600708','Aliança','PE','Mata Pernambucana'),
	('2600807','Altinho','PE','Agreste Pernambucano'),
	('2600906','Amaraji','PE','Mata Pernambucana'),
	('2601003','Angelim','PE','Agreste Pernambucano'),
	('2601052','Araçoiaba','PE','Metropolitana de Recife'),
	('2601102','Araripina','PE','Sertão Pernambucano'),
	('2601201','Arcoverde','PE','Sertão Pernambucano'),
	('2601300','Barra de Guabiraba','PE','Agreste Pernambucano'),
	('2601409','Barreiros','PE','Mata Pernambucana'),
	('2601508','Belém de Maria','PE','Mata Pernambucana'),
	('2601607','Belém do São Francisco','PE','São Francisco Pernambucano'),
	('2601706','Belo Jardim','PE','Agreste Pernambucano'),
	('2601805','Betânia','PE','Sertão Pernambucano'),
	('2601904','Bezerros','PE','Agreste Pernambucano'),
	('2602001','Bodocó','PE','Sertão Pernambucano'),
	('2602100','Bom Conselho','PE','Agreste Pernambucano'),
	('2602209','Bom Jardim','PE','Agreste Pernambucano'),
	('2602308','Bonito','PE','Agreste Pernambucano'),
	('2602407','Brejão','PE','Agreste Pernambucano'),
	('2602506','Brejinho','PE','Sertão Pernambucano'),
	('2602605','Brejo da Madre de Deus','PE','Agreste Pernambucano'),
	('2602704','Buenos Aires','PE','Mata Pernambucana'),
	('2602803','Buíque','PE','Agreste Pernambucano'),
	('2602902','Cabo de Santo Agostinho','PE','Metropolitana de Recife'),
	('2603009','Cabrobó','PE','São Francisco Pernambucano'),
	('2603108','Cachoeirinha','PE','Agreste Pernambucano'),
	('2603207','Caetés','PE','Agreste Pernambucano'),
	('2603306','Calçado','PE','Agreste Pernambucano'),
	('2603405','Calumbi','PE','Sertão Pernambucano'),
	('2603454','Camaragibe','PE','Metropolitana de Recife'),
	('2603504','Camocim de São Félix','PE','Agreste Pernambucano'),
	('2603603','Camutanga','PE','Mata Pernambucana'),
	('2603702','Canhotinho','PE','Agreste Pernambucano'),
	('2603801','Capoeiras','PE','Agreste Pernambucano'),
	('2603900','Carnaíba','PE','Sertão Pernambucano'),
	('2603926','Carnaubeira da Penha','PE','São Francisco Pernambucano'),
	('2604007','Carpina','PE','Mata Pernambucana'),
	('2604106','Caruaru','PE','Agreste Pernambucano'),
	('2604155','Casinhas','PE','Agreste Pernambucano'),
	('2604205','Catende','PE','Mata Pernambucana'),
	('2604304','Cedro','PE','Sertão Pernambucano'),
	('2604403','Chã de Alegria','PE','Mata Pernambucana'),
	('2604502','Chã Grande','PE','Mata Pernambucana'),
	('2604601','Condado','PE','Mata Pernambucana'),
	('2604700','Correntes','PE','Agreste Pernambucano'),
	('2604809','Cortês','PE','Mata Pernambucana'),
	('2604908','Cumaru','PE','Agreste Pernambucano'),
	('2605004','Cupira','PE','Agreste Pernambucano'),
	('2605103','Custódia','PE','Sertão Pernambucano'),
	('2605152','Dormentes','PE','São Francisco Pernambucano'),
	('2605202','Escada','PE','Mata Pernambucana'),
	('2605301','Exu','PE','Sertão Pernambucano'),
	('2605400','Feira Nova','PE','Agreste Pernambucano'),
	('2605459','Fernando de Noronha','PE','Metropolitana de Recife'),
	('2605509','Ferreiros','PE','Mata Pernambucana'),
	('2605608','Flores','PE','Sertão Pernambucano'),
	('2605707','Floresta','PE','São Francisco Pernambucano'),
	('2605806','Frei Miguelinho','PE','Agreste Pernambucano'),
	('2605905','Gameleira','PE','Mata Pernambucana'),
	('2606002','Garanhuns','PE','Agreste Pernambucano'),
	('2606101','Glória do Goitá','PE','Mata Pernambucana'),
	('2606200','Goiana','PE','Mata Pernambucana'),
	('2606309','Granito','PE','Sertão Pernambucano'),
	('2606408','Gravatá','PE','Agreste Pernambucano'),
	('2606507','Iati','PE','Agreste Pernambucano'),
	('2606606','Ibimirim','PE','Sertão Pernambucano'),
	('2606705','Ibirajuba','PE','Agreste Pernambucano'),
	('2606804','Igarassu','PE','Metropolitana de Recife'),
	('2606903','Iguaracy','PE','Sertão Pernambucano'),
	('2607000','Inajá','PE','Sertão Pernambucano'),
	('2607109','Ingazeira','PE','Sertão Pernambucano'),
	('2607208','Ipojuca','PE','Metropolitana de Recife'),
	('2607307','Ipubi','PE','Sertão Pernambucano'),
	('2607406','Itacuruba','PE','São Francisco Pernambucano'),
	('2607505','Itaíba','PE','Agreste Pernambucano'),
	('2607604','Ilha de Itamaracá','PE','Metropolitana de Recife'),
	('2607653','Itambé','PE','Mata Pernambucana'),
	('2607703','Itapetim','PE','Sertão Pernambucano'),
	('2607752','Itapissuma','PE','Metropolitana de Recife'),
	('2607802','Itaquitinga','PE','Mata Pernambucana'),
	('2607901','Jaboatão dos Guararapes','PE','Metropolitana de Recife'),
	('2607950','Jaqueira','PE','Mata Pernambucana'),
	('2608008','Jataúba','PE','Agreste Pernambucano'),
	('2608057','Jatobá','PE','São Francisco Pernambucano'),
	('2608107','João Alfredo','PE','Agreste Pernambucano'),
	('2608206','Joaquim Nabuco','PE','Mata Pernambucana'),
	('2608255','Jucati','PE','Agreste Pernambucano'),
	('2608305','Jupi','PE','Agreste Pernambucano'),
	('2608404','Jurema','PE','Agreste Pernambucano'),
	('2608453','Lagoa do Carro','PE','Mata Pernambucana'),
	('2608503','Lagoa de Itaenga','PE','Mata Pernambucana'),
	('2608602','Lagoa do Ouro','PE','Agreste Pernambucano'),
	('2608701','Lagoa dos Gatos','PE','Agreste Pernambucano'),
	('2608750','Lagoa Grande','PE','São Francisco Pernambucano'),
	('2608800','Lajedo','PE','Agreste Pernambucano'),
	('2608909','Limoeiro','PE','Agreste Pernambucano'),
	('2609006','Macaparana','PE','Mata Pernambucana'),
	('2609105','Machados','PE','Agreste Pernambucano'),
	('2609154','Manari','PE','Sertão Pernambucano'),
	('2609204','Maraial','PE','Mata Pernambucana'),
	('2609303','Mirandiba','PE','Sertão Pernambucano'),
	('2609402','Moreno','PE','Metropolitana de Recife'),
	('2609501','Nazaré da Mata','PE','Mata Pernambucana'),
	('2609600','Olinda','PE','Metropolitana de Recife'),
	('2609709','Orobó','PE','Agreste Pernambucano'),
	('2609808','Orocó','PE','São Francisco Pernambucano'),
	('2609907','Ouricuri','PE','Sertão Pernambucano'),
	('2610004','Palmares','PE','Mata Pernambucana'),
	('2610103','Palmeirina','PE','Agreste Pernambucano'),
	('2610202','Panelas','PE','Agreste Pernambucano'),
	('2610301','Paranatama','PE','Agreste Pernambucano'),
	('2610400','Parnamirim','PE','Sertão Pernambucano'),
	('2610509','Passira','PE','Agreste Pernambucano'),
	('2610608','Paudalho','PE','Mata Pernambucana'),
	('2610707','Paulista','PE','Metropolitana de Recife'),
	('2610806','Pedra','PE','Agreste Pernambucano'),
	('2610905','Pesqueira','PE','Agreste Pernambucano'),
	('2611002','Petrolândia','PE','São Francisco Pernambucano'),
	('2611101','Petrolina','PE','São Francisco Pernambucano'),
	('2611200','Poção','PE','Agreste Pernambucano'),
	('2611309','Pombos','PE','Mata Pernambucana'),
	('2611408','Primavera','PE','Mata Pernambucana'),
	('2611507','Quipapá','PE','Mata Pernambucana'),
	('2611533','Quixaba','PE','Sertão Pernambucano'),
	('2611606','Recife','PE','Metropolitana de Recife'),
	('2611705','Riacho das Almas','PE','Agreste Pernambucano'),
	('2611804','Ribeirão','PE','Mata Pernambucana'),
	('2611903','Rio Formoso','PE','Mata Pernambucana'),
	('2612000','Sairé','PE','Agreste Pernambucano'),
	('2612109','Salgadinho','PE','Agreste Pernambucano'),
	('2612208','Salgueiro','PE','Sertão Pernambucano'),
	('2612307','Saloá','PE','Agreste Pernambucano'),
	('2612406','Sanharó','PE','Agreste Pernambucano'),
	('2612455','Santa Cruz','PE','Sertão Pernambucano'),
	('2612471','Santa Cruz da Baixa Verde','PE','Sertão Pernambucano'),
	('2612505','Santa Cruz do Capibaribe','PE','Agreste Pernambucano'),
	('2612554','Santa Filomena','PE','Sertão Pernambucano'),
	('2612604','Santa Maria da Boa Vista','PE','São Francisco Pernambucano'),
	('2612703','Santa Maria do Cambucá','PE','Agreste Pernambucano'),
	('2612802','Santa Terezinha','PE','Sertão Pernambucano'),
	('2612901','São Benedito do Sul','PE','Mata Pernambucana'),
	('2613008','São Bento do Una','PE','Agreste Pernambucano'),
	('2613107','São Caitano','PE','Agreste Pernambucano'),
	('2613206','São João','PE','Agreste Pernambucano'),
	('2613305','São Joaquim do Monte','PE','Agreste Pernambucano'),
	('2613404','São José da Coroa Grande','PE','Mata Pernambucana'),
	('2613503','São José do Belmonte','PE','Sertão Pernambucano'),
	('2613602','São José do Egito','PE','Sertão Pernambucano'),
	('2613701','São Lourenço da Mata','PE','Metropolitana de Recife'),
	('2613800','São Vicente Férrer','PE','Agreste Pernambucano'),
	('2613909','Serra Talhada','PE','Sertão Pernambucano'),
	('2614006','Serrita','PE','Sertão Pernambucano'),
	('2614105','Sertânia','PE','Sertão Pernambucano'),
	('2614204','Sirinhaém','PE','Mata Pernambucana'),
	('2614303','Moreilândia','PE','Sertão Pernambucano'),
	('2614402','Solidão','PE','Sertão Pernambucano'),
	('2614501','Surubim','PE','Agreste Pernambucano'),
	('2614600','Tabira','PE','Sertão Pernambucano'),
	('2614709','Tacaimbó','PE','Agreste Pernambucano'),
	('2614808','Tacaratu','PE','São Francisco Pernambucano'),
	('2614857','Tamandaré','PE','Mata Pernambucana'),
	('2615003','Taquaritinga do Norte','PE','Agreste Pernambucano'),
	('2615102','Terezinha','PE','Agreste Pernambucano'),
	('2615201','Terra Nova','PE','São Francisco Pernambucano'),
	('2615300','Timbaúba','PE','Mata Pernambucana'),
	('2615409','Toritama','PE','Agreste Pernambucano'),
	('2615508','Tracunhaém','PE','Mata Pernambucana'),
	('2615607','Trindade','PE','Sertão Pernambucano'),
	('2615706','Triunfo','PE','Sertão Pernambucano'),
	('2615805','Tupanatinga','PE','Agreste Pernambucano'),
	('2615904','Tuparetama','PE','Sertão Pernambucano'),
	('2616001','Venturosa','PE','Agreste Pernambucano'),
	('2616100','Verdejante','PE','Sertão Pernambucano'),
	('2616183','Vertente do Lério','PE','Agreste Pernambucano'),
	('2616209','Vertentes','PE','Agreste Pernambucano'),
	('2616308','Vicência','PE','Mata Pernambucana'),
	('2616407','Vitória de Santo Antão','PE','Mata Pernambucana'),
	('2616506','Xexéu','PE','Mata Pernambucana'),
	('2700102','Água Branca','AL','Sertão Alagoano'),
	('2700201','Anadia','AL','Leste Alagoano'),
	('2700300','Arapiraca','AL','Agreste Alagoano'),
	('2700409','Atalaia','AL','Leste Alagoano'),
	('2700508','Barra de Santo Antônio','AL','Leste Alagoano'),
	('2700607','Barra de São Miguel','AL','Leste Alagoano'),
	('2700706','Batalha','AL','Sertão Alagoano'),
	('2700805','Belém','AL','Agreste Alagoano'),
	('2700904','Belo Monte','AL','Sertão Alagoano'),
	('2701001','Boca da Mata','AL','Leste Alagoano'),
	('2701100','Branquinha','AL','Leste Alagoano'),
	('2701209','Cacimbinhas','AL','Agreste Alagoano'),
	('2701308','Cajueiro','AL','Leste Alagoano'),
	('2701357','Campestre','AL','Leste Alagoano'),
	('2701407','Campo Alegre','AL','Leste Alagoano'),
	('2701506','Campo Grande','AL','Agreste Alagoano'),
	('2701605','Canapi','AL','Sertão Alagoano'),
	('2701704','Capela','AL','Leste Alagoano'),
	('2701803','Carneiros','AL','Sertão Alagoano'),
	('2701902','Chã Preta','AL','Leste Alagoano'),
	('2702009','Coité do Nóia','AL','Agreste Alagoano'),
	('2702108','Colônia Leopoldina','AL','Leste Alagoano'),
	('2702207','Coqueiro Seco','AL','Leste Alagoano'),
	('2702306','Coruripe','AL','Leste Alagoano'),
	('2702355','Craíbas','AL','Agreste Alagoano'),
	('2702405','Delmiro Gouveia','AL','Sertão Alagoano'),
	('2702504','Dois Riachos','AL','Sertão Alagoano'),
	('2702553','Estrela de Alagoas','AL','Agreste Alagoano'),
	('2702603','Feira Grande','AL','Agreste Alagoano'),
	('2702702','Feliz Deserto','AL','Leste Alagoano'),
	('2702801','Flexeiras','AL','Leste Alagoano'),
	('2702900','Girau do Ponciano','AL','Agreste Alagoano'),
	('2703007','Ibateguara','AL','Leste Alagoano'),
	('2703106','Igaci','AL','Agreste Alagoano'),
	('2703205','Igreja Nova','AL','Leste Alagoano'),
	('2703304','Inhapi','AL','Sertão Alagoano'),
	('2703403','Jacaré dos Homens','AL','Sertão Alagoano'),
	('2703502','Jacuípe','AL','Leste Alagoano'),
	('2703601','Japaratinga','AL','Leste Alagoano'),
	('2703700','Jaramataia','AL','Sertão Alagoano'),
	('2703759','Jequiá da Praia','AL','Leste Alagoano'),
	('2703809','Joaquim Gomes','AL','Leste Alagoano'),
	('2703908','Jundiá','AL','Leste Alagoano'),
	('2704005','Junqueiro','AL','Leste Alagoano'),
	('2704104','Lagoa da Canoa','AL','Agreste Alagoano'),
	('2704203','Limoeiro de Anadia','AL','Agreste Alagoano'),
	('2704302','Maceió','AL','Leste Alagoano'),
	('2704401','Major Isidoro','AL','Sertão Alagoano'),
	('2704500','Maragogi','AL','Leste Alagoano'),
	('2704609','Maravilha','AL','Sertão Alagoano'),
	('2704708','Marechal Deodoro','AL','Leste Alagoano'),
	('2704807','Maribondo','AL','Agreste Alagoano'),
	('2704906','Mar Vermelho','AL','Agreste Alagoano'),
	('2705002','Mata Grande','AL','Sertão Alagoano'),
	('2705101','Matriz de Camaragibe','AL','Leste Alagoano'),
	('2705200','Messias','AL','Leste Alagoano'),
	('2705309','Minador do Negrão','AL','Agreste Alagoano'),
	('2705408','Monteirópolis','AL','Sertão Alagoano'),
	('2705507','Murici','AL','Leste Alagoano'),
	('2705606','Novo Lino','AL','Leste Alagoano'),
	('2705705','Olho d\'Água das Flores','AL','Sertão Alagoano'),
	('2705804','Olho d\'Água do Casado','AL','Sertão Alagoano'),
	('2705903','Olho d\'Água Grande','AL','Agreste Alagoano'),
	('2706000','Olivença','AL','Sertão Alagoano'),
	('2706109','Ouro Branco','AL','Sertão Alagoano'),
	('2706208','Palestina','AL','Sertão Alagoano'),
	('2706307','Palmeira dos Índios','AL','Agreste Alagoano'),
	('2706406','Pão de Açúcar','AL','Sertão Alagoano'),
	('2706422','Pariconha','AL','Sertão Alagoano'),
	('2706448','Paripueira','AL','Leste Alagoano'),
	('2706505','Passo de Camaragibe','AL','Leste Alagoano'),
	('2706604','Paulo Jacinto','AL','Agreste Alagoano'),
	('2706703','Penedo','AL','Leste Alagoano'),
	('2706802','Piaçabuçu','AL','Leste Alagoano'),
	('2706901','Pilar','AL','Leste Alagoano'),
	('2707008','Pindoba','AL','Leste Alagoano'),
	('2707107','Piranhas','AL','Sertão Alagoano'),
	('2707206','Poço das Trincheiras','AL','Sertão Alagoano'),
	('2707305','Porto Calvo','AL','Leste Alagoano'),
	('2707404','Porto de Pedras','AL','Leste Alagoano'),
	('2707503','Porto Real do Colégio','AL','Leste Alagoano'),
	('2707602','Quebrangulo','AL','Agreste Alagoano'),
	('2707701','Rio Largo','AL','Leste Alagoano'),
	('2707800','Roteiro','AL','Leste Alagoano'),
	('2707909','Santa Luzia do Norte','AL','Leste Alagoano'),
	('2708006','Santana do Ipanema','AL','Sertão Alagoano'),
	('2708105','Santana do Mundaú','AL','Leste Alagoano'),
	('2708204','São Brás','AL','Agreste Alagoano'),
	('2708303','São José da Laje','AL','Leste Alagoano'),
	('2708402','São José da Tapera','AL','Sertão Alagoano'),
	('2708501','São Luís do Quitunde','AL','Leste Alagoano'),
	('2708600','São Miguel dos Campos','AL','Leste Alagoano'),
	('2708709','São Miguel dos Milagres','AL','Leste Alagoano'),
	('2708808','São Sebastião','AL','Agreste Alagoano'),
	('2708907','Satuba','AL','Leste Alagoano'),
	('2708956','Senador Rui Palmeira','AL','Sertão Alagoano'),
	('2709004','Tanque d\'Arca','AL','Agreste Alagoano'),
	('2709103','Taquarana','AL','Agreste Alagoano'),
	('2709152','Teotônio Vilela','AL','Leste Alagoano'),
	('2709202','Traipu','AL','Agreste Alagoano'),
	('2709301','União dos Palmares','AL','Leste Alagoano'),
	('2709400','Viçosa','AL','Leste Alagoano'),
	('2800100','Amparo de São Francisco','SE','Leste Sergipano'),
	('2800209','Aquidabã','SE','Agreste Sergipano'),
	('2800308','Aracaju','SE','Leste Sergipano'),
	('2800407','Arauá','SE','Leste Sergipano'),
	('2800506','Areia Branca','SE','Agreste Sergipano'),
	('2800605','Barra dos Coqueiros','SE','Leste Sergipano'),
	('2800670','Boquim','SE','Leste Sergipano'),
	('2800704','Brejo Grande','SE','Leste Sergipano'),
	('2801009','Campo do Brito','SE','Agreste Sergipano'),
	('2801108','Canhoba','SE','Leste Sergipano'),
	('2801207','Canindé de São Francisco','SE','Sertão Sergipano'),
	('2801306','Capela','SE','Leste Sergipano'),
	('2801405','Carira','SE','Sertão Sergipano'),
	('2801504','Carmópolis','SE','Leste Sergipano'),
	('2801603','Cedro de São João','SE','Leste Sergipano'),
	('2801702','Cristinápolis','SE','Leste Sergipano'),
	('2801900','Cumbe','SE','Agreste Sergipano'),
	('2802007','Divina Pastora','SE','Leste Sergipano'),
	('2802106','Estância','SE','Leste Sergipano'),
	('2802205','Feira Nova','SE','Sertão Sergipano'),
	('2802304','Frei Paulo','SE','Sertão Sergipano'),
	('2802403','Gararu','SE','Sertão Sergipano'),
	('2802502','General Maynard','SE','Leste Sergipano'),
	('2802601','Gracho Cardoso','SE','Sertão Sergipano'),
	('2802700','Ilha das Flores','SE','Leste Sergipano'),
	('2802809','Indiaroba','SE','Leste Sergipano'),
	('2802908','Itabaiana','SE','Agreste Sergipano'),
	('2803005','Itabaianinha','SE','Leste Sergipano'),
	('2803104','Itabi','SE','Sertão Sergipano'),
	('2803203','Itaporanga d\'Ajuda','SE','Leste Sergipano'),
	('2803302','Japaratuba','SE','Leste Sergipano'),
	('2803401','Japoatã','SE','Leste Sergipano'),
	('2803500','Lagarto','SE','Agreste Sergipano'),
	('2803609','Laranjeiras','SE','Leste Sergipano'),
	('2803708','Macambira','SE','Agreste Sergipano'),
	('2803807','Malhada dos Bois','SE','Agreste Sergipano'),
	('2803906','Malhador','SE','Agreste Sergipano'),
	('2804003','Maruim','SE','Leste Sergipano'),
	('2804102','Moita Bonita','SE','Agreste Sergipano'),
	('2804201','Monte Alegre de Sergipe','SE','Sertão Sergipano'),
	('2804300','Muribeca','SE','Agreste Sergipano'),
	('2804409','Neópolis','SE','Leste Sergipano'),
	('2804458','Nossa Senhora Aparecida','SE','Sertão Sergipano'),
	('2804508','Nossa Senhora da Glória','SE','Sertão Sergipano'),
	('2804607','Nossa Senhora das Dores','SE','Agreste Sergipano'),
	('2804706','Nossa Senhora de Lourdes','SE','Leste Sergipano'),
	('2804805','Nossa Senhora do Socorro','SE','Leste Sergipano'),
	('2804904','Pacatuba','SE','Leste Sergipano'),
	('2805000','Pedra Mole','SE','Sertão Sergipano'),
	('2805109','Pedrinhas','SE','Leste Sergipano'),
	('2805208','Pinhão','SE','Sertão Sergipano'),
	('2805307','Pirambu','SE','Leste Sergipano'),
	('2805406','Poço Redondo','SE','Sertão Sergipano'),
	('2805505','Poço Verde','SE','Agreste Sergipano'),
	('2805604','Porto da Folha','SE','Sertão Sergipano'),
	('2805703','Propriá','SE','Leste Sergipano'),
	('2805802','Riachão do Dantas','SE','Agreste Sergipano'),
	('2805901','Riachuelo','SE','Leste Sergipano'),
	('2806008','Ribeirópolis','SE','Sertão Sergipano'),
	('2806107','Rosário do Catete','SE','Leste Sergipano'),
	('2806206','Salgado','SE','Leste Sergipano'),
	('2806305','Santa Luzia do Itanhy','SE','Leste Sergipano'),
	('2806404','Santana do São Francisco','SE','Leste Sergipano'),
	('2806503','Santa Rosa de Lima','SE','Leste Sergipano'),
	('2806602','Santo Amaro das Brotas','SE','Leste Sergipano'),
	('2806701','São Cristóvão','SE','Leste Sergipano'),
	('2806800','São Domingos','SE','Agreste Sergipano'),
	('2806909','São Francisco','SE','Leste Sergipano'),
	('2807006','São Miguel do Aleixo','SE','Agreste Sergipano'),
	('2807105','Simão Dias','SE','Agreste Sergipano'),
	('2807204','Siriri','SE','Leste Sergipano'),
	('2807303','Telha','SE','Leste Sergipano'),
	('2807402','Tobias Barreto','SE','Agreste Sergipano'),
	('2807501','Tomar do Geru','SE','Leste Sergipano'),
	('2807600','Umbaúba','SE','Leste Sergipano'),
	('2900108','Abaíra','BA','Centro Sul Baiano'),
	('2900207','Abaré','BA','Vale São-Franciscano da Bahia'),
	('2900306','Acajutiba','BA','Nordeste Baiano'),
	('2900355','Adustina','BA','Nordeste Baiano'),
	('2900405','Água Fria','BA','Centro Norte Baiano'),
	('2900504','Érico Cardoso','BA','Centro Sul Baiano'),
	('2900603','Aiquara','BA','Centro Sul Baiano'),
	('2900702','Alagoinhas','BA','Nordeste Baiano'),
	('2900801','Alcobaça','BA','Sul Baiano'),
	('2900900','Almadina','BA','Sul Baiano'),
	('2901007','Amargosa','BA','Centro Sul Baiano'),
	('2901106','Amélia Rodrigues','BA','Metropolitana de Salvador'),
	('2901155','América Dourada','BA','Centro Norte Baiano'),
	('2901205','Anagé','BA','Centro Sul Baiano'),
	('2901304','Andaraí','BA','Centro Sul Baiano'),
	('2901353','Andorinha','BA','Centro Norte Baiano'),
	('2901403','Angical','BA','Extremo Oeste Baiano'),
	('2901502','Anguera','BA','Centro Norte Baiano'),
	('2901601','Antas','BA','Nordeste Baiano'),
	('2901700','Antônio Cardoso','BA','Centro Norte Baiano'),
	('2901809','Antônio Gonçalves','BA','Centro Norte Baiano'),
	('2901908','Aporá','BA','Nordeste Baiano'),
	('2901957','Apuarema','BA','Centro Sul Baiano'),
	('2902005','Aracatu','BA','Centro Sul Baiano'),
	('2902054','Araçás','BA','Nordeste Baiano'),
	('2902104','Araci','BA','Nordeste Baiano'),
	('2902203','Aramari','BA','Nordeste Baiano'),
	('2902252','Arataca','BA','Sul Baiano'),
	('2902302','Aratuípe','BA','Metropolitana de Salvador'),
	('2902401','Aurelino Leal','BA','Sul Baiano'),
	('2902500','Baianópolis','BA','Extremo Oeste Baiano'),
	('2902609','Baixa Grande','BA','Centro Norte Baiano'),
	('2902658','Banzaê','BA','Nordeste Baiano'),
	('2902708','Barra','BA','Vale São-Franciscano da Bahia'),
	('2902807','Barra da Estiva','BA','Centro Sul Baiano'),
	('2902906','Barra do Choça','BA','Centro Sul Baiano'),
	('2903003','Barra do Mendes','BA','Centro Norte Baiano'),
	('2903102','Barra do Rocha','BA','Sul Baiano'),
	('2903201','Barreiras','BA','Extremo Oeste Baiano'),
	('2903235','Barro Alto','BA','Centro Norte Baiano'),
	('2903276','Barrocas','BA','Nordeste Baiano'),
	('2903300','Barro Preto','BA','Sul Baiano'),
	('2903409','Belmonte','BA','Sul Baiano'),
	('2903508','Belo Campo','BA','Centro Sul Baiano'),
	('2903607','Biritinga','BA','Nordeste Baiano'),
	('2903706','Boa Nova','BA','Centro Sul Baiano'),
	('2903805','Boa Vista do Tupim','BA','Centro Norte Baiano'),
	('2903904','Bom Jesus da Lapa','BA','Vale São-Franciscano da Bahia'),
	('2903953','Bom Jesus da Serra','BA','Centro Sul Baiano'),
	('2904001','Boninal','BA','Centro Sul Baiano'),
	('2904050','Bonito','BA','Centro Sul Baiano'),
	('2904100','Boquira','BA','Centro Sul Baiano'),
	('2904209','Botuporã','BA','Centro Sul Baiano'),
	('2904308','Brejões','BA','Centro Sul Baiano'),
	('2904407','Brejolândia','BA','Extremo Oeste Baiano'),
	('2904506','Brotas de Macaúbas','BA','Centro Sul Baiano'),
	('2904605','Brumado','BA','Centro Sul Baiano'),
	('2904704','Buerarema','BA','Sul Baiano'),
	('2904753','Buritirama','BA','Vale São-Franciscano da Bahia'),
	('2904803','Caatiba','BA','Centro Sul Baiano'),
	('2904852','Cabaceiras do Paraguaçu','BA','Metropolitana de Salvador'),
	('2904902','Cachoeira','BA','Metropolitana de Salvador'),
	('2905008','Caculé','BA','Centro Sul Baiano'),
	('2905107','Caém','BA','Centro Norte Baiano'),
	('2905156','Caetanos','BA','Centro Sul Baiano'),
	('2905206','Caetité','BA','Centro Sul Baiano'),
	('2905305','Cafarnaum','BA','Centro Norte Baiano'),
	('2905404','Cairu','BA','Sul Baiano'),
	('2905503','Caldeirão Grande','BA','Centro Norte Baiano'),
	('2905602','Camacan','BA','Sul Baiano'),
	('2905701','Camaçari','BA','Metropolitana de Salvador'),
	('2905800','Camamu','BA','Sul Baiano'),
	('2905909','Campo Alegre de Lourdes','BA','Vale São-Franciscano da Bahia'),
	('2906006','Campo Formoso','BA','Centro Norte Baiano'),
	('2906105','Canápolis','BA','Extremo Oeste Baiano'),
	('2906204','Canarana','BA','Centro Norte Baiano'),
	('2906303','Canavieiras','BA','Sul Baiano'),
	('2906402','Candeal','BA','Nordeste Baiano'),
	('2906501','Candeias','BA','Metropolitana de Salvador'),
	('2906600','Candiba','BA','Centro Sul Baiano'),
	('2906709','Cândido Sales','BA','Centro Sul Baiano'),
	('2906808','Cansanção','BA','Nordeste Baiano'),
	('2906824','Canudos','BA','Nordeste Baiano'),
	('2906857','Capela do Alto Alegre','BA','Nordeste Baiano'),
	('2906873','Capim Grosso','BA','Centro Norte Baiano'),
	('2906899','Caraíbas','BA','Centro Sul Baiano'),
	('2906907','Caravelas','BA','Sul Baiano'),
	('2907004','Cardeal da Silva','BA','Nordeste Baiano'),
	('2907103','Carinhanha','BA','Vale São-Franciscano da Bahia'),
	('2907202','Casa Nova','BA','Vale São-Franciscano da Bahia'),
	('2907301','Castro Alves','BA','Metropolitana de Salvador'),
	('2907400','Catolândia','BA','Extremo Oeste Baiano'),
	('2907509','Catu','BA','Metropolitana de Salvador'),
	('2907558','Caturama','BA','Centro Sul Baiano'),
	('2907608','Central','BA','Centro Norte Baiano'),
	('2907707','Chorrochó','BA','Vale São-Franciscano da Bahia'),
	('2907806','Cícero Dantas','BA','Nordeste Baiano'),
	('2907905','Cipó','BA','Nordeste Baiano'),
	('2908002','Coaraci','BA','Sul Baiano'),
	('2908101','Cocos','BA','Extremo Oeste Baiano'),
	('2908200','Conceição da Feira','BA','Centro Norte Baiano'),
	('2908309','Conceição do Almeida','BA','Metropolitana de Salvador'),
	('2908408','Conceição do Coité','BA','Nordeste Baiano'),
	('2908507','Conceição do Jacuípe','BA','Centro Norte Baiano'),
	('2908606','Conde','BA','Nordeste Baiano'),
	('2908705','Condeúba','BA','Centro Sul Baiano'),
	('2908804','Contendas do Sincorá','BA','Centro Sul Baiano'),
	('2908903','Coração de Maria','BA','Centro Norte Baiano'),
	('2909000','Cordeiros','BA','Centro Sul Baiano'),
	('2909109','Coribe','BA','Extremo Oeste Baiano'),
	('2909208','Coronel João Sá','BA','Nordeste Baiano'),
	('2909307','Correntina','BA','Extremo Oeste Baiano'),
	('2909406','Cotegipe','BA','Extremo Oeste Baiano'),
	('2909505','Cravolândia','BA','Centro Sul Baiano'),
	('2909604','Crisópolis','BA','Nordeste Baiano'),
	('2909703','Cristópolis','BA','Extremo Oeste Baiano'),
	('2909802','Cruz das Almas','BA','Metropolitana de Salvador'),
	('2909901','Curaçá','BA','Vale São-Franciscano da Bahia'),
	('2910008','Dário Meira','BA','Centro Sul Baiano'),
	('2910057','Dias d\'Ávila','BA','Metropolitana de Salvador'),
	('2910107','Dom Basílio','BA','Centro Sul Baiano'),
	('2910206','Dom Macedo Costa','BA','Metropolitana de Salvador'),
	('2910305','Elísio Medrado','BA','Centro Norte Baiano'),
	('2910404','Encruzilhada','BA','Centro Sul Baiano'),
	('2910503','Entre Rios','BA','Nordeste Baiano'),
	('2910602','Esplanada','BA','Nordeste Baiano'),
	('2910701','Euclides da Cunha','BA','Nordeste Baiano'),
	('2910727','Eunápolis','BA','Sul Baiano'),
	('2910750','Fátima','BA','Nordeste Baiano'),
	('2910776','Feira da Mata','BA','Vale São-Franciscano da Bahia'),
	('2910800','Feira de Santana','BA','Centro Norte Baiano'),
	('2910859','Filadélfia','BA','Centro Norte Baiano'),
	('2910909','Firmino Alves','BA','Sul Baiano'),
	('2911006','Floresta Azul','BA','Sul Baiano'),
	('2911105','Formosa do Rio Preto','BA','Extremo Oeste Baiano'),
	('2911204','Gandu','BA','Sul Baiano'),
	('2911253','Gavião','BA','Nordeste Baiano'),
	('2911303','Gentio do Ouro','BA','Centro Norte Baiano'),
	('2911402','Glória','BA','Vale São-Franciscano da Bahia'),
	('2911501','Gongogi','BA','Sul Baiano'),
	('2911600','Governador Mangabeira','BA','Metropolitana de Salvador'),
	('2911659','Guajeru','BA','Centro Sul Baiano'),
	('2911709','Guanambi','BA','Centro Sul Baiano'),
	('2911808','Guaratinga','BA','Sul Baiano'),
	('2911857','Heliópolis','BA','Nordeste Baiano'),
	('2911907','Iaçu','BA','Centro Norte Baiano'),
	('2912004','Ibiassucê','BA','Centro Sul Baiano'),
	('2912103','Ibicaraí','BA','Sul Baiano'),
	('2912202','Ibicoara','BA','Centro Sul Baiano'),
	('2912301','Ibicuí','BA','Centro Sul Baiano'),
	('2912400','Ibipeba','BA','Centro Norte Baiano'),
	('2912509','Ibipitanga','BA','Centro Sul Baiano'),
	('2912608','Ibiquera','BA','Centro Norte Baiano'),
	('2912707','Ibirapitanga','BA','Sul Baiano'),
	('2912806','Ibirapuã','BA','Sul Baiano'),
	('2912905','Ibirataia','BA','Sul Baiano'),
	('2913002','Ibitiara','BA','Centro Sul Baiano'),
	('2913101','Ibititá','BA','Centro Norte Baiano'),
	('2913200','Ibotirama','BA','Vale São-Franciscano da Bahia'),
	('2913309','Ichu','BA','Nordeste Baiano'),
	('2913408','Igaporã','BA','Centro Sul Baiano'),
	('2913457','Igrapiúna','BA','Sul Baiano'),
	('2913507','Iguaí','BA','Centro Sul Baiano'),
	('2913606','Ilhéus','BA','Sul Baiano'),
	('2913705','Inhambupe','BA','Nordeste Baiano'),
	('2913804','Ipecaetá','BA','Centro Norte Baiano'),
	('2913903','Ipiaú','BA','Sul Baiano'),
	('2914000','Ipirá','BA','Centro Norte Baiano'),
	('2914109','Ipupiara','BA','Centro Sul Baiano'),
	('2914208','Irajuba','BA','Centro Sul Baiano'),
	('2914307','Iramaia','BA','Centro Sul Baiano'),
	('2914406','Iraquara','BA','Centro Norte Baiano'),
	('2914505','Irará','BA','Centro Norte Baiano'),
	('2914604','Irecê','BA','Centro Norte Baiano'),
	('2914653','Itabela','BA','Sul Baiano'),
	('2914703','Itaberaba','BA','Centro Norte Baiano'),
	('2914802','Itabuna','BA','Sul Baiano'),
	('2914901','Itacaré','BA','Sul Baiano'),
	('2915007','Itaeté','BA','Centro Sul Baiano'),
	('2915106','Itagi','BA','Centro Sul Baiano'),
	('2915205','Itagibá','BA','Sul Baiano'),
	('2915304','Itagimirim','BA','Sul Baiano'),
	('2915353','Itaguaçu da Bahia','BA','Vale São-Franciscano da Bahia'),
	('2915403','Itaju do Colônia','BA','Sul Baiano'),
	('2915502','Itajuípe','BA','Sul Baiano'),
	('2915601','Itamaraju','BA','Sul Baiano'),
	('2915700','Itamari','BA','Sul Baiano'),
	('2915809','Itambé','BA','Centro Sul Baiano'),
	('2915908','Itanagra','BA','Metropolitana de Salvador'),
	('2916005','Itanhém','BA','Sul Baiano'),
	('2916104','Itaparica','BA','Metropolitana de Salvador'),
	('2916203','Itapé','BA','Sul Baiano'),
	('2916302','Itapebi','BA','Sul Baiano'),
	('2916401','Itapetinga','BA','Centro Sul Baiano'),
	('2916500','Itapicuru','BA','Nordeste Baiano'),
	('2916609','Itapitanga','BA','Sul Baiano'),
	('2916708','Itaquara','BA','Centro Sul Baiano'),
	('2916807','Itarantim','BA','Centro Sul Baiano'),
	('2916856','Itatim','BA','Centro Norte Baiano'),
	('2916906','Itiruçu','BA','Centro Sul Baiano'),
	('2917003','Itiúba','BA','Centro Norte Baiano'),
	('2917102','Itororó','BA','Centro Sul Baiano'),
	('2917201','Ituaçu','BA','Centro Sul Baiano'),
	('2917300','Ituberá','BA','Sul Baiano'),
	('2917334','Iuiu','BA','Centro Sul Baiano'),
	('2917359','Jaborandi','BA','Extremo Oeste Baiano'),
	('2917409','Jacaraci','BA','Centro Sul Baiano'),
	('2917508','Jacobina','BA','Centro Norte Baiano'),
	('2917607','Jaguaquara','BA','Centro Sul Baiano'),
	('2917706','Jaguarari','BA','Centro Norte Baiano'),
	('2917805','Jaguaripe','BA','Metropolitana de Salvador'),
	('2917904','Jandaíra','BA','Nordeste Baiano'),
	('2918001','Jequié','BA','Centro Sul Baiano'),
	('2918100','Jeremoabo','BA','Nordeste Baiano'),
	('2918209','Jiquiriçá','BA','Centro Sul Baiano'),
	('2918308','Jitaúna','BA','Centro Sul Baiano'),
	('2918357','João Dourado','BA','Centro Norte Baiano'),
	('2918407','Juazeiro','BA','Vale São-Franciscano da Bahia'),
	('2918456','Jucuruçu','BA','Sul Baiano'),
	('2918506','Jussara','BA','Centro Norte Baiano'),
	('2918555','Jussari','BA','Sul Baiano'),
	('2918605','Jussiape','BA','Centro Sul Baiano'),
	('2918704','Lafaiete Coutinho','BA','Centro Sul Baiano'),
	('2918753','Lagoa Real','BA','Centro Sul Baiano'),
	('2918803','Laje','BA','Centro Sul Baiano'),
	('2918902','Lajedão','BA','Sul Baiano'),
	('2919009','Lajedinho','BA','Centro Norte Baiano'),
	('2919058','Lajedo do Tabocal','BA','Centro Sul Baiano'),
	('2919108','Lamarão','BA','Nordeste Baiano'),
	('2919157','Lapão','BA','Centro Norte Baiano'),
	('2919207','Lauro de Freitas','BA','Metropolitana de Salvador'),
	('2919306','Lençóis','BA','Centro Sul Baiano'),
	('2919405','Licínio de Almeida','BA','Centro Sul Baiano'),
	('2919504','Livramento de Nossa Senhora','BA','Centro Sul Baiano'),
	('2919553','Luís Eduardo Magalhães','BA','Extremo Oeste Baiano'),
	('2919603','Macajuba','BA','Centro Norte Baiano'),
	('2919702','Macarani','BA','Centro Sul Baiano'),
	('2919801','Macaúbas','BA','Centro Sul Baiano'),
	('2919900','Macururé','BA','Vale São-Franciscano da Bahia'),
	('2919926','Madre de Deus','BA','Metropolitana de Salvador'),
	('2919959','Maetinga','BA','Centro Sul Baiano'),
	('2920007','Maiquinique','BA','Centro Sul Baiano'),
	('2920106','Mairi','BA','Centro Norte Baiano'),
	('2920205','Malhada','BA','Centro Sul Baiano'),
	('2920304','Malhada de Pedras','BA','Centro Sul Baiano'),
	('2920403','Manoel Vitorino','BA','Centro Sul Baiano'),
	('2920452','Mansidão','BA','Extremo Oeste Baiano'),
	('2920502','Maracás','BA','Centro Sul Baiano'),
	('2920601','Maragogipe','BA','Metropolitana de Salvador'),
	('2920700','Maraú','BA','Sul Baiano'),
	('2920809','Marcionílio Souza','BA','Centro Sul Baiano'),
	('2920908','Mascote','BA','Sul Baiano'),
	('2921005','Mata de São João','BA','Metropolitana de Salvador'),
	('2921054','Matina','BA','Centro Sul Baiano'),
	('2921104','Medeiros Neto','BA','Sul Baiano'),
	('2921203','Miguel Calmon','BA','Centro Norte Baiano'),
	('2921302','Milagres','BA','Centro Sul Baiano'),
	('2921401','Mirangaba','BA','Centro Norte Baiano'),
	('2921450','Mirante','BA','Centro Sul Baiano'),
	('2921500','Monte Santo','BA','Nordeste Baiano'),
	('2921609','Morpará','BA','Vale São-Franciscano da Bahia'),
	('2921708','Morro do Chapéu','BA','Centro Norte Baiano'),
	('2921807','Mortugaba','BA','Centro Sul Baiano'),
	('2921906','Mucugê','BA','Centro Sul Baiano'),
	('2922003','Mucuri','BA','Sul Baiano'),
	('2922052','Mulungu do Morro','BA','Centro Norte Baiano'),
	('2922102','Mundo Novo','BA','Centro Norte Baiano'),
	('2922201','Muniz Ferreira','BA','Metropolitana de Salvador'),
	('2922250','Muquém do São Francisco','BA','Vale São-Franciscano da Bahia'),
	('2922300','Muritiba','BA','Metropolitana de Salvador'),
	('2922409','Mutuípe','BA','Centro Sul Baiano'),
	('2922508','Nazaré','BA','Metropolitana de Salvador'),
	('2922607','Nilo Peçanha','BA','Sul Baiano'),
	('2922656','Nordestina','BA','Nordeste Baiano'),
	('2922706','Nova Canaã','BA','Centro Sul Baiano'),
	('2922730','Nova Fátima','BA','Nordeste Baiano'),
	('2922755','Nova Ibiá','BA','Sul Baiano'),
	('2922805','Nova Itarana','BA','Centro Sul Baiano'),
	('2922854','Nova Redenção','BA','Centro Sul Baiano'),
	('2922904','Nova Soure','BA','Nordeste Baiano'),
	('2923001','Nova Viçosa','BA','Sul Baiano'),
	('2923035','Novo Horizonte','BA','Centro Sul Baiano'),
	('2923050','Novo Triunfo','BA','Nordeste Baiano'),
	('2923100','Olindina','BA','Nordeste Baiano'),
	('2923209','Oliveira dos Brejinhos','BA','Centro Sul Baiano'),
	('2923308','Ouriçangas','BA','Centro Norte Baiano'),
	('2923357','Ourolândia','BA','Centro Norte Baiano'),
	('2923407','Palmas de Monte Alto','BA','Centro Sul Baiano'),
	('2923506','Palmeiras','BA','Centro Sul Baiano'),
	('2923605','Paramirim','BA','Centro Sul Baiano'),
	('2923704','Paratinga','BA','Vale São-Franciscano da Bahia'),
	('2923803','Paripiranga','BA','Nordeste Baiano'),
	('2923902','Pau Brasil','BA','Sul Baiano'),
	('2924009','Paulo Afonso','BA','Vale São-Franciscano da Bahia'),
	('2924058','Pé de Serra','BA','Nordeste Baiano'),
	('2924108','Pedrão','BA','Centro Norte Baiano'),
	('2924207','Pedro Alexandre','BA','Nordeste Baiano'),
	('2924306','Piatã','BA','Centro Sul Baiano'),
	('2924405','Pilão Arcado','BA','Vale São-Franciscano da Bahia'),
	('2924504','Pindaí','BA','Centro Sul Baiano'),
	('2924603','Pindobaçu','BA','Centro Norte Baiano'),
	('2924652','Pintadas','BA','Centro Norte Baiano'),
	('2924678','Piraí do Norte','BA','Sul Baiano'),
	('2924702','Piripá','BA','Centro Sul Baiano'),
	('2924801','Piritiba','BA','Centro Norte Baiano'),
	('2924900','Planaltino','BA','Centro Sul Baiano'),
	('2925006','Planalto','BA','Centro Sul Baiano'),
	('2925105','Poções','BA','Centro Sul Baiano'),
	('2925204','Pojuca','BA','Metropolitana de Salvador'),
	('2925253','Ponto Novo','BA','Centro Norte Baiano'),
	('2925303','Porto Seguro','BA','Sul Baiano'),
	('2925402','Potiraguá','BA','Centro Sul Baiano'),
	('2925501','Prado','BA','Sul Baiano'),
	('2925600','Presidente Dutra','BA','Centro Norte Baiano'),
	('2925709','Presidente Jânio Quadros','BA','Centro Sul Baiano'),
	('2925758','Presidente Tancredo Neves','BA','Sul Baiano'),
	('2925808','Queimadas','BA','Nordeste Baiano'),
	('2925907','Quijingue','BA','Nordeste Baiano'),
	('2925931','Quixabeira','BA','Centro Norte Baiano'),
	('2925956','Rafael Jambeiro','BA','Centro Norte Baiano'),
	('2926004','Remanso','BA','Vale São-Franciscano da Bahia'),
	('2926103','Retirolândia','BA','Nordeste Baiano'),
	('2926202','Riachão das Neves','BA','Extremo Oeste Baiano'),
	('2926301','Riachão do Jacuípe','BA','Nordeste Baiano'),
	('2926400','Riacho de Santana','BA','Centro Sul Baiano'),
	('2926509','Ribeira do Amparo','BA','Nordeste Baiano'),
	('2926608','Ribeira do Pombal','BA','Nordeste Baiano'),
	('2926657','Ribeirão do Largo','BA','Centro Sul Baiano'),
	('2926707','Rio de Contas','BA','Centro Sul Baiano'),
	('2926806','Rio do Antônio','BA','Centro Sul Baiano'),
	('2926905','Rio do Pires','BA','Centro Sul Baiano'),
	('2927002','Rio Real','BA','Nordeste Baiano'),
	('2927101','Rodelas','BA','Vale São-Franciscano da Bahia'),
	('2927200','Ruy Barbosa','BA','Centro Norte Baiano'),
	('2927309','Salinas da Margarida','BA','Metropolitana de Salvador'),
	('2927408','Salvador','BA','Metropolitana de Salvador'),
	('2927507','Santa Bárbara','BA','Centro Norte Baiano'),
	('2927606','Santa Brígida','BA','Nordeste Baiano'),
	('2927705','Santa Cruz Cabrália','BA','Sul Baiano'),
	('2927804','Santa Cruz da Vitória','BA','Sul Baiano'),
	('2927903','Santa Inês','BA','Centro Sul Baiano'),
	('2928000','Santaluz','BA','Nordeste Baiano'),
	('2928059','Santa Luzia','BA','Sul Baiano'),
	('2928109','Santa Maria da Vitória','BA','Extremo Oeste Baiano'),
	('2928208','Santana','BA','Extremo Oeste Baiano'),
	('2928307','Santanópolis','BA','Centro Norte Baiano'),
	('2928406','Santa Rita de Cássia','BA','Extremo Oeste Baiano'),
	('2928505','Santa Terezinha','BA','Centro Norte Baiano'),
	('2928604','Santo Amaro','BA','Metropolitana de Salvador'),
	('2928703','Santo Antônio de Jesus','BA','Metropolitana de Salvador'),
	('2928802','Santo Estêvão','BA','Centro Norte Baiano'),
	('2928901','São Desidério','BA','Extremo Oeste Baiano'),
	('2928950','São Domingos','BA','Nordeste Baiano'),
	('2929008','São Félix','BA','Metropolitana de Salvador'),
	('2929057','São Félix do Coribe','BA','Extremo Oeste Baiano'),
	('2929107','São Felipe','BA','Metropolitana de Salvador'),
	('2929206','São Francisco do Conde','BA','Metropolitana de Salvador'),
	('2929255','São Gabriel','BA','Centro Norte Baiano'),
	('2929305','São Gonçalo dos Campos','BA','Centro Norte Baiano'),
	('2929354','São José da Vitória','BA','Sul Baiano'),
	('2929370','São José do Jacuípe','BA','Centro Norte Baiano'),
	('2929404','São Miguel das Matas','BA','Centro Sul Baiano'),
	('2929503','São Sebastião do Passé','BA','Metropolitana de Salvador'),
	('2929602','Sapeaçu','BA','Metropolitana de Salvador'),
	('2929701','Sátiro Dias','BA','Nordeste Baiano'),
	('2929750','Saubara','BA','Metropolitana de Salvador'),
	('2929800','Saúde','BA','Centro Norte Baiano'),
	('2929909','Seabra','BA','Centro Sul Baiano'),
	('2930006','Sebastião Laranjeiras','BA','Centro Sul Baiano'),
	('2930105','Senhor do Bonfim','BA','Centro Norte Baiano'),
	('2930154','Serra do Ramalho','BA','Vale São-Franciscano da Bahia'),
	('2930204','Sento Sé','BA','Vale São-Franciscano da Bahia'),
	('2930303','Serra Dourada','BA','Extremo Oeste Baiano'),
	('2930402','Serra Preta','BA','Centro Norte Baiano'),
	('2930501','Serrinha','BA','Nordeste Baiano'),
	('2930600','Serrolândia','BA','Centro Norte Baiano'),
	('2930709','Simões Filho','BA','Metropolitana de Salvador'),
	('2930758','Sítio do Mato','BA','Vale São-Franciscano da Bahia'),
	('2930766','Sítio do Quinto','BA','Nordeste Baiano'),
	('2930774','Sobradinho','BA','Vale São-Franciscano da Bahia'),
	('2930808','Souto Soares','BA','Centro Norte Baiano'),
	('2930907','Tabocas do Brejo Velho','BA','Extremo Oeste Baiano'),
	('2931004','Tanhaçu','BA','Centro Sul Baiano'),
	('2931053','Tanque Novo','BA','Centro Sul Baiano'),
	('2931103','Tanquinho','BA','Centro Norte Baiano'),
	('2931202','Taperoá','BA','Sul Baiano'),
	('2931301','Tapiramutá','BA','Centro Norte Baiano'),
	('2931350','Teixeira de Freitas','BA','Sul Baiano'),
	('2931400','Teodoro Sampaio','BA','Centro Norte Baiano'),
	('2931509','Teofilândia','BA','Nordeste Baiano'),
	('2931608','Teolândia','BA','Sul Baiano'),
	('2931707','Terra Nova','BA','Metropolitana de Salvador'),
	('2931806','Tremedal','BA','Centro Sul Baiano'),
	('2931905','Tucano','BA','Nordeste Baiano'),
	('2932002','Uauá','BA','Nordeste Baiano'),
	('2932101','Ubaíra','BA','Centro Sul Baiano'),
	('2932200','Ubaitaba','BA','Sul Baiano'),
	('2932309','Ubatã','BA','Sul Baiano'),
	('2932408','Uibaí','BA','Centro Norte Baiano'),
	('2932457','Umburanas','BA','Centro Norte Baiano'),
	('2932507','Una','BA','Sul Baiano'),
	('2932606','Urandi','BA','Centro Sul Baiano'),
	('2932705','Uruçuca','BA','Sul Baiano'),
	('2932804','Utinga','BA','Centro Sul Baiano'),
	('2932903','Valença','BA','Sul Baiano'),
	('2933000','Valente','BA','Nordeste Baiano'),
	('2933059','Várzea da Roça','BA','Centro Norte Baiano'),
	('2933109','Várzea do Poço','BA','Centro Norte Baiano'),
	('2933158','Várzea Nova','BA','Centro Norte Baiano'),
	('2933174','Varzedo','BA','Metropolitana de Salvador'),
	('2933208','Vera Cruz','BA','Metropolitana de Salvador'),
	('2933257','Vereda','BA','Sul Baiano'),
	('2933307','Vitória da Conquista','BA','Centro Sul Baiano'),
	('2933406','Wagner','BA','Centro Sul Baiano'),
	('2933455','Wanderley','BA','Extremo Oeste Baiano'),
	('2933505','Wenceslau Guimarães','BA','Sul Baiano'),
	('2933604','Xique-Xique','BA','Vale São-Franciscano da Bahia'),
	('3100104','Abadia dos Dourados','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3100203','Abaeté','MG','Central Mineira'),
	('3100302','Abre Campo','MG','Zona da Mata'),
	('3100401','Acaiaca','MG','Zona da Mata'),
	('3100500','Açucena','MG','Vale do Rio Doce'),
	('3100609','Água Boa','MG','Vale do Rio Doce'),
	('3100708','Água Comprida','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3100807','Aguanil','MG','Oeste de Minas'),
	('3100906','Águas Formosas','MG','Vale do Mucuri'),
	('3101003','Águas Vermelhas','MG','Norte de Minas'),
	('3101102','Aimorés','MG','Vale do Rio Doce'),
	('3101201','Aiuruoca','MG','Sul/Sudoeste de Minas'),
	('3101300','Alagoa','MG','Sul/Sudoeste de Minas'),
	('3101409','Albertina','MG','Sul/Sudoeste de Minas'),
	('3101508','Além Paraíba','MG','Zona da Mata'),
	('3101607','Alfenas','MG','Sul/Sudoeste de Minas'),
	('3101631','Alfredo Vasconcelos','MG','Campo das Vertentes'),
	('3101706','Almenara','MG','Jequitinhonha'),
	('3101805','Alpercata','MG','Vale do Rio Doce'),
	('3101904','Alpinópolis','MG','Sul/Sudoeste de Minas'),
	('3102001','Alterosa','MG','Sul/Sudoeste de Minas'),
	('3102050','Alto Caparaó','MG','Zona da Mata'),
	('3102100','Alto Rio Doce','MG','Zona da Mata'),
	('3102209','Alvarenga','MG','Vale do Rio Doce'),
	('3102308','Alvinópolis','MG','Metropolitana de Belo Horizonte'),
	('3102407','Alvorada de Minas','MG','Metropolitana de Belo Horizonte'),
	('3102506','Amparo do Serra','MG','Zona da Mata'),
	('3102605','Andradas','MG','Sul/Sudoeste de Minas'),
	('3102704','Cachoeira de Pajeú','MG','Jequitinhonha'),
	('3102803','Andrelândia','MG','Sul/Sudoeste de Minas'),
	('3102852','Angelândia','MG','Jequitinhonha'),
	('3102902','Antônio Carlos','MG','Campo das Vertentes'),
	('3103009','Antônio Dias','MG','Vale do Rio Doce'),
	('3103108','Antônio Prado de Minas','MG','Zona da Mata'),
	('3103207','Araçaí','MG','Metropolitana de Belo Horizonte'),
	('3103306','Aracitaba','MG','Zona da Mata'),
	('3103405','Araçuaí','MG','Jequitinhonha'),
	('3103504','Araguari','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3103603','Arantina','MG','Sul/Sudoeste de Minas'),
	('3103702','Araponga','MG','Zona da Mata'),
	('3103751','Araporã','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3103801','Arapuá','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3103900','Araújos','MG','Central Mineira'),
	('3104007','Araxá','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3104106','Arceburgo','MG','Sul/Sudoeste de Minas'),
	('3104205','Arcos','MG','Oeste de Minas'),
	('3104304','Areado','MG','Sul/Sudoeste de Minas'),
	('3104403','Argirita','MG','Zona da Mata'),
	('3104452','Aricanduva','MG','Jequitinhonha'),
	('3104502','Arinos','MG','Noroeste de Minas'),
	('3104601','Astolfo Dutra','MG','Zona da Mata'),
	('3104700','Ataléia','MG','Vale do Mucuri'),
	('3104809','Augusto de Lima','MG','Central Mineira'),
	('3104908','Baependi','MG','Sul/Sudoeste de Minas'),
	('3105004','Baldim','MG','Metropolitana de Belo Horizonte'),
	('3105103','Bambuí','MG','Oeste de Minas'),
	('3105202','Bandeira','MG','Jequitinhonha'),
	('3105301','Bandeira do Sul','MG','Sul/Sudoeste de Minas'),
	('3105400','Barão de Cocais','MG','Metropolitana de Belo Horizonte'),
	('3105509','Barão de Monte Alto','MG','Zona da Mata'),
	('3105608','Barbacena','MG','Campo das Vertentes'),
	('3105707','Barra Longa','MG','Zona da Mata'),
	('3105905','Barroso','MG','Campo das Vertentes'),
	('3106002','Bela Vista de Minas','MG','Metropolitana de Belo Horizonte'),
	('3106101','Belmiro Braga','MG','Zona da Mata'),
	('3106200','Belo Horizonte','MG','Metropolitana de Belo Horizonte'),
	('3106309','Belo Oriente','MG','Vale do Rio Doce'),
	('3106408','Belo Vale','MG','Metropolitana de Belo Horizonte'),
	('3106507','Berilo','MG','Jequitinhonha'),
	('3106606','Bertópolis','MG','Vale do Mucuri'),
	('3106655','Berizal','MG','Norte de Minas'),
	('3106705','Betim','MG','Metropolitana de Belo Horizonte'),
	('3106804','Bias Fortes','MG','Zona da Mata'),
	('3106903','Bicas','MG','Zona da Mata'),
	('3107000','Biquinhas','MG','Central Mineira'),
	('3107109','Boa Esperança','MG','Sul/Sudoeste de Minas'),
	('3107208','Bocaina de Minas','MG','Sul/Sudoeste de Minas'),
	('3107307','Bocaiúva','MG','Norte de Minas'),
	('3107406','Bom Despacho','MG','Central Mineira'),
	('3107505','Bom Jardim de Minas','MG','Sul/Sudoeste de Minas'),
	('3107604','Bom Jesus da Penha','MG','Sul/Sudoeste de Minas'),
	('3107703','Bom Jesus do Amparo','MG','Metropolitana de Belo Horizonte'),
	('3107802','Bom Jesus do Galho','MG','Vale do Rio Doce'),
	('3107901','Bom Repouso','MG','Sul/Sudoeste de Minas'),
	('3108008','Bom Sucesso','MG','Oeste de Minas'),
	('3108107','Bonfim','MG','Metropolitana de Belo Horizonte'),
	('3108206','Bonfinópolis de Minas','MG','Noroeste de Minas'),
	('3108255','Bonito de Minas','MG','Norte de Minas'),
	('3108305','Borda da Mata','MG','Sul/Sudoeste de Minas'),
	('3108404','Botelhos','MG','Sul/Sudoeste de Minas'),
	('3108503','Botumirim','MG','Norte de Minas'),
	('3108552','Brasilândia de Minas','MG','Noroeste de Minas'),
	('3108602','Brasília de Minas','MG','Norte de Minas'),
	('3108701','Brás Pires','MG','Zona da Mata'),
	('3108800','Braúnas','MG','Vale do Rio Doce'),
	('3108909','Brazópolis','MG','Sul/Sudoeste de Minas'),
	('3109006','Brumadinho','MG','Metropolitana de Belo Horizonte'),
	('3109105','Bueno Brandão','MG','Sul/Sudoeste de Minas'),
	('3109204','Buenópolis','MG','Central Mineira'),
	('3109253','Bugre','MG','Vale do Rio Doce'),
	('3109303','Buritis','MG','Noroeste de Minas'),
	('3109402','Buritizeiro','MG','Norte de Minas'),
	('3109451','Cabeceira Grande','MG','Noroeste de Minas'),
	('3109501','Cabo Verde','MG','Sul/Sudoeste de Minas'),
	('3109600','Cachoeira da Prata','MG','Metropolitana de Belo Horizonte'),
	('3109709','Cachoeira de Minas','MG','Sul/Sudoeste de Minas'),
	('3109808','Cachoeira Dourada','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3109907','Caetanópolis','MG','Metropolitana de Belo Horizonte'),
	('3110004','Caeté','MG','Metropolitana de Belo Horizonte'),
	('3110103','Caiana','MG','Zona da Mata'),
	('3110202','Cajuri','MG','Zona da Mata'),
	('3110301','Caldas','MG','Sul/Sudoeste de Minas'),
	('3110400','Camacho','MG','Oeste de Minas'),
	('3110509','Camanducaia','MG','Sul/Sudoeste de Minas'),
	('3110608','Cambuí','MG','Sul/Sudoeste de Minas'),
	('3110707','Cambuquira','MG','Sul/Sudoeste de Minas'),
	('3110806','Campanário','MG','Vale do Rio Doce'),
	('3110905','Campanha','MG','Sul/Sudoeste de Minas'),
	('3111002','Campestre','MG','Sul/Sudoeste de Minas'),
	('3111101','Campina Verde','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3111150','Campo Azul','MG','Norte de Minas'),
	('3111200','Campo Belo','MG','Oeste de Minas'),
	('3111309','Campo do Meio','MG','Sul/Sudoeste de Minas'),
	('3111408','Campo Florido','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3111507','Campos Altos','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3111606','Campos Gerais','MG','Sul/Sudoeste de Minas'),
	('3111705','Canaã','MG','Zona da Mata'),
	('3111804','Canápolis','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3111903','Cana Verde','MG','Oeste de Minas'),
	('3112000','Candeias','MG','Oeste de Minas'),
	('3112059','Cantagalo','MG','Vale do Rio Doce'),
	('3112109','Caparaó','MG','Zona da Mata'),
	('3112208','Capela Nova','MG','Campo das Vertentes'),
	('3112307','Capelinha','MG','Jequitinhonha'),
	('3112406','Capetinga','MG','Sul/Sudoeste de Minas'),
	('3112505','Capim Branco','MG','Metropolitana de Belo Horizonte'),
	('3112604','Capinópolis','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3112653','Capitão Andrade','MG','Vale do Rio Doce'),
	('3112703','Capitão Enéas','MG','Norte de Minas'),
	('3112802','Capitólio','MG','Sul/Sudoeste de Minas'),
	('3112901','Caputira','MG','Zona da Mata'),
	('3113008','Caraí','MG','Jequitinhonha'),
	('3113107','Caranaíba','MG','Campo das Vertentes'),
	('3113206','Carandaí','MG','Campo das Vertentes'),
	('3113305','Carangola','MG','Zona da Mata'),
	('3113404','Caratinga','MG','Vale do Rio Doce'),
	('3113503','Carbonita','MG','Jequitinhonha'),
	('3113602','Careaçu','MG','Sul/Sudoeste de Minas'),
	('3113701','Carlos Chagas','MG','Vale do Mucuri'),
	('3113800','Carmésia','MG','Vale do Rio Doce'),
	('3113909','Carmo da Cachoeira','MG','Sul/Sudoeste de Minas'),
	('3114006','Carmo da Mata','MG','Oeste de Minas'),
	('3114105','Carmo de Minas','MG','Sul/Sudoeste de Minas'),
	('3114204','Carmo do Cajuru','MG','Oeste de Minas'),
	('3114303','Carmo do Paranaíba','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3114402','Carmo do Rio Claro','MG','Sul/Sudoeste de Minas'),
	('3114501','Carmópolis de Minas','MG','Oeste de Minas'),
	('3114550','Carneirinho','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3114600','Carrancas','MG','Campo das Vertentes'),
	('3114709','Carvalhópolis','MG','Sul/Sudoeste de Minas'),
	('3114808','Carvalhos','MG','Sul/Sudoeste de Minas'),
	('3114907','Casa Grande','MG','Metropolitana de Belo Horizonte'),
	('3115003','Cascalho Rico','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3115102','Cássia','MG','Sul/Sudoeste de Minas'),
	('3115201','Conceição da Barra de Minas','MG','Campo das Vertentes'),
	('3115300','Cataguases','MG','Zona da Mata'),
	('3115359','Catas Altas','MG','Metropolitana de Belo Horizonte'),
	('3115409','Catas Altas da Noruega','MG','Metropolitana de Belo Horizonte'),
	('3115458','Catuji','MG','Vale do Mucuri'),
	('3115474','Catuti','MG','Norte de Minas'),
	('3115508','Caxambu','MG','Sul/Sudoeste de Minas'),
	('3115607','Cedro do Abaeté','MG','Central Mineira'),
	('3115706','Central de Minas','MG','Vale do Rio Doce'),
	('3115805','Centralina','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3115904','Chácara','MG','Zona da Mata'),
	('3116001','Chalé','MG','Zona da Mata'),
	('3116100','Chapada do Norte','MG','Jequitinhonha'),
	('3116159','Chapada Gaúcha','MG','Norte de Minas'),
	('3116209','Chiador','MG','Zona da Mata'),
	('3116308','Cipotânea','MG','Zona da Mata'),
	('3116407','Claraval','MG','Sul/Sudoeste de Minas'),
	('3116506','Claro dos Poções','MG','Norte de Minas'),
	('3116605','Cláudio','MG','Oeste de Minas'),
	('3116704','Coimbra','MG','Zona da Mata'),
	('3116803','Coluna','MG','Vale do Rio Doce'),
	('3116902','Comendador Gomes','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3117009','Comercinho','MG','Jequitinhonha'),
	('3117108','Conceição da Aparecida','MG','Sul/Sudoeste de Minas'),
	('3117207','Conceição das Pedras','MG','Sul/Sudoeste de Minas'),
	('3117306','Conceição das Alagoas','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3117405','Conceição de Ipanema','MG','Vale do Rio Doce'),
	('3117504','Conceição do Mato Dentro','MG','Metropolitana de Belo Horizonte'),
	('3117603','Conceição do Pará','MG','Oeste de Minas'),
	('3117702','Conceição do Rio Verde','MG','Sul/Sudoeste de Minas'),
	('3117801','Conceição dos Ouros','MG','Sul/Sudoeste de Minas'),
	('3117836','Cônego Marinho','MG','Norte de Minas'),
	('3117876','Confins','MG','Metropolitana de Belo Horizonte'),
	('3117900','Congonhal','MG','Sul/Sudoeste de Minas'),
	('3118007','Congonhas','MG','Metropolitana de Belo Horizonte'),
	('3118106','Congonhas do Norte','MG','Metropolitana de Belo Horizonte'),
	('3118205','Conquista','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3118304','Conselheiro Lafaiete','MG','Metropolitana de Belo Horizonte'),
	('3118403','Conselheiro Pena','MG','Vale do Rio Doce'),
	('3118502','Consolação','MG','Sul/Sudoeste de Minas'),
	('3118601','Contagem','MG','Metropolitana de Belo Horizonte'),
	('3118700','Coqueiral','MG','Sul/Sudoeste de Minas'),
	('3118809','Coração de Jesus','MG','Norte de Minas'),
	('3118908','Cordisburgo','MG','Metropolitana de Belo Horizonte'),
	('3119005','Cordislândia','MG','Sul/Sudoeste de Minas'),
	('3119104','Corinto','MG','Central Mineira'),
	('3119203','Coroaci','MG','Vale do Rio Doce'),
	('3119302','Coromandel','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3119401','Coronel Fabriciano','MG','Vale do Rio Doce'),
	('3119500','Coronel Murta','MG','Jequitinhonha'),
	('3119609','Coronel Pacheco','MG','Zona da Mata'),
	('3119708','Coronel Xavier Chaves','MG','Campo das Vertentes'),
	('3119807','Córrego Danta','MG','Oeste de Minas'),
	('3119906','Córrego do Bom Jesus','MG','Sul/Sudoeste de Minas'),
	('3119955','Córrego Fundo','MG','Oeste de Minas'),
	('3120003','Córrego Novo','MG','Vale do Rio Doce'),
	('3120102','Couto de Magalhães de Minas','MG','Jequitinhonha'),
	('3120151','Crisólita','MG','Vale do Mucuri'),
	('3120201','Cristais','MG','Oeste de Minas'),
	('3120300','Cristália','MG','Norte de Minas'),
	('3120409','Cristiano Otoni','MG','Metropolitana de Belo Horizonte'),
	('3120508','Cristina','MG','Sul/Sudoeste de Minas'),
	('3120607','Crucilândia','MG','Metropolitana de Belo Horizonte'),
	('3120706','Cruzeiro da Fortaleza','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3120805','Cruzília','MG','Sul/Sudoeste de Minas'),
	('3120839','Cuparaque','MG','Vale do Rio Doce'),
	('3120870','Curral de Dentro','MG','Norte de Minas'),
	('3120904','Curvelo','MG','Central Mineira'),
	('3121001','Datas','MG','Jequitinhonha'),
	('3121100','Delfim Moreira','MG','Sul/Sudoeste de Minas'),
	('3121209','Delfinópolis','MG','Sul/Sudoeste de Minas'),
	('3121258','Delta','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3121308','Descoberto','MG','Zona da Mata'),
	('3121407','Desterro de Entre Rios','MG','Metropolitana de Belo Horizonte'),
	('3121506','Desterro do Melo','MG','Campo das Vertentes'),
	('3121605','Diamantina','MG','Jequitinhonha'),
	('3121704','Diogo de Vasconcelos','MG','Metropolitana de Belo Horizonte'),
	('3121803','Dionísio','MG','Metropolitana de Belo Horizonte'),
	('3121902','Divinésia','MG','Zona da Mata'),
	('3122009','Divino','MG','Zona da Mata'),
	('3122108','Divino das Laranjeiras','MG','Vale do Rio Doce'),
	('3122207','Divinolândia de Minas','MG','Vale do Rio Doce'),
	('3122306','Divinópolis','MG','Oeste de Minas'),
	('3122355','Divisa Alegre','MG','Norte de Minas'),
	('3122405','Divisa Nova','MG','Sul/Sudoeste de Minas'),
	('3122454','Divisópolis','MG','Jequitinhonha'),
	('3122470','Dom Bosco','MG','Noroeste de Minas'),
	('3122504','Dom Cavati','MG','Vale do Rio Doce'),
	('3122603','Dom Joaquim','MG','Metropolitana de Belo Horizonte'),
	('3122702','Dom Silvério','MG','Zona da Mata'),
	('3122801','Dom Viçoso','MG','Sul/Sudoeste de Minas'),
	('3122900','Dona Eusébia','MG','Zona da Mata'),
	('3123007','Dores de Campos','MG','Campo das Vertentes'),
	('3123106','Dores de Guanhães','MG','Vale do Rio Doce'),
	('3123205','Dores do Indaiá','MG','Central Mineira'),
	('3123304','Dores do Turvo','MG','Zona da Mata'),
	('3123403','Doresópolis','MG','Oeste de Minas'),
	('3123502','Douradoquara','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3123528','Durandé','MG','Zona da Mata'),
	('3123601','Elói Mendes','MG','Sul/Sudoeste de Minas'),
	('3123700','Engenheiro Caldas','MG','Vale do Rio Doce'),
	('3123809','Engenheiro Navarro','MG','Norte de Minas'),
	('3123858','Entre Folhas','MG','Vale do Rio Doce'),
	('3123908','Entre Rios de Minas','MG','Metropolitana de Belo Horizonte'),
	('3124005','Ervália','MG','Zona da Mata'),
	('3124104','Esmeraldas','MG','Metropolitana de Belo Horizonte'),
	('3124203','Espera Feliz','MG','Zona da Mata'),
	('3124302','Espinosa','MG','Norte de Minas'),
	('3124401','Espírito Santo do Dourado','MG','Sul/Sudoeste de Minas'),
	('3124500','Estiva','MG','Sul/Sudoeste de Minas'),
	('3124609','Estrela Dalva','MG','Zona da Mata'),
	('3124708','Estrela do Indaiá','MG','Central Mineira'),
	('3124807','Estrela do Sul','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3124906','Eugenópolis','MG','Zona da Mata'),
	('3125002','Ewbank da Câmara','MG','Zona da Mata'),
	('3125101','Extrema','MG','Sul/Sudoeste de Minas'),
	('3125200','Fama','MG','Sul/Sudoeste de Minas'),
	('3125309','Faria Lemos','MG','Zona da Mata'),
	('3125408','Felício dos Santos','MG','Jequitinhonha'),
	('3125507','São Gonçalo do Rio Preto','MG','Jequitinhonha'),
	('3125606','Felisburgo','MG','Jequitinhonha'),
	('3125705','Felixlândia','MG','Central Mineira'),
	('3125804','Fernandes Tourinho','MG','Vale do Rio Doce'),
	('3125903','Ferros','MG','Metropolitana de Belo Horizonte'),
	('3125952','Fervedouro','MG','Zona da Mata'),
	('3126000','Florestal','MG','Metropolitana de Belo Horizonte'),
	('3126109','Formiga','MG','Oeste de Minas'),
	('3126208','Formoso','MG','Noroeste de Minas'),
	('3126307','Fortaleza de Minas','MG','Sul/Sudoeste de Minas'),
	('3126406','Fortuna de Minas','MG','Metropolitana de Belo Horizonte'),
	('3126505','Francisco Badaró','MG','Jequitinhonha'),
	('3126604','Francisco Dumont','MG','Norte de Minas'),
	('3126703','Francisco Sá','MG','Norte de Minas'),
	('3126752','Franciscópolis','MG','Vale do Mucuri'),
	('3126802','Frei Gaspar','MG','Vale do Mucuri'),
	('3126901','Frei Inocêncio','MG','Vale do Rio Doce'),
	('3126950','Frei Lagonegro','MG','Vale do Rio Doce'),
	('3127008','Fronteira','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3127057','Fronteira dos Vales','MG','Vale do Mucuri'),
	('3127073','Fruta de Leite','MG','Norte de Minas'),
	('3127107','Frutal','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3127206','Funilândia','MG','Metropolitana de Belo Horizonte'),
	('3127305','Galiléia','MG','Vale do Rio Doce'),
	('3127339','Gameleiras','MG','Norte de Minas'),
	('3127354','Glaucilândia','MG','Norte de Minas'),
	('3127370','Goiabeira','MG','Vale do Rio Doce'),
	('3127388','Goianá','MG','Zona da Mata'),
	('3127404','Gonçalves','MG','Sul/Sudoeste de Minas'),
	('3127503','Gonzaga','MG','Vale do Rio Doce'),
	('3127602','Gouveia','MG','Jequitinhonha'),
	('3127701','Governador Valadares','MG','Vale do Rio Doce'),
	('3127800','Grão Mogol','MG','Norte de Minas'),
	('3127909','Grupiara','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3128006','Guanhães','MG','Vale do Rio Doce'),
	('3128105','Guapé','MG','Sul/Sudoeste de Minas'),
	('3128204','Guaraciaba','MG','Zona da Mata'),
	('3128253','Guaraciama','MG','Norte de Minas'),
	('3128303','Guaranésia','MG','Sul/Sudoeste de Minas'),
	('3128402','Guarani','MG','Zona da Mata'),
	('3128501','Guarará','MG','Zona da Mata'),
	('3128600','Guarda-Mor','MG','Noroeste de Minas'),
	('3128709','Guaxupé','MG','Sul/Sudoeste de Minas'),
	('3128808','Guidoval','MG','Zona da Mata'),
	('3128907','Guimarânia','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3129004','Guiricema','MG','Zona da Mata'),
	('3129103','Gurinhatã','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3129202','Heliodora','MG','Sul/Sudoeste de Minas'),
	('3129301','Iapu','MG','Vale do Rio Doce'),
	('3129400','Ibertioga','MG','Campo das Vertentes'),
	('3129509','Ibiá','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3129608','Ibiaí','MG','Norte de Minas'),
	('3129657','Ibiracatu','MG','Norte de Minas'),
	('3129707','Ibiraci','MG','Sul/Sudoeste de Minas'),
	('3129806','Ibirité','MG','Metropolitana de Belo Horizonte'),
	('3129905','Ibitiúra de Minas','MG','Sul/Sudoeste de Minas'),
	('3130002','Ibituruna','MG','Oeste de Minas'),
	('3130051','Icaraí de Minas','MG','Norte de Minas'),
	('3130101','Igarapé','MG','Metropolitana de Belo Horizonte'),
	('3130200','Igaratinga','MG','Oeste de Minas'),
	('3130309','Iguatama','MG','Oeste de Minas'),
	('3130408','Ijaci','MG','Campo das Vertentes'),
	('3130507','Ilicínea','MG','Sul/Sudoeste de Minas'),
	('3130556','Imbé de Minas','MG','Vale do Rio Doce'),
	('3130606','Inconfidentes','MG','Sul/Sudoeste de Minas'),
	('3130655','Indaiabira','MG','Norte de Minas'),
	('3130705','Indianópolis','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3130804','Ingaí','MG','Campo das Vertentes'),
	('3130903','Inhapim','MG','Vale do Rio Doce'),
	('3131000','Inhaúma','MG','Metropolitana de Belo Horizonte'),
	('3131109','Inimutaba','MG','Central Mineira'),
	('3131158','Ipaba','MG','Vale do Rio Doce'),
	('3131208','Ipanema','MG','Vale do Rio Doce'),
	('3131307','Ipatinga','MG','Vale do Rio Doce'),
	('3131406','Ipiaçu','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3131505','Ipuiúna','MG','Sul/Sudoeste de Minas'),
	('3131604','Iraí de Minas','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3131703','Itabira','MG','Metropolitana de Belo Horizonte'),
	('3131802','Itabirinha','MG','Vale do Rio Doce'),
	('3131901','Itabirito','MG','Metropolitana de Belo Horizonte'),
	('3132008','Itacambira','MG','Norte de Minas'),
	('3132107','Itacarambi','MG','Norte de Minas'),
	('3132206','Itaguara','MG','Metropolitana de Belo Horizonte'),
	('3132305','Itaipé','MG','Vale do Mucuri'),
	('3132404','Itajubá','MG','Sul/Sudoeste de Minas'),
	('3132503','Itamarandiba','MG','Jequitinhonha'),
	('3132602','Itamarati de Minas','MG','Zona da Mata'),
	('3132701','Itambacuri','MG','Vale do Rio Doce'),
	('3132800','Itambé do Mato Dentro','MG','Metropolitana de Belo Horizonte'),
	('3132909','Itamogi','MG','Sul/Sudoeste de Minas'),
	('3133006','Itamonte','MG','Sul/Sudoeste de Minas'),
	('3133105','Itanhandu','MG','Sul/Sudoeste de Minas'),
	('3133204','Itanhomi','MG','Vale do Rio Doce'),
	('3133303','Itaobim','MG','Jequitinhonha'),
	('3133402','Itapagipe','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3133501','Itapecerica','MG','Oeste de Minas'),
	('3133600','Itapeva','MG','Sul/Sudoeste de Minas'),
	('3133709','Itatiaiuçu','MG','Metropolitana de Belo Horizonte'),
	('3133758','Itaú de Minas','MG','Sul/Sudoeste de Minas'),
	('3133808','Itaúna','MG','Oeste de Minas'),
	('3133907','Itaverava','MG','Metropolitana de Belo Horizonte'),
	('3134004','Itinga','MG','Jequitinhonha'),
	('3134103','Itueta','MG','Vale do Rio Doce'),
	('3134202','Ituiutaba','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3134301','Itumirim','MG','Campo das Vertentes'),
	('3134400','Iturama','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3134509','Itutinga','MG','Campo das Vertentes'),
	('3134608','Jaboticatubas','MG','Metropolitana de Belo Horizonte'),
	('3134707','Jacinto','MG','Jequitinhonha'),
	('3134806','Jacuí','MG','Sul/Sudoeste de Minas'),
	('3134905','Jacutinga','MG','Sul/Sudoeste de Minas'),
	('3135001','Jaguaraçu','MG','Vale do Rio Doce'),
	('3135050','Jaíba','MG','Norte de Minas'),
	('3135076','Jampruca','MG','Vale do Rio Doce'),
	('3135100','Janaúba','MG','Norte de Minas'),
	('3135209','Januária','MG','Norte de Minas'),
	('3135308','Japaraíba','MG','Central Mineira'),
	('3135357','Japonvar','MG','Norte de Minas'),
	('3135407','Jeceaba','MG','Metropolitana de Belo Horizonte'),
	('3135456','Jenipapo de Minas','MG','Jequitinhonha'),
	('3135506','Jequeri','MG','Zona da Mata'),
	('3135605','Jequitaí','MG','Norte de Minas'),
	('3135704','Jequitibá','MG','Metropolitana de Belo Horizonte'),
	('3135803','Jequitinhonha','MG','Jequitinhonha'),
	('3135902','Jesuânia','MG','Sul/Sudoeste de Minas'),
	('3136009','Joaíma','MG','Jequitinhonha'),
	('3136108','Joanésia','MG','Vale do Rio Doce'),
	('3136207','João Monlevade','MG','Metropolitana de Belo Horizonte'),
	('3136306','João Pinheiro','MG','Noroeste de Minas'),
	('3136405','Joaquim Felício','MG','Central Mineira'),
	('3136504','Jordânia','MG','Jequitinhonha'),
	('3136520','José Gonçalves de Minas','MG','Jequitinhonha'),
	('3136553','José Raydan','MG','Vale do Rio Doce'),
	('3136579','Josenópolis','MG','Norte de Minas'),
	('3136603','Nova União','MG','Metropolitana de Belo Horizonte'),
	('3136652','Juatuba','MG','Metropolitana de Belo Horizonte'),
	('3136702','Juiz de Fora','MG','Zona da Mata'),
	('3136801','Juramento','MG','Norte de Minas'),
	('3136900','Juruaia','MG','Sul/Sudoeste de Minas'),
	('3136959','Juvenília','MG','Norte de Minas'),
	('3137007','Ladainha','MG','Vale do Mucuri'),
	('3137106','Lagamar','MG','Noroeste de Minas'),
	('3137205','Lagoa da Prata','MG','Central Mineira'),
	('3137304','Lagoa dos Patos','MG','Norte de Minas'),
	('3137403','Lagoa Dourada','MG','Campo das Vertentes'),
	('3137502','Lagoa Formosa','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3137536','Lagoa Grande','MG','Noroeste de Minas'),
	('3137601','Lagoa Santa','MG','Metropolitana de Belo Horizonte'),
	('3137700','Lajinha','MG','Zona da Mata'),
	('3137809','Lambari','MG','Sul/Sudoeste de Minas'),
	('3137908','Lamim','MG','Zona da Mata'),
	('3138005','Laranjal','MG','Zona da Mata'),
	('3138104','Lassance','MG','Norte de Minas'),
	('3138203','Lavras','MG','Campo das Vertentes'),
	('3138302','Leandro Ferreira','MG','Central Mineira'),
	('3138351','Leme do Prado','MG','Jequitinhonha'),
	('3138401','Leopoldina','MG','Zona da Mata'),
	('3138500','Liberdade','MG','Sul/Sudoeste de Minas'),
	('3138609','Lima Duarte','MG','Zona da Mata'),
	('3138625','Limeira do Oeste','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3138658','Lontra','MG','Norte de Minas'),
	('3138674','Luisburgo','MG','Zona da Mata'),
	('3138682','Luislândia','MG','Norte de Minas'),
	('3138708','Luminárias','MG','Campo das Vertentes'),
	('3138807','Luz','MG','Central Mineira'),
	('3138906','Machacalis','MG','Vale do Mucuri'),
	('3139003','Machado','MG','Sul/Sudoeste de Minas'),
	('3139102','Madre de Deus de Minas','MG','Campo das Vertentes'),
	('3139201','Malacacheta','MG','Vale do Mucuri'),
	('3139250','Mamonas','MG','Norte de Minas'),
	('3139300','Manga','MG','Norte de Minas'),
	('3139409','Manhuaçu','MG','Zona da Mata'),
	('3139508','Manhumirim','MG','Zona da Mata'),
	('3139607','Mantena','MG','Vale do Rio Doce'),
	('3139706','Maravilhas','MG','Metropolitana de Belo Horizonte'),
	('3139805','Mar de Espanha','MG','Zona da Mata'),
	('3139904','Maria da Fé','MG','Sul/Sudoeste de Minas'),
	('3140001','Mariana','MG','Metropolitana de Belo Horizonte'),
	('3140100','Marilac','MG','Vale do Rio Doce'),
	('3140159','Mário Campos','MG','Metropolitana de Belo Horizonte'),
	('3140209','Maripá de Minas','MG','Zona da Mata'),
	('3140308','Marliéria','MG','Vale do Rio Doce'),
	('3140407','Marmelópolis','MG','Sul/Sudoeste de Minas'),
	('3140506','Martinho Campos','MG','Central Mineira'),
	('3140530','Martins Soares','MG','Zona da Mata'),
	('3140555','Mata Verde','MG','Jequitinhonha'),
	('3140605','Materlândia','MG','Vale do Rio Doce'),
	('3140704','Mateus Leme','MG','Metropolitana de Belo Horizonte'),
	('3140803','Matias Barbosa','MG','Zona da Mata'),
	('3140852','Matias Cardoso','MG','Norte de Minas'),
	('3140902','Matipó','MG','Zona da Mata'),
	('3141009','Mato Verde','MG','Norte de Minas'),
	('3141108','Matozinhos','MG','Metropolitana de Belo Horizonte'),
	('3141207','Matutina','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3141306','Medeiros','MG','Oeste de Minas'),
	('3141405','Medina','MG','Jequitinhonha'),
	('3141504','Mendes Pimentel','MG','Vale do Rio Doce'),
	('3141603','Mercês','MG','Zona da Mata'),
	('3141702','Mesquita','MG','Vale do Rio Doce'),
	('3141801','Minas Novas','MG','Jequitinhonha'),
	('3141900','Minduri','MG','Sul/Sudoeste de Minas'),
	('3142007','Mirabela','MG','Norte de Minas'),
	('3142106','Miradouro','MG','Zona da Mata'),
	('3142205','Miraí','MG','Zona da Mata'),
	('3142254','Miravânia','MG','Norte de Minas'),
	('3142304','Moeda','MG','Metropolitana de Belo Horizonte'),
	('3142403','Moema','MG','Central Mineira'),
	('3142502','Monjolos','MG','Central Mineira'),
	('3142601','Monsenhor Paulo','MG','Sul/Sudoeste de Minas'),
	('3142700','Montalvânia','MG','Norte de Minas'),
	('3142809','Monte Alegre de Minas','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3142908','Monte Azul','MG','Norte de Minas'),
	('3143005','Monte Belo','MG','Sul/Sudoeste de Minas'),
	('3143104','Monte Carmelo','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3143153','Monte Formoso','MG','Jequitinhonha'),
	('3143203','Monte Santo de Minas','MG','Sul/Sudoeste de Minas'),
	('3143302','Montes Claros','MG','Norte de Minas'),
	('3143401','Monte Sião','MG','Sul/Sudoeste de Minas'),
	('3143450','Montezuma','MG','Norte de Minas'),
	('3143500','Morada Nova de Minas','MG','Central Mineira'),
	('3143609','Morro da Garça','MG','Central Mineira'),
	('3143708','Morro do Pilar','MG','Metropolitana de Belo Horizonte'),
	('3143807','Munhoz','MG','Sul/Sudoeste de Minas'),
	('3143906','Muriaé','MG','Zona da Mata'),
	('3144003','Mutum','MG','Vale do Rio Doce'),
	('3144102','Muzambinho','MG','Sul/Sudoeste de Minas'),
	('3144201','Nacip Raydan','MG','Vale do Rio Doce'),
	('3144300','Nanuque','MG','Vale do Mucuri'),
	('3144359','Naque','MG','Vale do Rio Doce'),
	('3144375','Natalândia','MG','Noroeste de Minas'),
	('3144409','Natércia','MG','Sul/Sudoeste de Minas'),
	('3144508','Nazareno','MG','Campo das Vertentes'),
	('3144607','Nepomuceno','MG','Campo das Vertentes'),
	('3144656','Ninheira','MG','Norte de Minas'),
	('3144672','Nova Belém','MG','Vale do Rio Doce'),
	('3144706','Nova Era','MG','Metropolitana de Belo Horizonte'),
	('3144805','Nova Lima','MG','Metropolitana de Belo Horizonte'),
	('3144904','Nova Módica','MG','Vale do Rio Doce'),
	('3145000','Nova Ponte','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3145059','Nova Porteirinha','MG','Norte de Minas'),
	('3145109','Nova Resende','MG','Sul/Sudoeste de Minas'),
	('3145208','Nova Serrana','MG','Oeste de Minas'),
	('3145307','Novo Cruzeiro','MG','Jequitinhonha'),
	('3145356','Novo Oriente de Minas','MG','Vale do Mucuri'),
	('3145372','Novorizonte','MG','Norte de Minas'),
	('3145406','Olaria','MG','Zona da Mata'),
	('3145455','Olhos-d\'Água','MG','Norte de Minas'),
	('3145505','Olímpio Noronha','MG','Sul/Sudoeste de Minas'),
	('3145604','Oliveira','MG','Oeste de Minas'),
	('3145703','Oliveira Fortes','MG','Zona da Mata'),
	('3145802','Onça de Pitangui','MG','Metropolitana de Belo Horizonte'),
	('3145851','Oratórios','MG','Zona da Mata'),
	('3145877','Orizânia','MG','Zona da Mata'),
	('3145901','Ouro Branco','MG','Metropolitana de Belo Horizonte'),
	('3146008','Ouro Fino','MG','Sul/Sudoeste de Minas'),
	('3146107','Ouro Preto','MG','Metropolitana de Belo Horizonte'),
	('3146206','Ouro Verde de Minas','MG','Vale do Mucuri'),
	('3146255','Padre Carvalho','MG','Norte de Minas'),
	('3146305','Padre Paraíso','MG','Jequitinhonha'),
	('3146404','Paineiras','MG','Central Mineira'),
	('3146503','Pains','MG','Oeste de Minas'),
	('3146552','Pai Pedro','MG','Norte de Minas'),
	('3146602','Paiva','MG','Zona da Mata'),
	('3146701','Palma','MG','Zona da Mata'),
	('3146750','Palmópolis','MG','Jequitinhonha'),
	('3146909','Papagaios','MG','Metropolitana de Belo Horizonte'),
	('3147006','Paracatu','MG','Noroeste de Minas'),
	('3147105','Pará de Minas','MG','Metropolitana de Belo Horizonte'),
	('3147204','Paraguaçu','MG','Sul/Sudoeste de Minas'),
	('3147303','Paraisópolis','MG','Sul/Sudoeste de Minas'),
	('3147402','Paraopeba','MG','Metropolitana de Belo Horizonte'),
	('3147501','Passabém','MG','Metropolitana de Belo Horizonte'),
	('3147600','Passa Quatro','MG','Sul/Sudoeste de Minas'),
	('3147709','Passa Tempo','MG','Oeste de Minas'),
	('3147808','Passa Vinte','MG','Sul/Sudoeste de Minas'),
	('3147907','Passos','MG','Sul/Sudoeste de Minas'),
	('3147956','Patis','MG','Norte de Minas'),
	('3148004','Patos de Minas','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3148103','Patrocínio','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3148202','Patrocínio do Muriaé','MG','Zona da Mata'),
	('3148301','Paula Cândido','MG','Zona da Mata'),
	('3148400','Paulistas','MG','Vale do Rio Doce'),
	('3148509','Pavão','MG','Vale do Mucuri'),
	('3148608','Peçanha','MG','Vale do Rio Doce'),
	('3148707','Pedra Azul','MG','Jequitinhonha'),
	('3148756','Pedra Bonita','MG','Zona da Mata'),
	('3148806','Pedra do Anta','MG','Zona da Mata'),
	('3148905','Pedra do Indaiá','MG','Oeste de Minas'),
	('3149002','Pedra Dourada','MG','Zona da Mata'),
	('3149101','Pedralva','MG','Sul/Sudoeste de Minas'),
	('3149150','Pedras de Maria da Cruz','MG','Norte de Minas'),
	('3149200','Pedrinópolis','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3149309','Pedro Leopoldo','MG','Metropolitana de Belo Horizonte'),
	('3149408','Pedro Teixeira','MG','Zona da Mata'),
	('3149507','Pequeri','MG','Zona da Mata'),
	('3149606','Pequi','MG','Metropolitana de Belo Horizonte'),
	('3149705','Perdigão','MG','Oeste de Minas'),
	('3149804','Perdizes','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3149903','Perdões','MG','Oeste de Minas'),
	('3149952','Periquito','MG','Vale do Rio Doce'),
	('3150000','Pescador','MG','Vale do Rio Doce'),
	('3150109','Piau','MG','Zona da Mata'),
	('3150158','Piedade de Caratinga','MG','Vale do Rio Doce'),
	('3150208','Piedade de Ponte Nova','MG','Zona da Mata'),
	('3150307','Piedade do Rio Grande','MG','Campo das Vertentes'),
	('3150406','Piedade dos Gerais','MG','Metropolitana de Belo Horizonte'),
	('3150505','Pimenta','MG','Oeste de Minas'),
	('3150539','Pingo d\'Água','MG','Vale do Rio Doce'),
	('3150570','Pintópolis','MG','Norte de Minas'),
	('3150604','Piracema','MG','Oeste de Minas'),
	('3150703','Pirajuba','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3150802','Piranga','MG','Zona da Mata'),
	('3150901','Piranguçu','MG','Sul/Sudoeste de Minas'),
	('3151008','Piranguinho','MG','Sul/Sudoeste de Minas'),
	('3151107','Pirapetinga','MG','Zona da Mata'),
	('3151206','Pirapora','MG','Norte de Minas'),
	('3151305','Piraúba','MG','Zona da Mata'),
	('3151404','Pitangui','MG','Metropolitana de Belo Horizonte'),
	('3151503','Piumhi','MG','Oeste de Minas'),
	('3151602','Planura','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3151701','Poço Fundo','MG','Sul/Sudoeste de Minas'),
	('3151800','Poços de Caldas','MG','Sul/Sudoeste de Minas'),
	('3151909','Pocrane','MG','Vale do Rio Doce'),
	('3152006','Pompéu','MG','Central Mineira'),
	('3152105','Ponte Nova','MG','Zona da Mata'),
	('3152131','Ponto Chique','MG','Norte de Minas'),
	('3152170','Ponto dos Volantes','MG','Jequitinhonha'),
	('3152204','Porteirinha','MG','Norte de Minas'),
	('3152303','Porto Firme','MG','Zona da Mata'),
	('3152402','Poté','MG','Vale do Mucuri'),
	('3152501','Pouso Alegre','MG','Sul/Sudoeste de Minas'),
	('3152600','Pouso Alto','MG','Sul/Sudoeste de Minas'),
	('3152709','Prados','MG','Campo das Vertentes'),
	('3152808','Prata','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3152907','Pratápolis','MG','Sul/Sudoeste de Minas'),
	('3153004','Pratinha','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3153103','Presidente Bernardes','MG','Zona da Mata'),
	('3153202','Presidente Juscelino','MG','Central Mineira'),
	('3153301','Presidente Kubitschek','MG','Jequitinhonha'),
	('3153400','Presidente Olegário','MG','Noroeste de Minas'),
	('3153509','Alto Jequitibá','MG','Zona da Mata'),
	('3153608','Prudente de Morais','MG','Metropolitana de Belo Horizonte'),
	('3153707','Quartel Geral','MG','Central Mineira'),
	('3153806','Queluzito','MG','Metropolitana de Belo Horizonte'),
	('3153905','Raposos','MG','Metropolitana de Belo Horizonte'),
	('3154002','Raul Soares','MG','Zona da Mata'),
	('3154101','Recreio','MG','Zona da Mata'),
	('3154150','Reduto','MG','Zona da Mata'),
	('3154200','Resende Costa','MG','Campo das Vertentes'),
	('3154309','Resplendor','MG','Vale do Rio Doce'),
	('3154408','Ressaquinha','MG','Campo das Vertentes'),
	('3154457','Riachinho','MG','Norte de Minas'),
	('3154507','Riacho dos Machados','MG','Norte de Minas'),
	('3154606','Ribeirão das Neves','MG','Metropolitana de Belo Horizonte'),
	('3154705','Ribeirão Vermelho','MG','Campo das Vertentes'),
	('3154804','Rio Acima','MG','Metropolitana de Belo Horizonte'),
	('3154903','Rio Casca','MG','Zona da Mata'),
	('3155009','Rio Doce','MG','Zona da Mata'),
	('3155108','Rio do Prado','MG','Jequitinhonha'),
	('3155207','Rio Espera','MG','Zona da Mata'),
	('3155306','Rio Manso','MG','Metropolitana de Belo Horizonte'),
	('3155405','Rio Novo','MG','Zona da Mata'),
	('3155504','Rio Paranaíba','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3155603','Rio Pardo de Minas','MG','Norte de Minas'),
	('3155702','Rio Piracicaba','MG','Metropolitana de Belo Horizonte'),
	('3155801','Rio Pomba','MG','Zona da Mata'),
	('3155900','Rio Preto','MG','Zona da Mata'),
	('3156007','Rio Vermelho','MG','Metropolitana de Belo Horizonte'),
	('3156106','Ritápolis','MG','Campo das Vertentes'),
	('3156205','Rochedo de Minas','MG','Zona da Mata'),
	('3156304','Rodeiro','MG','Zona da Mata'),
	('3156403','Romaria','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3156452','Rosário da Limeira','MG','Zona da Mata'),
	('3156502','Rubelita','MG','Norte de Minas'),
	('3156601','Rubim','MG','Jequitinhonha'),
	('3156700','Sabará','MG','Metropolitana de Belo Horizonte'),
	('3156809','Sabinópolis','MG','Vale do Rio Doce'),
	('3156908','Sacramento','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3157005','Salinas','MG','Norte de Minas'),
	('3157104','Salto da Divisa','MG','Jequitinhonha'),
	('3157203','Santa Bárbara','MG','Metropolitana de Belo Horizonte'),
	('3157252','Santa Bárbara do Leste','MG','Vale do Rio Doce'),
	('3157278','Santa Bárbara do Monte Verde','MG','Zona da Mata'),
	('3157302','Santa Bárbara do Tugúrio','MG','Campo das Vertentes'),
	('3157336','Santa Cruz de Minas','MG','Campo das Vertentes'),
	('3157377','Santa Cruz de Salinas','MG','Norte de Minas'),
	('3157401','Santa Cruz do Escalvado','MG','Zona da Mata'),
	('3157500','Santa Efigênia de Minas','MG','Vale do Rio Doce'),
	('3157609','Santa Fé de Minas','MG','Norte de Minas'),
	('3157658','Santa Helena de Minas','MG','Vale do Mucuri'),
	('3157708','Santa Juliana','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3157807','Santa Luzia','MG','Metropolitana de Belo Horizonte'),
	('3157906','Santa Margarida','MG','Zona da Mata'),
	('3158003','Santa Maria de Itabira','MG','Metropolitana de Belo Horizonte'),
	('3158102','Santa Maria do Salto','MG','Jequitinhonha'),
	('3158201','Santa Maria do Suaçuí','MG','Vale do Rio Doce'),
	('3158300','Santana da Vargem','MG','Sul/Sudoeste de Minas'),
	('3158409','Santana de Cataguases','MG','Zona da Mata'),
	('3158508','Santana de Pirapama','MG','Metropolitana de Belo Horizonte'),
	('3158607','Santana do Deserto','MG','Zona da Mata'),
	('3158706','Santana do Garambéu','MG','Campo das Vertentes'),
	('3158805','Santana do Jacaré','MG','Oeste de Minas'),
	('3158904','Santana do Manhuaçu','MG','Zona da Mata'),
	('3158953','Santana do Paraíso','MG','Vale do Rio Doce'),
	('3159001','Santana do Riacho','MG','Metropolitana de Belo Horizonte'),
	('3159100','Santana dos Montes','MG','Metropolitana de Belo Horizonte'),
	('3159209','Santa Rita de Caldas','MG','Sul/Sudoeste de Minas'),
	('3159308','Santa Rita de Jacutinga','MG','Zona da Mata'),
	('3159357','Santa Rita de Minas','MG','Vale do Rio Doce'),
	('3159407','Santa Rita de Ibitipoca','MG','Zona da Mata'),
	('3159506','Santa Rita do Itueto','MG','Vale do Rio Doce'),
	('3159605','Santa Rita do Sapucaí','MG','Sul/Sudoeste de Minas'),
	('3159704','Santa Rosa da Serra','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3159803','Santa Vitória','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3159902','Santo Antônio do Amparo','MG','Oeste de Minas'),
	('3160009','Santo Antônio do Aventureiro','MG','Zona da Mata'),
	('3160108','Santo Antônio do Grama','MG','Zona da Mata'),
	('3160207','Santo Antônio do Itambé','MG','Metropolitana de Belo Horizonte'),
	('3160306','Santo Antônio do Jacinto','MG','Jequitinhonha'),
	('3160405','Santo Antônio do Monte','MG','Oeste de Minas'),
	('3160454','Santo Antônio do Retiro','MG','Norte de Minas'),
	('3160504','Santo Antônio do Rio Abaixo','MG','Metropolitana de Belo Horizonte'),
	('3160603','Santo Hipólito','MG','Central Mineira'),
	('3160702','Santos Dumont','MG','Zona da Mata'),
	('3160801','São Bento Abade','MG','Sul/Sudoeste de Minas'),
	('3160900','São Brás do Suaçuí','MG','Metropolitana de Belo Horizonte'),
	('3160959','São Domingos das Dores','MG','Vale do Rio Doce'),
	('3161007','São Domingos do Prata','MG','Metropolitana de Belo Horizonte'),
	('3161056','São Félix de Minas','MG','Vale do Rio Doce'),
	('3161106','São Francisco','MG','Norte de Minas'),
	('3161205','São Francisco de Paula','MG','Oeste de Minas'),
	('3161304','São Francisco de Sales','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3161403','São Francisco do Glória','MG','Zona da Mata'),
	('3161502','São Geraldo','MG','Zona da Mata'),
	('3161601','São Geraldo da Piedade','MG','Vale do Rio Doce'),
	('3161650','São Geraldo do Baixio','MG','Vale do Rio Doce'),
	('3161700','São Gonçalo do Abaeté','MG','Noroeste de Minas'),
	('3161809','São Gonçalo do Pará','MG','Oeste de Minas'),
	('3161908','São Gonçalo do Rio Abaixo','MG','Metropolitana de Belo Horizonte'),
	('3162005','São Gonçalo do Sapucaí','MG','Sul/Sudoeste de Minas'),
	('3162104','São Gotardo','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3162203','São João Batista do Glória','MG','Sul/Sudoeste de Minas'),
	('3162252','São João da Lagoa','MG','Norte de Minas'),
	('3162302','São João da Mata','MG','Sul/Sudoeste de Minas'),
	('3162401','São João da Ponte','MG','Norte de Minas'),
	('3162450','São João das Missões','MG','Norte de Minas'),
	('3162500','São João del Rei','MG','Campo das Vertentes'),
	('3162559','São João do Manhuaçu','MG','Zona da Mata'),
	('3162575','São João do Manteninha','MG','Vale do Rio Doce'),
	('3162609','São João do Oriente','MG','Vale do Rio Doce'),
	('3162658','São João do Pacuí','MG','Norte de Minas'),
	('3162708','São João do Paraíso','MG','Norte de Minas'),
	('3162807','São João Evangelista','MG','Vale do Rio Doce'),
	('3162906','São João Nepomuceno','MG','Zona da Mata'),
	('3162922','São Joaquim de Bicas','MG','Metropolitana de Belo Horizonte'),
	('3162948','São José da Barra','MG','Sul/Sudoeste de Minas'),
	('3162955','São José da Lapa','MG','Metropolitana de Belo Horizonte'),
	('3163003','São José da Safira','MG','Vale do Rio Doce'),
	('3163102','São José da Varginha','MG','Metropolitana de Belo Horizonte'),
	('3163201','São José do Alegre','MG','Sul/Sudoeste de Minas'),
	('3163300','São José do Divino','MG','Vale do Rio Doce'),
	('3163409','São José do Goiabal','MG','Metropolitana de Belo Horizonte'),
	('3163508','São José do Jacuri','MG','Vale do Rio Doce'),
	('3163607','São José do Mantimento','MG','Zona da Mata'),
	('3163706','São Lourenço','MG','Sul/Sudoeste de Minas'),
	('3163805','São Miguel do Anta','MG','Zona da Mata'),
	('3163904','São Pedro da União','MG','Sul/Sudoeste de Minas'),
	('3164001','São Pedro dos Ferros','MG','Zona da Mata'),
	('3164100','São Pedro do Suaçuí','MG','Vale do Rio Doce'),
	('3164209','São Romão','MG','Norte de Minas'),
	('3164308','São Roque de Minas','MG','Oeste de Minas'),
	('3164407','São Sebastião da Bela Vista','MG','Sul/Sudoeste de Minas'),
	('3164431','São Sebastião da Vargem Alegre','MG','Zona da Mata'),
	('3164472','São Sebastião do Anta','MG','Vale do Rio Doce'),
	('3164506','São Sebastião do Maranhão','MG','Vale do Rio Doce'),
	('3164605','São Sebastião do Oeste','MG','Oeste de Minas'),
	('3164704','São Sebastião do Paraíso','MG','Sul/Sudoeste de Minas'),
	('3164803','São Sebastião do Rio Preto','MG','Metropolitana de Belo Horizonte'),
	('3164902','São Sebastião do Rio Verde','MG','Sul/Sudoeste de Minas'),
	('3165008','São Tiago','MG','Campo das Vertentes'),
	('3165107','São Tomás de Aquino','MG','Sul/Sudoeste de Minas'),
	('3165206','São Thomé das Letras','MG','Sul/Sudoeste de Minas'),
	('3165305','São Vicente de Minas','MG','Sul/Sudoeste de Minas'),
	('3165404','Sapucaí-Mirim','MG','Sul/Sudoeste de Minas'),
	('3165503','Sardoá','MG','Vale do Rio Doce'),
	('3165537','Sarzedo','MG','Metropolitana de Belo Horizonte'),
	('3165552','Setubinha','MG','Vale do Mucuri'),
	('3165560','Sem-Peixe','MG','Zona da Mata'),
	('3165578','Senador Amaral','MG','Sul/Sudoeste de Minas'),
	('3165602','Senador Cortes','MG','Zona da Mata'),
	('3165701','Senador Firmino','MG','Zona da Mata'),
	('3165800','Senador José Bento','MG','Sul/Sudoeste de Minas'),
	('3165909','Senador Modestino Gonçalves','MG','Jequitinhonha'),
	('3166006','Senhora de Oliveira','MG','Zona da Mata'),
	('3166105','Senhora do Porto','MG','Vale do Rio Doce'),
	('3166204','Senhora dos Remédios','MG','Campo das Vertentes'),
	('3166303','Sericita','MG','Zona da Mata'),
	('3166402','Seritinga','MG','Sul/Sudoeste de Minas'),
	('3166501','Serra Azul de Minas','MG','Metropolitana de Belo Horizonte'),
	('3166600','Serra da Saudade','MG','Central Mineira'),
	('3166709','Serra dos Aimorés','MG','Vale do Mucuri'),
	('3166808','Serra do Salitre','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3166907','Serrania','MG','Sul/Sudoeste de Minas'),
	('3166956','Serranópolis de Minas','MG','Norte de Minas'),
	('3167004','Serranos','MG','Sul/Sudoeste de Minas'),
	('3167103','Serro','MG','Metropolitana de Belo Horizonte'),
	('3167202','Sete Lagoas','MG','Metropolitana de Belo Horizonte'),
	('3167301','Silveirânia','MG','Zona da Mata'),
	('3167400','Silvianópolis','MG','Sul/Sudoeste de Minas'),
	('3167509','Simão Pereira','MG','Zona da Mata'),
	('3167608','Simonésia','MG','Zona da Mata'),
	('3167707','Sobrália','MG','Vale do Rio Doce'),
	('3167806','Soledade de Minas','MG','Sul/Sudoeste de Minas'),
	('3167905','Tabuleiro','MG','Zona da Mata'),
	('3168002','Taiobeiras','MG','Norte de Minas'),
	('3168051','Taparuba','MG','Vale do Rio Doce'),
	('3168101','Tapira','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3168200','Tapiraí','MG','Oeste de Minas'),
	('3168309','Taquaraçu de Minas','MG','Metropolitana de Belo Horizonte'),
	('3168408','Tarumirim','MG','Vale do Rio Doce'),
	('3168507','Teixeiras','MG','Zona da Mata'),
	('3168606','Teófilo Otoni','MG','Vale do Mucuri'),
	('3168705','Timóteo','MG','Vale do Rio Doce'),
	('3168804','Tiradentes','MG','Campo das Vertentes'),
	('3168903','Tiros','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3169000','Tocantins','MG','Zona da Mata'),
	('3169059','Tocos do Moji','MG','Sul/Sudoeste de Minas'),
	('3169109','Toledo','MG','Sul/Sudoeste de Minas'),
	('3169208','Tombos','MG','Zona da Mata'),
	('3169307','Três Corações','MG','Sul/Sudoeste de Minas'),
	('3169356','Três Marias','MG','Central Mineira'),
	('3169406','Três Pontas','MG','Sul/Sudoeste de Minas'),
	('3169505','Tumiritinga','MG','Vale do Rio Doce'),
	('3169604','Tupaciguara','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3169703','Turmalina','MG','Jequitinhonha'),
	('3169802','Turvolândia','MG','Sul/Sudoeste de Minas'),
	('3169901','Ubá','MG','Zona da Mata'),
	('3170008','Ubaí','MG','Norte de Minas'),
	('3170057','Ubaporanga','MG','Vale do Rio Doce'),
	('3170107','Uberaba','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3170206','Uberlândia','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3170305','Umburatiba','MG','Vale do Mucuri'),
	('3170404','Unaí','MG','Noroeste de Minas'),
	('3170438','União de Minas','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3170479','Uruana de Minas','MG','Noroeste de Minas'),
	('3170503','Urucânia','MG','Zona da Mata'),
	('3170529','Urucuia','MG','Norte de Minas'),
	('3170578','Vargem Alegre','MG','Vale do Rio Doce'),
	('3170602','Vargem Bonita','MG','Oeste de Minas'),
	('3170651','Vargem Grande do Rio Pardo','MG','Norte de Minas'),
	('3170701','Varginha','MG','Sul/Sudoeste de Minas'),
	('3170750','Varjão de Minas','MG','Noroeste de Minas'),
	('3170800','Várzea da Palma','MG','Norte de Minas'),
	('3170909','Varzelândia','MG','Norte de Minas'),
	('3171006','Vazante','MG','Noroeste de Minas'),
	('3171030','Verdelândia','MG','Norte de Minas'),
	('3171071','Veredinha','MG','Jequitinhonha'),
	('3171105','Veríssimo','MG','Triângulo Mineiro/Alto Paranaíba'),
	('3171154','Vermelho Novo','MG','Zona da Mata'),
	('3171204','Vespasiano','MG','Metropolitana de Belo Horizonte'),
	('3171303','Viçosa','MG','Zona da Mata'),
	('3171402','Vieiras','MG','Zona da Mata'),
	('3171501','Mathias Lobato','MG','Vale do Rio Doce'),
	('3171600','Virgem da Lapa','MG','Jequitinhonha'),
	('3171709','Virgínia','MG','Sul/Sudoeste de Minas'),
	('3171808','Virginópolis','MG','Vale do Rio Doce'),
	('3171907','Virgolândia','MG','Vale do Rio Doce'),
	('3172004','Visconde do Rio Branco','MG','Zona da Mata'),
	('3172103','Volta Grande','MG','Zona da Mata'),
	('3172202','Wenceslau Braz','MG','Sul/Sudoeste de Minas'),
	('3200102','Afonso Cláudio','ES','Central Espírito-santense'),
	('3200136','Águia Branca','ES','Noroeste Espírito-santense'),
	('3200169','Água Doce do Norte','ES','Noroeste Espírito-santense'),
	('3200201','Alegre','ES','Sul Espírito-santense'),
	('3200300','Alfredo Chaves','ES','Central Espírito-santense'),
	('3200359','Alto Rio Novo','ES','Noroeste Espírito-santense'),
	('3200409','Anchieta','ES','Central Espírito-santense'),
	('3200508','Apiacá','ES','Sul Espírito-santense'),
	('3200607','Aracruz','ES','Litoral Norte Espírito-santense'),
	('3200706','Atílio Vivacqua','ES','Sul Espírito-santense'),
	('3200805','Baixo Guandu','ES','Noroeste Espírito-santense'),
	('3200904','Barra de São Francisco','ES','Noroeste Espírito-santense'),
	('3201001','Boa Esperança','ES','Noroeste Espírito-santense'),
	('3201100','Bom Jesus do Norte','ES','Sul Espírito-santense'),
	('3201159','Brejetuba','ES','Central Espírito-santense'),
	('3201209','Cachoeiro de Itapemirim','ES','Sul Espírito-santense'),
	('3201308','Cariacica','ES','Central Espírito-santense'),
	('3201407','Castelo','ES','Sul Espírito-santense'),
	('3201506','Colatina','ES','Noroeste Espírito-santense'),
	('3201605','Conceição da Barra','ES','Litoral Norte Espírito-santense'),
	('3201704','Conceição do Castelo','ES','Central Espírito-santense'),
	('3201803','Divino de São Lourenço','ES','Sul Espírito-santense'),
	('3201902','Domingos Martins','ES','Central Espírito-santense'),
	('3202009','Dores do Rio Preto','ES','Sul Espírito-santense'),
	('3202108','Ecoporanga','ES','Noroeste Espírito-santense'),
	('3202207','Fundão','ES','Litoral Norte Espírito-santense'),
	('3202256','Governador Lindenberg','ES','Noroeste Espírito-santense'),
	('3202306','Guaçuí','ES','Sul Espírito-santense'),
	('3202405','Guarapari','ES','Central Espírito-santense'),
	('3202454','Ibatiba','ES','Sul Espírito-santense'),
	('3202504','Ibiraçu','ES','Litoral Norte Espírito-santense'),
	('3202553','Ibitirama','ES','Sul Espírito-santense'),
	('3202603','Iconha','ES','Central Espírito-santense'),
	('3202652','Irupi','ES','Sul Espírito-santense'),
	('3202702','Itaguaçu','ES','Central Espírito-santense'),
	('3202801','Itapemirim','ES','Sul Espírito-santense'),
	('3202900','Itarana','ES','Central Espírito-santense'),
	('3203007','Iúna','ES','Sul Espírito-santense'),
	('3203056','Jaguaré','ES','Litoral Norte Espírito-santense'),
	('3203106','Jerônimo Monteiro','ES','Sul Espírito-santense'),
	('3203130','João Neiva','ES','Litoral Norte Espírito-santense'),
	('3203163','Laranja da Terra','ES','Central Espírito-santense'),
	('3203205','Linhares','ES','Litoral Norte Espírito-santense'),
	('3203304','Mantenópolis','ES','Noroeste Espírito-santense'),
	('3203320','Marataízes','ES','Sul Espírito-santense'),
	('3203346','Marechal Floriano','ES','Central Espírito-santense'),
	('3203353','Marilândia','ES','Noroeste Espírito-santense'),
	('3203403','Mimoso do Sul','ES','Sul Espírito-santense'),
	('3203502','Montanha','ES','Litoral Norte Espírito-santense'),
	('3203601','Mucurici','ES','Litoral Norte Espírito-santense'),
	('3203700','Muniz Freire','ES','Sul Espírito-santense'),
	('3203809','Muqui','ES','Sul Espírito-santense'),
	('3203908','Nova Venécia','ES','Noroeste Espírito-santense'),
	('3204005','Pancas','ES','Noroeste Espírito-santense'),
	('3204054','Pedro Canário','ES','Litoral Norte Espírito-santense'),
	('3204104','Pinheiros','ES','Litoral Norte Espírito-santense'),
	('3204203','Piúma','ES','Central Espírito-santense'),
	('3204252','Ponto Belo','ES','Litoral Norte Espírito-santense'),
	('3204302','Presidente Kennedy','ES','Sul Espírito-santense'),
	('3204351','Rio Bananal','ES','Litoral Norte Espírito-santense'),
	('3204401','Rio Novo do Sul','ES','Central Espírito-santense'),
	('3204500','Santa Leopoldina','ES','Central Espírito-santense'),
	('3204559','Santa Maria de Jetibá','ES','Central Espírito-santense'),
	('3204609','Santa Teresa','ES','Central Espírito-santense'),
	('3204658','São Domingos do Norte','ES','Noroeste Espírito-santense'),
	('3204708','São Gabriel da Palha','ES','Noroeste Espírito-santense'),
	('3204807','São José do Calçado','ES','Sul Espírito-santense'),
	('3204906','São Mateus','ES','Litoral Norte Espírito-santense'),
	('3204955','São Roque do Canaã','ES','Central Espírito-santense'),
	('3205002','Serra','ES','Central Espírito-santense'),
	('3205010','Sooretama','ES','Litoral Norte Espírito-santense'),
	('3205036','Vargem Alta','ES','Sul Espírito-santense'),
	('3205069','Venda Nova do Imigrante','ES','Central Espírito-santense'),
	('3205101','Viana','ES','Central Espírito-santense'),
	('3205150','Vila Pavão','ES','Noroeste Espírito-santense'),
	('3205176','Vila Valério','ES','Noroeste Espírito-santense'),
	('3205200','Vila Velha','ES','Central Espírito-santense'),
	('3205309','Vitória','ES','Central Espírito-santense'),
	('3300100','Angra dos Reis','RJ','Sul Fluminense'),
	('3300159','Aperibé','RJ','Noroeste Fluminense'),
	('3300209','Araruama','RJ','Baixadas'),
	('3300225','Areal','RJ','Centro Fluminense'),
	('3300233','Armação dos Búzios','RJ','Baixadas'),
	('3300258','Arraial do Cabo','RJ','Baixadas'),
	('3300308','Barra do Piraí','RJ','Sul Fluminense'),
	('3300407','Barra Mansa','RJ','Sul Fluminense'),
	('3300456','Belford Roxo','RJ','Metropolitana do Rio de Janeiro'),
	('3300506','Bom Jardim','RJ','Centro Fluminense'),
	('3300605','Bom Jesus do Itabapoana','RJ','Noroeste Fluminense'),
	('3300704','Cabo Frio','RJ','Baixadas'),
	('3300803','Cachoeiras de Macacu','RJ','Metropolitana do Rio de Janeiro'),
	('3300902','Cambuci','RJ','Noroeste Fluminense'),
	('3300936','Carapebus','RJ','Norte Fluminense'),
	('3300951','Comendador Levy Gasparian','RJ','Centro Fluminense'),
	('3301009','Campos dos Goytacazes','RJ','Norte Fluminense'),
	('3301108','Cantagalo','RJ','Centro Fluminense'),
	('3301157','Cardoso Moreira','RJ','Norte Fluminense'),
	('3301207','Carmo','RJ','Centro Fluminense'),
	('3301306','Casimiro de Abreu','RJ','Baixadas'),
	('3301405','Conceição de Macabu','RJ','Norte Fluminense'),
	('3301504','Cordeiro','RJ','Centro Fluminense'),
	('3301603','Duas Barras','RJ','Centro Fluminense'),
	('3301702','Duque de Caxias','RJ','Metropolitana do Rio de Janeiro'),
	('3301801','Engenheiro Paulo de Frontin','RJ','Metropolitana do Rio de Janeiro'),
	('3301850','Guapimirim','RJ','Metropolitana do Rio de Janeiro'),
	('3301876','Iguaba Grande','RJ','Baixadas'),
	('3301900','Itaboraí','RJ','Metropolitana do Rio de Janeiro'),
	('3302007','Itaguaí','RJ','Metropolitana do Rio de Janeiro'),
	('3302056','Italva','RJ','Noroeste Fluminense'),
	('3302106','Itaocara','RJ','Noroeste Fluminense'),
	('3302205','Itaperuna','RJ','Noroeste Fluminense'),
	('3302254','Itatiaia','RJ','Sul Fluminense'),
	('3302270','Japeri','RJ','Metropolitana do Rio de Janeiro'),
	('3302304','Laje do Muriaé','RJ','Noroeste Fluminense'),
	('3302403','Macaé','RJ','Norte Fluminense'),
	('3302452','Macuco','RJ','Centro Fluminense'),
	('3302502','Magé','RJ','Metropolitana do Rio de Janeiro'),
	('3302601','Mangaratiba','RJ','Metropolitana do Rio de Janeiro'),
	('3302700','Maricá','RJ','Metropolitana do Rio de Janeiro'),
	('3302809','Mendes','RJ','Metropolitana do Rio de Janeiro'),
	('3302858','Mesquita','RJ','Metropolitana do Rio de Janeiro'),
	('3302908','Miguel Pereira','RJ','Metropolitana do Rio de Janeiro'),
	('3303005','Miracema','RJ','Noroeste Fluminense'),
	('3303104','Natividade','RJ','Noroeste Fluminense'),
	('3303203','Nilópolis','RJ','Metropolitana do Rio de Janeiro'),
	('3303302','Niterói','RJ','Metropolitana do Rio de Janeiro'),
	('3303401','Nova Friburgo','RJ','Centro Fluminense'),
	('3303500','Nova Iguaçu','RJ','Metropolitana do Rio de Janeiro'),
	('3303609','Paracambi','RJ','Metropolitana do Rio de Janeiro'),
	('3303708','Paraíba do Sul','RJ','Centro Fluminense'),
	('3303807','Paraty','RJ','Sul Fluminense'),
	('3303856','Paty do Alferes','RJ','Metropolitana do Rio de Janeiro'),
	('3303906','Petrópolis','RJ','Metropolitana do Rio de Janeiro'),
	('3303955','Pinheiral','RJ','Sul Fluminense'),
	('3304003','Piraí','RJ','Sul Fluminense'),
	('3304102','Porciúncula','RJ','Noroeste Fluminense'),
	('3304110','Porto Real','RJ','Sul Fluminense'),
	('3304128','Quatis','RJ','Sul Fluminense'),
	('3304144','Queimados','RJ','Metropolitana do Rio de Janeiro'),
	('3304151','Quissamã','RJ','Norte Fluminense'),
	('3304201','Resende','RJ','Sul Fluminense'),
	('3304300','Rio Bonito','RJ','Metropolitana do Rio de Janeiro'),
	('3304409','Rio Claro','RJ','Sul Fluminense'),
	('3304508','Rio das Flores','RJ','Sul Fluminense'),
	('3304524','Rio das Ostras','RJ','Baixadas'),
	('3304557','Rio de Janeiro','RJ','Metropolitana do Rio de Janeiro'),
	('3304607','Santa Maria Madalena','RJ','Centro Fluminense'),
	('3304706','Santo Antônio de Pádua','RJ','Noroeste Fluminense'),
	('3304755','São Francisco de Itabapoana','RJ','Norte Fluminense'),
	('3304805','São Fidélis','RJ','Norte Fluminense'),
	('3304904','São Gonçalo','RJ','Metropolitana do Rio de Janeiro'),
	('3305000','São João da Barra','RJ','Norte Fluminense'),
	('3305109','São João de Meriti','RJ','Metropolitana do Rio de Janeiro'),
	('3305133','São José de Ubá','RJ','Noroeste Fluminense'),
	('3305158','São José do Vale do Rio Preto','RJ','Metropolitana do Rio de Janeiro'),
	('3305208','São Pedro da Aldeia','RJ','Baixadas'),
	('3305307','São Sebastião do Alto','RJ','Centro Fluminense'),
	('3305406','Sapucaia','RJ','Centro Fluminense'),
	('3305505','Saquarema','RJ','Baixadas'),
	('3305554','Seropédica','RJ','Metropolitana do Rio de Janeiro'),
	('3305604','Silva Jardim','RJ','Baixadas'),
	('3305703','Sumidouro','RJ','Centro Fluminense'),
	('3305752','Tanguá','RJ','Metropolitana do Rio de Janeiro'),
	('3305802','Teresópolis','RJ','Metropolitana do Rio de Janeiro'),
	('3305901','Trajano de Moraes','RJ','Centro Fluminense'),
	('3306008','Três Rios','RJ','Centro Fluminense'),
	('3306107','Valença','RJ','Sul Fluminense'),
	('3306156','Varre-Sai','RJ','Noroeste Fluminense'),
	('3306206','Vassouras','RJ','Metropolitana do Rio de Janeiro'),
	('3306305','Volta Redonda','RJ','Sul Fluminense'),
	('3500105','Adamantina','SP','Presidente Prudente'),
	('3500204','Adolfo','SP','São José do Rio Preto'),
	('3500303','Aguaí','SP','Campinas'),
	('3500402','Águas da Prata','SP','Campinas'),
	('3500501','Águas de Lindóia','SP','Campinas'),
	('3500550','Águas de Santa Bárbara','SP','Bauru'),
	('3500600','Águas de São Pedro','SP','Piracicaba'),
	('3500709','Agudos','SP','Bauru'),
	('3500758','Alambari','SP','Itapetininga'),
	('3500808','Alfredo Marcondes','SP','Presidente Prudente'),
	('3500907','Altair','SP','São José do Rio Preto'),
	('3501004','Altinópolis','SP','Ribeirão Preto'),
	('3501103','Alto Alegre','SP','Araçatuba'),
	('3501152','Alumínio','SP','Macro Metropolitana Paulista'),
	('3501202','Álvares Florence','SP','São José do Rio Preto'),
	('3501301','Álvares Machado','SP','Presidente Prudente'),
	('3501400','Álvaro de Carvalho','SP','Marília'),
	('3501509','Alvinlândia','SP','Marília'),
	('3501608','Americana','SP','Campinas'),
	('3501707','Américo Brasiliense','SP','Araraquara'),
	('3501806','Américo de Campos','SP','São José do Rio Preto'),
	('3501905','Amparo','SP','Campinas'),
	('3502002','Analândia','SP','Araraquara'),
	('3502101','Andradina','SP','Araçatuba'),
	('3502200','Angatuba','SP','Itapetininga'),
	('3502309','Anhembi','SP','Bauru'),
	('3502408','Anhumas','SP','Presidente Prudente'),
	('3502507','Aparecida','SP','Vale do Paraíba Paulista'),
	('3502606','Aparecida d\'Oeste','SP','São José do Rio Preto'),
	('3502705','Apiaí','SP','Itapetininga'),
	('3502754','Araçariguama','SP','Macro Metropolitana Paulista'),
	('3502804','Araçatuba','SP','Araçatuba'),
	('3502903','Araçoiaba da Serra','SP','Macro Metropolitana Paulista'),
	('3503000','Aramina','SP','Ribeirão Preto'),
	('3503109','Arandu','SP','Bauru'),
	('3503158','Arapeí','SP','Vale do Paraíba Paulista'),
	('3503208','Araraquara','SP','Araraquara'),
	('3503307','Araras','SP','Piracicaba'),
	('3503356','Arco-Íris','SP','Marília'),
	('3503406','Arealva','SP','Bauru'),
	('3503505','Areias','SP','Vale do Paraíba Paulista'),
	('3503604','Areiópolis','SP','Bauru'),
	('3503703','Ariranha','SP','São José do Rio Preto'),
	('3503802','Artur Nogueira','SP','Campinas'),
	('3503901','Arujá','SP','Metropolitana de São Paulo'),
	('3503950','Aspásia','SP','São José do Rio Preto'),
	('3504008','Assis','SP','Assis'),
	('3504107','Atibaia','SP','Macro Metropolitana Paulista'),
	('3504206','Auriflama','SP','São José do Rio Preto'),
	('3504305','Avaí','SP','Bauru'),
	('3504404','Avanhandava','SP','Araçatuba'),
	('3504503','Avaré','SP','Bauru'),
	('3504602','Bady Bassitt','SP','São José do Rio Preto'),
	('3504701','Balbinos','SP','Bauru'),
	('3504800','Bálsamo','SP','São José do Rio Preto'),
	('3504909','Bananal','SP','Vale do Paraíba Paulista'),
	('3505005','Barão de Antonina','SP','Itapetininga'),
	('3505104','Barbosa','SP','Araçatuba'),
	('3505203','Bariri','SP','Bauru'),
	('3505302','Barra Bonita','SP','Bauru'),
	('3505351','Barra do Chapéu','SP','Itapetininga'),
	('3505401','Barra do Turvo','SP','Litoral Sul Paulista'),
	('3505500','Barretos','SP','Ribeirão Preto'),
	('3505609','Barrinha','SP','Ribeirão Preto'),
	('3505708','Barueri','SP','Metropolitana de São Paulo'),
	('3505807','Bastos','SP','Marília'),
	('3505906','Batatais','SP','Ribeirão Preto'),
	('3506003','Bauru','SP','Bauru'),
	('3506102','Bebedouro','SP','Ribeirão Preto'),
	('3506201','Bento de Abreu','SP','Araçatuba'),
	('3506300','Bernardino de Campos','SP','Assis'),
	('3506359','Bertioga','SP','Metropolitana de São Paulo'),
	('3506409','Bilac','SP','Araçatuba'),
	('3506508','Birigui','SP','Araçatuba'),
	('3506607','Biritiba Mirim','SP','Metropolitana de São Paulo'),
	('3506706','Boa Esperança do Sul','SP','Araraquara'),
	('3506805','Bocaina','SP','Bauru'),
	('3506904','Bofete','SP','Bauru'),
	('3507001','Boituva','SP','Itapetininga'),
	('3507100','Bom Jesus dos Perdões','SP','Macro Metropolitana Paulista'),
	('3507159','Bom Sucesso de Itararé','SP','Itapetininga'),
	('3507209','Borá','SP','Assis'),
	('3507308','Boracéia','SP','Bauru'),
	('3507407','Borborema','SP','Araraquara'),
	('3507456','Borebi','SP','Bauru'),
	('3507506','Botucatu','SP','Bauru'),
	('3507605','Bragança Paulista','SP','Macro Metropolitana Paulista'),
	('3507704','Braúna','SP','Araçatuba'),
	('3507753','Brejo Alegre','SP','Araçatuba'),
	('3507803','Brodowski','SP','Ribeirão Preto'),
	('3507902','Brotas','SP','Piracicaba'),
	('3508009','Buri','SP','Itapetininga'),
	('3508108','Buritama','SP','Araçatuba'),
	('3508207','Buritizal','SP','Ribeirão Preto'),
	('3508306','Cabrália Paulista','SP','Bauru'),
	('3508405','Cabreúva','SP','Macro Metropolitana Paulista'),
	('3508504','Caçapava','SP','Vale do Paraíba Paulista'),
	('3508603','Cachoeira Paulista','SP','Vale do Paraíba Paulista'),
	('3508702','Caconde','SP','Campinas'),
	('3508801','Cafelândia','SP','Bauru'),
	('3508900','Caiabu','SP','Presidente Prudente'),
	('3509007','Caieiras','SP','Metropolitana de São Paulo'),
	('3509106','Caiuá','SP','Presidente Prudente'),
	('3509205','Cajamar','SP','Metropolitana de São Paulo'),
	('3509254','Cajati','SP','Litoral Sul Paulista'),
	('3509304','Cajobi','SP','São José do Rio Preto'),
	('3509403','Cajuru','SP','Ribeirão Preto'),
	('3509452','Campina do Monte Alegre','SP','Itapetininga'),
	('3509502','Campinas','SP','Campinas'),
	('3509601','Campo Limpo Paulista','SP','Macro Metropolitana Paulista'),
	('3509700','Campos do Jordão','SP','Vale do Paraíba Paulista'),
	('3509809','Campos Novos Paulista','SP','Assis'),
	('3509908','Cananéia','SP','Litoral Sul Paulista'),
	('3509957','Canas','SP','Vale do Paraíba Paulista'),
	('3510005','Cândido Mota','SP','Assis'),
	('3510104','Cândido Rodrigues','SP','Ribeirão Preto'),
	('3510153','Canitar','SP','Assis'),
	('3510203','Capão Bonito','SP','Itapetininga'),
	('3510302','Capela do Alto','SP','Macro Metropolitana Paulista'),
	('3510401','Capivari','SP','Piracicaba'),
	('3510500','Caraguatatuba','SP','Vale do Paraíba Paulista'),
	('3510609','Carapicuíba','SP','Metropolitana de São Paulo'),
	('3510708','Cardoso','SP','São José do Rio Preto'),
	('3510807','Casa Branca','SP','Campinas'),
	('3510906','Cássia dos Coqueiros','SP','Ribeirão Preto'),
	('3511003','Castilho','SP','Araçatuba'),
	('3511102','Catanduva','SP','São José do Rio Preto'),
	('3511201','Catiguá','SP','São José do Rio Preto'),
	('3511300','Cedral','SP','São José do Rio Preto'),
	('3511409','Cerqueira César','SP','Bauru'),
	('3511508','Cerquilho','SP','Itapetininga'),
	('3511607','Cesário Lange','SP','Itapetininga'),
	('3511706','Charqueada','SP','Piracicaba'),
	('3511904','Clementina','SP','Araçatuba'),
	('3512001','Colina','SP','Ribeirão Preto'),
	('3512100','Colômbia','SP','Ribeirão Preto'),
	('3512209','Conchal','SP','Piracicaba'),
	('3512308','Conchas','SP','Bauru'),
	('3512407','Cordeirópolis','SP','Piracicaba'),
	('3512506','Coroados','SP','Araçatuba'),
	('3512605','Coronel Macedo','SP','Itapetininga'),
	('3512704','Corumbataí','SP','Piracicaba'),
	('3512803','Cosmópolis','SP','Campinas'),
	('3512902','Cosmorama','SP','São José do Rio Preto'),
	('3513009','Cotia','SP','Metropolitana de São Paulo'),
	('3513108','Cravinhos','SP','Ribeirão Preto'),
	('3513207','Cristais Paulista','SP','Ribeirão Preto'),
	('3513306','Cruzália','SP','Assis'),
	('3513405','Cruzeiro','SP','Vale do Paraíba Paulista'),
	('3513504','Cubatão','SP','Metropolitana de São Paulo'),
	('3513603','Cunha','SP','Vale do Paraíba Paulista'),
	('3513702','Descalvado','SP','Araraquara'),
	('3513801','Diadema','SP','Metropolitana de São Paulo'),
	('3513850','Dirce Reis','SP','São José do Rio Preto'),
	('3513900','Divinolândia','SP','Campinas'),
	('3514007','Dobrada','SP','Araraquara'),
	('3514106','Dois Córregos','SP','Bauru'),
	('3514205','Dolcinópolis','SP','São José do Rio Preto'),
	('3514304','Dourado','SP','Araraquara'),
	('3514403','Dracena','SP','Presidente Prudente'),
	('3514502','Duartina','SP','Bauru'),
	('3514601','Dumont','SP','Ribeirão Preto'),
	('3514700','Echaporã','SP','Marília'),
	('3514809','Eldorado','SP','Litoral Sul Paulista'),
	('3514908','Elias Fausto','SP','Campinas'),
	('3514924','Elisiário','SP','São José do Rio Preto'),
	('3514957','Embaúba','SP','São José do Rio Preto'),
	('3515004','Embu das Artes','SP','Metropolitana de São Paulo'),
	('3515103','Embu-Guaçu','SP','Metropolitana de São Paulo'),
	('3515129','Emilianópolis','SP','Presidente Prudente'),
	('3515152','Engenheiro Coelho','SP','Campinas'),
	('3515186','Espírito Santo do Pinhal','SP','Campinas'),
	('3515194','Espírito Santo do Turvo','SP','Assis'),
	('3515202','Estrela d\'Oeste','SP','São José do Rio Preto'),
	('3515301','Estrela do Norte','SP','Presidente Prudente'),
	('3515350','Euclides da Cunha Paulista','SP','Presidente Prudente'),
	('3515400','Fartura','SP','Assis'),
	('3515509','Fernandópolis','SP','São José do Rio Preto'),
	('3515608','Fernando Prestes','SP','Ribeirão Preto'),
	('3515657','Fernão','SP','Marília'),
	('3515707','Ferraz de Vasconcelos','SP','Metropolitana de São Paulo'),
	('3515806','Flora Rica','SP','Presidente Prudente'),
	('3515905','Floreal','SP','São José do Rio Preto'),
	('3516002','Flórida Paulista','SP','Presidente Prudente'),
	('3516101','Florínea','SP','Assis'),
	('3516200','Franca','SP','Ribeirão Preto'),
	('3516309','Francisco Morato','SP','Metropolitana de São Paulo'),
	('3516408','Franco da Rocha','SP','Metropolitana de São Paulo'),
	('3516507','Gabriel Monteiro','SP','Araçatuba'),
	('3516606','Gália','SP','Marília'),
	('3516705','Garça','SP','Marília'),
	('3516804','Gastão Vidigal','SP','São José do Rio Preto'),
	('3516853','Gavião Peixoto','SP','Araraquara'),
	('3516903','General Salgado','SP','São José do Rio Preto'),
	('3517000','Getulina','SP','Bauru'),
	('3517109','Glicério','SP','Araçatuba'),
	('3517208','Guaiçara','SP','Bauru'),
	('3517307','Guaimbê','SP','Bauru'),
	('3517406','Guaíra','SP','Ribeirão Preto'),
	('3517505','Guapiaçu','SP','São José do Rio Preto'),
	('3517604','Guapiara','SP','Itapetininga'),
	('3517703','Guará','SP','Ribeirão Preto'),
	('3517802','Guaraçaí','SP','Araçatuba'),
	('3517901','Guaraci','SP','São José do Rio Preto'),
	('3518008','Guarani d\'Oeste','SP','São José do Rio Preto'),
	('3518107','Guarantã','SP','Bauru'),
	('3518206','Guararapes','SP','Araçatuba'),
	('3518305','Guararema','SP','Metropolitana de São Paulo'),
	('3518404','Guaratinguetá','SP','Vale do Paraíba Paulista'),
	('3518503','Guareí','SP','Itapetininga'),
	('3518602','Guariba','SP','Ribeirão Preto'),
	('3518701','Guarujá','SP','Metropolitana de São Paulo'),
	('3518800','Guarulhos','SP','Metropolitana de São Paulo'),
	('3518859','Guatapará','SP','Ribeirão Preto'),
	('3518909','Guzolândia','SP','São José do Rio Preto'),
	('3519006','Herculândia','SP','Marília'),
	('3519055','Holambra','SP','Campinas'),
	('3519071','Hortolândia','SP','Campinas'),
	('3519105','Iacanga','SP','Bauru'),
	('3519204','Iacri','SP','Marília'),
	('3519253','Iaras','SP','Bauru'),
	('3519303','Ibaté','SP','Araraquara'),
	('3519402','Ibirá','SP','São José do Rio Preto'),
	('3519501','Ibirarema','SP','Assis'),
	('3519600','Ibitinga','SP','Araraquara'),
	('3519709','Ibiúna','SP','Macro Metropolitana Paulista'),
	('3519808','Icém','SP','São José do Rio Preto'),
	('3519907','Iepê','SP','Assis'),
	('3520004','Igaraçu do Tietê','SP','Bauru'),
	('3520103','Igarapava','SP','Ribeirão Preto'),
	('3520202','Igaratá','SP','Vale do Paraíba Paulista'),
	('3520301','Iguape','SP','Litoral Sul Paulista'),
	('3520400','Ilhabela','SP','Vale do Paraíba Paulista'),
	('3520426','Ilha Comprida','SP','Litoral Sul Paulista'),
	('3520442','Ilha Solteira','SP','Araçatuba'),
	('3520509','Indaiatuba','SP','Campinas'),
	('3520608','Indiana','SP','Presidente Prudente'),
	('3520707','Indiaporã','SP','São José do Rio Preto'),
	('3520806','Inúbia Paulista','SP','Presidente Prudente'),
	('3520905','Ipaussu','SP','Assis'),
	('3521002','Iperó','SP','Macro Metropolitana Paulista'),
	('3521101','Ipeúna','SP','Piracicaba'),
	('3521150','Ipiguá','SP','São José do Rio Preto'),
	('3521200','Iporanga','SP','Itapetininga'),
	('3521309','Ipuã','SP','Ribeirão Preto'),
	('3521408','Iracemápolis','SP','Piracicaba'),
	('3521507','Irapuã','SP','São José do Rio Preto'),
	('3521606','Irapuru','SP','Presidente Prudente'),
	('3521705','Itaberá','SP','Itapetininga'),
	('3521804','Itaí','SP','Bauru'),
	('3521903','Itajobi','SP','São José do Rio Preto'),
	('3522000','Itaju','SP','Bauru'),
	('3522109','Itanhaém','SP','Litoral Sul Paulista'),
	('3522158','Itaoca','SP','Itapetininga'),
	('3522208','Itapecerica da Serra','SP','Metropolitana de São Paulo'),
	('3522307','Itapetininga','SP','Itapetininga'),
	('3522406','Itapeva','SP','Itapetininga'),
	('3522505','Itapevi','SP','Metropolitana de São Paulo'),
	('3522604','Itapira','SP','Campinas'),
	('3522653','Itapirapuã Paulista','SP','Itapetininga'),
	('3522703','Itápolis','SP','Araraquara'),
	('3522802','Itaporanga','SP','Itapetininga'),
	('3522901','Itapuí','SP','Bauru'),
	('3523008','Itapura','SP','Araçatuba'),
	('3523107','Itaquaquecetuba','SP','Metropolitana de São Paulo'),
	('3523206','Itararé','SP','Itapetininga'),
	('3523305','Itariri','SP','Litoral Sul Paulista'),
	('3523404','Itatiba','SP','Macro Metropolitana Paulista'),
	('3523503','Itatinga','SP','Bauru'),
	('3523602','Itirapina','SP','Piracicaba'),
	('3523701','Itirapuã','SP','Ribeirão Preto'),
	('3523800','Itobi','SP','Campinas'),
	('3523909','Itu','SP','Macro Metropolitana Paulista'),
	('3524006','Itupeva','SP','Macro Metropolitana Paulista'),
	('3524105','Ituverava','SP','Ribeirão Preto'),
	('3524204','Jaborandi','SP','Ribeirão Preto'),
	('3524303','Jaboticabal','SP','Ribeirão Preto'),
	('3524402','Jacareí','SP','Vale do Paraíba Paulista'),
	('3524501','Jaci','SP','São José do Rio Preto'),
	('3524600','Jacupiranga','SP','Litoral Sul Paulista'),
	('3524709','Jaguariúna','SP','Campinas'),
	('3524808','Jales','SP','São José do Rio Preto'),
	('3524907','Jambeiro','SP','Vale do Paraíba Paulista'),
	('3525003','Jandira','SP','Metropolitana de São Paulo'),
	('3525102','Jardinópolis','SP','Ribeirão Preto'),
	('3525201','Jarinu','SP','Macro Metropolitana Paulista'),
	('3525300','Jaú','SP','Bauru'),
	('3525409','Jeriquara','SP','Ribeirão Preto'),
	('3525508','Joanópolis','SP','Macro Metropolitana Paulista'),
	('3525607','João Ramalho','SP','Presidente Prudente'),
	('3525706','José Bonifácio','SP','São José do Rio Preto'),
	('3525805','Júlio Mesquita','SP','Bauru'),
	('3525854','Jumirim','SP','Piracicaba'),
	('3525904','Jundiaí','SP','Macro Metropolitana Paulista'),
	('3526001','Junqueirópolis','SP','Presidente Prudente'),
	('3526100','Juquiá','SP','Litoral Sul Paulista'),
	('3526209','Juquitiba','SP','Metropolitana de São Paulo'),
	('3526308','Lagoinha','SP','Vale do Paraíba Paulista'),
	('3526407','Laranjal Paulista','SP','Itapetininga'),
	('3526506','Lavínia','SP','Araçatuba'),
	('3526605','Lavrinhas','SP','Vale do Paraíba Paulista'),
	('3526704','Leme','SP','Piracicaba'),
	('3526803','Lençóis Paulista','SP','Bauru'),
	('3526902','Limeira','SP','Piracicaba'),
	('3527009','Lindóia','SP','Campinas'),
	('3527108','Lins','SP','Bauru'),
	('3527207','Lorena','SP','Vale do Paraíba Paulista'),
	('3527256','Lourdes','SP','Araçatuba'),
	('3527306','Louveira','SP','Macro Metropolitana Paulista'),
	('3527405','Lucélia','SP','Presidente Prudente'),
	('3527504','Lucianópolis','SP','Bauru'),
	('3527603','Luís Antônio','SP','Ribeirão Preto'),
	('3527702','Luiziânia','SP','Araçatuba'),
	('3527801','Lupércio','SP','Marília'),
	('3527900','Lutécia','SP','Assis'),
	('3528007','Macatuba','SP','Bauru'),
	('3528106','Macaubal','SP','São José do Rio Preto'),
	('3528205','Macedônia','SP','São José do Rio Preto'),
	('3528304','Magda','SP','São José do Rio Preto'),
	('3528403','Mairinque','SP','Macro Metropolitana Paulista'),
	('3528502','Mairiporã','SP','Metropolitana de São Paulo'),
	('3528601','Manduri','SP','Assis'),
	('3528700','Marabá Paulista','SP','Presidente Prudente'),
	('3528809','Maracaí','SP','Assis'),
	('3528858','Marapoama','SP','São José do Rio Preto'),
	('3528908','Mariápolis','SP','Presidente Prudente'),
	('3529005','Marília','SP','Marília'),
	('3529104','Marinópolis','SP','São José do Rio Preto'),
	('3529203','Martinópolis','SP','Presidente Prudente'),
	('3529302','Matão','SP','Araraquara'),
	('3529401','Mauá','SP','Metropolitana de São Paulo'),
	('3529500','Mendonça','SP','São José do Rio Preto'),
	('3529609','Meridiano','SP','São José do Rio Preto'),
	('3529658','Mesópolis','SP','São José do Rio Preto'),
	('3529708','Miguelópolis','SP','Ribeirão Preto'),
	('3529807','Mineiros do Tietê','SP','Bauru'),
	('3529906','Miracatu','SP','Litoral Sul Paulista'),
	('3530003','Mira Estrela','SP','São José do Rio Preto'),
	('3530102','Mirandópolis','SP','Araçatuba'),
	('3530201','Mirante do Paranapanema','SP','Presidente Prudente'),
	('3530300','Mirassol','SP','São José do Rio Preto'),
	('3530409','Mirassolândia','SP','São José do Rio Preto'),
	('3530508','Mococa','SP','Campinas'),
	('3530607','Mogi das Cruzes','SP','Metropolitana de São Paulo'),
	('3530706','Mogi Guaçu','SP','Campinas'),
	('3530805','Mogi Mirim','SP','Campinas'),
	('3530904','Mombuca','SP','Piracicaba'),
	('3531001','Monções','SP','São José do Rio Preto'),
	('3531100','Mongaguá','SP','Litoral Sul Paulista'),
	('3531209','Monte Alegre do Sul','SP','Campinas'),
	('3531308','Monte Alto','SP','Ribeirão Preto'),
	('3531407','Monte Aprazível','SP','São José do Rio Preto'),
	('3531506','Monte Azul Paulista','SP','Ribeirão Preto'),
	('3531605','Monte Castelo','SP','Presidente Prudente'),
	('3531704','Monteiro Lobato','SP','Vale do Paraíba Paulista'),
	('3531803','Monte Mor','SP','Campinas'),
	('3531902','Morro Agudo','SP','Ribeirão Preto'),
	('3532009','Morungaba','SP','Macro Metropolitana Paulista'),
	('3532058','Motuca','SP','Araraquara'),
	('3532108','Murutinga do Sul','SP','Araçatuba'),
	('3532157','Nantes','SP','Assis'),
	('3532207','Narandiba','SP','Presidente Prudente'),
	('3532306','Natividade da Serra','SP','Vale do Paraíba Paulista'),
	('3532405','Nazaré Paulista','SP','Macro Metropolitana Paulista'),
	('3532504','Neves Paulista','SP','São José do Rio Preto'),
	('3532603','Nhandeara','SP','São José do Rio Preto'),
	('3532702','Nipoã','SP','São José do Rio Preto'),
	('3532801','Nova Aliança','SP','São José do Rio Preto'),
	('3532827','Nova Campina','SP','Itapetininga'),
	('3532843','Nova Canaã Paulista','SP','São José do Rio Preto'),
	('3532868','Nova Castilho','SP','São José do Rio Preto'),
	('3532900','Nova Europa','SP','Araraquara'),
	('3533007','Nova Granada','SP','São José do Rio Preto'),
	('3533106','Nova Guataporanga','SP','Presidente Prudente'),
	('3533205','Nova Independência','SP','Araçatuba'),
	('3533254','Novais','SP','São José do Rio Preto'),
	('3533304','Nova Luzitânia','SP','São José do Rio Preto'),
	('3533403','Nova Odessa','SP','Campinas'),
	('3533502','Novo Horizonte','SP','São José do Rio Preto'),
	('3533601','Nuporanga','SP','Ribeirão Preto'),
	('3533700','Ocauçu','SP','Marília'),
	('3533809','Óleo','SP','Assis'),
	('3533908','Olímpia','SP','São José do Rio Preto'),
	('3534005','Onda Verde','SP','São José do Rio Preto'),
	('3534104','Oriente','SP','Marília'),
	('3534203','Orindiúva','SP','São José do Rio Preto'),
	('3534302','Orlândia','SP','Ribeirão Preto'),
	('3534401','Osasco','SP','Metropolitana de São Paulo'),
	('3534500','Oscar Bressane','SP','Marília'),
	('3534609','Osvaldo Cruz','SP','Presidente Prudente'),
	('3534708','Ourinhos','SP','Assis'),
	('3534757','Ouroeste','SP','São José do Rio Preto'),
	('3534807','Ouro Verde','SP','Presidente Prudente'),
	('3534906','Pacaembu','SP','Presidente Prudente'),
	('3535002','Palestina','SP','São José do Rio Preto'),
	('3535101','Palmares Paulista','SP','São José do Rio Preto'),
	('3535200','Palmeira d\'Oeste','SP','São José do Rio Preto'),
	('3535309','Palmital','SP','Assis'),
	('3535408','Panorama','SP','Presidente Prudente'),
	('3535507','Paraguaçu Paulista','SP','Assis'),
	('3535606','Paraibuna','SP','Vale do Paraíba Paulista'),
	('3535705','Paraíso','SP','São José do Rio Preto'),
	('3535804','Paranapanema','SP','Bauru'),
	('3535903','Paranapuã','SP','São José do Rio Preto'),
	('3536000','Parapuã','SP','Presidente Prudente'),
	('3536109','Pardinho','SP','Bauru'),
	('3536208','Pariquera-Açu','SP','Litoral Sul Paulista'),
	('3536257','Parisi','SP','São José do Rio Preto'),
	('3536307','Patrocínio Paulista','SP','Ribeirão Preto'),
	('3536406','Paulicéia','SP','Presidente Prudente'),
	('3536505','Paulínia','SP','Campinas'),
	('3536570','Paulistânia','SP','Bauru'),
	('3536604','Paulo de Faria','SP','São José do Rio Preto'),
	('3536703','Pederneiras','SP','Bauru'),
	('3536802','Pedra Bela','SP','Campinas'),
	('3536901','Pedranópolis','SP','São José do Rio Preto'),
	('3537008','Pedregulho','SP','Ribeirão Preto'),
	('3537107','Pedreira','SP','Campinas'),
	('3537156','Pedrinhas Paulista','SP','Assis'),
	('3537206','Pedro de Toledo','SP','Litoral Sul Paulista'),
	('3537305','Penápolis','SP','Araçatuba'),
	('3537404','Pereira Barreto','SP','Araçatuba'),
	('3537503','Pereiras','SP','Itapetininga'),
	('3537602','Peruíbe','SP','Litoral Sul Paulista'),
	('3537701','Piacatu','SP','Araçatuba'),
	('3537800','Piedade','SP','Macro Metropolitana Paulista'),
	('3537909','Pilar do Sul','SP','Macro Metropolitana Paulista'),
	('3538006','Pindamonhangaba','SP','Vale do Paraíba Paulista'),
	('3538105','Pindorama','SP','São José do Rio Preto'),
	('3538204','Pinhalzinho','SP','Campinas'),
	('3538303','Piquerobi','SP','Presidente Prudente'),
	('3538501','Piquete','SP','Vale do Paraíba Paulista'),
	('3538600','Piracaia','SP','Macro Metropolitana Paulista'),
	('3538709','Piracicaba','SP','Piracicaba'),
	('3538808','Piraju','SP','Assis'),
	('3538907','Pirajuí','SP','Bauru'),
	('3539004','Pirangi','SP','Ribeirão Preto'),
	('3539103','Pirapora do Bom Jesus','SP','Metropolitana de São Paulo'),
	('3539202','Pirapozinho','SP','Presidente Prudente'),
	('3539301','Pirassununga','SP','Campinas'),
	('3539400','Piratininga','SP','Bauru'),
	('3539509','Pitangueiras','SP','Ribeirão Preto'),
	('3539608','Planalto','SP','São José do Rio Preto'),
	('3539707','Platina','SP','Assis'),
	('3539806','Poá','SP','Metropolitana de São Paulo'),
	('3539905','Poloni','SP','São José do Rio Preto'),
	('3540002','Pompéia','SP','Marília'),
	('3540101','Pongaí','SP','Bauru'),
	('3540200','Pontal','SP','Ribeirão Preto'),
	('3540259','Pontalinda','SP','São José do Rio Preto'),
	('3540309','Pontes Gestal','SP','São José do Rio Preto'),
	('3540408','Populina','SP','São José do Rio Preto'),
	('3540507','Porangaba','SP','Itapetininga'),
	('3540606','Porto Feliz','SP','Macro Metropolitana Paulista'),
	('3540705','Porto Ferreira','SP','Campinas'),
	('3540754','Potim','SP','Vale do Paraíba Paulista'),
	('3540804','Potirendaba','SP','São José do Rio Preto'),
	('3540853','Pracinha','SP','Presidente Prudente'),
	('3540903','Pradópolis','SP','Ribeirão Preto'),
	('3541000','Praia Grande','SP','Metropolitana de São Paulo'),
	('3541059','Pratânia','SP','Bauru'),
	('3541109','Presidente Alves','SP','Bauru'),
	('3541208','Presidente Bernardes','SP','Presidente Prudente'),
	('3541307','Presidente Epitácio','SP','Presidente Prudente'),
	('3541406','Presidente Prudente','SP','Presidente Prudente'),
	('3541505','Presidente Venceslau','SP','Presidente Prudente'),
	('3541604','Promissão','SP','Bauru'),
	('3541653','Quadra','SP','Itapetininga'),
	('3541703','Quatá','SP','Assis'),
	('3541802','Queiroz','SP','Marília'),
	('3541901','Queluz','SP','Vale do Paraíba Paulista'),
	('3542008','Quintana','SP','Marília'),
	('3542107','Rafard','SP','Piracicaba'),
	('3542206','Rancharia','SP','Presidente Prudente'),
	('3542305','Redenção da Serra','SP','Vale do Paraíba Paulista'),
	('3542404','Regente Feijó','SP','Presidente Prudente'),
	('3542503','Reginópolis','SP','Bauru'),
	('3542602','Registro','SP','Litoral Sul Paulista'),
	('3542701','Restinga','SP','Ribeirão Preto'),
	('3542800','Ribeira','SP','Itapetininga'),
	('3542909','Ribeirão Bonito','SP','Araraquara'),
	('3543006','Ribeirão Branco','SP','Itapetininga'),
	('3543105','Ribeirão Corrente','SP','Ribeirão Preto'),
	('3543204','Ribeirão do Sul','SP','Assis'),
	('3543238','Ribeirão dos Índios','SP','Presidente Prudente'),
	('3543253','Ribeirão Grande','SP','Itapetininga'),
	('3543303','Ribeirão Pires','SP','Metropolitana de São Paulo'),
	('3543402','Ribeirão Preto','SP','Ribeirão Preto'),
	('3543501','Riversul','SP','Itapetininga'),
	('3543600','Rifaina','SP','Ribeirão Preto'),
	('3543709','Rincão','SP','Araraquara'),
	('3543808','Rinópolis','SP','Presidente Prudente'),
	('3543907','Rio Claro','SP','Piracicaba'),
	('3544004','Rio das Pedras','SP','Piracicaba'),
	('3544103','Rio Grande da Serra','SP','Metropolitana de São Paulo'),
	('3544202','Riolândia','SP','São José do Rio Preto'),
	('3544251','Rosana','SP','Presidente Prudente'),
	('3544301','Roseira','SP','Vale do Paraíba Paulista'),
	('3544400','Rubiácea','SP','Araçatuba'),
	('3544509','Rubinéia','SP','São José do Rio Preto'),
	('3544608','Sabino','SP','Bauru'),
	('3544707','Sagres','SP','Presidente Prudente'),
	('3544806','Sales','SP','São José do Rio Preto'),
	('3544905','Sales Oliveira','SP','Ribeirão Preto'),
	('3545001','Salesópolis','SP','Metropolitana de São Paulo'),
	('3545100','Salmourão','SP','Presidente Prudente'),
	('3545159','Saltinho','SP','Piracicaba'),
	('3545209','Salto','SP','Macro Metropolitana Paulista'),
	('3545308','Salto de Pirapora','SP','Macro Metropolitana Paulista'),
	('3545407','Salto Grande','SP','Assis'),
	('3545506','Sandovalina','SP','Presidente Prudente'),
	('3545605','Santa Adélia','SP','São José do Rio Preto'),
	('3545704','Santa Albertina','SP','São José do Rio Preto'),
	('3545803','Santa Bárbara d\'Oeste','SP','Campinas'),
	('3546009','Santa Branca','SP','Vale do Paraíba Paulista'),
	('3546108','Santa Clara d\'Oeste','SP','São José do Rio Preto'),
	('3546207','Santa Cruz da Conceição','SP','Piracicaba'),
	('3546256','Santa Cruz da Esperança','SP','Ribeirão Preto'),
	('3546306','Santa Cruz das Palmeiras','SP','Campinas'),
	('3546405','Santa Cruz do Rio Pardo','SP','Assis'),
	('3546504','Santa Ernestina','SP','Ribeirão Preto'),
	('3546603','Santa Fé do Sul','SP','São José do Rio Preto'),
	('3546702','Santa Gertrudes','SP','Piracicaba'),
	('3546801','Santa Isabel','SP','Metropolitana de São Paulo'),
	('3546900','Santa Lúcia','SP','Araraquara'),
	('3547007','Santa Maria da Serra','SP','Piracicaba'),
	('3547106','Santa Mercedes','SP','Presidente Prudente'),
	('3547205','Santana da Ponte Pensa','SP','São José do Rio Preto'),
	('3547304','Santana de Parnaíba','SP','Metropolitana de São Paulo'),
	('3547403','Santa Rita d\'Oeste','SP','São José do Rio Preto'),
	('3547502','Santa Rita do Passa Quatro','SP','Ribeirão Preto'),
	('3547601','Santa Rosa de Viterbo','SP','Ribeirão Preto'),
	('3547650','Santa Salete','SP','São José do Rio Preto'),
	('3547700','Santo Anastácio','SP','Presidente Prudente'),
	('3547809','Santo André','SP','Metropolitana de São Paulo'),
	('3547908','Santo Antônio da Alegria','SP','Ribeirão Preto'),
	('3548005','Santo Antônio de Posse','SP','Campinas'),
	('3548054','Santo Antônio do Aracanguá','SP','Araçatuba'),
	('3548104','Santo Antônio do Jardim','SP','Campinas'),
	('3548203','Santo Antônio do Pinhal','SP','Vale do Paraíba Paulista'),
	('3548302','Santo Expedito','SP','Presidente Prudente'),
	('3548401','Santópolis do Aguapeí','SP','Araçatuba'),
	('3548500','Santos','SP','Metropolitana de São Paulo'),
	('3548609','São Bento do Sapucaí','SP','Vale do Paraíba Paulista'),
	('3548708','São Bernardo do Campo','SP','Metropolitana de São Paulo'),
	('3548807','São Caetano do Sul','SP','Metropolitana de São Paulo'),
	('3548906','São Carlos','SP','Araraquara'),
	('3549003','São Francisco','SP','São José do Rio Preto'),
	('3549102','São João da Boa Vista','SP','Campinas'),
	('3549201','São João das Duas Pontes','SP','São José do Rio Preto'),
	('3549250','São João de Iracema','SP','São José do Rio Preto'),
	('3549300','São João do Pau d\'Alho','SP','Presidente Prudente'),
	('3549409','São Joaquim da Barra','SP','Ribeirão Preto'),
	('3549508','São José da Bela Vista','SP','Ribeirão Preto'),
	('3549607','São José do Barreiro','SP','Vale do Paraíba Paulista'),
	('3549706','São José do Rio Pardo','SP','Campinas'),
	('3549805','São José do Rio Preto','SP','São José do Rio Preto'),
	('3549904','São José dos Campos','SP','Vale do Paraíba Paulista'),
	('3549953','São Lourenço da Serra','SP','Metropolitana de São Paulo'),
	('3550001','São Luiz do Paraitinga','SP','Vale do Paraíba Paulista'),
	('3550100','São Manuel','SP','Bauru'),
	('3550209','São Miguel Arcanjo','SP','Macro Metropolitana Paulista'),
	('3550308','São Paulo','SP','Metropolitana de São Paulo'),
	('3550407','São Pedro','SP','Piracicaba'),
	('3550506','São Pedro do Turvo','SP','Assis'),
	('3550605','São Roque','SP','Macro Metropolitana Paulista'),
	('3550704','São Sebastião','SP','Vale do Paraíba Paulista'),
	('3550803','São Sebastião da Grama','SP','Campinas'),
	('3550902','São Simão','SP','Ribeirão Preto'),
	('3551009','São Vicente','SP','Metropolitana de São Paulo'),
	('3551108','Sarapuí','SP','Macro Metropolitana Paulista'),
	('3551207','Sarutaiá','SP','Assis'),
	('3551306','Sebastianópolis do Sul','SP','São José do Rio Preto'),
	('3551405','Serra Azul','SP','Ribeirão Preto'),
	('3551504','Serrana','SP','Ribeirão Preto'),
	('3551603','Serra Negra','SP','Campinas'),
	('3551702','Sertãozinho','SP','Ribeirão Preto'),
	('3551801','Sete Barras','SP','Litoral Sul Paulista'),
	('3551900','Severínia','SP','São José do Rio Preto'),
	('3552007','Silveiras','SP','Vale do Paraíba Paulista'),
	('3552106','Socorro','SP','Campinas'),
	('3552205','Sorocaba','SP','Macro Metropolitana Paulista'),
	('3552304','Sud Mennucci','SP','Araçatuba'),
	('3552403','Sumaré','SP','Campinas'),
	('3552502','Suzano','SP','Metropolitana de São Paulo'),
	('3552551','Suzanápolis','SP','Araçatuba'),
	('3552601','Tabapuã','SP','São José do Rio Preto'),
	('3552700','Tabatinga','SP','Araraquara'),
	('3552809','Taboão da Serra','SP','Metropolitana de São Paulo'),
	('3552908','Taciba','SP','Presidente Prudente'),
	('3553005','Taguaí','SP','Assis'),
	('3553104','Taiaçu','SP','Ribeirão Preto'),
	('3553203','Taiúva','SP','Ribeirão Preto'),
	('3553302','Tambaú','SP','Campinas'),
	('3553401','Tanabi','SP','São José do Rio Preto'),
	('3553500','Tapiraí','SP','Macro Metropolitana Paulista'),
	('3553609','Tapiratiba','SP','Campinas'),
	('3553658','Taquaral','SP','Ribeirão Preto'),
	('3553708','Taquaritinga','SP','Ribeirão Preto'),
	('3553807','Taquarituba','SP','Itapetininga'),
	('3553856','Taquarivaí','SP','Itapetininga'),
	('3553906','Tarabai','SP','Presidente Prudente'),
	('3553955','Tarumã','SP','Assis'),
	('3554003','Tatuí','SP','Itapetininga'),
	('3554102','Taubaté','SP','Vale do Paraíba Paulista'),
	('3554201','Tejupá','SP','Assis'),
	('3554300','Teodoro Sampaio','SP','Presidente Prudente'),
	('3554409','Terra Roxa','SP','Ribeirão Preto'),
	('3554508','Tietê','SP','Piracicaba'),
	('3554607','Timburi','SP','Assis'),
	('3554656','Torre de Pedra','SP','Itapetininga'),
	('3554706','Torrinha','SP','Piracicaba'),
	('3554755','Trabiju','SP','Araraquara'),
	('3554805','Tremembé','SP','Vale do Paraíba Paulista'),
	('3554904','Três Fronteiras','SP','São José do Rio Preto'),
	('3554953','Tuiuti','SP','Macro Metropolitana Paulista'),
	('3555000','Tupã','SP','Marília'),
	('3555109','Tupi Paulista','SP','Presidente Prudente'),
	('3555208','Turiúba','SP','Araçatuba'),
	('3555307','Turmalina','SP','São José do Rio Preto'),
	('3555356','Ubarana','SP','São José do Rio Preto'),
	('3555406','Ubatuba','SP','Vale do Paraíba Paulista'),
	('3555505','Ubirajara','SP','Bauru'),
	('3555604','Uchoa','SP','São José do Rio Preto'),
	('3555703','União Paulista','SP','São José do Rio Preto'),
	('3555802','Urânia','SP','São José do Rio Preto'),
	('3555901','Uru','SP','Bauru'),
	('3556008','Urupês','SP','São José do Rio Preto'),
	('3556107','Valentim Gentil','SP','São José do Rio Preto'),
	('3556206','Valinhos','SP','Campinas'),
	('3556305','Valparaíso','SP','Araçatuba'),
	('3556354','Vargem','SP','Macro Metropolitana Paulista'),
	('3556404','Vargem Grande do Sul','SP','Campinas'),
	('3556453','Vargem Grande Paulista','SP','Metropolitana de São Paulo'),
	('3556503','Várzea Paulista','SP','Macro Metropolitana Paulista'),
	('3556602','Vera Cruz','SP','Marília'),
	('3556701','Vinhedo','SP','Campinas'),
	('3556800','Viradouro','SP','Ribeirão Preto'),
	('3556909','Vista Alegre do Alto','SP','Ribeirão Preto'),
	('3556958','Vitória Brasil','SP','São José do Rio Preto'),
	('3557006','Votorantim','SP','Macro Metropolitana Paulista'),
	('3557105','Votuporanga','SP','São José do Rio Preto'),
	('3557154','Zacarias','SP','São José do Rio Preto'),
	('3557204','Chavantes','SP','Assis'),
	('3557303','Estiva Gerbi','SP','Campinas'),
	('4100103','Abatiá','PR','Norte Pioneiro Paranaense'),
	('4100202','Adrianópolis','PR','Metropolitana de Curitiba'),
	('4100301','Agudos do Sul','PR','Metropolitana de Curitiba'),
	('4100400','Almirante Tamandaré','PR','Metropolitana de Curitiba'),
	('4100459','Altamira do Paraná','PR','Centro Ocidental Paranaense'),
	('4100509','Altônia','PR','Noroeste Paranaense'),
	('4100608','Alto Paraná','PR','Noroeste Paranaense'),
	('4100707','Alto Piquiri','PR','Noroeste Paranaense'),
	('4100806','Alvorada do Sul','PR','Norte Central Paranaense'),
	('4100905','Amaporã','PR','Noroeste Paranaense'),
	('4101002','Ampére','PR','Sudoeste Paranaense'),
	('4101051','Anahy','PR','Oeste Paranaense'),
	('4101101','Andirá','PR','Norte Pioneiro Paranaense'),
	('4101150','Ângulo','PR','Norte Central Paranaense'),
	('4101200','Antonina','PR','Metropolitana de Curitiba'),
	('4101309','Antônio Olinto','PR','Sudeste Paranaense'),
	('4101408','Apucarana','PR','Norte Central Paranaense'),
	('4101507','Arapongas','PR','Norte Central Paranaense'),
	('4101606','Arapoti','PR','Centro Oriental Paranaense'),
	('4101655','Arapuã','PR','Norte Central Paranaense'),
	('4101705','Araruna','PR','Centro Ocidental Paranaense'),
	('4101804','Araucária','PR','Metropolitana de Curitiba'),
	('4101853','Ariranha do Ivaí','PR','Norte Central Paranaense'),
	('4101903','Assaí','PR','Norte Pioneiro Paranaense'),
	('4102000','Assis Chateaubriand','PR','Oeste Paranaense'),
	('4102109','Astorga','PR','Norte Central Paranaense'),
	('4102208','Atalaia','PR','Norte Central Paranaense'),
	('4102307','Balsa Nova','PR','Metropolitana de Curitiba'),
	('4102406','Bandeirantes','PR','Norte Pioneiro Paranaense'),
	('4102505','Barbosa Ferraz','PR','Centro Ocidental Paranaense'),
	('4102604','Barracão','PR','Sudoeste Paranaense'),
	('4102703','Barra do Jacaré','PR','Norte Pioneiro Paranaense'),
	('4102752','Bela Vista da Caroba','PR','Sudoeste Paranaense'),
	('4102802','Bela Vista do Paraíso','PR','Norte Central Paranaense'),
	('4102901','Bituruna','PR','Sudeste Paranaense'),
	('4103008','Boa Esperança','PR','Centro Ocidental Paranaense'),
	('4103024','Boa Esperança do Iguaçu','PR','Sudoeste Paranaense'),
	('4103040','Boa Ventura de São Roque','PR','Centro-Sul Paranaense'),
	('4103057','Boa Vista da Aparecida','PR','Oeste Paranaense'),
	('4103107','Bocaiúva do Sul','PR','Metropolitana de Curitiba'),
	('4103156','Bom Jesus do Sul','PR','Sudoeste Paranaense'),
	('4103206','Bom Sucesso','PR','Norte Central Paranaense'),
	('4103222','Bom Sucesso do Sul','PR','Sudoeste Paranaense'),
	('4103305','Borrazópolis','PR','Norte Central Paranaense'),
	('4103354','Braganey','PR','Oeste Paranaense'),
	('4103370','Brasilândia do Sul','PR','Noroeste Paranaense'),
	('4103404','Cafeara','PR','Norte Central Paranaense'),
	('4103453','Cafelândia','PR','Oeste Paranaense'),
	('4103479','Cafezal do Sul','PR','Noroeste Paranaense'),
	('4103503','Califórnia','PR','Norte Central Paranaense'),
	('4103602','Cambará','PR','Norte Pioneiro Paranaense'),
	('4103701','Cambé','PR','Norte Central Paranaense'),
	('4103800','Cambira','PR','Norte Central Paranaense'),
	('4103909','Campina da Lagoa','PR','Centro Ocidental Paranaense'),
	('4103958','Campina do Simão','PR','Centro-Sul Paranaense'),
	('4104006','Campina Grande do Sul','PR','Metropolitana de Curitiba'),
	('4104055','Campo Bonito','PR','Oeste Paranaense'),
	('4104105','Campo do Tenente','PR','Metropolitana de Curitiba'),
	('4104204','Campo Largo','PR','Metropolitana de Curitiba'),
	('4104253','Campo Magro','PR','Metropolitana de Curitiba'),
	('4104303','Campo Mourão','PR','Centro Ocidental Paranaense'),
	('4104402','Cândido de Abreu','PR','Norte Central Paranaense'),
	('4104428','Candói','PR','Centro-Sul Paranaense'),
	('4104451','Cantagalo','PR','Centro-Sul Paranaense'),
	('4104501','Capanema','PR','Sudoeste Paranaense'),
	('4104600','Capitão Leônidas Marques','PR','Oeste Paranaense'),
	('4104659','Carambeí','PR','Centro Oriental Paranaense'),
	('4104709','Carlópolis','PR','Norte Pioneiro Paranaense'),
	('4104808','Cascavel','PR','Oeste Paranaense'),
	('4104907','Castro','PR','Centro Oriental Paranaense'),
	('4105003','Catanduvas','PR','Oeste Paranaense'),
	('4105102','Centenário do Sul','PR','Norte Central Paranaense'),
	('4105201','Cerro Azul','PR','Metropolitana de Curitiba'),
	('4105300','Céu Azul','PR','Oeste Paranaense'),
	('4105409','Chopinzinho','PR','Sudoeste Paranaense'),
	('4105508','Cianorte','PR','Noroeste Paranaense'),
	('4105607','Cidade Gaúcha','PR','Noroeste Paranaense'),
	('4105706','Clevelândia','PR','Centro-Sul Paranaense'),
	('4105805','Colombo','PR','Metropolitana de Curitiba'),
	('4105904','Colorado','PR','Norte Central Paranaense'),
	('4106001','Congonhinhas','PR','Norte Pioneiro Paranaense'),
	('4106100','Conselheiro Mairinck','PR','Norte Pioneiro Paranaense'),
	('4106209','Contenda','PR','Metropolitana de Curitiba'),
	('4106308','Corbélia','PR','Oeste Paranaense'),
	('4106407','Cornélio Procópio','PR','Norte Pioneiro Paranaense'),
	('4106456','Coronel Domingos Soares','PR','Centro-Sul Paranaense'),
	('4106506','Coronel Vivida','PR','Sudoeste Paranaense'),
	('4106555','Corumbataí do Sul','PR','Centro Ocidental Paranaense'),
	('4106571','Cruzeiro do Iguaçu','PR','Sudoeste Paranaense'),
	('4106605','Cruzeiro do Oeste','PR','Noroeste Paranaense'),
	('4106704','Cruzeiro do Sul','PR','Noroeste Paranaense'),
	('4106803','Cruz Machado','PR','Sudeste Paranaense'),
	('4106852','Cruzmaltina','PR','Norte Central Paranaense'),
	('4106902','Curitiba','PR','Metropolitana de Curitiba'),
	('4107009','Curiúva','PR','Norte Pioneiro Paranaense'),
	('4107108','Diamante do Norte','PR','Noroeste Paranaense'),
	('4107124','Diamante do Sul','PR','Oeste Paranaense'),
	('4107157','Diamante D\'Oeste','PR','Oeste Paranaense'),
	('4107207','Dois Vizinhos','PR','Sudoeste Paranaense'),
	('4107256','Douradina','PR','Noroeste Paranaense'),
	('4107306','Doutor Camargo','PR','Norte Central Paranaense'),
	('4107405','Enéas Marques','PR','Sudoeste Paranaense'),
	('4107504','Engenheiro Beltrão','PR','Centro Ocidental Paranaense'),
	('4107520','Esperança Nova','PR','Noroeste Paranaense'),
	('4107538','Entre Rios do Oeste','PR','Oeste Paranaense'),
	('4107546','Espigão Alto do Iguaçu','PR','Centro-Sul Paranaense'),
	('4107553','Farol','PR','Centro Ocidental Paranaense'),
	('4107603','Faxinal','PR','Norte Central Paranaense'),
	('4107652','Fazenda Rio Grande','PR','Metropolitana de Curitiba'),
	('4107702','Fênix','PR','Centro Ocidental Paranaense'),
	('4107736','Fernandes Pinheiro','PR','Sudeste Paranaense'),
	('4107751','Figueira','PR','Norte Pioneiro Paranaense'),
	('4107801','Floraí','PR','Norte Central Paranaense'),
	('4107850','Flor da Serra do Sul','PR','Sudoeste Paranaense'),
	('4107900','Floresta','PR','Norte Central Paranaense'),
	('4108007','Florestópolis','PR','Norte Central Paranaense'),
	('4108106','Flórida','PR','Norte Central Paranaense'),
	('4108205','Formosa do Oeste','PR','Oeste Paranaense'),
	('4108304','Foz do Iguaçu','PR','Oeste Paranaense'),
	('4108320','Francisco Alves','PR','Noroeste Paranaense'),
	('4108403','Francisco Beltrão','PR','Sudoeste Paranaense'),
	('4108452','Foz do Jordão','PR','Centro-Sul Paranaense'),
	('4108502','General Carneiro','PR','Sudeste Paranaense'),
	('4108551','Godoy Moreira','PR','Norte Central Paranaense'),
	('4108601','Goioerê','PR','Centro Ocidental Paranaense'),
	('4108650','Goioxim','PR','Centro-Sul Paranaense'),
	('4108700','Grandes Rios','PR','Norte Central Paranaense'),
	('4108809','Guaíra','PR','Oeste Paranaense'),
	('4108908','Guairaçá','PR','Noroeste Paranaense'),
	('4108957','Guamiranga','PR','Sudeste Paranaense'),
	('4109005','Guapirama','PR','Norte Pioneiro Paranaense'),
	('4109104','Guaporema','PR','Noroeste Paranaense'),
	('4109203','Guaraci','PR','Norte Central Paranaense'),
	('4109302','Guaraniaçu','PR','Oeste Paranaense'),
	('4109401','Guarapuava','PR','Centro-Sul Paranaense'),
	('4109500','Guaraqueçaba','PR','Metropolitana de Curitiba'),
	('4109609','Guaratuba','PR','Metropolitana de Curitiba'),
	('4109658','Honório Serpa','PR','Centro-Sul Paranaense'),
	('4109708','Ibaiti','PR','Norte Pioneiro Paranaense'),
	('4109757','Ibema','PR','Oeste Paranaense'),
	('4109807','Ibiporã','PR','Norte Central Paranaense'),
	('4109906','Icaraíma','PR','Noroeste Paranaense'),
	('4110003','Iguaraçu','PR','Norte Central Paranaense'),
	('4110052','Iguatu','PR','Oeste Paranaense'),
	('4110078','Imbaú','PR','Centro Oriental Paranaense'),
	('4110102','Imbituva','PR','Sudeste Paranaense'),
	('4110201','Inácio Martins','PR','Centro-Sul Paranaense'),
	('4110300','Inajá','PR','Noroeste Paranaense'),
	('4110409','Indianópolis','PR','Noroeste Paranaense'),
	('4110508','Ipiranga','PR','Sudeste Paranaense'),
	('4110607','Iporã','PR','Noroeste Paranaense'),
	('4110656','Iracema do Oeste','PR','Oeste Paranaense'),
	('4110706','Irati','PR','Sudeste Paranaense'),
	('4110805','Iretama','PR','Centro Ocidental Paranaense'),
	('4110904','Itaguajé','PR','Norte Central Paranaense'),
	('4110953','Itaipulândia','PR','Oeste Paranaense'),
	('4111001','Itambaracá','PR','Norte Pioneiro Paranaense'),
	('4111100','Itambé','PR','Norte Central Paranaense'),
	('4111209','Itapejara d\'Oeste','PR','Sudoeste Paranaense'),
	('4111258','Itaperuçu','PR','Metropolitana de Curitiba'),
	('4111308','Itaúna do Sul','PR','Noroeste Paranaense'),
	('4111407','Ivaí','PR','Sudeste Paranaense'),
	('4111506','Ivaiporã','PR','Norte Central Paranaense'),
	('4111555','Ivaté','PR','Noroeste Paranaense'),
	('4111605','Ivatuba','PR','Norte Central Paranaense'),
	('4111704','Jaboti','PR','Norte Pioneiro Paranaense'),
	('4111803','Jacarezinho','PR','Norte Pioneiro Paranaense'),
	('4111902','Jaguapitã','PR','Norte Central Paranaense'),
	('4112009','Jaguariaíva','PR','Centro Oriental Paranaense'),
	('4112108','Jandaia do Sul','PR','Norte Central Paranaense'),
	('4112207','Janiópolis','PR','Centro Ocidental Paranaense'),
	('4112306','Japira','PR','Norte Pioneiro Paranaense'),
	('4112405','Japurá','PR','Noroeste Paranaense'),
	('4112504','Jardim Alegre','PR','Norte Central Paranaense'),
	('4112603','Jardim Olinda','PR','Noroeste Paranaense'),
	('4112702','Jataizinho','PR','Norte Pioneiro Paranaense'),
	('4112751','Jesuítas','PR','Oeste Paranaense'),
	('4112801','Joaquim Távora','PR','Norte Pioneiro Paranaense'),
	('4112900','Jundiaí do Sul','PR','Norte Pioneiro Paranaense'),
	('4112959','Juranda','PR','Centro Ocidental Paranaense'),
	('4113007','Jussara','PR','Noroeste Paranaense'),
	('4113106','Kaloré','PR','Norte Central Paranaense'),
	('4113205','Lapa','PR','Metropolitana de Curitiba'),
	('4113254','Laranjal','PR','Centro-Sul Paranaense'),
	('4113304','Laranjeiras do Sul','PR','Centro-Sul Paranaense'),
	('4113403','Leópolis','PR','Norte Pioneiro Paranaense'),
	('4113429','Lidianópolis','PR','Norte Central Paranaense'),
	('4113452','Lindoeste','PR','Oeste Paranaense'),
	('4113502','Loanda','PR','Noroeste Paranaense'),
	('4113601','Lobato','PR','Norte Central Paranaense'),
	('4113700','Londrina','PR','Norte Central Paranaense'),
	('4113734','Luiziana','PR','Centro Ocidental Paranaense'),
	('4113759','Lunardelli','PR','Norte Central Paranaense'),
	('4113809','Lupionópolis','PR','Norte Central Paranaense'),
	('4113908','Mallet','PR','Sudeste Paranaense'),
	('4114005','Mamborê','PR','Centro Ocidental Paranaense'),
	('4114104','Mandaguaçu','PR','Norte Central Paranaense'),
	('4114203','Mandaguari','PR','Norte Central Paranaense'),
	('4114302','Mandirituba','PR','Metropolitana de Curitiba'),
	('4114351','Manfrinópolis','PR','Sudoeste Paranaense'),
	('4114401','Mangueirinha','PR','Centro-Sul Paranaense'),
	('4114500','Manoel Ribas','PR','Norte Central Paranaense'),
	('4114609','Marechal Cândido Rondon','PR','Oeste Paranaense'),
	('4114708','Maria Helena','PR','Noroeste Paranaense'),
	('4114807','Marialva','PR','Norte Central Paranaense'),
	('4114906','Marilândia do Sul','PR','Norte Central Paranaense'),
	('4115002','Marilena','PR','Noroeste Paranaense'),
	('4115101','Mariluz','PR','Noroeste Paranaense'),
	('4115200','Maringá','PR','Norte Central Paranaense'),
	('4115309','Mariópolis','PR','Sudoeste Paranaense'),
	('4115358','Maripá','PR','Oeste Paranaense'),
	('4115408','Marmeleiro','PR','Sudoeste Paranaense'),
	('4115457','Marquinho','PR','Centro-Sul Paranaense'),
	('4115507','Marumbi','PR','Norte Central Paranaense'),
	('4115606','Matelândia','PR','Oeste Paranaense'),
	('4115705','Matinhos','PR','Metropolitana de Curitiba'),
	('4115739','Mato Rico','PR','Centro-Sul Paranaense'),
	('4115754','Mauá da Serra','PR','Norte Central Paranaense'),
	('4115804','Medianeira','PR','Oeste Paranaense'),
	('4115853','Mercedes','PR','Oeste Paranaense'),
	('4115903','Mirador','PR','Noroeste Paranaense'),
	('4116000','Miraselva','PR','Norte Central Paranaense'),
	('4116059','Missal','PR','Oeste Paranaense'),
	('4116109','Moreira Sales','PR','Centro Ocidental Paranaense'),
	('4116208','Morretes','PR','Metropolitana de Curitiba'),
	('4116307','Munhoz de Melo','PR','Norte Central Paranaense'),
	('4116406','Nossa Senhora das Graças','PR','Norte Central Paranaense'),
	('4116505','Nova Aliança do Ivaí','PR','Noroeste Paranaense'),
	('4116604','Nova América da Colina','PR','Norte Pioneiro Paranaense'),
	('4116703','Nova Aurora','PR','Oeste Paranaense'),
	('4116802','Nova Cantu','PR','Centro Ocidental Paranaense'),
	('4116901','Nova Esperança','PR','Norte Central Paranaense'),
	('4116950','Nova Esperança do Sudoeste','PR','Sudoeste Paranaense'),
	('4117008','Nova Fátima','PR','Norte Pioneiro Paranaense'),
	('4117057','Nova Laranjeiras','PR','Centro-Sul Paranaense'),
	('4117107','Nova Londrina','PR','Noroeste Paranaense'),
	('4117206','Nova Olímpia','PR','Noroeste Paranaense'),
	('4117214','Nova Santa Bárbara','PR','Norte Pioneiro Paranaense'),
	('4117222','Nova Santa Rosa','PR','Oeste Paranaense'),
	('4117255','Nova Prata do Iguaçu','PR','Sudoeste Paranaense'),
	('4117271','Nova Tebas','PR','Norte Central Paranaense'),
	('4117297','Novo Itacolomi','PR','Norte Central Paranaense'),
	('4117305','Ortigueira','PR','Centro Oriental Paranaense'),
	('4117404','Ourizona','PR','Norte Central Paranaense'),
	('4117453','Ouro Verde do Oeste','PR','Oeste Paranaense'),
	('4117503','Paiçandu','PR','Norte Central Paranaense'),
	('4117602','Palmas','PR','Centro-Sul Paranaense'),
	('4117701','Palmeira','PR','Centro Oriental Paranaense'),
	('4117800','Palmital','PR','Centro-Sul Paranaense'),
	('4117909','Palotina','PR','Oeste Paranaense'),
	('4118006','Paraíso do Norte','PR','Noroeste Paranaense'),
	('4118105','Paranacity','PR','Noroeste Paranaense'),
	('4118204','Paranaguá','PR','Metropolitana de Curitiba'),
	('4118303','Paranapoema','PR','Noroeste Paranaense'),
	('4118402','Paranavaí','PR','Noroeste Paranaense'),
	('4118451','Pato Bragado','PR','Oeste Paranaense'),
	('4118501','Pato Branco','PR','Sudoeste Paranaense'),
	('4118600','Paula Freitas','PR','Sudeste Paranaense'),
	('4118709','Paulo Frontin','PR','Sudeste Paranaense'),
	('4118808','Peabiru','PR','Centro Ocidental Paranaense'),
	('4118857','Perobal','PR','Noroeste Paranaense'),
	('4118907','Pérola','PR','Noroeste Paranaense'),
	('4119004','Pérola d\'Oeste','PR','Sudoeste Paranaense'),
	('4119103','Piên','PR','Metropolitana de Curitiba'),
	('4119152','Pinhais','PR','Metropolitana de Curitiba'),
	('4119202','Pinhalão','PR','Norte Pioneiro Paranaense'),
	('4119251','Pinhal de São Bento','PR','Sudoeste Paranaense'),
	('4119301','Pinhão','PR','Centro-Sul Paranaense'),
	('4119400','Piraí do Sul','PR','Centro Oriental Paranaense'),
	('4119509','Piraquara','PR','Metropolitana de Curitiba'),
	('4119608','Pitanga','PR','Centro-Sul Paranaense'),
	('4119657','Pitangueiras','PR','Norte Central Paranaense'),
	('4119707','Planaltina do Paraná','PR','Noroeste Paranaense'),
	('4119806','Planalto','PR','Sudoeste Paranaense'),
	('4119905','Ponta Grossa','PR','Centro Oriental Paranaense'),
	('4119954','Pontal do Paraná','PR','Metropolitana de Curitiba'),
	('4120002','Porecatu','PR','Norte Central Paranaense'),
	('4120101','Porto Amazonas','PR','Metropolitana de Curitiba'),
	('4120150','Porto Barreiro','PR','Centro-Sul Paranaense'),
	('4120200','Porto Rico','PR','Noroeste Paranaense'),
	('4120309','Porto Vitória','PR','Sudeste Paranaense'),
	('4120333','Prado Ferreira','PR','Norte Central Paranaense'),
	('4120358','Pranchita','PR','Sudoeste Paranaense'),
	('4120408','Presidente Castelo Branco','PR','Norte Central Paranaense'),
	('4120507','Primeiro de Maio','PR','Norte Central Paranaense'),
	('4120606','Prudentópolis','PR','Sudeste Paranaense'),
	('4120655','Quarto Centenário','PR','Centro Ocidental Paranaense'),
	('4120705','Quatiguá','PR','Norte Pioneiro Paranaense'),
	('4120804','Quatro Barras','PR','Metropolitana de Curitiba'),
	('4120853','Quatro Pontes','PR','Oeste Paranaense'),
	('4120903','Quedas do Iguaçu','PR','Centro-Sul Paranaense'),
	('4121000','Querência do Norte','PR','Noroeste Paranaense'),
	('4121109','Quinta do Sol','PR','Centro Ocidental Paranaense'),
	('4121208','Quitandinha','PR','Metropolitana de Curitiba'),
	('4121257','Ramilândia','PR','Oeste Paranaense'),
	('4121307','Rancho Alegre','PR','Norte Pioneiro Paranaense'),
	('4121356','Rancho Alegre D\'Oeste','PR','Centro Ocidental Paranaense'),
	('4121406','Realeza','PR','Sudoeste Paranaense'),
	('4121505','Rebouças','PR','Sudeste Paranaense'),
	('4121604','Renascença','PR','Sudoeste Paranaense'),
	('4121703','Reserva','PR','Centro Oriental Paranaense'),
	('4121752','Reserva do Iguaçu','PR','Centro-Sul Paranaense'),
	('4121802','Ribeirão Claro','PR','Norte Pioneiro Paranaense'),
	('4121901','Ribeirão do Pinhal','PR','Norte Pioneiro Paranaense'),
	('4122008','Rio Azul','PR','Sudeste Paranaense'),
	('4122107','Rio Bom','PR','Norte Central Paranaense'),
	('4122156','Rio Bonito do Iguaçu','PR','Centro-Sul Paranaense'),
	('4122172','Rio Branco do Ivaí','PR','Norte Central Paranaense'),
	('4122206','Rio Branco do Sul','PR','Metropolitana de Curitiba'),
	('4122305','Rio Negro','PR','Metropolitana de Curitiba'),
	('4122404','Rolândia','PR','Norte Central Paranaense'),
	('4122503','Roncador','PR','Centro Ocidental Paranaense'),
	('4122602','Rondon','PR','Noroeste Paranaense'),
	('4122651','Rosário do Ivaí','PR','Norte Central Paranaense'),
	('4122701','Sabáudia','PR','Norte Central Paranaense'),
	('4122800','Salgado Filho','PR','Sudoeste Paranaense'),
	('4122909','Salto do Itararé','PR','Norte Pioneiro Paranaense'),
	('4123006','Salto do Lontra','PR','Sudoeste Paranaense'),
	('4123105','Santa Amélia','PR','Norte Pioneiro Paranaense'),
	('4123204','Santa Cecília do Pavão','PR','Norte Pioneiro Paranaense'),
	('4123303','Santa Cruz de Monte Castelo','PR','Noroeste Paranaense'),
	('4123402','Santa Fé','PR','Norte Central Paranaense'),
	('4123501','Santa Helena','PR','Oeste Paranaense'),
	('4123600','Santa Inês','PR','Norte Central Paranaense'),
	('4123709','Santa Isabel do Ivaí','PR','Noroeste Paranaense'),
	('4123808','Santa Izabel do Oeste','PR','Sudoeste Paranaense'),
	('4123824','Santa Lúcia','PR','Oeste Paranaense'),
	('4123857','Santa Maria do Oeste','PR','Centro-Sul Paranaense'),
	('4123907','Santa Mariana','PR','Norte Pioneiro Paranaense'),
	('4123956','Santa Mônica','PR','Noroeste Paranaense'),
	('4124004','Santana do Itararé','PR','Norte Pioneiro Paranaense'),
	('4124020','Santa Tereza do Oeste','PR','Oeste Paranaense'),
	('4124053','Santa Terezinha de Itaipu','PR','Oeste Paranaense'),
	('4124103','Santo Antônio da Platina','PR','Norte Pioneiro Paranaense'),
	('4124202','Santo Antônio do Caiuá','PR','Noroeste Paranaense'),
	('4124301','Santo Antônio do Paraíso','PR','Norte Pioneiro Paranaense'),
	('4124400','Santo Antônio do Sudoeste','PR','Sudoeste Paranaense'),
	('4124509','Santo Inácio','PR','Norte Central Paranaense'),
	('4124608','São Carlos do Ivaí','PR','Noroeste Paranaense'),
	('4124707','São Jerônimo da Serra','PR','Norte Pioneiro Paranaense'),
	('4124806','São João','PR','Sudoeste Paranaense'),
	('4124905','São João do Caiuá','PR','Noroeste Paranaense'),
	('4125001','São João do Ivaí','PR','Norte Central Paranaense'),
	('4125100','São João do Triunfo','PR','Sudeste Paranaense'),
	('4125209','São Jorge d\'Oeste','PR','Sudoeste Paranaense'),
	('4125308','São Jorge do Ivaí','PR','Norte Central Paranaense'),
	('4125357','São Jorge do Patrocínio','PR','Noroeste Paranaense'),
	('4125407','São José da Boa Vista','PR','Norte Pioneiro Paranaense'),
	('4125456','São José das Palmeiras','PR','Oeste Paranaense'),
	('4125506','São José dos Pinhais','PR','Metropolitana de Curitiba'),
	('4125555','São Manoel do Paraná','PR','Noroeste Paranaense'),
	('4125605','São Mateus do Sul','PR','Sudeste Paranaense'),
	('4125704','São Miguel do Iguaçu','PR','Oeste Paranaense'),
	('4125753','São Pedro do Iguaçu','PR','Oeste Paranaense'),
	('4125803','São Pedro do Ivaí','PR','Norte Central Paranaense'),
	('4125902','São Pedro do Paraná','PR','Noroeste Paranaense'),
	('4126009','São Sebastião da Amoreira','PR','Norte Pioneiro Paranaense'),
	('4126108','São Tomé','PR','Noroeste Paranaense'),
	('4126207','Sapopema','PR','Norte Pioneiro Paranaense'),
	('4126256','Sarandi','PR','Norte Central Paranaense'),
	('4126272','Saudade do Iguaçu','PR','Sudoeste Paranaense'),
	('4126306','Sengés','PR','Centro Oriental Paranaense'),
	('4126355','Serranópolis do Iguaçu','PR','Oeste Paranaense'),
	('4126405','Sertaneja','PR','Norte Pioneiro Paranaense'),
	('4126504','Sertanópolis','PR','Norte Central Paranaense'),
	('4126603','Siqueira Campos','PR','Norte Pioneiro Paranaense'),
	('4126652','Sulina','PR','Sudoeste Paranaense'),
	('4126678','Tamarana','PR','Norte Central Paranaense'),
	('4126702','Tamboara','PR','Noroeste Paranaense'),
	('4126801','Tapejara','PR','Noroeste Paranaense'),
	('4126900','Tapira','PR','Noroeste Paranaense'),
	('4127007','Teixeira Soares','PR','Sudeste Paranaense'),
	('4127106','Telêmaco Borba','PR','Centro Oriental Paranaense'),
	('4127205','Terra Boa','PR','Centro Ocidental Paranaense'),
	('4127304','Terra Rica','PR','Noroeste Paranaense'),
	('4127403','Terra Roxa','PR','Oeste Paranaense'),
	('4127502','Tibagi','PR','Centro Oriental Paranaense'),
	('4127601','Tijucas do Sul','PR','Metropolitana de Curitiba'),
	('4127700','Toledo','PR','Oeste Paranaense'),
	('4127809','Tomazina','PR','Norte Pioneiro Paranaense'),
	('4127858','Três Barras do Paraná','PR','Oeste Paranaense'),
	('4127882','Tunas do Paraná','PR','Metropolitana de Curitiba'),
	('4127908','Tuneiras do Oeste','PR','Noroeste Paranaense'),
	('4127957','Tupãssi','PR','Oeste Paranaense'),
	('4127965','Turvo','PR','Centro-Sul Paranaense'),
	('4128005','Ubiratã','PR','Centro Ocidental Paranaense'),
	('4128104','Umuarama','PR','Noroeste Paranaense'),
	('4128203','União da Vitória','PR','Sudeste Paranaense'),
	('4128302','Uniflor','PR','Norte Central Paranaense'),
	('4128401','Uraí','PR','Norte Pioneiro Paranaense'),
	('4128500','Wenceslau Braz','PR','Norte Pioneiro Paranaense'),
	('4128534','Ventania','PR','Centro Oriental Paranaense'),
	('4128559','Vera Cruz do Oeste','PR','Oeste Paranaense'),
	('4128609','Verê','PR','Sudoeste Paranaense'),
	('4128625','Alto Paraíso','PR','Noroeste Paranaense'),
	('4128633','Doutor Ulysses','PR','Metropolitana de Curitiba'),
	('4128658','Virmond','PR','Centro-Sul Paranaense'),
	('4128708','Vitorino','PR','Sudoeste Paranaense'),
	('4128807','Xambrê','PR','Noroeste Paranaense'),
	('4200051','Abdon Batista','SC','Serrana'),
	('4200101','Abelardo Luz','SC','Oeste Catarinense'),
	('4200200','Agrolândia','SC','Vale do Itajaí'),
	('4200309','Agronômica','SC','Vale do Itajaí'),
	('4200408','Água Doce','SC','Oeste Catarinense'),
	('4200507','Águas de Chapecó','SC','Oeste Catarinense'),
	('4200556','Águas Frias','SC','Oeste Catarinense'),
	('4200606','Águas Mornas','SC','Grande Florianópolis'),
	('4200705','Alfredo Wagner','SC','Grande Florianópolis'),
	('4200754','Alto Bela Vista','SC','Oeste Catarinense'),
	('4200804','Anchieta','SC','Oeste Catarinense'),
	('4200903','Angelina','SC','Grande Florianópolis'),
	('4201000','Anita Garibaldi','SC','Serrana'),
	('4201109','Anitápolis','SC','Grande Florianópolis'),
	('4201208','Antônio Carlos','SC','Grande Florianópolis'),
	('4201257','Apiúna','SC','Vale do Itajaí'),
	('4201273','Arabutã','SC','Oeste Catarinense'),
	('4201307','Araquari','SC','Norte Catarinense'),
	('4201406','Araranguá','SC','Sul Catarinense'),
	('4201505','Armazém','SC','Sul Catarinense'),
	('4201604','Arroio Trinta','SC','Oeste Catarinense'),
	('4201653','Arvoredo','SC','Oeste Catarinense'),
	('4201703','Ascurra','SC','Vale do Itajaí'),
	('4201802','Atalanta','SC','Vale do Itajaí'),
	('4201901','Aurora','SC','Vale do Itajaí'),
	('4201950','Balneário Arroio do Silva','SC','Sul Catarinense'),
	('4202008','Balneário Camboriú','SC','Vale do Itajaí'),
	('4202057','Balneário Barra do Sul','SC','Norte Catarinense'),
	('4202073','Balneário Gaivota','SC','Sul Catarinense'),
	('4202081','Bandeirante','SC','Oeste Catarinense'),
	('4202099','Barra Bonita','SC','Oeste Catarinense'),
	('4202107','Barra Velha','SC','Vale do Itajaí'),
	('4202131','Bela Vista do Toldo','SC','Norte Catarinense'),
	('4202156','Belmonte','SC','Oeste Catarinense'),
	('4202206','Benedito Novo','SC','Vale do Itajaí'),
	('4202305','Biguaçu','SC','Grande Florianópolis'),
	('4202404','Blumenau','SC','Vale do Itajaí'),
	('4202438','Bocaina do Sul','SC','Serrana'),
	('4202453','Bombinhas','SC','Vale do Itajaí'),
	('4202503','Bom Jardim da Serra','SC','Serrana'),
	('4202537','Bom Jesus','SC','Oeste Catarinense'),
	('4202578','Bom Jesus do Oeste','SC','Oeste Catarinense'),
	('4202602','Bom Retiro','SC','Serrana'),
	('4202701','Botuverá','SC','Vale do Itajaí'),
	('4202800','Braço do Norte','SC','Sul Catarinense'),
	('4202859','Braço do Trombudo','SC','Vale do Itajaí'),
	('4202875','Brunópolis','SC','Serrana'),
	('4202909','Brusque','SC','Vale do Itajaí'),
	('4203006','Caçador','SC','Oeste Catarinense'),
	('4203105','Caibi','SC','Oeste Catarinense'),
	('4203154','Calmon','SC','Oeste Catarinense'),
	('4203204','Camboriú','SC','Vale do Itajaí'),
	('4203253','Capão Alto','SC','Serrana'),
	('4203303','Campo Alegre','SC','Norte Catarinense'),
	('4203402','Campo Belo do Sul','SC','Serrana'),
	('4203501','Campo Erê','SC','Oeste Catarinense'),
	('4203600','Campos Novos','SC','Serrana'),
	('4203709','Canelinha','SC','Grande Florianópolis'),
	('4203808','Canoinhas','SC','Norte Catarinense'),
	('4203907','Capinzal','SC','Oeste Catarinense'),
	('4203956','Capivari de Baixo','SC','Sul Catarinense'),
	('4204004','Catanduvas','SC','Oeste Catarinense'),
	('4204103','Caxambu do Sul','SC','Oeste Catarinense'),
	('4204152','Celso Ramos','SC','Serrana'),
	('4204178','Cerro Negro','SC','Serrana'),
	('4204194','Chapadão do Lageado','SC','Vale do Itajaí'),
	('4204202','Chapecó','SC','Oeste Catarinense'),
	('4204251','Cocal do Sul','SC','Sul Catarinense'),
	('4204301','Concórdia','SC','Oeste Catarinense'),
	('4204350','Cordilheira Alta','SC','Oeste Catarinense'),
	('4204400','Coronel Freitas','SC','Oeste Catarinense'),
	('4204459','Coronel Martins','SC','Oeste Catarinense'),
	('4204509','Corupá','SC','Norte Catarinense'),
	('4204558','Correia Pinto','SC','Serrana'),
	('4204608','Criciúma','SC','Sul Catarinense'),
	('4204707','Cunha Porã','SC','Oeste Catarinense'),
	('4204756','Cunhataí','SC','Oeste Catarinense'),
	('4204806','Curitibanos','SC','Serrana'),
	('4204905','Descanso','SC','Oeste Catarinense'),
	('4205001','Dionísio Cerqueira','SC','Oeste Catarinense'),
	('4205100','Dona Emma','SC','Vale do Itajaí'),
	('4205159','Doutor Pedrinho','SC','Vale do Itajaí'),
	('4205175','Entre Rios','SC','Oeste Catarinense'),
	('4205191','Ermo','SC','Sul Catarinense'),
	('4205209','Erval Velho','SC','Oeste Catarinense'),
	('4205308','Faxinal dos Guedes','SC','Oeste Catarinense'),
	('4205357','Flor do Sertão','SC','Oeste Catarinense'),
	('4205407','Florianópolis','SC','Grande Florianópolis'),
	('4205431','Formosa do Sul','SC','Oeste Catarinense'),
	('4205456','Forquilhinha','SC','Sul Catarinense'),
	('4205506','Fraiburgo','SC','Oeste Catarinense'),
	('4205555','Frei Rogério','SC','Serrana'),
	('4205605','Galvão','SC','Oeste Catarinense'),
	('4205704','Garopaba','SC','Sul Catarinense'),
	('4205803','Garuva','SC','Norte Catarinense'),
	('4205902','Gaspar','SC','Vale do Itajaí'),
	('4206009','Governador Celso Ramos','SC','Grande Florianópolis'),
	('4206108','Grão Pará','SC','Sul Catarinense'),
	('4206207','Gravatal','SC','Sul Catarinense'),
	('4206306','Guabiruba','SC','Vale do Itajaí'),
	('4206405','Guaraciaba','SC','Oeste Catarinense'),
	('4206504','Guaramirim','SC','Norte Catarinense'),
	('4206603','Guarujá do Sul','SC','Oeste Catarinense'),
	('4206652','Guatambú','SC','Oeste Catarinense'),
	('4206702','Herval d\'Oeste','SC','Oeste Catarinense'),
	('4206751','Ibiam','SC','Oeste Catarinense'),
	('4206801','Ibicaré','SC','Oeste Catarinense'),
	('4206900','Ibirama','SC','Vale do Itajaí'),
	('4207007','Içara','SC','Sul Catarinense'),
	('4207106','Ilhota','SC','Vale do Itajaí'),
	('4207205','Imaruí','SC','Sul Catarinense'),
	('4207304','Imbituba','SC','Sul Catarinense'),
	('4207403','Imbuia','SC','Vale do Itajaí'),
	('4207502','Indaial','SC','Vale do Itajaí'),
	('4207577','Iomerê','SC','Oeste Catarinense'),
	('4207601','Ipira','SC','Oeste Catarinense'),
	('4207650','Iporã do Oeste','SC','Oeste Catarinense'),
	('4207684','Ipuaçu','SC','Oeste Catarinense'),
	('4207700','Ipumirim','SC','Oeste Catarinense'),
	('4207759','Iraceminha','SC','Oeste Catarinense'),
	('4207809','Irani','SC','Oeste Catarinense'),
	('4207858','Irati','SC','Oeste Catarinense'),
	('4207908','Irineópolis','SC','Norte Catarinense'),
	('4208005','Itá','SC','Oeste Catarinense'),
	('4208104','Itaiópolis','SC','Norte Catarinense'),
	('4208203','Itajaí','SC','Vale do Itajaí'),
	('4208302','Itapema','SC','Vale do Itajaí'),
	('4208401','Itapiranga','SC','Oeste Catarinense'),
	('4208450','Itapoá','SC','Norte Catarinense'),
	('4208500','Ituporanga','SC','Vale do Itajaí'),
	('4208609','Jaborá','SC','Oeste Catarinense'),
	('4208708','Jacinto Machado','SC','Sul Catarinense'),
	('4208807','Jaguaruna','SC','Sul Catarinense'),
	('4208906','Jaraguá do Sul','SC','Norte Catarinense'),
	('4208955','Jardinópolis','SC','Oeste Catarinense'),
	('4209003','Joaçaba','SC','Oeste Catarinense'),
	('4209102','Joinville','SC','Norte Catarinense'),
	('4209151','José Boiteux','SC','Vale do Itajaí'),
	('4209177','Jupiá','SC','Oeste Catarinense'),
	('4209201','Lacerdópolis','SC','Oeste Catarinense'),
	('4209300','Lages','SC','Serrana'),
	('4209409','Laguna','SC','Sul Catarinense'),
	('4209458','Lajeado Grande','SC','Oeste Catarinense'),
	('4209508','Laurentino','SC','Vale do Itajaí'),
	('4209607','Lauro Müller','SC','Sul Catarinense'),
	('4209706','Lebon Régis','SC','Oeste Catarinense'),
	('4209805','Leoberto Leal','SC','Grande Florianópolis'),
	('4209854','Lindóia do Sul','SC','Oeste Catarinense'),
	('4209904','Lontras','SC','Vale do Itajaí'),
	('4210001','Luiz Alves','SC','Vale do Itajaí'),
	('4210035','Luzerna','SC','Oeste Catarinense'),
	('4210050','Macieira','SC','Oeste Catarinense'),
	('4210100','Mafra','SC','Norte Catarinense'),
	('4210209','Major Gercino','SC','Grande Florianópolis'),
	('4210308','Major Vieira','SC','Norte Catarinense'),
	('4210407','Maracajá','SC','Sul Catarinense'),
	('4210506','Maravilha','SC','Oeste Catarinense'),
	('4210555','Marema','SC','Oeste Catarinense'),
	('4210605','Massaranduba','SC','Norte Catarinense'),
	('4210704','Matos Costa','SC','Oeste Catarinense'),
	('4210803','Meleiro','SC','Sul Catarinense'),
	('4210852','Mirim Doce','SC','Vale do Itajaí'),
	('4210902','Modelo','SC','Oeste Catarinense'),
	('4211009','Mondaí','SC','Oeste Catarinense'),
	('4211058','Monte Carlo','SC','Serrana'),
	('4211108','Monte Castelo','SC','Norte Catarinense'),
	('4211207','Morro da Fumaça','SC','Sul Catarinense'),
	('4211256','Morro Grande','SC','Sul Catarinense'),
	('4211306','Navegantes','SC','Vale do Itajaí'),
	('4211405','Nova Erechim','SC','Oeste Catarinense'),
	('4211454','Nova Itaberaba','SC','Oeste Catarinense'),
	('4211504','Nova Trento','SC','Grande Florianópolis'),
	('4211603','Nova Veneza','SC','Sul Catarinense'),
	('4211652','Novo Horizonte','SC','Oeste Catarinense'),
	('4211702','Orleans','SC','Sul Catarinense'),
	('4211751','Otacílio Costa','SC','Serrana'),
	('4211801','Ouro','SC','Oeste Catarinense'),
	('4211850','Ouro Verde','SC','Oeste Catarinense'),
	('4211876','Paial','SC','Oeste Catarinense'),
	('4211892','Painel','SC','Serrana'),
	('4211900','Palhoça','SC','Grande Florianópolis'),
	('4212007','Palma Sola','SC','Oeste Catarinense'),
	('4212056','Palmeira','SC','Serrana'),
	('4212106','Palmitos','SC','Oeste Catarinense'),
	('4212205','Papanduva','SC','Norte Catarinense'),
	('4212239','Paraíso','SC','Oeste Catarinense'),
	('4212254','Passo de Torres','SC','Sul Catarinense'),
	('4212270','Passos Maia','SC','Oeste Catarinense'),
	('4212304','Paulo Lopes','SC','Grande Florianópolis'),
	('4212403','Pedras Grandes','SC','Sul Catarinense'),
	('4212502','Penha','SC','Vale do Itajaí'),
	('4212601','Peritiba','SC','Oeste Catarinense'),
	('4212650','Pescaria Brava','SC','Sul Catarinense'),
	('4212700','Petrolândia','SC','Vale do Itajaí'),
	('4212809','Balneário Piçarras','SC','Vale do Itajaí'),
	('4212908','Pinhalzinho','SC','Oeste Catarinense'),
	('4213005','Pinheiro Preto','SC','Oeste Catarinense'),
	('4213104','Piratuba','SC','Oeste Catarinense'),
	('4213153','Planalto Alegre','SC','Oeste Catarinense'),
	('4213203','Pomerode','SC','Vale do Itajaí'),
	('4213302','Ponte Alta','SC','Serrana'),
	('4213351','Ponte Alta do Norte','SC','Serrana'),
	('4213401','Ponte Serrada','SC','Oeste Catarinense'),
	('4213500','Porto Belo','SC','Vale do Itajaí'),
	('4213609','Porto União','SC','Norte Catarinense'),
	('4213708','Pouso Redondo','SC','Vale do Itajaí'),
	('4213807','Praia Grande','SC','Sul Catarinense'),
	('4213906','Presidente Castello Branco','SC','Oeste Catarinense'),
	('4214003','Presidente Getúlio','SC','Vale do Itajaí'),
	('4214102','Presidente Nereu','SC','Vale do Itajaí'),
	('4214151','Princesa','SC','Oeste Catarinense'),
	('4214201','Quilombo','SC','Oeste Catarinense'),
	('4214300','Rancho Queimado','SC','Grande Florianópolis'),
	('4214409','Rio das Antas','SC','Oeste Catarinense'),
	('4214508','Rio do Campo','SC','Vale do Itajaí'),
	('4214607','Rio do Oeste','SC','Vale do Itajaí'),
	('4214706','Rio dos Cedros','SC','Vale do Itajaí'),
	('4214805','Rio do Sul','SC','Vale do Itajaí'),
	('4214904','Rio Fortuna','SC','Sul Catarinense'),
	('4215000','Rio Negrinho','SC','Norte Catarinense'),
	('4215059','Rio Rufino','SC','Serrana'),
	('4215075','Riqueza','SC','Oeste Catarinense'),
	('4215109','Rodeio','SC','Vale do Itajaí'),
	('4215208','Romelândia','SC','Oeste Catarinense'),
	('4215307','Salete','SC','Vale do Itajaí'),
	('4215356','Saltinho','SC','Oeste Catarinense'),
	('4215406','Salto Veloso','SC','Oeste Catarinense'),
	('4215455','Sangão','SC','Sul Catarinense'),
	('4215505','Santa Cecília','SC','Serrana'),
	('4215554','Santa Helena','SC','Oeste Catarinense'),
	('4215604','Santa Rosa de Lima','SC','Sul Catarinense'),
	('4215653','Santa Rosa do Sul','SC','Sul Catarinense'),
	('4215679','Santa Terezinha','SC','Norte Catarinense'),
	('4215687','Santa Terezinha do Progresso','SC','Oeste Catarinense'),
	('4215695','Santiago do Sul','SC','Oeste Catarinense'),
	('4215703','Santo Amaro da Imperatriz','SC','Grande Florianópolis'),
	('4215752','São Bernardino','SC','Oeste Catarinense'),
	('4215802','São Bento do Sul','SC','Norte Catarinense'),
	('4215901','São Bonifácio','SC','Grande Florianópolis'),
	('4216008','São Carlos','SC','Oeste Catarinense'),
	('4216057','São Cristóvão do Sul','SC','Serrana'),
	('4216107','São Domingos','SC','Oeste Catarinense'),
	('4216206','São Francisco do Sul','SC','Norte Catarinense'),
	('4216255','São João do Oeste','SC','Oeste Catarinense'),
	('4216305','São João Batista','SC','Grande Florianópolis'),
	('4216354','São João do Itaperiú','SC','Vale do Itajaí'),
	('4216404','São João do Sul','SC','Sul Catarinense'),
	('4216503','São Joaquim','SC','Serrana'),
	('4216602','São José','SC','Grande Florianópolis'),
	('4216701','São José do Cedro','SC','Oeste Catarinense'),
	('4216800','São José do Cerrito','SC','Serrana'),
	('4216909','São Lourenço do Oeste','SC','Oeste Catarinense'),
	('4217006','São Ludgero','SC','Sul Catarinense'),
	('4217105','São Martinho','SC','Sul Catarinense'),
	('4217154','São Miguel da Boa Vista','SC','Oeste Catarinense'),
	('4217204','São Miguel do Oeste','SC','Oeste Catarinense'),
	('4217253','São Pedro de Alcântara','SC','Grande Florianópolis'),
	('4217303','Saudades','SC','Oeste Catarinense'),
	('4217402','Schroeder','SC','Norte Catarinense'),
	('4217501','Seara','SC','Oeste Catarinense'),
	('4217550','Serra Alta','SC','Oeste Catarinense'),
	('4217600','Siderópolis','SC','Sul Catarinense'),
	('4217709','Sombrio','SC','Sul Catarinense'),
	('4217758','Sul Brasil','SC','Oeste Catarinense'),
	('4217808','Taió','SC','Vale do Itajaí'),
	('4217907','Tangará','SC','Oeste Catarinense'),
	('4217956','Tigrinhos','SC','Oeste Catarinense'),
	('4218004','Tijucas','SC','Grande Florianópolis'),
	('4218103','Timbé do Sul','SC','Sul Catarinense'),
	('4218202','Timbó','SC','Vale do Itajaí'),
	('4218251','Timbó Grande','SC','Norte Catarinense'),
	('4218301','Três Barras','SC','Norte Catarinense'),
	('4218350','Treviso','SC','Sul Catarinense'),
	('4218400','Treze de Maio','SC','Sul Catarinense'),
	('4218509','Treze Tílias','SC','Oeste Catarinense'),
	('4218608','Trombudo Central','SC','Vale do Itajaí'),
	('4218707','Tubarão','SC','Sul Catarinense'),
	('4218756','Tunápolis','SC','Oeste Catarinense'),
	('4218806','Turvo','SC','Sul Catarinense'),
	('4218855','União do Oeste','SC','Oeste Catarinense'),
	('4218905','Urubici','SC','Serrana'),
	('4218954','Urupema','SC','Serrana'),
	('4219002','Urussanga','SC','Sul Catarinense'),
	('4219101','Vargeão','SC','Oeste Catarinense'),
	('4219150','Vargem','SC','Serrana'),
	('4219176','Vargem Bonita','SC','Oeste Catarinense'),
	('4219200','Vidal Ramos','SC','Vale do Itajaí'),
	('4219309','Videira','SC','Oeste Catarinense'),
	('4219358','Vitor Meireles','SC','Vale do Itajaí'),
	('4219408','Witmarsum','SC','Vale do Itajaí'),
	('4219507','Xanxerê','SC','Oeste Catarinense'),
	('4219606','Xavantina','SC','Oeste Catarinense'),
	('4219705','Xaxim','SC','Oeste Catarinense'),
	('4219853','Zortéa','SC','Serrana'),
	('4220000','Balneário Rincão','SC','Sul Catarinense'),
	('4300034','Aceguá','RS','Sudoeste Rio-grandense'),
	('4300059','Água Santa','RS','Noroeste Rio-grandense'),
	('4300109','Agudo','RS','Centro Ocidental Rio-grandense'),
	('4300208','Ajuricaba','RS','Noroeste Rio-grandense'),
	('4300307','Alecrim','RS','Noroeste Rio-grandense'),
	('4300406','Alegrete','RS','Sudoeste Rio-grandense'),
	('4300455','Alegria','RS','Noroeste Rio-grandense'),
	('4300471','Almirante Tamandaré do Sul','RS','Noroeste Rio-grandense'),
	('4300505','Alpestre','RS','Noroeste Rio-grandense'),
	('4300554','Alto Alegre','RS','Noroeste Rio-grandense'),
	('4300570','Alto Feliz','RS','Metropolitana de Porto Alegre'),
	('4300604','Alvorada','RS','Metropolitana de Porto Alegre'),
	('4300638','Amaral Ferrador','RS','Sudeste Rio-grandense'),
	('4300646','Ametista do Sul','RS','Noroeste Rio-grandense'),
	('4300661','André da Rocha','RS','Nordeste Rio-grandense'),
	('4300703','Anta Gorda','RS','Nordeste Rio-grandense'),
	('4300802','Antônio Prado','RS','Nordeste Rio-grandense'),
	('4300851','Arambaré','RS','Metropolitana de Porto Alegre'),
	('4300877','Araricá','RS','Metropolitana de Porto Alegre'),
	('4300901','Aratiba','RS','Noroeste Rio-grandense'),
	('4301008','Arroio do Meio','RS','Centro Oriental Rio-grandense'),
	('4301057','Arroio do Sal','RS','Metropolitana de Porto Alegre'),
	('4301073','Arroio do Padre','RS','Sudeste Rio-grandense'),
	('4301107','Arroio dos Ratos','RS','Metropolitana de Porto Alegre'),
	('4301206','Arroio do Tigre','RS','Centro Oriental Rio-grandense'),
	('4301305','Arroio Grande','RS','Sudeste Rio-grandense'),
	('4301404','Arvorezinha','RS','Nordeste Rio-grandense'),
	('4301503','Augusto Pestana','RS','Noroeste Rio-grandense'),
	('4301552','Áurea','RS','Noroeste Rio-grandense'),
	('4301602','Bagé','RS','Sudoeste Rio-grandense'),
	('4301636','Balneário Pinhal','RS','Metropolitana de Porto Alegre'),
	('4301651','Barão','RS','Metropolitana de Porto Alegre'),
	('4301701','Barão de Cotegipe','RS','Noroeste Rio-grandense'),
	('4301750','Barão do Triunfo','RS','Metropolitana de Porto Alegre'),
	('4301800','Barracão','RS','Noroeste Rio-grandense'),
	('4301859','Barra do Guarita','RS','Noroeste Rio-grandense'),
	('4301875','Barra do Quaraí','RS','Sudoeste Rio-grandense'),
	('4301909','Barra do Ribeiro','RS','Metropolitana de Porto Alegre'),
	('4301925','Barra do Rio Azul','RS','Noroeste Rio-grandense'),
	('4301958','Barra Funda','RS','Noroeste Rio-grandense'),
	('4302006','Barros Cassal','RS','Noroeste Rio-grandense'),
	('4302055','Benjamin Constant do Sul','RS','Noroeste Rio-grandense'),
	('4302105','Bento Gonçalves','RS','Nordeste Rio-grandense'),
	('4302154','Boa Vista das Missões','RS','Noroeste Rio-grandense'),
	('4302204','Boa Vista do Buricá','RS','Noroeste Rio-grandense'),
	('4302220','Boa Vista do Cadeado','RS','Noroeste Rio-grandense'),
	('4302238','Boa Vista do Incra','RS','Noroeste Rio-grandense'),
	('4302253','Boa Vista do Sul','RS','Nordeste Rio-grandense'),
	('4302303','Bom Jesus','RS','Nordeste Rio-grandense'),
	('4302352','Bom Princípio','RS','Metropolitana de Porto Alegre'),
	('4302378','Bom Progresso','RS','Noroeste Rio-grandense'),
	('4302402','Bom Retiro do Sul','RS','Centro Oriental Rio-grandense'),
	('4302451','Boqueirão do Leão','RS','Centro Oriental Rio-grandense'),
	('4302501','Bossoroca','RS','Noroeste Rio-grandense'),
	('4302584','Bozano','RS','Noroeste Rio-grandense'),
	('4302600','Braga','RS','Noroeste Rio-grandense'),
	('4302659','Brochier','RS','Metropolitana de Porto Alegre'),
	('4302709','Butiá','RS','Metropolitana de Porto Alegre'),
	('4302808','Caçapava do Sul','RS','Sudeste Rio-grandense'),
	('4302907','Cacequi','RS','Centro Ocidental Rio-grandense'),
	('4303004','Cachoeira do Sul','RS','Centro Oriental Rio-grandense'),
	('4303103','Cachoeirinha','RS','Metropolitana de Porto Alegre'),
	('4303202','Cacique Doble','RS','Noroeste Rio-grandense'),
	('4303301','Caibaté','RS','Noroeste Rio-grandense'),
	('4303400','Caiçara','RS','Noroeste Rio-grandense'),
	('4303509','Camaquã','RS','Metropolitana de Porto Alegre'),
	('4303558','Camargo','RS','Noroeste Rio-grandense'),
	('4303608','Cambará do Sul','RS','Nordeste Rio-grandense'),
	('4303673','Campestre da Serra','RS','Nordeste Rio-grandense'),
	('4303707','Campina das Missões','RS','Noroeste Rio-grandense'),
	('4303806','Campinas do Sul','RS','Noroeste Rio-grandense'),
	('4303905','Campo Bom','RS','Metropolitana de Porto Alegre'),
	('4304002','Campo Novo','RS','Noroeste Rio-grandense'),
	('4304101','Campos Borges','RS','Noroeste Rio-grandense'),
	('4304200','Candelária','RS','Centro Oriental Rio-grandense'),
	('4304309','Cândido Godói','RS','Noroeste Rio-grandense'),
	('4304358','Candiota','RS','Sudeste Rio-grandense'),
	('4304408','Canela','RS','Metropolitana de Porto Alegre'),
	('4304507','Canguçu','RS','Sudeste Rio-grandense'),
	('4304606','Canoas','RS','Metropolitana de Porto Alegre'),
	('4304614','Canudos do Vale','RS','Centro Oriental Rio-grandense'),
	('4304622','Capão Bonito do Sul','RS','Nordeste Rio-grandense'),
	('4304630','Capão da Canoa','RS','Metropolitana de Porto Alegre'),
	('4304655','Capão do Cipó','RS','Centro Ocidental Rio-grandense'),
	('4304663','Capão do Leão','RS','Sudeste Rio-grandense'),
	('4304671','Capivari do Sul','RS','Metropolitana de Porto Alegre'),
	('4304689','Capela de Santana','RS','Metropolitana de Porto Alegre'),
	('4304697','Capitão','RS','Centro Oriental Rio-grandense'),
	('4304705','Carazinho','RS','Noroeste Rio-grandense'),
	('4304713','Caraá','RS','Metropolitana de Porto Alegre'),
	('4304804','Carlos Barbosa','RS','Nordeste Rio-grandense'),
	('4304853','Carlos Gomes','RS','Noroeste Rio-grandense'),
	('4304903','Casca','RS','Noroeste Rio-grandense'),
	('4304952','Caseiros','RS','Noroeste Rio-grandense'),
	('4305009','Catuípe','RS','Noroeste Rio-grandense'),
	('4305108','Caxias do Sul','RS','Nordeste Rio-grandense'),
	('4305116','Centenário','RS','Noroeste Rio-grandense'),
	('4305124','Cerrito','RS','Sudeste Rio-grandense'),
	('4305132','Cerro Branco','RS','Centro Oriental Rio-grandense'),
	('4305157','Cerro Grande','RS','Noroeste Rio-grandense'),
	('4305173','Cerro Grande do Sul','RS','Metropolitana de Porto Alegre'),
	('4305207','Cerro Largo','RS','Noroeste Rio-grandense'),
	('4305306','Chapada','RS','Noroeste Rio-grandense'),
	('4305355','Charqueadas','RS','Metropolitana de Porto Alegre'),
	('4305371','Charrua','RS','Noroeste Rio-grandense'),
	('4305405','Chiapetta','RS','Noroeste Rio-grandense'),
	('4305439','Chuí','RS','Sudeste Rio-grandense'),
	('4305447','Chuvisca','RS','Metropolitana de Porto Alegre'),
	('4305454','Cidreira','RS','Metropolitana de Porto Alegre'),
	('4305504','Ciríaco','RS','Noroeste Rio-grandense'),
	('4305587','Colinas','RS','Centro Oriental Rio-grandense'),
	('4305603','Colorado','RS','Noroeste Rio-grandense'),
	('4305702','Condor','RS','Noroeste Rio-grandense'),
	('4305801','Constantina','RS','Noroeste Rio-grandense');

INSERT INTO `municipio` (`codigoIbge`, `nome`, `uf`, `nomeRegiao`)
VALUES
	('4305835','Coqueiro Baixo','RS','Centro Oriental Rio-grandense'),
	('4305850','Coqueiros do Sul','RS','Noroeste Rio-grandense'),
	('4305871','Coronel Barros','RS','Noroeste Rio-grandense'),
	('4305900','Coronel Bicaco','RS','Noroeste Rio-grandense'),
	('4305934','Coronel Pilar','RS','Nordeste Rio-grandense'),
	('4305959','Cotiporã','RS','Nordeste Rio-grandense'),
	('4305975','Coxilha','RS','Noroeste Rio-grandense'),
	('4306007','Crissiumal','RS','Noroeste Rio-grandense'),
	('4306056','Cristal','RS','Sudeste Rio-grandense'),
	('4306072','Cristal do Sul','RS','Noroeste Rio-grandense'),
	('4306106','Cruz Alta','RS','Noroeste Rio-grandense'),
	('4306130','Cruzaltense','RS','Noroeste Rio-grandense'),
	('4306205','Cruzeiro do Sul','RS','Centro Oriental Rio-grandense'),
	('4306304','David Canabarro','RS','Noroeste Rio-grandense'),
	('4306320','Derrubadas','RS','Noroeste Rio-grandense'),
	('4306353','Dezesseis de Novembro','RS','Noroeste Rio-grandense'),
	('4306379','Dilermando de Aguiar','RS','Centro Ocidental Rio-grandense'),
	('4306403','Dois Irmãos','RS','Metropolitana de Porto Alegre'),
	('4306429','Dois Irmãos das Missões','RS','Noroeste Rio-grandense'),
	('4306452','Dois Lajeados','RS','Nordeste Rio-grandense'),
	('4306502','Dom Feliciano','RS','Metropolitana de Porto Alegre'),
	('4306551','Dom Pedro de Alcântara','RS','Metropolitana de Porto Alegre'),
	('4306601','Dom Pedrito','RS','Sudoeste Rio-grandense'),
	('4306700','Dona Francisca','RS','Centro Ocidental Rio-grandense'),
	('4306734','Doutor Maurício Cardoso','RS','Noroeste Rio-grandense'),
	('4306759','Doutor Ricardo','RS','Centro Oriental Rio-grandense'),
	('4306767','Eldorado do Sul','RS','Metropolitana de Porto Alegre'),
	('4306809','Encantado','RS','Centro Oriental Rio-grandense'),
	('4306908','Encruzilhada do Sul','RS','Sudeste Rio-grandense'),
	('4306924','Engenho Velho','RS','Noroeste Rio-grandense'),
	('4306932','Entre-Ijuís','RS','Noroeste Rio-grandense'),
	('4306957','Entre Rios do Sul','RS','Noroeste Rio-grandense'),
	('4306973','Erebango','RS','Noroeste Rio-grandense'),
	('4307005','Erechim','RS','Noroeste Rio-grandense'),
	('4307054','Ernestina','RS','Noroeste Rio-grandense'),
	('4307104','Herval','RS','Sudeste Rio-grandense'),
	('4307203','Erval Grande','RS','Noroeste Rio-grandense'),
	('4307302','Erval Seco','RS','Noroeste Rio-grandense'),
	('4307401','Esmeralda','RS','Nordeste Rio-grandense'),
	('4307450','Esperança do Sul','RS','Noroeste Rio-grandense'),
	('4307500','Espumoso','RS','Noroeste Rio-grandense'),
	('4307559','Estação','RS','Noroeste Rio-grandense'),
	('4307609','Estância Velha','RS','Metropolitana de Porto Alegre'),
	('4307708','Esteio','RS','Metropolitana de Porto Alegre'),
	('4307807','Estrela','RS','Centro Oriental Rio-grandense'),
	('4307815','Estrela Velha','RS','Centro Oriental Rio-grandense'),
	('4307831','Eugênio de Castro','RS','Noroeste Rio-grandense'),
	('4307864','Fagundes Varela','RS','Nordeste Rio-grandense'),
	('4307906','Farroupilha','RS','Nordeste Rio-grandense'),
	('4308003','Faxinal do Soturno','RS','Centro Ocidental Rio-grandense'),
	('4308052','Faxinalzinho','RS','Noroeste Rio-grandense'),
	('4308078','Fazenda Vilanova','RS','Centro Oriental Rio-grandense'),
	('4308102','Feliz','RS','Metropolitana de Porto Alegre'),
	('4308201','Flores da Cunha','RS','Nordeste Rio-grandense'),
	('4308250','Floriano Peixoto','RS','Noroeste Rio-grandense'),
	('4308300','Fontoura Xavier','RS','Noroeste Rio-grandense'),
	('4308409','Formigueiro','RS','Centro Ocidental Rio-grandense'),
	('4308433','Forquetinha','RS','Centro Oriental Rio-grandense'),
	('4308458','Fortaleza dos Valos','RS','Noroeste Rio-grandense'),
	('4308508','Frederico Westphalen','RS','Noroeste Rio-grandense'),
	('4308607','Garibaldi','RS','Nordeste Rio-grandense'),
	('4308656','Garruchos','RS','Sudoeste Rio-grandense'),
	('4308706','Gaurama','RS','Noroeste Rio-grandense'),
	('4308805','General Câmara','RS','Metropolitana de Porto Alegre'),
	('4308854','Gentil','RS','Noroeste Rio-grandense'),
	('4308904','Getúlio Vargas','RS','Noroeste Rio-grandense'),
	('4309001','Giruá','RS','Noroeste Rio-grandense'),
	('4309050','Glorinha','RS','Metropolitana de Porto Alegre'),
	('4309100','Gramado','RS','Metropolitana de Porto Alegre'),
	('4309126','Gramado dos Loureiros','RS','Noroeste Rio-grandense'),
	('4309159','Gramado Xavier','RS','Centro Oriental Rio-grandense'),
	('4309209','Gravataí','RS','Metropolitana de Porto Alegre'),
	('4309258','Guabiju','RS','Nordeste Rio-grandense'),
	('4309308','Guaíba','RS','Metropolitana de Porto Alegre'),
	('4309407','Guaporé','RS','Nordeste Rio-grandense'),
	('4309506','Guarani das Missões','RS','Noroeste Rio-grandense'),
	('4309555','Harmonia','RS','Metropolitana de Porto Alegre'),
	('4309571','Herveiras','RS','Centro Oriental Rio-grandense'),
	('4309605','Horizontina','RS','Noroeste Rio-grandense'),
	('4309654','Hulha Negra','RS','Sudoeste Rio-grandense'),
	('4309704','Humaitá','RS','Noroeste Rio-grandense'),
	('4309753','Ibarama','RS','Centro Oriental Rio-grandense'),
	('4309803','Ibiaçá','RS','Noroeste Rio-grandense'),
	('4309902','Ibiraiaras','RS','Noroeste Rio-grandense'),
	('4309951','Ibirapuitã','RS','Noroeste Rio-grandense'),
	('4310009','Ibirubá','RS','Noroeste Rio-grandense'),
	('4310108','Igrejinha','RS','Metropolitana de Porto Alegre'),
	('4310207','Ijuí','RS','Noroeste Rio-grandense'),
	('4310306','Ilópolis','RS','Nordeste Rio-grandense'),
	('4310330','Imbé','RS','Metropolitana de Porto Alegre'),
	('4310363','Imigrante','RS','Centro Oriental Rio-grandense'),
	('4310405','Independência','RS','Noroeste Rio-grandense'),
	('4310413','Inhacorá','RS','Noroeste Rio-grandense'),
	('4310439','Ipê','RS','Nordeste Rio-grandense'),
	('4310462','Ipiranga do Sul','RS','Noroeste Rio-grandense'),
	('4310504','Iraí','RS','Noroeste Rio-grandense'),
	('4310538','Itaara','RS','Centro Ocidental Rio-grandense'),
	('4310553','Itacurubi','RS','Centro Ocidental Rio-grandense'),
	('4310579','Itapuca','RS','Nordeste Rio-grandense'),
	('4310603','Itaqui','RS','Sudoeste Rio-grandense'),
	('4310652','Itati','RS','Metropolitana de Porto Alegre'),
	('4310702','Itatiba do Sul','RS','Noroeste Rio-grandense'),
	('4310751','Ivorá','RS','Centro Ocidental Rio-grandense'),
	('4310801','Ivoti','RS','Metropolitana de Porto Alegre'),
	('4310850','Jaboticaba','RS','Noroeste Rio-grandense'),
	('4310876','Jacuizinho','RS','Noroeste Rio-grandense'),
	('4310900','Jacutinga','RS','Noroeste Rio-grandense'),
	('4311007','Jaguarão','RS','Sudeste Rio-grandense'),
	('4311106','Jaguari','RS','Centro Ocidental Rio-grandense'),
	('4311122','Jaquirana','RS','Nordeste Rio-grandense'),
	('4311130','Jari','RS','Centro Ocidental Rio-grandense'),
	('4311155','Jóia','RS','Noroeste Rio-grandense'),
	('4311205','Júlio de Castilhos','RS','Centro Ocidental Rio-grandense'),
	('4311239','Lagoa Bonita do Sul','RS','Centro Oriental Rio-grandense'),
	('4311254','Lagoão','RS','Noroeste Rio-grandense'),
	('4311270','Lagoa dos Três Cantos','RS','Noroeste Rio-grandense'),
	('4311304','Lagoa Vermelha','RS','Nordeste Rio-grandense'),
	('4311403','Lajeado','RS','Centro Oriental Rio-grandense'),
	('4311429','Lajeado do Bugre','RS','Noroeste Rio-grandense'),
	('4311502','Lavras do Sul','RS','Sudoeste Rio-grandense'),
	('4311601','Liberato Salzano','RS','Noroeste Rio-grandense'),
	('4311627','Lindolfo Collor','RS','Metropolitana de Porto Alegre'),
	('4311643','Linha Nova','RS','Metropolitana de Porto Alegre'),
	('4311700','Machadinho','RS','Noroeste Rio-grandense'),
	('4311718','Maçambará','RS','Sudoeste Rio-grandense'),
	('4311734','Mampituba','RS','Metropolitana de Porto Alegre'),
	('4311759','Manoel Viana','RS','Sudoeste Rio-grandense'),
	('4311775','Maquiné','RS','Metropolitana de Porto Alegre'),
	('4311791','Maratá','RS','Metropolitana de Porto Alegre'),
	('4311809','Marau','RS','Noroeste Rio-grandense'),
	('4311908','Marcelino Ramos','RS','Noroeste Rio-grandense'),
	('4311981','Mariana Pimentel','RS','Metropolitana de Porto Alegre'),
	('4312005','Mariano Moro','RS','Noroeste Rio-grandense'),
	('4312054','Marques de Souza','RS','Centro Oriental Rio-grandense'),
	('4312104','Mata','RS','Centro Ocidental Rio-grandense'),
	('4312138','Mato Castelhano','RS','Noroeste Rio-grandense'),
	('4312153','Mato Leitão','RS','Centro Oriental Rio-grandense'),
	('4312179','Mato Queimado','RS','Noroeste Rio-grandense'),
	('4312203','Maximiliano de Almeida','RS','Noroeste Rio-grandense'),
	('4312252','Minas do Leão','RS','Metropolitana de Porto Alegre'),
	('4312302','Miraguaí','RS','Noroeste Rio-grandense'),
	('4312351','Montauri','RS','Nordeste Rio-grandense'),
	('4312377','Monte Alegre dos Campos','RS','Nordeste Rio-grandense'),
	('4312385','Monte Belo do Sul','RS','Nordeste Rio-grandense'),
	('4312401','Montenegro','RS','Metropolitana de Porto Alegre'),
	('4312427','Mormaço','RS','Noroeste Rio-grandense'),
	('4312443','Morrinhos do Sul','RS','Metropolitana de Porto Alegre'),
	('4312450','Morro Redondo','RS','Sudeste Rio-grandense'),
	('4312476','Morro Reuter','RS','Metropolitana de Porto Alegre'),
	('4312500','Mostardas','RS','Metropolitana de Porto Alegre'),
	('4312609','Muçum','RS','Centro Oriental Rio-grandense'),
	('4312617','Muitos Capões','RS','Nordeste Rio-grandense'),
	('4312625','Muliterno','RS','Noroeste Rio-grandense'),
	('4312658','Não-Me-Toque','RS','Noroeste Rio-grandense'),
	('4312674','Nicolau Vergueiro','RS','Noroeste Rio-grandense'),
	('4312708','Nonoai','RS','Noroeste Rio-grandense'),
	('4312757','Nova Alvorada','RS','Nordeste Rio-grandense'),
	('4312807','Nova Araçá','RS','Nordeste Rio-grandense'),
	('4312906','Nova Bassano','RS','Nordeste Rio-grandense'),
	('4312955','Nova Boa Vista','RS','Noroeste Rio-grandense'),
	('4313003','Nova Bréscia','RS','Centro Oriental Rio-grandense'),
	('4313011','Nova Candelária','RS','Noroeste Rio-grandense'),
	('4313037','Nova Esperança do Sul','RS','Centro Ocidental Rio-grandense'),
	('4313060','Nova Hartz','RS','Metropolitana de Porto Alegre'),
	('4313086','Nova Pádua','RS','Nordeste Rio-grandense'),
	('4313102','Nova Palma','RS','Centro Ocidental Rio-grandense'),
	('4313201','Nova Petrópolis','RS','Metropolitana de Porto Alegre'),
	('4313300','Nova Prata','RS','Nordeste Rio-grandense'),
	('4313334','Nova Ramada','RS','Noroeste Rio-grandense'),
	('4313359','Nova Roma do Sul','RS','Nordeste Rio-grandense'),
	('4313375','Nova Santa Rita','RS','Metropolitana de Porto Alegre'),
	('4313391','Novo Cabrais','RS','Centro Oriental Rio-grandense'),
	('4313409','Novo Hamburgo','RS','Metropolitana de Porto Alegre'),
	('4313425','Novo Machado','RS','Noroeste Rio-grandense'),
	('4313441','Novo Tiradentes','RS','Noroeste Rio-grandense'),
	('4313466','Novo Xingu','RS','Noroeste Rio-grandense'),
	('4313490','Novo Barreiro','RS','Noroeste Rio-grandense'),
	('4313508','Osório','RS','Metropolitana de Porto Alegre'),
	('4313607','Paim Filho','RS','Noroeste Rio-grandense'),
	('4313656','Palmares do Sul','RS','Metropolitana de Porto Alegre'),
	('4313706','Palmeira das Missões','RS','Noroeste Rio-grandense'),
	('4313805','Palmitinho','RS','Noroeste Rio-grandense'),
	('4313904','Panambi','RS','Noroeste Rio-grandense'),
	('4313953','Pantano Grande','RS','Centro Oriental Rio-grandense'),
	('4314001','Paraí','RS','Nordeste Rio-grandense'),
	('4314027','Paraíso do Sul','RS','Centro Oriental Rio-grandense'),
	('4314035','Pareci Novo','RS','Metropolitana de Porto Alegre'),
	('4314050','Parobé','RS','Metropolitana de Porto Alegre'),
	('4314068','Passa Sete','RS','Centro Oriental Rio-grandense'),
	('4314076','Passo do Sobrado','RS','Centro Oriental Rio-grandense'),
	('4314100','Passo Fundo','RS','Noroeste Rio-grandense'),
	('4314134','Paulo Bento','RS','Noroeste Rio-grandense'),
	('4314159','Paverama','RS','Centro Oriental Rio-grandense'),
	('4314175','Pedras Altas','RS','Sudeste Rio-grandense'),
	('4314209','Pedro Osório','RS','Sudeste Rio-grandense'),
	('4314308','Pejuçara','RS','Noroeste Rio-grandense'),
	('4314407','Pelotas','RS','Sudeste Rio-grandense'),
	('4314423','Picada Café','RS','Metropolitana de Porto Alegre'),
	('4314456','Pinhal','RS','Noroeste Rio-grandense'),
	('4314464','Pinhal da Serra','RS','Nordeste Rio-grandense'),
	('4314472','Pinhal Grande','RS','Centro Ocidental Rio-grandense'),
	('4314498','Pinheirinho do Vale','RS','Noroeste Rio-grandense'),
	('4314506','Pinheiro Machado','RS','Sudeste Rio-grandense'),
	('4314548','Pinto Bandeira','RS','Nordeste Rio-grandense'),
	('4314555','Pirapó','RS','Noroeste Rio-grandense'),
	('4314605','Piratini','RS','Sudeste Rio-grandense'),
	('4314704','Planalto','RS','Noroeste Rio-grandense'),
	('4314753','Poço das Antas','RS','Metropolitana de Porto Alegre'),
	('4314779','Pontão','RS','Noroeste Rio-grandense'),
	('4314787','Ponte Preta','RS','Noroeste Rio-grandense'),
	('4314803','Portão','RS','Metropolitana de Porto Alegre'),
	('4314902','Porto Alegre','RS','Metropolitana de Porto Alegre'),
	('4315008','Porto Lucena','RS','Noroeste Rio-grandense'),
	('4315057','Porto Mauá','RS','Noroeste Rio-grandense'),
	('4315073','Porto Vera Cruz','RS','Noroeste Rio-grandense'),
	('4315107','Porto Xavier','RS','Noroeste Rio-grandense'),
	('4315131','Pouso Novo','RS','Centro Oriental Rio-grandense'),
	('4315149','Presidente Lucena','RS','Metropolitana de Porto Alegre'),
	('4315156','Progresso','RS','Centro Oriental Rio-grandense'),
	('4315172','Protásio Alves','RS','Nordeste Rio-grandense'),
	('4315206','Putinga','RS','Nordeste Rio-grandense'),
	('4315305','Quaraí','RS','Sudoeste Rio-grandense'),
	('4315313','Quatro Irmãos','RS','Noroeste Rio-grandense'),
	('4315321','Quevedos','RS','Centro Ocidental Rio-grandense'),
	('4315354','Quinze de Novembro','RS','Noroeste Rio-grandense'),
	('4315404','Redentora','RS','Noroeste Rio-grandense'),
	('4315453','Relvado','RS','Centro Oriental Rio-grandense'),
	('4315503','Restinga Sêca','RS','Centro Ocidental Rio-grandense'),
	('4315552','Rio dos Índios','RS','Noroeste Rio-grandense'),
	('4315602','Rio Grande','RS','Sudeste Rio-grandense'),
	('4315701','Rio Pardo','RS','Centro Oriental Rio-grandense'),
	('4315750','Riozinho','RS','Metropolitana de Porto Alegre'),
	('4315800','Roca Sales','RS','Centro Oriental Rio-grandense'),
	('4315909','Rodeio Bonito','RS','Noroeste Rio-grandense'),
	('4315958','Rolador','RS','Noroeste Rio-grandense'),
	('4316006','Rolante','RS','Metropolitana de Porto Alegre'),
	('4316105','Ronda Alta','RS','Noroeste Rio-grandense'),
	('4316204','Rondinha','RS','Noroeste Rio-grandense'),
	('4316303','Roque Gonzales','RS','Noroeste Rio-grandense'),
	('4316402','Rosário do Sul','RS','Sudoeste Rio-grandense'),
	('4316428','Sagrada Família','RS','Noroeste Rio-grandense'),
	('4316436','Saldanha Marinho','RS','Noroeste Rio-grandense'),
	('4316451','Salto do Jacuí','RS','Noroeste Rio-grandense'),
	('4316477','Salvador das Missões','RS','Noroeste Rio-grandense'),
	('4316501','Salvador do Sul','RS','Metropolitana de Porto Alegre'),
	('4316600','Sananduva','RS','Noroeste Rio-grandense'),
	('4316709','Santa Bárbara do Sul','RS','Noroeste Rio-grandense'),
	('4316733','Santa Cecília do Sul','RS','Noroeste Rio-grandense'),
	('4316758','Santa Clara do Sul','RS','Centro Oriental Rio-grandense'),
	('4316808','Santa Cruz do Sul','RS','Centro Oriental Rio-grandense'),
	('4316907','Santa Maria','RS','Centro Ocidental Rio-grandense'),
	('4316956','Santa Maria do Herval','RS','Metropolitana de Porto Alegre'),
	('4316972','Santa Margarida do Sul','RS','Sudoeste Rio-grandense'),
	('4317004','Santana da Boa Vista','RS','Sudeste Rio-grandense'),
	('4317103','Sant\'Ana do Livramento','RS','Sudoeste Rio-grandense'),
	('4317202','Santa Rosa','RS','Noroeste Rio-grandense'),
	('4317251','Santa Tereza','RS','Nordeste Rio-grandense'),
	('4317301','Santa Vitória do Palmar','RS','Sudeste Rio-grandense'),
	('4317400','Santiago','RS','Centro Ocidental Rio-grandense'),
	('4317509','Santo Ângelo','RS','Noroeste Rio-grandense'),
	('4317558','Santo Antônio do Palma','RS','Noroeste Rio-grandense'),
	('4317608','Santo Antônio da Patrulha','RS','Metropolitana de Porto Alegre'),
	('4317707','Santo Antônio das Missões','RS','Noroeste Rio-grandense'),
	('4317756','Santo Antônio do Planalto','RS','Noroeste Rio-grandense'),
	('4317806','Santo Augusto','RS','Noroeste Rio-grandense'),
	('4317905','Santo Cristo','RS','Noroeste Rio-grandense'),
	('4317954','Santo Expedito do Sul','RS','Noroeste Rio-grandense'),
	('4318002','São Borja','RS','Sudoeste Rio-grandense'),
	('4318051','São Domingos do Sul','RS','Noroeste Rio-grandense'),
	('4318101','São Francisco de Assis','RS','Sudoeste Rio-grandense'),
	('4318200','São Francisco de Paula','RS','Nordeste Rio-grandense'),
	('4318309','São Gabriel','RS','Sudoeste Rio-grandense'),
	('4318408','São Jerônimo','RS','Metropolitana de Porto Alegre'),
	('4318424','São João da Urtiga','RS','Noroeste Rio-grandense'),
	('4318432','São João do Polêsine','RS','Centro Ocidental Rio-grandense'),
	('4318440','São Jorge','RS','Nordeste Rio-grandense'),
	('4318457','São José das Missões','RS','Noroeste Rio-grandense'),
	('4318465','São José do Herval','RS','Noroeste Rio-grandense'),
	('4318481','São José do Hortêncio','RS','Metropolitana de Porto Alegre'),
	('4318499','São José do Inhacorá','RS','Noroeste Rio-grandense'),
	('4318507','São José do Norte','RS','Sudeste Rio-grandense'),
	('4318606','São José do Ouro','RS','Noroeste Rio-grandense'),
	('4318614','São José do Sul','RS','Metropolitana de Porto Alegre'),
	('4318622','São José dos Ausentes','RS','Nordeste Rio-grandense'),
	('4318705','São Leopoldo','RS','Metropolitana de Porto Alegre'),
	('4318804','São Lourenço do Sul','RS','Sudeste Rio-grandense'),
	('4318903','São Luiz Gonzaga','RS','Noroeste Rio-grandense'),
	('4319000','São Marcos','RS','Nordeste Rio-grandense'),
	('4319109','São Martinho','RS','Noroeste Rio-grandense'),
	('4319125','São Martinho da Serra','RS','Centro Ocidental Rio-grandense'),
	('4319158','São Miguel das Missões','RS','Noroeste Rio-grandense'),
	('4319208','São Nicolau','RS','Noroeste Rio-grandense'),
	('4319307','São Paulo das Missões','RS','Noroeste Rio-grandense'),
	('4319356','São Pedro da Serra','RS','Metropolitana de Porto Alegre'),
	('4319364','São Pedro das Missões','RS','Noroeste Rio-grandense'),
	('4319372','São Pedro do Butiá','RS','Noroeste Rio-grandense'),
	('4319406','São Pedro do Sul','RS','Centro Ocidental Rio-grandense'),
	('4319505','São Sebastião do Caí','RS','Metropolitana de Porto Alegre'),
	('4319604','São Sepé','RS','Centro Ocidental Rio-grandense'),
	('4319703','São Valentim','RS','Noroeste Rio-grandense'),
	('4319711','São Valentim do Sul','RS','Nordeste Rio-grandense'),
	('4319737','São Valério do Sul','RS','Noroeste Rio-grandense'),
	('4319752','São Vendelino','RS','Metropolitana de Porto Alegre'),
	('4319802','São Vicente do Sul','RS','Centro Ocidental Rio-grandense'),
	('4319901','Sapiranga','RS','Metropolitana de Porto Alegre'),
	('4320008','Sapucaia do Sul','RS','Metropolitana de Porto Alegre'),
	('4320107','Sarandi','RS','Noroeste Rio-grandense'),
	('4320206','Seberi','RS','Noroeste Rio-grandense'),
	('4320230','Sede Nova','RS','Noroeste Rio-grandense'),
	('4320263','Segredo','RS','Centro Oriental Rio-grandense'),
	('4320305','Selbach','RS','Noroeste Rio-grandense'),
	('4320321','Senador Salgado Filho','RS','Noroeste Rio-grandense'),
	('4320354','Sentinela do Sul','RS','Metropolitana de Porto Alegre'),
	('4320404','Serafina Corrêa','RS','Nordeste Rio-grandense'),
	('4320453','Sério','RS','Centro Oriental Rio-grandense'),
	('4320503','Sertão','RS','Noroeste Rio-grandense'),
	('4320552','Sertão Santana','RS','Metropolitana de Porto Alegre'),
	('4320578','Sete de Setembro','RS','Noroeste Rio-grandense'),
	('4320602','Severiano de Almeida','RS','Noroeste Rio-grandense'),
	('4320651','Silveira Martins','RS','Centro Ocidental Rio-grandense'),
	('4320677','Sinimbu','RS','Centro Oriental Rio-grandense'),
	('4320701','Sobradinho','RS','Centro Oriental Rio-grandense'),
	('4320800','Soledade','RS','Noroeste Rio-grandense'),
	('4320859','Tabaí','RS','Centro Oriental Rio-grandense'),
	('4320909','Tapejara','RS','Noroeste Rio-grandense'),
	('4321006','Tapera','RS','Noroeste Rio-grandense'),
	('4321105','Tapes','RS','Metropolitana de Porto Alegre'),
	('4321204','Taquara','RS','Metropolitana de Porto Alegre'),
	('4321303','Taquari','RS','Centro Oriental Rio-grandense'),
	('4321329','Taquaruçu do Sul','RS','Noroeste Rio-grandense'),
	('4321352','Tavares','RS','Metropolitana de Porto Alegre'),
	('4321402','Tenente Portela','RS','Noroeste Rio-grandense'),
	('4321436','Terra de Areia','RS','Metropolitana de Porto Alegre'),
	('4321451','Teutônia','RS','Centro Oriental Rio-grandense'),
	('4321469','Tio Hugo','RS','Noroeste Rio-grandense'),
	('4321477','Tiradentes do Sul','RS','Noroeste Rio-grandense'),
	('4321493','Toropi','RS','Centro Ocidental Rio-grandense'),
	('4321501','Torres','RS','Metropolitana de Porto Alegre'),
	('4321600','Tramandaí','RS','Metropolitana de Porto Alegre'),
	('4321626','Travesseiro','RS','Centro Oriental Rio-grandense'),
	('4321634','Três Arroios','RS','Noroeste Rio-grandense'),
	('4321667','Três Cachoeiras','RS','Metropolitana de Porto Alegre'),
	('4321709','Três Coroas','RS','Metropolitana de Porto Alegre'),
	('4321808','Três de Maio','RS','Noroeste Rio-grandense'),
	('4321832','Três Forquilhas','RS','Metropolitana de Porto Alegre'),
	('4321857','Três Palmeiras','RS','Noroeste Rio-grandense'),
	('4321907','Três Passos','RS','Noroeste Rio-grandense'),
	('4321956','Trindade do Sul','RS','Noroeste Rio-grandense'),
	('4322004','Triunfo','RS','Metropolitana de Porto Alegre'),
	('4322103','Tucunduva','RS','Noroeste Rio-grandense'),
	('4322152','Tunas','RS','Noroeste Rio-grandense'),
	('4322186','Tupanci do Sul','RS','Noroeste Rio-grandense'),
	('4322202','Tupanciretã','RS','Centro Ocidental Rio-grandense'),
	('4322251','Tupandi','RS','Metropolitana de Porto Alegre'),
	('4322301','Tuparendi','RS','Noroeste Rio-grandense'),
	('4322327','Turuçu','RS','Sudeste Rio-grandense'),
	('4322343','Ubiretama','RS','Noroeste Rio-grandense'),
	('4322350','União da Serra','RS','Nordeste Rio-grandense'),
	('4322376','Unistalda','RS','Centro Ocidental Rio-grandense'),
	('4322400','Uruguaiana','RS','Sudoeste Rio-grandense'),
	('4322509','Vacaria','RS','Nordeste Rio-grandense'),
	('4322525','Vale Verde','RS','Metropolitana de Porto Alegre'),
	('4322533','Vale do Sol','RS','Centro Oriental Rio-grandense'),
	('4322541','Vale Real','RS','Metropolitana de Porto Alegre'),
	('4322558','Vanini','RS','Noroeste Rio-grandense'),
	('4322608','Venâncio Aires','RS','Centro Oriental Rio-grandense'),
	('4322707','Vera Cruz','RS','Centro Oriental Rio-grandense'),
	('4322806','Veranópolis','RS','Nordeste Rio-grandense'),
	('4322855','Vespasiano Corrêa','RS','Centro Oriental Rio-grandense'),
	('4322905','Viadutos','RS','Noroeste Rio-grandense'),
	('4323002','Viamão','RS','Metropolitana de Porto Alegre'),
	('4323101','Vicente Dutra','RS','Noroeste Rio-grandense'),
	('4323200','Victor Graeff','RS','Noroeste Rio-grandense'),
	('4323309','Vila Flores','RS','Nordeste Rio-grandense'),
	('4323358','Vila Lângaro','RS','Noroeste Rio-grandense'),
	('4323408','Vila Maria','RS','Noroeste Rio-grandense'),
	('4323457','Vila Nova do Sul','RS','Centro Ocidental Rio-grandense'),
	('4323507','Vista Alegre','RS','Noroeste Rio-grandense'),
	('4323606','Vista Alegre do Prata','RS','Nordeste Rio-grandense'),
	('4323705','Vista Gaúcha','RS','Noroeste Rio-grandense'),
	('4323754','Vitória das Missões','RS','Noroeste Rio-grandense'),
	('4323770','Westfália','RS','Centro Oriental Rio-grandense'),
	('4323804','Xangri-lá','RS','Metropolitana de Porto Alegre'),
	('5000203','Água Clara','MS','Leste de Mato Grosso do Sul'),
	('5000252','Alcinópolis','MS','Centro Norte de Mato Grosso do Sul'),
	('5000609','Amambai','MS','Sudoeste de Mato Grosso do Sul'),
	('5000708','Anastácio','MS','Pantanais Sul Mato-grossense'),
	('5000807','Anaurilândia','MS','Leste de Mato Grosso do Sul'),
	('5000856','Angélica','MS','Sudoeste de Mato Grosso do Sul'),
	('5000906','Antônio João','MS','Sudoeste de Mato Grosso do Sul'),
	('5001003','Aparecida do Taboado','MS','Leste de Mato Grosso do Sul'),
	('5001102','Aquidauana','MS','Pantanais Sul Mato-grossense'),
	('5001243','Aral Moreira','MS','Sudoeste de Mato Grosso do Sul'),
	('5001508','Bandeirantes','MS','Centro Norte de Mato Grosso do Sul'),
	('5001904','Bataguassu','MS','Leste de Mato Grosso do Sul'),
	('5002001','Batayporã','MS','Leste de Mato Grosso do Sul'),
	('5002100','Bela Vista','MS','Sudoeste de Mato Grosso do Sul'),
	('5002159','Bodoquena','MS','Sudoeste de Mato Grosso do Sul'),
	('5002209','Bonito','MS','Sudoeste de Mato Grosso do Sul'),
	('5002308','Brasilândia','MS','Leste de Mato Grosso do Sul'),
	('5002407','Caarapó','MS','Sudoeste de Mato Grosso do Sul'),
	('5002605','Camapuã','MS','Centro Norte de Mato Grosso do Sul'),
	('5002704','Campo Grande','MS','Centro Norte de Mato Grosso do Sul'),
	('5002803','Caracol','MS','Sudoeste de Mato Grosso do Sul'),
	('5002902','Cassilândia','MS','Leste de Mato Grosso do Sul'),
	('5002951','Chapadão do Sul','MS','Leste de Mato Grosso do Sul'),
	('5003108','Corguinho','MS','Centro Norte de Mato Grosso do Sul'),
	('5003157','Coronel Sapucaia','MS','Sudoeste de Mato Grosso do Sul'),
	('5003207','Corumbá','MS','Pantanais Sul Mato-grossense'),
	('5003256','Costa Rica','MS','Leste de Mato Grosso do Sul'),
	('5003306','Coxim','MS','Centro Norte de Mato Grosso do Sul'),
	('5003454','Deodápolis','MS','Sudoeste de Mato Grosso do Sul'),
	('5003488','Dois Irmãos do Buriti','MS','Pantanais Sul Mato-grossense'),
	('5003504','Douradina','MS','Sudoeste de Mato Grosso do Sul'),
	('5003702','Dourados','MS','Sudoeste de Mato Grosso do Sul'),
	('5003751','Eldorado','MS','Sudoeste de Mato Grosso do Sul'),
	('5003801','Fátima do Sul','MS','Sudoeste de Mato Grosso do Sul'),
	('5003900','Figueirão','MS','Centro Norte de Mato Grosso do Sul'),
	('5004007','Glória de Dourados','MS','Sudoeste de Mato Grosso do Sul'),
	('5004106','Guia Lopes da Laguna','MS','Sudoeste de Mato Grosso do Sul'),
	('5004304','Iguatemi','MS','Sudoeste de Mato Grosso do Sul'),
	('5004403','Inocência','MS','Leste de Mato Grosso do Sul'),
	('5004502','Itaporã','MS','Sudoeste de Mato Grosso do Sul'),
	('5004601','Itaquiraí','MS','Sudoeste de Mato Grosso do Sul'),
	('5004700','Ivinhema','MS','Sudoeste de Mato Grosso do Sul'),
	('5004809','Japorã','MS','Sudoeste de Mato Grosso do Sul'),
	('5004908','Jaraguari','MS','Centro Norte de Mato Grosso do Sul'),
	('5005004','Jardim','MS','Sudoeste de Mato Grosso do Sul'),
	('5005103','Jateí','MS','Sudoeste de Mato Grosso do Sul'),
	('5005152','Juti','MS','Sudoeste de Mato Grosso do Sul'),
	('5005202','Ladário','MS','Pantanais Sul Mato-grossense'),
	('5005251','Laguna Carapã','MS','Sudoeste de Mato Grosso do Sul'),
	('5005400','Maracaju','MS','Sudoeste de Mato Grosso do Sul'),
	('5005608','Miranda','MS','Pantanais Sul Mato-grossense'),
	('5005681','Mundo Novo','MS','Sudoeste de Mato Grosso do Sul'),
	('5005707','Naviraí','MS','Sudoeste de Mato Grosso do Sul'),
	('5005806','Nioaque','MS','Sudoeste de Mato Grosso do Sul'),
	('5006002','Nova Alvorada do Sul','MS','Sudoeste de Mato Grosso do Sul'),
	('5006200','Nova Andradina','MS','Leste de Mato Grosso do Sul'),
	('5006259','Novo Horizonte do Sul','MS','Sudoeste de Mato Grosso do Sul'),
	('5006275','Paraíso das Águas','MS','Leste de Mato Grosso do Sul'),
	('5006309','Paranaíba','MS','Leste de Mato Grosso do Sul'),
	('5006358','Paranhos','MS','Sudoeste de Mato Grosso do Sul'),
	('5006408','Pedro Gomes','MS','Centro Norte de Mato Grosso do Sul'),
	('5006606','Ponta Porã','MS','Sudoeste de Mato Grosso do Sul'),
	('5006903','Porto Murtinho','MS','Pantanais Sul Mato-grossense'),
	('5007109','Ribas do Rio Pardo','MS','Leste de Mato Grosso do Sul'),
	('5007208','Rio Brilhante','MS','Sudoeste de Mato Grosso do Sul'),
	('5007307','Rio Negro','MS','Centro Norte de Mato Grosso do Sul'),
	('5007406','Rio Verde de Mato Grosso','MS','Centro Norte de Mato Grosso do Sul'),
	('5007505','Rochedo','MS','Centro Norte de Mato Grosso do Sul'),
	('5007554','Santa Rita do Pardo','MS','Leste de Mato Grosso do Sul'),
	('5007695','São Gabriel do Oeste','MS','Centro Norte de Mato Grosso do Sul'),
	('5007703','Sete Quedas','MS','Sudoeste de Mato Grosso do Sul'),
	('5007802','Selvíria','MS','Leste de Mato Grosso do Sul'),
	('5007901','Sidrolândia','MS','Centro Norte de Mato Grosso do Sul'),
	('5007935','Sonora','MS','Centro Norte de Mato Grosso do Sul'),
	('5007950','Tacuru','MS','Sudoeste de Mato Grosso do Sul'),
	('5007976','Taquarussu','MS','Leste de Mato Grosso do Sul'),
	('5008008','Terenos','MS','Centro Norte de Mato Grosso do Sul'),
	('5008305','Três Lagoas','MS','Leste de Mato Grosso do Sul'),
	('5008404','Vicentina','MS','Sudoeste de Mato Grosso do Sul'),
	('5100102','Acorizal','MT','Centro-Sul Mato-grossense'),
	('5100201','Água Boa','MT','Nordeste Mato-grossense'),
	('5100250','Alta Floresta','MT','Norte Mato-grossense'),
	('5100300','Alto Araguaia','MT','Sudeste Mato-grossense'),
	('5100359','Alto Boa Vista','MT','Nordeste Mato-grossense'),
	('5100409','Alto Garças','MT','Sudeste Mato-grossense'),
	('5100508','Alto Paraguai','MT','Centro-Sul Mato-grossense'),
	('5100607','Alto Taquari','MT','Sudeste Mato-grossense'),
	('5100805','Apiacás','MT','Norte Mato-grossense'),
	('5101001','Araguaiana','MT','Nordeste Mato-grossense'),
	('5101209','Araguainha','MT','Sudeste Mato-grossense'),
	('5101258','Araputanga','MT','Sudoeste Mato-grossense'),
	('5101308','Arenápolis','MT','Centro-Sul Mato-grossense'),
	('5101407','Aripuanã','MT','Norte Mato-grossense'),
	('5101605','Barão de Melgaço','MT','Centro-Sul Mato-grossense'),
	('5101704','Barra do Bugres','MT','Sudoeste Mato-grossense'),
	('5101803','Barra do Garças','MT','Nordeste Mato-grossense'),
	('5101852','Bom Jesus do Araguaia','MT','Nordeste Mato-grossense'),
	('5101902','Brasnorte','MT','Norte Mato-grossense'),
	('5102504','Cáceres','MT','Centro-Sul Mato-grossense'),
	('5102603','Campinápolis','MT','Nordeste Mato-grossense'),
	('5102637','Campo Novo do Parecis','MT','Norte Mato-grossense'),
	('5102678','Campo Verde','MT','Sudeste Mato-grossense'),
	('5102686','Campos de Júlio','MT','Norte Mato-grossense'),
	('5102694','Canabrava do Norte','MT','Nordeste Mato-grossense'),
	('5102702','Canarana','MT','Nordeste Mato-grossense'),
	('5102793','Carlinda','MT','Norte Mato-grossense'),
	('5102850','Castanheira','MT','Norte Mato-grossense'),
	('5103007','Chapada dos Guimarães','MT','Centro-Sul Mato-grossense'),
	('5103056','Cláudia','MT','Norte Mato-grossense'),
	('5103106','Cocalinho','MT','Nordeste Mato-grossense'),
	('5103205','Colíder','MT','Norte Mato-grossense'),
	('5103254','Colniza','MT','Norte Mato-grossense'),
	('5103304','Comodoro','MT','Norte Mato-grossense'),
	('5103353','Confresa','MT','Nordeste Mato-grossense'),
	('5103361','Conquista D\'Oeste','MT','Sudoeste Mato-grossense'),
	('5103379','Cotriguaçu','MT','Norte Mato-grossense'),
	('5103403','Cuiabá','MT','Centro-Sul Mato-grossense'),
	('5103437','Curvelândia','MT','Centro-Sul Mato-grossense'),
	('5103452','Denise','MT','Sudoeste Mato-grossense'),
	('5103502','Diamantino','MT','Norte Mato-grossense'),
	('5103601','Dom Aquino','MT','Sudeste Mato-grossense'),
	('5103700','Feliz Natal','MT','Norte Mato-grossense'),
	('5103809','Figueirópolis D\'Oeste','MT','Sudoeste Mato-grossense'),
	('5103858','Gaúcha do Norte','MT','Norte Mato-grossense'),
	('5103908','General Carneiro','MT','Sudeste Mato-grossense'),
	('5103957','Glória D\'Oeste','MT','Sudoeste Mato-grossense'),
	('5104104','Guarantã do Norte','MT','Norte Mato-grossense'),
	('5104203','Guiratinga','MT','Sudeste Mato-grossense'),
	('5104500','Indiavaí','MT','Sudoeste Mato-grossense'),
	('5104526','Ipiranga do Norte','MT','Norte Mato-grossense'),
	('5104542','Itanhangá','MT','Norte Mato-grossense'),
	('5104559','Itaúba','MT','Norte Mato-grossense'),
	('5104609','Itiquira','MT','Sudeste Mato-grossense'),
	('5104807','Jaciara','MT','Sudeste Mato-grossense'),
	('5104906','Jangada','MT','Centro-Sul Mato-grossense'),
	('5105002','Jauru','MT','Sudoeste Mato-grossense'),
	('5105101','Juara','MT','Norte Mato-grossense'),
	('5105150','Juína','MT','Norte Mato-grossense'),
	('5105176','Juruena','MT','Norte Mato-grossense'),
	('5105200','Juscimeira','MT','Sudeste Mato-grossense'),
	('5105234','Lambari D\'Oeste','MT','Sudoeste Mato-grossense'),
	('5105259','Lucas do Rio Verde','MT','Norte Mato-grossense'),
	('5105309','Luciara','MT','Nordeste Mato-grossense'),
	('5105507','Vila Bela da Santíssima Trindade','MT','Sudoeste Mato-grossense'),
	('5105580','Marcelândia','MT','Norte Mato-grossense'),
	('5105606','Matupá','MT','Norte Mato-grossense'),
	('5105622','Mirassol d\'Oeste','MT','Sudoeste Mato-grossense'),
	('5105903','Nobres','MT','Norte Mato-grossense'),
	('5106000','Nortelândia','MT','Centro-Sul Mato-grossense'),
	('5106109','Nossa Senhora do Livramento','MT','Centro-Sul Mato-grossense'),
	('5106158','Nova Bandeirantes','MT','Norte Mato-grossense'),
	('5106174','Nova Nazaré','MT','Nordeste Mato-grossense'),
	('5106182','Nova Lacerda','MT','Sudoeste Mato-grossense'),
	('5106190','Nova Santa Helena','MT','Norte Mato-grossense'),
	('5106208','Nova Brasilândia','MT','Norte Mato-grossense'),
	('5106216','Nova Canaã do Norte','MT','Norte Mato-grossense'),
	('5106224','Nova Mutum','MT','Norte Mato-grossense'),
	('5106232','Nova Olímpia','MT','Sudoeste Mato-grossense'),
	('5106240','Nova Ubiratã','MT','Norte Mato-grossense'),
	('5106257','Nova Xavantina','MT','Nordeste Mato-grossense'),
	('5106265','Novo Mundo','MT','Norte Mato-grossense'),
	('5106273','Novo Horizonte do Norte','MT','Norte Mato-grossense'),
	('5106281','Novo São Joaquim','MT','Nordeste Mato-grossense'),
	('5106299','Paranaíta','MT','Norte Mato-grossense'),
	('5106307','Paranatinga','MT','Norte Mato-grossense'),
	('5106315','Novo Santo Antônio','MT','Nordeste Mato-grossense'),
	('5106372','Pedra Preta','MT','Sudeste Mato-grossense'),
	('5106422','Peixoto de Azevedo','MT','Norte Mato-grossense'),
	('5106455','Planalto da Serra','MT','Norte Mato-grossense'),
	('5106505','Poconé','MT','Centro-Sul Mato-grossense'),
	('5106653','Pontal do Araguaia','MT','Sudeste Mato-grossense'),
	('5106703','Ponte Branca','MT','Sudeste Mato-grossense'),
	('5106752','Pontes e Lacerda','MT','Sudoeste Mato-grossense'),
	('5106778','Porto Alegre do Norte','MT','Nordeste Mato-grossense'),
	('5106802','Porto dos Gaúchos','MT','Norte Mato-grossense'),
	('5106828','Porto Esperidião','MT','Sudoeste Mato-grossense'),
	('5106851','Porto Estrela','MT','Sudoeste Mato-grossense'),
	('5107008','Poxoréu','MT','Sudeste Mato-grossense'),
	('5107040','Primavera do Leste','MT','Sudeste Mato-grossense'),
	('5107065','Querência','MT','Nordeste Mato-grossense'),
	('5107107','São José dos Quatro Marcos','MT','Sudoeste Mato-grossense'),
	('5107156','Reserva do Cabaçal','MT','Sudoeste Mato-grossense'),
	('5107180','Ribeirão Cascalheira','MT','Nordeste Mato-grossense'),
	('5107198','Ribeirãozinho','MT','Sudeste Mato-grossense'),
	('5107206','Rio Branco','MT','Sudoeste Mato-grossense'),
	('5107248','Santa Carmem','MT','Norte Mato-grossense'),
	('5107263','Santo Afonso','MT','Centro-Sul Mato-grossense'),
	('5107297','São José do Povo','MT','Sudeste Mato-grossense'),
	('5107305','São José do Rio Claro','MT','Norte Mato-grossense'),
	('5107354','São José do Xingu','MT','Nordeste Mato-grossense'),
	('5107404','São Pedro da Cipa','MT','Sudeste Mato-grossense'),
	('5107578','Rondolândia','MT','Norte Mato-grossense'),
	('5107602','Rondonópolis','MT','Sudeste Mato-grossense'),
	('5107701','Rosário Oeste','MT','Centro-Sul Mato-grossense'),
	('5107743','Santa Cruz do Xingu','MT','Nordeste Mato-grossense'),
	('5107750','Salto do Céu','MT','Sudoeste Mato-grossense'),
	('5107768','Santa Rita do Trivelato','MT','Norte Mato-grossense'),
	('5107776','Santa Terezinha','MT','Nordeste Mato-grossense'),
	('5107792','Santo Antônio do Leste','MT','Nordeste Mato-grossense'),
	('5107800','Santo Antônio do Leverger','MT','Centro-Sul Mato-grossense'),
	('5107859','São Félix do Araguaia','MT','Nordeste Mato-grossense'),
	('5107875','Sapezal','MT','Norte Mato-grossense'),
	('5107883','Serra Nova Dourada','MT','Nordeste Mato-grossense'),
	('5107909','Sinop','MT','Norte Mato-grossense'),
	('5107925','Sorriso','MT','Norte Mato-grossense'),
	('5107941','Tabaporã','MT','Norte Mato-grossense'),
	('5107958','Tangará da Serra','MT','Sudoeste Mato-grossense'),
	('5108006','Tapurah','MT','Norte Mato-grossense'),
	('5108055','Terra Nova do Norte','MT','Norte Mato-grossense'),
	('5108105','Tesouro','MT','Sudeste Mato-grossense'),
	('5108204','Torixoréu','MT','Sudeste Mato-grossense'),
	('5108303','União do Sul','MT','Norte Mato-grossense'),
	('5108352','Vale de São Domingos','MT','Sudoeste Mato-grossense'),
	('5108402','Várzea Grande','MT','Centro-Sul Mato-grossense'),
	('5108501','Vera','MT','Norte Mato-grossense'),
	('5108600','Vila Rica','MT','Nordeste Mato-grossense'),
	('5108808','Nova Guarita','MT','Norte Mato-grossense'),
	('5108857','Nova Marilândia','MT','Centro-Sul Mato-grossense'),
	('5108907','Nova Maringá','MT','Norte Mato-grossense'),
	('5108956','Nova Monte Verde','MT','Norte Mato-grossense'),
	('5200050','Abadia de Goiás','GO','Centro Goiano'),
	('5200100','Abadiânia','GO','Leste Goiano'),
	('5200134','Acreúna','GO','Sul Goiano'),
	('5200159','Adelândia','GO','Centro Goiano'),
	('5200175','Água Fria de Goiás','GO','Leste Goiano'),
	('5200209','Água Limpa','GO','Sul Goiano'),
	('5200258','Águas Lindas de Goiás','GO','Leste Goiano'),
	('5200308','Alexânia','GO','Leste Goiano'),
	('5200506','Aloândia','GO','Sul Goiano'),
	('5200555','Alto Horizonte','GO','Norte Goiano'),
	('5200605','Alto Paraíso de Goiás','GO','Norte Goiano'),
	('5200803','Alvorada do Norte','GO','Leste Goiano'),
	('5200829','Amaralina','GO','Norte Goiano'),
	('5200852','Americano do Brasil','GO','Centro Goiano'),
	('5200902','Amorinópolis','GO','Centro Goiano'),
	('5201108','Anápolis','GO','Centro Goiano'),
	('5201207','Anhanguera','GO','Sul Goiano'),
	('5201306','Anicuns','GO','Centro Goiano'),
	('5201405','Aparecida de Goiânia','GO','Centro Goiano'),
	('5201454','Aparecida do Rio Doce','GO','Sul Goiano'),
	('5201504','Aporé','GO','Sul Goiano'),
	('5201603','Araçu','GO','Centro Goiano'),
	('5201702','Aragarças','GO','Noroeste Goiano'),
	('5201801','Aragoiânia','GO','Centro Goiano'),
	('5202155','Araguapaz','GO','Noroeste Goiano'),
	('5202353','Arenópolis','GO','Noroeste Goiano'),
	('5202502','Aruanã','GO','Noroeste Goiano'),
	('5202601','Aurilândia','GO','Centro Goiano'),
	('5202809','Avelinópolis','GO','Centro Goiano'),
	('5203104','Baliza','GO','Noroeste Goiano'),
	('5203203','Barro Alto','GO','Centro Goiano'),
	('5203302','Bela Vista de Goiás','GO','Centro Goiano'),
	('5203401','Bom Jardim de Goiás','GO','Noroeste Goiano'),
	('5203500','Bom Jesus de Goiás','GO','Sul Goiano'),
	('5203559','Bonfinópolis','GO','Centro Goiano'),
	('5203575','Bonópolis','GO','Norte Goiano'),
	('5203609','Brazabrantes','GO','Centro Goiano'),
	('5203807','Britânia','GO','Noroeste Goiano'),
	('5203906','Buriti Alegre','GO','Sul Goiano'),
	('5203939','Buriti de Goiás','GO','Centro Goiano'),
	('5203962','Buritinópolis','GO','Leste Goiano'),
	('5204003','Cabeceiras','GO','Leste Goiano'),
	('5204102','Cachoeira Alta','GO','Sul Goiano'),
	('5204201','Cachoeira de Goiás','GO','Centro Goiano'),
	('5204250','Cachoeira Dourada','GO','Sul Goiano'),
	('5204300','Caçu','GO','Sul Goiano'),
	('5204409','Caiapônia','GO','Sul Goiano'),
	('5204508','Caldas Novas','GO','Sul Goiano'),
	('5204557','Caldazinha','GO','Centro Goiano'),
	('5204607','Campestre de Goiás','GO','Sul Goiano'),
	('5204656','Campinaçu','GO','Norte Goiano'),
	('5204706','Campinorte','GO','Norte Goiano'),
	('5204805','Campo Alegre de Goiás','GO','Sul Goiano'),
	('5204854','Campo Limpo de Goiás','GO','Centro Goiano'),
	('5204904','Campos Belos','GO','Norte Goiano'),
	('5204953','Campos Verdes','GO','Norte Goiano'),
	('5205000','Carmo do Rio Verde','GO','Centro Goiano'),
	('5205059','Castelândia','GO','Sul Goiano'),
	('5205109','Catalão','GO','Sul Goiano'),
	('5205208','Caturaí','GO','Centro Goiano'),
	('5205307','Cavalcante','GO','Norte Goiano'),
	('5205406','Ceres','GO','Centro Goiano'),
	('5205455','Cezarina','GO','Sul Goiano'),
	('5205471','Chapadão do Céu','GO','Sul Goiano'),
	('5205497','Cidade Ocidental','GO','Leste Goiano'),
	('5205513','Cocalzinho de Goiás','GO','Leste Goiano'),
	('5205521','Colinas do Sul','GO','Norte Goiano'),
	('5205703','Córrego do Ouro','GO','Centro Goiano'),
	('5205802','Corumbá de Goiás','GO','Leste Goiano'),
	('5205901','Corumbaíba','GO','Sul Goiano'),
	('5206206','Cristalina','GO','Leste Goiano'),
	('5206305','Cristianópolis','GO','Sul Goiano'),
	('5206404','Crixás','GO','Noroeste Goiano'),
	('5206503','Cromínia','GO','Sul Goiano'),
	('5206602','Cumari','GO','Sul Goiano'),
	('5206701','Damianópolis','GO','Leste Goiano'),
	('5206800','Damolândia','GO','Centro Goiano'),
	('5206909','Davinópolis','GO','Sul Goiano'),
	('5207105','Diorama','GO','Noroeste Goiano'),
	('5207253','Doverlândia','GO','Sul Goiano'),
	('5207352','Edealina','GO','Sul Goiano'),
	('5207402','Edéia','GO','Sul Goiano'),
	('5207501','Estrela do Norte','GO','Norte Goiano'),
	('5207535','Faina','GO','Noroeste Goiano'),
	('5207600','Fazenda Nova','GO','Centro Goiano'),
	('5207808','Firminópolis','GO','Centro Goiano'),
	('5207907','Flores de Goiás','GO','Leste Goiano'),
	('5208004','Formosa','GO','Leste Goiano'),
	('5208103','Formoso','GO','Norte Goiano'),
	('5208152','Gameleira de Goiás','GO','Sul Goiano'),
	('5208301','Divinópolis de Goiás','GO','Leste Goiano'),
	('5208400','Goianápolis','GO','Centro Goiano'),
	('5208509','Goiandira','GO','Sul Goiano'),
	('5208608','Goianésia','GO','Centro Goiano'),
	('5208707','Goiânia','GO','Centro Goiano'),
	('5208806','Goianira','GO','Centro Goiano'),
	('5208905','Goiás','GO','Noroeste Goiano'),
	('5209101','Goiatuba','GO','Sul Goiano'),
	('5209150','Gouvelândia','GO','Sul Goiano'),
	('5209200','Guapó','GO','Centro Goiano'),
	('5209291','Guaraíta','GO','Centro Goiano'),
	('5209408','Guarani de Goiás','GO','Leste Goiano'),
	('5209457','Guarinos','GO','Centro Goiano'),
	('5209606','Heitoraí','GO','Centro Goiano'),
	('5209705','Hidrolândia','GO','Centro Goiano'),
	('5209804','Hidrolina','GO','Centro Goiano'),
	('5209903','Iaciara','GO','Leste Goiano'),
	('5209937','Inaciolândia','GO','Sul Goiano'),
	('5209952','Indiara','GO','Sul Goiano'),
	('5210000','Inhumas','GO','Centro Goiano'),
	('5210109','Ipameri','GO','Sul Goiano'),
	('5210158','Ipiranga de Goiás','GO','Centro Goiano'),
	('5210208','Iporá','GO','Centro Goiano'),
	('5210307','Israelândia','GO','Centro Goiano'),
	('5210406','Itaberaí','GO','Centro Goiano'),
	('5210562','Itaguari','GO','Centro Goiano'),
	('5210604','Itaguaru','GO','Centro Goiano'),
	('5210802','Itajá','GO','Sul Goiano'),
	('5210901','Itapaci','GO','Centro Goiano'),
	('5211008','Itapirapuã','GO','Noroeste Goiano'),
	('5211206','Itapuranga','GO','Centro Goiano'),
	('5211305','Itarumã','GO','Sul Goiano'),
	('5211404','Itauçu','GO','Centro Goiano'),
	('5211503','Itumbiara','GO','Sul Goiano'),
	('5211602','Ivolândia','GO','Centro Goiano'),
	('5211701','Jandaia','GO','Sul Goiano'),
	('5211800','Jaraguá','GO','Centro Goiano'),
	('5211909','Jataí','GO','Sul Goiano'),
	('5212006','Jaupaci','GO','Centro Goiano'),
	('5212055','Jesúpolis','GO','Centro Goiano'),
	('5212105','Joviânia','GO','Sul Goiano'),
	('5212204','Jussara','GO','Noroeste Goiano'),
	('5212253','Lagoa Santa','GO','Sul Goiano'),
	('5212303','Leopoldo de Bulhões','GO','Centro Goiano'),
	('5212501','Luziânia','GO','Leste Goiano'),
	('5212600','Mairipotaba','GO','Sul Goiano'),
	('5212709','Mambaí','GO','Leste Goiano'),
	('5212808','Mara Rosa','GO','Norte Goiano'),
	('5212907','Marzagão','GO','Sul Goiano'),
	('5212956','Matrinchã','GO','Noroeste Goiano'),
	('5213004','Maurilândia','GO','Sul Goiano'),
	('5213053','Mimoso de Goiás','GO','Leste Goiano'),
	('5213087','Minaçu','GO','Norte Goiano'),
	('5213103','Mineiros','GO','Sul Goiano'),
	('5213400','Moiporá','GO','Centro Goiano'),
	('5213509','Monte Alegre de Goiás','GO','Norte Goiano'),
	('5213707','Montes Claros de Goiás','GO','Noroeste Goiano'),
	('5213756','Montividiu','GO','Sul Goiano'),
	('5213772','Montividiu do Norte','GO','Norte Goiano'),
	('5213806','Morrinhos','GO','Sul Goiano'),
	('5213855','Morro Agudo de Goiás','GO','Centro Goiano'),
	('5213905','Mossâmedes','GO','Centro Goiano'),
	('5214002','Mozarlândia','GO','Noroeste Goiano'),
	('5214051','Mundo Novo','GO','Noroeste Goiano'),
	('5214101','Mutunópolis','GO','Norte Goiano'),
	('5214408','Nazário','GO','Centro Goiano'),
	('5214507','Nerópolis','GO','Centro Goiano'),
	('5214606','Niquelândia','GO','Norte Goiano'),
	('5214705','Nova América','GO','Centro Goiano'),
	('5214804','Nova Aurora','GO','Sul Goiano'),
	('5214838','Nova Crixás','GO','Noroeste Goiano'),
	('5214861','Nova Glória','GO','Centro Goiano'),
	('5214879','Nova Iguaçu de Goiás','GO','Norte Goiano'),
	('5214903','Nova Roma','GO','Norte Goiano'),
	('5215009','Nova Veneza','GO','Centro Goiano'),
	('5215207','Novo Brasil','GO','Centro Goiano'),
	('5215231','Novo Gama','GO','Leste Goiano'),
	('5215256','Novo Planalto','GO','Noroeste Goiano'),
	('5215306','Orizona','GO','Sul Goiano'),
	('5215405','Ouro Verde de Goiás','GO','Centro Goiano'),
	('5215504','Ouvidor','GO','Sul Goiano'),
	('5215603','Padre Bernardo','GO','Leste Goiano'),
	('5215652','Palestina de Goiás','GO','Sul Goiano'),
	('5215702','Palmeiras de Goiás','GO','Sul Goiano'),
	('5215801','Palmelo','GO','Sul Goiano'),
	('5215900','Palminópolis','GO','Sul Goiano'),
	('5216007','Panamá','GO','Sul Goiano'),
	('5216304','Paranaiguara','GO','Sul Goiano'),
	('5216403','Paraúna','GO','Sul Goiano'),
	('5216452','Perolândia','GO','Sul Goiano'),
	('5216809','Petrolina de Goiás','GO','Centro Goiano'),
	('5216908','Pilar de Goiás','GO','Centro Goiano'),
	('5217104','Piracanjuba','GO','Sul Goiano'),
	('5217203','Piranhas','GO','Noroeste Goiano'),
	('5217302','Pirenópolis','GO','Leste Goiano'),
	('5217401','Pires do Rio','GO','Sul Goiano'),
	('5217609','Planaltina','GO','Leste Goiano'),
	('5217708','Pontalina','GO','Sul Goiano'),
	('5218003','Porangatu','GO','Norte Goiano'),
	('5218052','Porteirão','GO','Sul Goiano'),
	('5218102','Portelândia','GO','Sul Goiano'),
	('5218300','Posse','GO','Leste Goiano'),
	('5218391','Professor Jamil','GO','Sul Goiano'),
	('5218508','Quirinópolis','GO','Sul Goiano'),
	('5218607','Rialma','GO','Centro Goiano'),
	('5218706','Rianápolis','GO','Centro Goiano'),
	('5218789','Rio Quente','GO','Sul Goiano'),
	('5218805','Rio Verde','GO','Sul Goiano'),
	('5218904','Rubiataba','GO','Centro Goiano'),
	('5219001','Sanclerlândia','GO','Centro Goiano'),
	('5219100','Santa Bárbara de Goiás','GO','Centro Goiano'),
	('5219209','Santa Cruz de Goiás','GO','Sul Goiano'),
	('5219258','Santa Fé de Goiás','GO','Noroeste Goiano'),
	('5219308','Santa Helena de Goiás','GO','Sul Goiano'),
	('5219357','Santa Isabel','GO','Centro Goiano'),
	('5219407','Santa Rita do Araguaia','GO','Sul Goiano'),
	('5219456','Santa Rita do Novo Destino','GO','Centro Goiano'),
	('5219506','Santa Rosa de Goiás','GO','Centro Goiano'),
	('5219605','Santa Tereza de Goiás','GO','Norte Goiano'),
	('5219704','Santa Terezinha de Goiás','GO','Norte Goiano'),
	('5219712','Santo Antônio da Barra','GO','Sul Goiano'),
	('5219738','Santo Antônio de Goiás','GO','Centro Goiano'),
	('5219753','Santo Antônio do Descoberto','GO','Leste Goiano'),
	('5219803','São Domingos','GO','Leste Goiano'),
	('5219902','São Francisco de Goiás','GO','Centro Goiano'),
	('5220009','São João d\'Aliança','GO','Norte Goiano'),
	('5220058','São João da Paraúna','GO','Sul Goiano'),
	('5220108','São Luís de Montes Belos','GO','Centro Goiano'),
	('5220157','São Luiz do Norte','GO','Centro Goiano'),
	('5220207','São Miguel do Araguaia','GO','Noroeste Goiano'),
	('5220264','São Miguel do Passa Quatro','GO','Sul Goiano'),
	('5220280','São Patrício','GO','Centro Goiano'),
	('5220405','São Simão','GO','Sul Goiano'),
	('5220454','Senador Canedo','GO','Centro Goiano'),
	('5220504','Serranópolis','GO','Sul Goiano'),
	('5220603','Silvânia','GO','Sul Goiano'),
	('5220686','Simolândia','GO','Leste Goiano'),
	('5220702','Sítio d\'Abadia','GO','Leste Goiano'),
	('5221007','Taquaral de Goiás','GO','Centro Goiano'),
	('5221080','Teresina de Goiás','GO','Norte Goiano'),
	('5221197','Terezópolis de Goiás','GO','Centro Goiano'),
	('5221304','Três Ranchos','GO','Sul Goiano'),
	('5221403','Trindade','GO','Centro Goiano'),
	('5221452','Trombas','GO','Norte Goiano'),
	('5221502','Turvânia','GO','Centro Goiano'),
	('5221551','Turvelândia','GO','Sul Goiano'),
	('5221577','Uirapuru','GO','Noroeste Goiano'),
	('5221601','Uruaçu','GO','Norte Goiano'),
	('5221700','Uruana','GO','Centro Goiano'),
	('5221809','Urutaí','GO','Sul Goiano'),
	('5221858','Valparaíso de Goiás','GO','Leste Goiano'),
	('5221908','Varjão','GO','Sul Goiano'),
	('5222005','Vianópolis','GO','Sul Goiano'),
	('5222054','Vicentinópolis','GO','Sul Goiano'),
	('5222203','Vila Boa','GO','Leste Goiano'),
	('5222302','Vila Propício','GO','Leste Goiano'),
	('5300108','Brasília','DF','Distrito Federal');

/*!40000 ALTER TABLE `municipio` ENABLE KEYS */;
UNLOCK TABLES;


# Dump of table prefeitura
# ------------------------------------------------------------

LOCK TABLES `prefeitura` WRITE;
/*!40000 ALTER TABLE `prefeitura` DISABLE KEYS */;

INSERT INTO `prefeitura` (`codigoMunicipio`, `cnpj`)
VALUES
	('1100015','18511471000120'),
	('1100023','18511471000124'),
	('1100346','18511471000123'),
	('1100379','18511471000121'),
	('1100403','18511471000122');

/*!40000 ALTER TABLE `prefeitura` ENABLE KEYS */;
UNLOCK TABLES;


# Dump of table regiao
# ------------------------------------------------------------

LOCK TABLES `regiao` WRITE;
/*!40000 ALTER TABLE `regiao` DISABLE KEYS */;

INSERT INTO `regiao` (`nomeRegiao`, `uf`)
VALUES
	('Vale do Acre','AC'),
	('Vale do Juruá','AC'),
	('Agreste Alagoano','AL'),
	('Leste Alagoano','AL'),
	('Sertão Alagoano','AL'),
	('Centro Amazonense','AM'),
	('Norte Amazonense','AM'),
	('Sudoeste Amazonense','AM'),
	('Sul Amazonense','AM'),
	('Norte do Amapá','AP'),
	('Sul do Amapá','AP'),
	('Centro Norte Baiano','BA'),
	('Centro Sul Baiano','BA'),
	('Extremo Oeste Baiano','BA'),
	('Metropolitana de Salvador','BA'),
	('Nordeste Baiano','BA'),
	('Sul Baiano','BA'),
	('Vale São-Franciscano da Bahia','BA'),
	('Centro-Sul Cearense','CE'),
	('Jaguaribe','CE'),
	('Metropolitana de Fortaleza','CE'),
	('Noroeste Cearense','CE'),
	('Norte Cearense','CE'),
	('Sertões Cearenses','CE'),
	('Sul Cearense','CE'),
	('Distrito Federal','DF'),
	('Central Espírito-santense','ES'),
	('Litoral Norte Espírito-santense','ES'),
	('Noroeste Espírito-santense','ES'),
	('Sul Espírito-santense','ES'),
	('Centro Goiano','GO'),
	('Leste Goiano','GO'),
	('Noroeste Goiano','GO'),
	('Norte Goiano','GO'),
	('Sul Goiano','GO'),
	('Centro Maranhense','MA'),
	('Leste Maranhense','MA'),
	('Norte Maranhense','MA'),
	('Oeste Maranhense','MA'),
	('Sul Maranhense','MA'),
	('Campo das Vertentes','MG'),
	('Central Mineira','MG'),
	('Jequitinhonha','MG'),
	('Metropolitana de Belo Horizonte','MG'),
	('Noroeste de Minas','MG'),
	('Norte de Minas','MG'),
	('Oeste de Minas','MG'),
	('Sul/Sudoeste de Minas','MG'),
	('Triângulo Mineiro/Alto Paranaíba','MG'),
	('Vale do Mucuri','MG'),
	('Vale do Rio Doce','MG'),
	('Zona da Mata','MG'),
	('Centro Norte de Mato Grosso do Sul','MS'),
	('Leste de Mato Grosso do Sul','MS'),
	('Pantanais Sul Mato-grossense','MS'),
	('Sudoeste de Mato Grosso do Sul','MS'),
	('Centro-Sul Mato-grossense','MT'),
	('Nordeste Mato-grossense','MT'),
	('Norte Mato-grossense','MT'),
	('Sudeste Mato-grossense','MT'),
	('Sudoeste Mato-grossense','MT'),
	('Baixo Amazonas','PA'),
	('Marajó','PA'),
	('Metropolitana de Belém','PA'),
	('Nordeste Paraense','PA'),
	('Sudeste Paraense','PA'),
	('Sudoeste Paraense','PA'),
	('Agreste Paraibano','PB'),
	('Borborema','PB'),
	('Mata Paraibana','PB'),
	('Sertão Paraibano','PB'),
	('Agreste Pernambucano','PE'),
	('Mata Pernambucana','PE'),
	('Metropolitana de Recife','PE'),
	('São Francisco Pernambucano','PE'),
	('Sertão Pernambucano','PE'),
	('Centro-Norte Piauiense','PI'),
	('Norte Piauiense','PI'),
	('Sudeste Piauiense','PI'),
	('Sudoeste Piauiense','PI'),
	('Centro Ocidental Paranaense','PR'),
	('Centro Oriental Paranaense','PR'),
	('Centro-Sul Paranaense','PR'),
	('Metropolitana de Curitiba','PR'),
	('Noroeste Paranaense','PR'),
	('Norte Central Paranaense','PR'),
	('Norte Pioneiro Paranaense','PR'),
	('Oeste Paranaense','PR'),
	('Sudeste Paranaense','PR'),
	('Sudoeste Paranaense','PR'),
	('Baixadas','RJ'),
	('Centro Fluminense','RJ'),
	('Metropolitana do Rio de Janeiro','RJ'),
	('Noroeste Fluminense','RJ'),
	('Norte Fluminense','RJ'),
	('Sul Fluminense','RJ'),
	('Agreste Potiguar','RN'),
	('Central Potiguar','RN'),
	('Leste Potiguar','RN'),
	('Oeste Potiguar','RN'),
	('Leste Rondoniense','RO'),
	('Madeira-Guaporé','RO'),
	('Norte de Roraima','RR'),
	('Sul de Roraima','RR'),
	('Centro Ocidental Rio-grandense','RS'),
	('Centro Oriental Rio-grandense','RS'),
	('Metropolitana de Porto Alegre','RS'),
	('Nordeste Rio-grandense','RS'),
	('Noroeste Rio-grandense','RS'),
	('Sudeste Rio-grandense','RS'),
	('Sudoeste Rio-grandense','RS'),
	('Grande Florianópolis','SC'),
	('Norte Catarinense','SC'),
	('Oeste Catarinense','SC'),
	('Serrana','SC'),
	('Sul Catarinense','SC'),
	('Vale do Itajaí','SC'),
	('Agreste Sergipano','SE'),
	('Leste Sergipano','SE'),
	('Sertão Sergipano','SE'),
	('Araçatuba','SP'),
	('Araraquara','SP'),
	('Assis','SP'),
	('Bauru','SP'),
	('Campinas','SP'),
	('Itapetininga','SP'),
	('Litoral Sul Paulista','SP'),
	('Macro Metropolitana Paulista','SP'),
	('Marília','SP'),
	('Metropolitana de São Paulo','SP'),
	('Piracicaba','SP'),
	('Presidente Prudente','SP'),
	('Ribeirão Preto','SP'),
	('São José do Rio Preto','SP'),
	('Vale do Paraíba Paulista','SP'),
	('Ocidental do Tocantins','TO'),
	('Oriental do Tocantins','TO');

/*!40000 ALTER TABLE `regiao` ENABLE KEYS */;
UNLOCK TABLES;



/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;
/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
""",


# MULTICHAIN END
):
            try:
                store.ddl(stmt)
            except Exception:
                store.log.error("Failed: %s", stmt)
                raise

        for key in ['chain', 'datadir',
# MULTICHAIN START
                    'asset',
# MULTICHAIN END
                    'tx', 'txout', 'pubkey', 'txin', 'block']:
            store.create_sequence(key)

        store.sql("INSERT INTO abe_lock (lock_id) VALUES (1)")

        # Insert some well-known chain metadata.
        for conf in CHAIN_CONFIG:
            conf = conf.copy()
            conf["name"] = conf.pop("chain")
            if 'policy' in conf:
                policy = conf.pop('policy')
            else:
                policy = conf['name']

            chain = Chain.create(policy, **conf)
            store.insert_chain(chain)

        store.sql("""
            INSERT INTO pubkey (pubkey_id, pubkey_hash) VALUES (?, ?)""",
                  (NULL_PUBKEY_ID, store.binin(NULL_PUBKEY_HASH)))

        if store.args.use_firstbits:
            store.config['use_firstbits'] = "true"
            store.ddl(
                """CREATE TABLE abe_firstbits (
                    pubkey_id       NUMERIC(26) NOT NULL,
                    block_id        NUMERIC(14) NOT NULL,
                    address_version VARBINARY(10) NOT NULL,
                    firstbits       VARCHAR(50) NOT NULL,
                    PRIMARY KEY (address_version, pubkey_id, block_id),
                    FOREIGN KEY (pubkey_id) REFERENCES pubkey (pubkey_id),
                    FOREIGN KEY (block_id) REFERENCES block (block_id)
                )""")
            store.ddl(
                """CREATE INDEX x_abe_firstbits
                    ON abe_firstbits (address_version, firstbits)""")
        else:
            store.config['use_firstbits'] = "false"

        store.config['keep_scriptsig'] = \
            "true" if store.args.keep_scriptsig else "false"

        store.save_config()
        store.commit()

    def insert_chain(store, chain):
        chain.id = store.new_id("chain")
# MULTICHAIN START
        store.sql("""
            INSERT INTO chain (
                chain_id, chain_magic, chain_name, chain_code3,
                chain_address_checksum, chain_address_version, chain_script_addr_vers, chain_policy, chain_decimals,
                chain_protocol_version
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                  (chain.id, store.binin(chain.magic), chain.name,
                   chain.code3, store.binin(chain.address_checksum), store.binin(chain.address_version), store.binin(chain.script_addr_vers),
                   chain.policy, chain.decimals, chain.protocol_version))
# MULTICHAIN END

    def get_lock(store):
        if store.version_below('Abe26'):
            return None
        conn = store.connect()
        cur = conn.cursor()
        cur.execute("UPDATE abe_lock SET pid = %d WHERE lock_id = 1"
                    % (os.getpid(),))
        if cur.rowcount != 1:
            raise Exception("unexpected rowcount")
        cur.close()

        # Check whether database supports concurrent updates.  Where it
        # doesn't (SQLite) we get exclusive access automatically.
        try:
            import random
            letters = "".join([chr(random.randint(65, 90)) for x in xrange(10)])
            store.sql("""
                INSERT INTO configvar (configvar_name, configvar_value)
                VALUES (?, ?)""",
                      ("upgrade-lock-" + letters, 'x'))
        except Exception:
            store.release_lock(conn)
            conn = None

        store.rollback()

        # XXX Should reread config.

        return conn

    def release_lock(store, conn):
        if conn:
            conn.rollback()
            conn.close()

    def version_below(store, vers):
        try:
            sv = float(store.config['schema_version'].replace(SCHEMA_TYPE, ''))
        except ValueError:
            return False
        vers = float(vers.replace(SCHEMA_TYPE, ''))
        return sv < vers

    def configure(store):
        config = store._sql.configure()
        store.init_binfuncs()
        for name in config.keys():
            store.config['sql.' + name] = config[name]

    def save_config(store):
        store.config['schema_version'] = SCHEMA_VERSION
        for name in store.config.keys():
            store.save_configvar(name)

    def save_configvar(store, name):
        store.sql("UPDATE configvar SET configvar_value = ?"
                  " WHERE configvar_name = ?", (store.config[name], name))
        if store.rowcount() == 0:
            store.sql("INSERT INTO configvar (configvar_name, configvar_value)"
                      " VALUES (?, ?)", (name, store.config[name]))

    def set_configvar(store, name, value):
        store.config[name] = value
        store.save_configvar(name)

    def cache_block(store, block_id, height, prev_id, search_id):
        assert isinstance(block_id, int), block_id
        assert isinstance(height, int), height
        assert prev_id is None or isinstance(prev_id, int)
        assert search_id is None or isinstance(search_id, int)
        block = {
            'height':    height,
            'prev_id':   prev_id,
            'search_id': search_id}
        store._blocks[block_id] = block
        return block

    def _load_block(store, block_id):
        block = store._blocks.get(block_id)
        if block is None:
            row = store.selectrow("""
                SELECT block_height, prev_block_id, search_block_id
                  FROM block
                 WHERE block_id = ?""", (block_id,))
            if row is None:
                return None
            height, prev_id, search_id = row
            block = store.cache_block(
                block_id, int(height),
                None if prev_id is None else int(prev_id),
                None if search_id is None else int(search_id))
        return block

    def get_block_id_at_height(store, height, descendant_id):
        if height is None:
            return None
        while True:
            block = store._load_block(descendant_id)
            if block['height'] == height:
                return descendant_id
            descendant_id = block[
                'search_id'
                if util.get_search_height(block['height']) >= height else
                'prev_id']

    def is_descended_from(store, block_id, ancestor_id):
#        ret = store._is_descended_from(block_id, ancestor_id)
#        store.log.debug("%d is%s descended from %d", block_id, '' if ret else ' NOT', ancestor_id)
#        return ret
#    def _is_descended_from(store, block_id, ancestor_id):
        block = store._load_block(block_id)
        ancestor = store._load_block(ancestor_id)
        height = ancestor['height']
        return block['height'] >= height and \
            store.get_block_id_at_height(height, block_id) == ancestor_id

    def get_block_height(store, block_id):
        return store._load_block(int(block_id))['height']

    def find_prev(store, hash):
        row = store.selectrow("""
            SELECT block_id, block_height, block_chain_work,
                   block_total_satoshis, block_total_seconds,
                   block_satoshi_seconds, block_total_ss, block_nTime
              FROM block
             WHERE block_hash=?""", (store.hashin(hash),))
        if row is None:
            return (None, None, None, None, None, None, None, None)
        (id, height, chain_work, satoshis, seconds, satoshi_seconds,
         total_ss, nTime) = row
        return (id, None if height is None else int(height),
                store.binout_int(chain_work),
                None if satoshis is None else int(satoshis),
                None if seconds is None else int(seconds),
                None if satoshi_seconds is None else int(satoshi_seconds),
                None if total_ss is None else int(total_ss),
                int(nTime))

    def import_block(store, b, chain_ids=None, chain=None):

        # Import new transactions.

        if chain_ids is None:
            chain_ids = frozenset() if chain is None else frozenset([chain.id])

        b['value_in'] = 0
        b['value_out'] = 0
        b['value_destroyed'] = 0
        tx_hash_array = []

        # In the common case, all the block's txins _are_ linked, and we
        # can avoid a query if we notice this.
        all_txins_linked = True

        for pos in xrange(len(b['transactions'])):
            tx = b['transactions'][pos]
            
            if 'hash' not in tx:
                if chain is None:
                    store.log.debug("Falling back to SHA256 transaction hash")
                    tx['hash'] = util.double_sha256(tx['__data__'])
                else:
                    tx['hash'] = chain.transaction_hash(tx['__data__'])

            tx_hash_array.append(tx['hash'])
            tx['tx_id'] = store.tx_find_id_and_value(tx, pos == 0)

            if tx['tx_id']:
                all_txins_linked = False
            else:
                if store.commit_bytes == 0:
                    tx['tx_id'] = store.import_and_commit_tx(tx, pos == 0, chain)
                else:
                    tx['tx_id'] = store.import_tx(tx, pos == 0, chain)
                if tx.get('unlinked_count', 1) > 0:
                    all_txins_linked = False

            if tx['value_in'] is None:
                b['value_in'] = None
            elif b['value_in'] is not None:
                b['value_in'] += tx['value_in']
            b['value_out'] += tx['value_out']
            b['value_destroyed'] += tx['value_destroyed']

        # Get a new block ID.
        block_id = int(store.new_id("block"))
        b['block_id'] = block_id

        if chain is not None:
            # Verify Merkle root.
            if b['hashMerkleRoot'] != chain.merkle_root(tx_hash_array):
                raise MerkleRootMismatch(b['hash'], tx_hash_array)

        # Look for the parent block.
        hashPrev = b['hashPrev']
        if chain is None:
            # XXX No longer used.
            is_genesis = hashPrev == util.GENESIS_HASH_PREV
        else:
            is_genesis = hashPrev == chain.genesis_hash_prev

        (prev_block_id, prev_height, prev_work, prev_satoshis,
         prev_seconds, prev_ss, prev_total_ss, prev_nTime) = (
            (None, -1, 0, 0, 0, 0, 0, b['nTime'])
            if is_genesis else
            store.find_prev(hashPrev))

        b['prev_block_id'] = prev_block_id
        b['height'] = None if prev_height is None else prev_height + 1
        b['chain_work'] = util.calculate_work(prev_work, b['nBits'])

        if prev_seconds is None:
            b['seconds'] = None
        else:
            b['seconds'] = prev_seconds + b['nTime'] - prev_nTime
        if prev_satoshis is None or prev_satoshis < 0 or b['value_in'] is None:
            # XXX Abuse this field to save work in adopt_orphans.
            b['satoshis'] = -1 - b['value_destroyed']
        else:
            b['satoshis'] = prev_satoshis + b['value_out'] - b['value_in'] \
                - b['value_destroyed']

        if prev_satoshis is None or prev_satoshis < 0:
            ss_created = None
            b['total_ss'] = None
        else:
            ss_created = prev_satoshis * (b['nTime'] - prev_nTime)
            b['total_ss'] = prev_total_ss + ss_created

        if b['height'] is None or b['height'] < 2:
            b['search_block_id'] = None
        else:
            b['search_block_id'] = store.get_block_id_at_height(
                util.get_search_height(int(b['height'])),
                None if prev_block_id is None else int(prev_block_id))

        # Insert the block table row.
        try:
            unix_date_timestamp = int(store.intin(b['nTime']))
            from datetime import datetime
            current_datetime = datetime.utcfromtimestamp(unix_date_timestamp).strftime('%Y-%m-%d %H-%M-%S')
            
            hashString = '000'
            try:
                hashString = str(b['hashString'])
            except:
                hashString = str(b['hash'])

            store.sql(
                """INSERT INTO block (
                    block_id, block_hash, block_hash_string, block_version, block_hashMerkleRoot,
                    block_nTime, block_datetime, block_nBits, block_nNonce, block_height,
                    prev_block_id, block_chain_work, block_value_in,
                    block_value_out, block_total_satoshis,
                    block_total_seconds, block_total_ss, block_num_tx,
                    search_block_id
                ) VALUES (
                    ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
                )""",
                (block_id, store.hashin(b['hash']), hashString,
                 store.intin(b['version']), store.hashin(b['hashMerkleRoot']), 
                 store.intin(b['nTime']), current_datetime, store.intin(b['nBits']), 
                 store.intin(b['nNonce']), b['height'], prev_block_id,
                 store.binin_int(b['chain_work'], WORK_BITS),
                 store.intin(b['value_in']), store.intin(b['value_out']),
                 store.intin(b['satoshis']), store.intin(b['seconds']),
                 store.intin(b['total_ss']),
                 len(b['transactions']), b['search_block_id']))

        except store.dbmodule.DatabaseError:

            if store.commit_bytes == 0:
                # Rollback won't undo any previous changes, since we
                # always commit.
                store.rollback()
                # If the exception is due to another process having
                # inserted the same block, it is okay.
                row = store.selectrow("""
                    SELECT block_id, block_satoshi_seconds
                      FROM block
                     WHERE block_hash = ?""",
                    (store.hashin(b['hash']),))
                if row:
                    store.log.info("Block already inserted; block_id %d unsued",
                                   block_id)
                    b['block_id'] = int(row[0])
                    b['ss'] = None if row[1] is None else int(row[1])
                    store.offer_block_to_chains(b, chain_ids)
                    return

            # This is not an expected error, or our caller may have to
            # rewind a block file.  Let them deal with it.
            raise
        
        # List the block's transactions in block_tx.
        for tx_pos in xrange(len(b['transactions'])):
            tx = b['transactions'][tx_pos]
            store.sql("""
                INSERT INTO block_tx
                    (block_id, tx_id, tx_pos)
                VALUES (?, ?, ?)""",
                      (block_id, tx['tx_id'], tx_pos))
            store.log.info("block_tx %d %d", block_id, tx['tx_id'])


        if b['height'] is not None:
            store._populate_block_txin(block_id)

            if all_txins_linked or not store._has_unlinked_txins(block_id):
                b['ss_destroyed'] = store._get_block_ss_destroyed(
                    block_id, b['nTime'],
                    map(lambda tx: tx['tx_id'], b['transactions']))
                if ss_created is None or prev_ss is None:
                    b['ss'] = None
                else:
                    b['ss'] = prev_ss + ss_created - b['ss_destroyed']

                store.sql("""
                    UPDATE block
                       SET block_satoshi_seconds = ?,
                           block_ss_destroyed = ?
                     WHERE block_id = ?""",
                          (store.intin(b['ss']),
                           store.intin(b['ss_destroyed']),
                           block_id))
            else:
                b['ss_destroyed'] = None
                b['ss'] = None

        # Store the inverse hashPrev relationship or mark the block as
        # an orphan.
        if prev_block_id:
            store.sql("""
                INSERT INTO block_next (block_id, next_block_id)
                VALUES (?, ?)""", (prev_block_id, block_id))
        elif not is_genesis:
            store.sql("INSERT INTO orphan_block (block_id, block_hashPrev)" +
                      " VALUES (?, ?)", (block_id, store.hashin(b['hashPrev'])))

        for row in store.selectall("""
            SELECT block_id FROM orphan_block WHERE block_hashPrev = ?""",
                                   (store.hashin(b['hash']),)):
            (orphan_id,) = row
            store.sql("UPDATE block SET prev_block_id = ? WHERE block_id = ?",
                      (block_id, orphan_id))
            store.sql("""
                INSERT INTO block_next (block_id, next_block_id)
                VALUES (?, ?)""", (block_id, orphan_id))
            store.sql("DELETE FROM orphan_block WHERE block_id = ?",
                      (orphan_id,))

        # offer_block_to_chains calls adopt_orphans, which propagates
        # block_height and other cumulative data to the blocks
        # attached above.
        store.offer_block_to_chains(b, chain_ids)

        return block_id

    def _populate_block_txin(store, block_id):
        # Create rows in block_txin.  In case of duplicate transactions,
        # choose the one with the lowest block ID.  XXX For consistency,
        # it should be the lowest height instead of block ID.
        for row in store.selectall("""
            SELECT txin.txin_id, MIN(obt.block_id)
              FROM block_tx bt
              JOIN txin ON (txin.tx_id = bt.tx_id)
              JOIN txout ON (txin.txout_id = txout.txout_id)
              JOIN block_tx obt ON (txout.tx_id = obt.tx_id)
              JOIN block ob ON (obt.block_id = ob.block_id)
             WHERE bt.block_id = ?
               AND ob.block_chain_work IS NOT NULL
             GROUP BY txin.txin_id""", (block_id,)):
            (txin_id, oblock_id) = row
            if store.is_descended_from(block_id, int(oblock_id)):
                store.sql("""
                    INSERT INTO block_txin (block_id, txin_id, out_block_id)
                    VALUES (?, ?, ?)""",
                          (block_id, txin_id, oblock_id))

    def _has_unlinked_txins(store, block_id):
        (unlinked_count,) = store.selectrow("""
            SELECT COUNT(1)
              FROM block_tx bt
              JOIN txin ON (bt.tx_id = txin.tx_id)
              JOIN unlinked_txin u ON (txin.txin_id = u.txin_id)
             WHERE bt.block_id = ?""", (block_id,))
        return unlinked_count > 0

    def _get_block_ss_destroyed(store, block_id, nTime, tx_ids):
        block_ss_destroyed = 0
        for tx_id in tx_ids:
            destroyed = int(store.selectrow("""
                SELECT COALESCE(SUM(txout_approx.txout_approx_value *
                                    (? - b.block_nTime)), 0)
                  FROM block_txin bti
                  JOIN txin ON (bti.txin_id = txin.txin_id)
                  JOIN txout_approx ON (txin.txout_id = txout_approx.txout_id)
                  JOIN block_tx obt ON (txout_approx.tx_id = obt.tx_id)
                  JOIN block b ON (obt.block_id = b.block_id)
                 WHERE bti.block_id = ? AND txin.tx_id = ?""",
                                            (nTime, block_id, tx_id))[0])
            block_ss_destroyed += destroyed
        return block_ss_destroyed

    # Propagate cumulative values to descendant blocks.  Return info
    # about the longest chains containing b.  The returned dictionary
    # is keyed by the chain_id of a chain whose validation policy b
    # satisfies.  Each value is a pair (block, work) where block is
    # the best block descended from b in the given chain, and work is
    # the sum of orphan_work and the work between b and block.  Only
    # chains in chain_mask are considered.  Even if no known chain
    # contains b, this routine populates any descendant blocks'
    # cumulative statistics that are known for b and returns an empty
    # dictionary.
    def adopt_orphans(store, b, orphan_work, chain_ids, chain_mask):

        # XXX As originally written, this function occasionally hit
        # Python's recursion limit.  I am rewriting it iteratively
        # with minimal changes, hence the odd style.  Guido is
        # particularly unhelpful here, rejecting even labeled loops.

        ret = [None]
        def receive(x):
            ret[0] = x
        def doit():
            store._adopt_orphans_1(stack)
        stack = [receive, chain_mask, chain_ids, orphan_work, b, doit]
        while stack:
            stack.pop()()
        return ret[0]

    def _adopt_orphans_1(store, stack):
        def doit():
            store._adopt_orphans_1(stack)
        def continuation(x):
            store._adopt_orphans_2(stack, x)
        def didit():
            ret = stack.pop()
            stack.pop()(ret)

        b = stack.pop()
        orphan_work = stack.pop()
        chain_ids = stack.pop()
        chain_mask = stack.pop()
        ret = {}
        stack += [ ret, didit ]

        block_id = b['block_id']
        height = None if b['height'] is None else int(b['height'] + 1)

        # If adding block b, b will not yet be in chain_candidate, so
        # we rely on the chain_ids argument.  If called recursively,
        # look up chain_ids in chain_candidate.
        if not chain_ids:
            if chain_mask:
                chain_mask = chain_mask.intersection(
                    store.find_chains_containing_block(block_id))
            chain_ids = chain_mask

        for chain_id in chain_ids:
            ret[chain_id] = (b, orphan_work)

        for row in store.selectall("""
            SELECT bn.next_block_id, b.block_nBits,
                   b.block_value_out, b.block_value_in, b.block_nTime,
                   b.block_total_satoshis
              FROM block_next bn
              JOIN block b ON (bn.next_block_id = b.block_id)
             WHERE bn.block_id = ?""", (block_id,)):
            next_id, nBits, value_out, value_in, nTime, satoshis = row
            nBits = int(nBits)
            nTime = int(nTime)
            satoshis = None if satoshis is None else int(satoshis)
            new_work = util.calculate_work(orphan_work, nBits)

            if b['chain_work'] is None:
                chain_work = None
            else:
                chain_work = b['chain_work'] + new_work - orphan_work

            if value_in is None:
                value, count1, count2 = store.selectrow("""
                    SELECT SUM(txout.txout_value),
                           COUNT(1),
                           COUNT(txout.txout_value)
                      FROM block_tx bt
                      JOIN txin ON (bt.tx_id = txin.tx_id)
                      LEFT JOIN txout ON (txout.txout_id = txin.txout_id)
                     WHERE bt.block_id = ?""", (next_id,))
                if count1 == count2 + 1:
                    value_in = int(value)
                else:
                    store.log.warning(
                        "not updating block %d value_in: %s != %s + 1",
                        next_id, repr(count1), repr(count2))
            else:
                value_in = int(value_in)
            generated = None if value_in is None else int(value_out - value_in)

            if b['seconds'] is None:
                seconds = None
                total_ss = None
            else:
                new_seconds = nTime - b['nTime']
                seconds = b['seconds'] + new_seconds
                if b['total_ss'] is None or b['satoshis'] is None:
                    total_ss = None
                else:
                    total_ss = b['total_ss'] + new_seconds * b['satoshis']

            if satoshis < 0 and b['satoshis'] is not None and \
                    b['satoshis'] >= 0 and generated is not None:
                satoshis += 1 + b['satoshis'] + generated

            if height is None or height < 2:
                search_block_id = None
            else:
                search_block_id = store.get_block_id_at_height(
                    util.get_search_height(height), int(block_id))

            store.sql("""
                UPDATE block
                   SET block_height = ?,
                       block_chain_work = ?,
                       block_value_in = ?,
                       block_total_seconds = ?,
                       block_total_satoshis = ?,
                       block_total_ss = ?,
                       search_block_id = ?
                 WHERE block_id = ?""",
                      (height, store.binin_int(chain_work, WORK_BITS),
                       store.intin(value_in),
                       store.intin(seconds), store.intin(satoshis),
                       store.intin(total_ss), search_block_id,
                       next_id))

            ss = None

            if height is not None:
                store.sql("""
                    UPDATE chain_candidate SET block_height = ?
                     WHERE block_id = ?""",
                    (height, next_id))

                store._populate_block_txin(int(next_id))

                if b['ss'] is None or store._has_unlinked_txins(next_id):
                    pass
                else:
                    tx_ids = map(
                        lambda row: row[0],
                        store.selectall("""
                            SELECT tx_id
                              FROM block_tx
                             WHERE block_id = ?""", (next_id,)))
                    destroyed = store._get_block_ss_destroyed(
                        next_id, nTime, tx_ids)
                    ss = b['ss'] + b['satoshis'] * (nTime - b['nTime']) \
                        - destroyed

                    store.sql("""
                        UPDATE block
                           SET block_satoshi_seconds = ?,
                               block_ss_destroyed = ?
                         WHERE block_id = ?""",
                              (store.intin(ss),
                               store.intin(destroyed),
                               next_id))

                if store.use_firstbits:
                    for (addr_vers,) in store.selectall("""
                        SELECT c.chain_address_version
                          FROM chain c
                          JOIN chain_candidate cc ON (c.chain_id = cc.chain_id)
                         WHERE cc.block_id = ?""", (next_id,)):
                        store.do_vers_firstbits(addr_vers, int(next_id))

            nb = {
                "block_id": next_id,
                "height": height,
                "chain_work": chain_work,
                "nTime": nTime,
                "seconds": seconds,
                "satoshis": satoshis,
                "total_ss": total_ss,
                "ss": ss}

            stack += [ret, continuation,
                      chain_mask, None, new_work, nb, doit]

    def _adopt_orphans_2(store, stack, next_ret):
        ret = stack.pop()
        for chain_id in ret.keys():
            pair = next_ret[chain_id]
            if pair and pair[1] > ret[chain_id][1]:
                ret[chain_id] = pair

    def _export_scriptPubKey(store, txout, chain, scriptPubKey):
        """In txout, set script_type, address_version, binaddr, and for multisig, required_signatures."""

        if scriptPubKey is None:
            txout['script_type'] = None
            txout['binaddr'] = None
            txout['address_version'] = None
            return

        script_type, data = chain.parse_txout_script(scriptPubKey)
        txout['script_type'] = script_type
        txout['address_version'] = chain.address_version

        if script_type == Chain.SCRIPT_TYPE_PUBKEY:
            txout['binaddr'] = chain.pubkey_hash(data)
        elif script_type == Chain.SCRIPT_TYPE_ADDRESS:
            txout['binaddr'] = data
        elif script_type == Chain.SCRIPT_TYPE_P2SH:
            txout['address_version'] = chain.script_addr_vers
            txout['binaddr'] = data
        elif script_type == Chain.SCRIPT_TYPE_MULTISIG:
            txout['required_signatures'] = data['m']
            txout['binaddr'] = chain.pubkey_hash(scriptPubKey)
            txout['subbinaddr'] = [
                chain.pubkey_hash(pubkey)
                for pubkey in data['pubkeys']
                ]
        elif script_type == Chain.SCRIPT_TYPE_BURN:
            txout['binaddr'] = NULL_PUBKEY_HASH
        # MULTICHAIN START
        elif script_type == Chain.SCRIPT_TYPE_MULTICHAIN:
            txout['binaddr'] = data
        elif script_type == Chain.SCRIPT_TYPE_MULTICHAIN_P2SH:
            txout['address_version'] = chain.script_addr_vers
            txout['binaddr'] = data
        elif script_type == Chain.SCRIPT_TYPE_MULTICHAIN_ENTITY_PERMISSION:
            txout['binaddr'] = data.get('pubkey_hash')
        # MULTICHAIN END
        else:
            txout['binaddr'] = None

    def export_block(store, chain=None, block_hash=None, block_number=None):
        """
        Return a dict with the following:

        * chain_candidates[]
            * chain
            * in_longest
        * chain_satoshis
        * chain_satoshi_seconds
        * chain_work
        * fees
        * generated
        * hash
        * hashMerkleRoot
        * hashPrev
        * height
        * nBits
        * next_block_hashes
        * nNonce
        * nTime
        * satoshis_destroyed
        * satoshi_seconds
        * transactions[]
            * fees
            * hash
            * in[]
                * address_version
                * binaddr
                * value
            * out[]
                * address_version
                * binaddr
                * value
            * size
        * value_out
        * version

        Additionally, for multisig inputs and outputs:

        * subbinaddr[]
        * required_signatures

        Additionally, for proof-of-stake chains:

        * is_proof_of_stake
        * proof_of_stake_generated
        """

        if block_number is None and block_hash is None:
            raise ValueError("export_block requires either block_hash or block_number")

        where = []
        bind = []

        if chain is not None:
            where.append('chain_id = ?')
            bind.append(chain.id)

        if block_hash is not None:
            where.append('block_hash = ?')
            bind.append(store.hashin_hex(block_hash))

        if block_number is not None:
            where.append('block_height = ? AND in_longest = 1')
            bind.append(block_number)

        sql = """
            SELECT
                chain_id,
                in_longest,
                block_id,
                block_hash,
                block_version,
                block_hashMerkleRoot,
                block_nTime,
                block_nBits,
                block_nNonce,
                block_height,
                prev_block_hash,
                block_chain_work,
                block_value_in,
                block_value_out,
                block_total_satoshis,
                block_total_seconds,
                block_satoshi_seconds,
                block_total_ss,
                block_ss_destroyed,
                block_num_tx
              FROM chain_summary
             WHERE """ + ' AND '.join(where) + """
             ORDER BY
                in_longest DESC,
                chain_id DESC"""
        rows = store.selectall(sql, bind)

        if len(rows) == 0:
            return None

        row = rows[0][2:]
        def parse_cc(row):
            chain_id, in_longest = row[:2]
            return { "chain": store.get_chain_by_id(chain_id), "in_longest": in_longest }

        # Absent the chain argument, default to highest chain_id, preferring to avoid side chains.
        cc = map(parse_cc, rows)

        # "chain" may be None, but "found_chain" will not.
        found_chain = chain
        if found_chain is None:
            if len(cc) > 0:
                found_chain = cc[0]['chain']
            else:
                # Should not normally get here.
                found_chain = store.get_default_chain()

        (block_id, block_hash, block_version, hashMerkleRoot,
         nTime, nBits, nNonce, height,
         prev_block_hash, block_chain_work, value_in, value_out,
         satoshis, seconds, ss, total_ss, destroyed, num_tx) = (
            row[0], store.hashout_hex(row[1]), row[2],
            store.hashout_hex(row[3]), row[4], int(row[5]), row[6],
            row[7], store.hashout_hex(row[8]),
            store.binout_int(row[9]), int(row[10]), int(row[11]),
            None if row[12] is None else int(row[12]),
            None if row[13] is None else int(row[13]),
            None if row[14] is None else int(row[14]),
            None if row[15] is None else int(row[15]),
            None if row[16] is None else int(row[16]),
            int(row[17]),
            )

        next_hashes = [
            store.hashout_hex(hash) for hash, il in
            store.selectall("""
            SELECT DISTINCT n.block_hash, cc.in_longest
              FROM block_next bn
              JOIN block n ON (bn.next_block_id = n.block_id)
              JOIN chain_candidate cc ON (n.block_id = cc.block_id)
             WHERE bn.block_id = ?
             ORDER BY cc.in_longest DESC""",
                            (block_id,)) ]

        tx_ids = []
        txs = {}
        block_out = 0
        block_in = 0

        for row in store.selectall("""
            SELECT tx_id, tx_hash, tx_size, txout_value, txout_scriptPubKey
              FROM txout_detail
             WHERE block_id = ?
             ORDER BY tx_pos, txout_pos
        """, (block_id,)):
            tx_id, tx_hash, tx_size, txout_value, scriptPubKey = (
                row[0], row[1], row[2], int(row[3]), store.binout(row[4]))
            tx = txs.get(tx_id)
            if tx is None:
                tx_ids.append(tx_id)
                txs[tx_id] = {
                    "hash": store.hashout_hex(tx_hash),
                    "total_out": 0,
                    "total_in": 0,
                    "out": [],
                    "in": [],
                    "size": int(tx_size),
                    }
                tx = txs[tx_id]
            tx['total_out'] += txout_value
            block_out += txout_value

            txout = { 'value': txout_value }
            store._export_scriptPubKey(txout, found_chain, scriptPubKey)
            tx['out'].append(txout)

        for row in store.selectall("""
            SELECT tx_id, txin_value, txin_scriptPubKey
              FROM txin_detail
             WHERE block_id = ?
             ORDER BY tx_pos, txin_pos
        """, (block_id,)):
            tx_id, txin_value, scriptPubKey = (
                row[0], 0 if row[1] is None else int(row[1]),
                store.binout(row[2]))
            tx = txs.get(tx_id)
            if tx is None:
                # Strange, inputs but no outputs?
                tx_ids.append(tx_id)
                tx_hash, tx_size = store.selectrow("""
                    SELECT tx_hash, tx_size FROM tx WHERE tx_id = ?""",
                                           (tx_id,))
                txs[tx_id] = {
                    "hash": store.hashout_hex(tx_hash),
                    "total_out": 0,
                    "total_in": 0,
                    "out": [],
                    "in": [],
                    "size": int(tx_size),
                    }
                tx = txs[tx_id]
            tx['total_in'] += txin_value
            block_in += txin_value

            txin = { 'value': txin_value }
            store._export_scriptPubKey(txin, found_chain, scriptPubKey)
            tx['in'].append(txin)

        generated = block_out - block_in
        coinbase_tx = txs[tx_ids[0]]
        coinbase_tx['fees'] = 0
        block_fees = coinbase_tx['total_out'] - generated

        b = {
            'chain_candidates':      cc,
            'chain_satoshis':        satoshis,
            'chain_satoshi_seconds': total_ss,
            'chain_work':            block_chain_work,
            'fees':                  block_fees,
            'generated':             generated,
            'hash':                  block_hash,
            'hashMerkleRoot':        hashMerkleRoot,
            'hashPrev':              prev_block_hash,
            'height':                height,
            'nBits':                 nBits,
            'next_block_hashes':     next_hashes,
            'nNonce':                nNonce,
            'nTime':                 nTime,
            'satoshis_destroyed':    destroyed,
            'satoshi_seconds':       ss,
            'transactions':          [txs[tx_id] for tx_id in tx_ids],
            'value_out':             block_out,
            'version':               block_version,
            }

        is_stake_chain = chain is not None and chain.has_feature('nvc_proof_of_stake')
        if is_stake_chain:
            # Proof-of-stake display based loosely on CryptoManiac/novacoin and
            # http://nvc.cryptocoinexplorer.com.
            b['is_proof_of_stake'] = len(tx_ids) > 1 and coinbase_tx['total_out'] == 0

        for tx_id in tx_ids[1:]:
            tx = txs[tx_id]
            tx['fees'] = tx['total_in'] - tx['total_out']

        if is_stake_chain and b['is_proof_of_stake']:
            b['proof_of_stake_generated'] = -txs[tx_ids[1]]['fees']
            txs[tx_ids[1]]['fees'] = 0
            b['fees'] += b['proof_of_stake_generated']

        return b

    def tx_find_id_and_value(store, tx, is_coinbase, check_only=False):
        row = store.selectrow("""
            SELECT tx.tx_id, SUM(txout.txout_value), SUM(
                       CASE WHEN txout.pubkey_id > 0 THEN txout.txout_value
                            ELSE 0 END)
              FROM tx
              LEFT JOIN txout ON (tx.tx_id = txout.tx_id)
             WHERE tx_hash = ?
             GROUP BY tx.tx_id""",
                              (store.hashin(tx['hash']),))
        if row:
            if check_only:
                 # Don't update tx, saves a statement when all we care is
                 # whenever tx_id is in store
                 return row[0]

            tx_id, value_out, undestroyed = row
            value_out = 0 if value_out is None else int(value_out)
            undestroyed = 0 if undestroyed is None else int(undestroyed)
            count_in, value_in = store.selectrow("""
                SELECT COUNT(1), SUM(prevout.txout_value)
                  FROM txin
                  JOIN txout prevout ON (txin.txout_id = prevout.txout_id)
                 WHERE txin.tx_id = ?""", (tx_id,))
            if (count_in or 0) < len(tx['txIn']):
                value_in = 0 if is_coinbase else None
            tx['value_in'] = None if value_in is None else int(value_in)
            tx['value_out'] = value_out
            tx['value_destroyed'] = value_out - undestroyed
            return tx_id

        return None

    def import_tx(store, tx, is_coinbase, chain):
        tx_id = store.new_id("tx")
        dbhash = store.hashin(tx['hash'])

        #print "import_tx: {}".format(util.long_hex(tx['hash'][::-1]))
                
        if 'size' not in tx:
            tx['size'] = len(tx['__data__'])

        store.sql("""
            INSERT INTO tx (tx_id, tx_hash, tx_version, tx_lockTime, tx_size)
            VALUES (?, ?, ?, ?, ?)""",
                  (tx_id, dbhash, store.intin(tx['version']),
                   store.intin(tx['lockTime']), tx['size']))

        # Import transaction outputs.
        tx['value_out'] = 0
        tx['value_destroyed'] = 0
        for pos in xrange(len(tx['txOut'])):
            txout = tx['txOut'][pos]
            tx['value_out'] += txout['value']
            txout_id = store.new_id("txout")

            pubkey_id = store.script_to_pubkey_id(chain, txout['scriptPubKey'])
            if pubkey_id is not None and pubkey_id <= 0:
                tx['value_destroyed'] += txout['value']

            store.sql("""
                INSERT INTO txout (
                    txout_id, tx_id, txout_pos, txout_value,
                    txout_scriptPubKey, pubkey_id
                ) VALUES (?, ?, ?, ?, ?, ?)""",
                      (txout_id, tx_id, pos, store.intin(txout['value']),
                       store.binin(txout['scriptPubKey']), pubkey_id))
            for row in store.selectall("""
                SELECT unlinked_txin.txin_id, tx_hash, txin_pos
                  FROM unlinked_txin LEFT JOIN txin ON (unlinked_txin.txin_id = txin.txin_id) LEFT JOIN tx ON (txin.tx_id = tx.tx_id)
                 WHERE txout_tx_hash = ?
                   AND txout_pos = ?""", (dbhash, pos)):
                (txin_id, spender_hash, spender_n) = row
                #print "Unlinked: id {} {},{} -> {},{} delete".format(txin_id, util.long_hex(tx['hash'][::-1]), pos, store.hashout_hex(spender_hash), spender_n)
                store.spent_txout_assets(tx['hash'], pos, chain, store.hashout(spender_hash), spender_n) # MULTICHAIN - deduct asset quantities now if couldn't find before
                store.sql("UPDATE txin SET txout_id = ? WHERE txin_id = ?",
                          (txout_id, txin_id))
                store.sql("DELETE FROM unlinked_txin WHERE txin_id = ?",
                          (txin_id,))

# MULTICHAIN START
            binscript = store.binout(txout['scriptPubKey'])
            script_type, data = chain.parse_txout_script(binscript)
            if pubkey_id is not None and script_type in [Chain.SCRIPT_TYPE_MULTICHAIN, Chain.SCRIPT_TYPE_MULTICHAIN_P2SH]:
                data = util.get_multichain_op_drop_data(binscript)
                if data is not None:
                    opdrop_type, val = util.parse_op_drop_data(data, chain)
                    if opdrop_type==util.OP_DROP_TYPE_ISSUE_ASSET:
                        (prefix, ) = struct.unpack("<H", dbhash[0:2])

                        row = store.selectrow("""
                             SELECT asset_id FROM asset WHERE asset.prefix = ?
                             """, (prefix,))
                        if row is None: # the usual case
                            new_asset_id = store.new_id("asset")
                            store.sql("""
                                INSERT INTO asset (asset_id, tx_id, chain_id, name, multiplier, issue_qty, prefix)
                                VALUES (?, ?, ?, ?, ?, ?, ?)""",
                                (new_asset_id, tx_id, chain.id, store.binin(""), 0, val, prefix ))
                        else: # if we are updating a half-accurate record
                            new_asset_id = row[0]
                            store.sql("""
                                UPDATE asset SET tx_id = ?, issue_qty = ?
                                WHERE asset_id = ?
                                """,
                                (tx_id, val, new_asset_id))

                        store.update_asset_address_balance(new_asset_id, pubkey_id, val, tx['hash']);

                        store.sql("""
                            INSERT INTO asset_txid (asset_id, tx_id, txout_pos)
                            VALUES (?, ?, ?)""",
                            (new_asset_id, tx_id, pos))
                        # txout['scriptPubKey'] or binscript work fine here
                        vers = chain.address_version
                        the_script_type, pubkey_hash = chain.parse_txout_script(txout['scriptPubKey'])
                        checksum = chain.address_checksum
                        if checksum is None:
                            address = util.hash_to_address(vers, pubkey_hash)
                        else:
                            address = util.hash_to_address_multichain(vers, pubkey_hash, checksum)
                        #print "New asset issued to address: {}, balance {}".format(address, val)
                    elif opdrop_type==util.OP_DROP_TYPE_SEND_ASSET or opdrop_type==util.OP_DROP_TYPE_ISSUE_MORE_ASSET:
                        msgparts = []
                        for dict in val:
                            quantity = dict['quantity']
                            assetref = dict['assetref']
                            if chain.protocol_version < 10007:
                                prefix = int( assetref.split('-')[-1] )
                            else:
                                (prefix, ) = struct.unpack("<H", binascii.unhexlify(assetref)[0:2])

                            vers = chain.address_version
                            the_script_type, pubkey_hash = chain.parse_txout_script(txout['scriptPubKey'])
                            checksum = chain.address_checksum
                            if checksum is None:
                                address = util.hash_to_address(vers, pubkey_hash)
                            else:
                                address = util.hash_to_address_multichain(vers, pubkey_hash, checksum)
                            
                            asset_id=store.prefix_to_assetid_or_new(prefix, chain)
                            store.update_asset_address_balance(asset_id, pubkey_id, quantity, tx['hash']);

                            store.sql("""
                                INSERT INTO asset_txid (asset_id, tx_id, txout_pos)
                                VALUES (?,?,?)""",
                            (asset_id, tx_id, pos))
                            
                    elif opdrop_type==util.OP_DROP_TYPE_PERMISSION:
                        #print 'Permissions command detected'
                        pass
            elif pubkey_id is None and script_type is Chain.SCRIPT_TYPE_MULTICHAIN_OP_RETURN:
                opreturn_type, val = util.parse_op_return_data(data, chain)
                # Extract mandatory metadata and update asset column
                # Legacy protocol 10006
                if opreturn_type==util.OP_RETURN_TYPE_ISSUE_ASSET:
                    store.sql("""
                        UPDATE asset
                           SET name = ?, multiplier = ?
                         WHERE tx_id = ?
                         """, (unicode(val['name'], 'latin-1'), val['multiplier'], tx_id))
                    store.sql("""
                    INSERT INTO asset_txid (asset_id, tx_id, txout_pos)
                    VALUES ( (SELECT asset_id FROM asset WHERE tx_id = ? AND name = ?) , ?, ?)""",
                    (tx_id, unicode(val['name'], 'latin-1'), tx_id, pos))
            elif pubkey_id is None and script_type is Chain.SCRIPT_TYPE_MULTICHAIN_SPKN:
                # Protocol 10007
                opdrop_type, val = util.parse_op_drop_data(data, chain)
                if opdrop_type==util.OP_DROP_TYPE_SPKN_NEW_ISSUE:
                    store.sql("""
                         UPDATE asset
                            SET name = ?, multiplier = ?
                          WHERE tx_id = ?
                          """, (unicode(val.get('Asset Name',''), 'latin-1'), val.get('Quantity Multiple',1), tx_id))
                    store.sql("""
                         INSERT INTO asset_txid (asset_id, tx_id, txout_pos)
                         VALUES ( (SELECT asset_id FROM asset WHERE tx_id = ? AND name = ?) , ?, ?)""",
                         (tx_id, unicode(val.get('Asset Name',''), 'latin-1'), tx_id, pos))

# MULTICHAIN END

        # Import transaction inputs.
        tx['value_in'] = 0
        tx['unlinked_count'] = 0
        for pos in xrange(len(tx['txIn'])):
            txin = tx['txIn'][pos]
            txin_id = store.new_id("txin")

            if is_coinbase:
                txout_id = None
            else:
                txout_id, value = store.lookup_txout(
                    txin['prevout_hash'], txin['prevout_n'])
                if value is None:
                    tx['value_in'] = None
                elif tx['value_in'] is not None:
                    tx['value_in'] += value

            store.sql("""
                INSERT INTO txin (
                    txin_id, tx_id, txin_pos, txout_id""" + (""",
                    txin_scriptSig, txin_sequence""" if store.keep_scriptsig
                                                             else "") + """
                ) VALUES (?, ?, ?, ?""" + (", ?, ?" if store.keep_scriptsig
                                           else "") + """)""",
                      (txin_id, tx_id, pos, txout_id,
                       store.binin(txin['scriptSig']),
                       store.intin(txin['sequence'])) if store.keep_scriptsig
                      else (txin_id, tx_id, pos, txout_id))
            
            if not is_coinbase and txout_id is None:
                tx['unlinked_count'] += 1
                store.sql("""
                    INSERT INTO unlinked_txin (
                        txin_id, txout_tx_hash, txout_pos
                    ) VALUES (?, ?, ?)""",
                          (txin_id, store.hashin(txin['prevout_hash']),
                           store.intin(txin['prevout_n'])))
                #print "Unlinked: id {} {},{} -> {},{} insert".format(txin_id,
                #    util.long_hex(txin['prevout_hash'][::-1]), txin['prevout_n'], util.long_hex(tx['hash'][::-1]), pos)

# MULTICHAIN START
            if txout_id is not None:
                store.spent_txout_assets(txin['prevout_hash'], txin['prevout_n'], chain, tx['hash'], pos)
# MULTICHAIN END

        # XXX Could populate PUBKEY.PUBKEY with txin scripts...
        # or leave that to an offline process.  Nothing in this program
        # requires them.
        return tx_id

# MULTICHAIN START
    def spent_txout_assets(store, prevout_hash, prevout_n, chain, spender_hash, spender_n):
        binscript = store.lookup_txout_scriptpubkey(prevout_hash, prevout_n)

        #if binscript is None:
        #    print "Unlinked error: hash {} vout {}".format(util.long_hex(prevout_hash[::-1]), prevout_n)
        
        if binscript is not None:
            spent_tx_hash = store.hashout(prevout_hash)     # reverse out, otherwise it is backwards
            vers = chain.address_version
            the_script_type, data = chain.parse_txout_script(binscript)     # data is usually the pubkey_hash but could be dict

            if the_script_type is Chain.SCRIPT_TYPE_MULTICHAIN_ENTITY_PERMISSION:
                pubkey_hash = data['pubkey_hash']
            else:
                pubkey_hash = data

            if the_script_type is Chain.SCRIPT_TYPE_MULTICHAIN_P2SH:
                vers = chain.script_addr_vers
            checksum = chain.address_checksum
            if checksum is None:
                address = util.hash_to_address(vers, pubkey_hash)
            else:
                address = util.hash_to_address_multichain(vers, pubkey_hash, checksum)
            pubkey_id = store.pubkey_hash_to_id(pubkey_hash, 0)

            if the_script_type in [Chain.SCRIPT_TYPE_MULTICHAIN, Chain.SCRIPT_TYPE_MULTICHAIN_P2SH]:
                data = util.get_multichain_op_drop_data(binscript)
                if data is not None:
                    opdrop_type, val = util.parse_op_drop_data(data, chain)
                    if opdrop_type==util.OP_DROP_TYPE_ISSUE_ASSET:
                        (prefix, ) = struct.unpack("<H", spent_tx_hash[0:2])
                        
                        asset_id=store.prefix_to_assetid_or_new(prefix, chain)
                        store.update_asset_address_balance(asset_id, pubkey_id, -val, spender_hash)

                    elif opdrop_type in [util.OP_DROP_TYPE_SEND_ASSET, util.OP_DROP_TYPE_ISSUE_MORE_ASSET]:
                        # Spending sent tx or issue more tx
                        for dict in val:
                            quantity = dict['quantity']
                            assetref = dict['assetref']
                            if chain.protocol_version < 10007:
                                prefix = int( assetref.split('-')[-1] )
                            else:
                                (prefix, ) = struct.unpack("<H", binascii.unhexlify(assetref)[0:2])
                                # If txid begins 5484... the prefix is 0x8454 in decimal.
                                # x-y-zzzz  where zzzz = 33876

                            asset_id=store.prefix_to_assetid_or_new(prefix, chain)
                            store.update_asset_address_balance(asset_id, pubkey_id, -quantity, spender_hash)

                    elif opdrop_type==util.OP_DROP_TYPE_PERMISSION:
                        #print 'Spending tx with Permissions command'
                        pass
                        
    def prefix_to_assetid_or_new(store, prefix, chain):
        row = store.selectrow("""
             SELECT asset_id FROM asset WHERE asset.prefix = ?
             """, (prefix,))
        if row is None: # if we get unlucky and this comes before asset issuance, make a half-accurate record that is updated later
            asset_id = store.new_id("asset")
            store.sql("""
                INSERT INTO asset (asset_id, tx_id, chain_id, name, multiplier, issue_qty, prefix)
                VALUES (?, ?, ?, ?, ?, ?, ?)""",
                (asset_id, 1, chain.id, store.binin(""), 0, 0, prefix )) # fake most field values
        else:
            asset_id = row[0]
        return asset_id
    
    def update_asset_address_balance(store, asset_id, pubkey_id, quantity, tx_hash):
        store.sql("""
            INSERT IGNORE INTO asset_address_balance (asset_id, pubkey_id, balance)
            VALUES (?,?,0)""",
        (asset_id, pubkey_id))
        store.sql("""
            UPDATE asset_address_balance
               SET balance = balance + ?
             WHERE pubkey_id = ? AND asset_id =?
             """, (quantity, pubkey_id, asset_id))
        #print "BAL: {} pubkey {} val {}".format(util.long_hex(tx_hash[::-1]), pubkey_id, quantity) 
        
# MULTICHAIN END
    
    def import_and_commit_tx(store, tx, is_coinbase, chain):
        try:
            tx_id = store.import_tx(tx, is_coinbase, chain)
            store.commit()

        except store.dbmodule.DatabaseError:
            store.rollback()
            # Violation of tx_hash uniqueness?
            tx_id = store.tx_find_id_and_value(tx, is_coinbase)
            if not tx_id:
                raise

        return tx_id

    def maybe_import_binary_tx(store, chain_name, binary_tx):
        if chain_name is None:
            chain = store.get_default_chain()
        else:
            chain = store.get_chain_by_name(chain_name)

        tx_hash = chain.transaction_hash(binary_tx)

        (count,) = store.selectrow(
            "SELECT COUNT(1) FROM tx WHERE tx_hash = ?",
            (store.hashin(tx_hash),))

        if count == 0:
            tx = chain.parse_transaction(binary_tx)
            tx['hash'] = tx_hash
            store.import_tx(tx, chain.is_coinbase_tx(tx), chain)
            store.imported_bytes(tx['size'])

    def export_tx(store, tx_id=None, tx_hash=None, decimals=8, format="api", chain=None):
        """Return a dict as seen by /rawtx or None if not found."""

        # TODO: merge _export_tx_detail with export_tx.
        if format == 'browser':
            return store._export_tx_detail(tx_hash, chain=chain)

        tx = {}
        is_bin = format == "binary"

        if tx_id is not None:
            row = store.selectrow("""
                SELECT tx_hash, tx_version, tx_lockTime, tx_size
                  FROM tx
                 WHERE tx_id = ?
            """, (tx_id,))
            if row is None:
                return None
            tx['hash'] = store.hashout_hex(row[0])

        elif tx_hash is not None:
            row = store.selectrow("""
                SELECT tx_id, tx_version, tx_lockTime, tx_size
                  FROM tx
                 WHERE tx_hash = ?
            """, (store.hashin_hex(tx_hash),))
            if row is None:
                return None
            tx['hash'] = tx_hash.decode('hex')[::-1] if is_bin else tx_hash
            tx_id = row[0]

        else:
            raise ValueError("export_tx requires either tx_id or tx_hash.")

        tx['version' if is_bin else 'ver']        = int(row[1])
        tx['lockTime' if is_bin else 'lock_time'] = int(row[2])
        tx['size'] = int(row[3])

        txins = []
        tx['txIn' if is_bin else 'in'] = txins
        for row in store.selectall("""
            SELECT
                COALESCE(tx.tx_hash, uti.txout_tx_hash),
                COALESCE(txout.txout_pos, uti.txout_pos)""" + (""",
                txin_scriptSig,
                txin_sequence""" if store.keep_scriptsig else "") + """
            FROM txin
            LEFT JOIN txout ON (txin.txout_id = txout.txout_id)
            LEFT JOIN tx ON (txout.tx_id = tx.tx_id)
            LEFT JOIN unlinked_txin uti ON (txin.txin_id = uti.txin_id)
            WHERE txin.tx_id = ?
            ORDER BY txin.txin_pos""", (tx_id,)):
            prevout_hash = row[0]
            prevout_n = None if row[1] is None else int(row[1])
            if is_bin:
                txin = {
                    'prevout_hash': store.hashout(prevout_hash),
                    'prevout_n': prevout_n}
            else:
                if prevout_hash is None:
                    prev_out = {
                        'hash': "0" * 64,  # XXX should store this?
                        'n': 0xffffffff}   # XXX should store this?
                else:
                    prev_out = {
                        'hash': store.hashout_hex(prevout_hash),
                        'n': prevout_n}
                txin = {'prev_out': prev_out}
            if store.keep_scriptsig:
                scriptSig = row[2]
                sequence = row[3]
                if is_bin:
                    txin['scriptSig'] = store.binout(scriptSig)
                else:
                    txin['raw_scriptSig'] = store.binout_hex(scriptSig)
                txin['sequence'] = None if sequence is None else int(sequence)
            txins.append(txin)

        txouts = []
        tx['txOut' if is_bin else 'out'] = txouts
        for satoshis, scriptPubKey in store.selectall("""
            SELECT txout_value, txout_scriptPubKey
              FROM txout
             WHERE tx_id = ?
            ORDER BY txout_pos""", (tx_id,)):

            if is_bin:
                txout = {
                    'value': int(satoshis),
                    'scriptPubKey': store.binout(scriptPubKey)}
            else:
                coin = 10 ** decimals
                satoshis = int(satoshis)
                integer = satoshis / coin
                frac = satoshis % coin
                txout = {
                    'value': ("%%d.%%0%dd" % (decimals,)) % (integer, frac),
                    'raw_scriptPubKey': store.binout_hex(scriptPubKey)}
            txouts.append(txout)

        if not is_bin:
            tx['vin_sz'] = len(txins)
            tx['vout_sz'] = len(txouts)

        return tx

    def _export_tx_detail(store, tx_hash, chain):
        try:
            dbhash = store.hashin_hex(tx_hash)
        except TypeError:
            raise MalformedHash()

        row = store.selectrow("""
            SELECT tx_id, tx_version, tx_lockTime, tx_size
              FROM tx
             WHERE tx_hash = ?
        """, (dbhash,))
        if row is None:
            return None

        tx_id = int(row[0])
        tx = {
            'hash': tx_hash,
            'version': int(row[1]),
            'lockTime': int(row[2]),
            'size': int(row[3]),
            }

        def parse_tx_cc(row):
            return {
                'chain': store.get_chain_by_id(row[0]),
                'in_longest': int(row[1]),
                'block_nTime': int(row[2]),
                'block_height': None if row[3] is None else int(row[3]),
                'block_hash': store.hashout_hex(row[4]),
                'tx_pos': int(row[5])
                }

        tx['chain_candidates'] = map(parse_tx_cc, store.selectall("""
            SELECT cc.chain_id, cc.in_longest,
                   b.block_nTime, b.block_height, b.block_hash,
                   block_tx.tx_pos
              FROM chain_candidate cc
              JOIN block b ON (b.block_id = cc.block_id)
              JOIN block_tx ON (block_tx.block_id = b.block_id)
             WHERE block_tx.tx_id = ?
             ORDER BY cc.chain_id, cc.in_longest DESC, b.block_hash
        """, (tx_id,)))

        if chain is None:
            if len(tx['chain_candidates']) > 0:
                chain = tx['chain_candidates'][0]['chain']
            else:
                chain = store.get_default_chain()

        def parse_row(row):
            pos, script, value, o_hash, o_pos = row[:5]
            script = store.binout(script)
            scriptPubKey = store.binout(row[5]) if len(row) >5 else script

            ret = {
                "pos": int(pos),
                "binscript": script,
                "value": None if value is None else int(value),
                "o_hash": store.hashout_hex(o_hash),
                "o_pos": None if o_pos is None else int(o_pos),
                }
            store._export_scriptPubKey(ret, chain, scriptPubKey)
# MULTICHAIN START
            ret['multichain_scriptPubKey'] = scriptPubKey if len(row) > 5 else None
# MULTICHAIN END
            return ret

        # XXX Unneeded outer join.
        tx['in'] = map(parse_row, store.selectall("""
            SELECT
                txin.txin_pos""" + (""",
                txin.txin_scriptSig""" if store.keep_scriptsig else """,
                NULL""") + """,
                txout.txout_value,
                COALESCE(prevtx.tx_hash, u.txout_tx_hash),
                COALESCE(txout.txout_pos, u.txout_pos),
                txout.txout_scriptPubKey
              FROM txin
              LEFT JOIN txout ON (txout.txout_id = txin.txout_id)
              LEFT JOIN tx prevtx ON (txout.tx_id = prevtx.tx_id)
              LEFT JOIN unlinked_txin u ON (u.txin_id = txin.txin_id)
             WHERE txin.tx_id = ?
             ORDER BY txin.txin_pos
        """, (tx_id,)))

        # XXX Only one outer join needed.
        tx['out'] = map(parse_row, store.selectall("""
            SELECT
                txout.txout_pos,
                txout.txout_scriptPubKey,
                txout.txout_value,
                nexttx.tx_hash,
                txin.txin_pos
              FROM txout
              LEFT JOIN txin ON (txin.txout_id = txout.txout_id)
              LEFT JOIN tx nexttx ON (txin.tx_id = nexttx.tx_id)
             WHERE txout.tx_id = ?
             ORDER BY txout.txout_pos
        """, (tx_id,)))

        def sum_values(rows):
            ret = 0
            for row in rows:
                if row['value'] is None:
                    return None
                ret += row['value']
            return ret

        tx['value_in'] = sum_values(tx['in'])
        tx['value_out'] = sum_values(tx['out'])

        return tx

    def export_address_history(store, address, chain=None, max_rows=-1, types=frozenset(['direct', 'escrow'])):
        version, binaddr = util.decode_check_address_multichain(address)
        if binaddr is None:
            raise MalformedAddress("Invalid address")

        balance = {}
        received = {}
        sent = {}
        counts = [0, 0]
        chains = []

        def adj_balance(txpoint):
            chain = txpoint['chain']

            if chain.id not in balance:
                chains.append(chain)
                balance[chain.id] = 0
                received[chain.id] = 0
                sent[chain.id] = 0

            if txpoint['type'] == 'direct':
                value = txpoint['value']
                balance[chain.id] += value
                if txpoint['is_out']:
                    sent[chain.id] -= value
                else:
                    received[chain.id] += value
                counts[txpoint['is_out']] += 1

        dbhash = store.binin(binaddr)
        txpoints = []

        def parse_row(is_out, row_type, nTime, chain_id, height, blk_hash, tx_hash, pos, value, script=None):
            chain = store.get_chain_by_id(chain_id)
            txpoint = {
                'type':     row_type,
                'is_out':   int(is_out),
                'nTime':    int(nTime),
                'chain':    chain,
                'height':   int(height),
                'blk_hash': store.hashout_hex(blk_hash),
                'tx_hash':  store.hashout_hex(tx_hash),
                'pos':      int(pos),
                'value':    int(value),
                }
            if script is not None:
                store._export_scriptPubKey(txpoint, chain, store.binout(script))

            return txpoint

        def parse_direct_in(row):  return parse_row(True, 'direct', *row)
        def parse_direct_out(row): return parse_row(False, 'direct', *row)
        def parse_escrow_in(row):  return parse_row(True, 'escrow', *row)
        def parse_escrow_out(row): return parse_row(False, 'escrow', *row)

        def get_received(escrow):
            return store.selectall("""
                SELECT
                    b.block_nTime,
                    cc.chain_id,
                    b.block_height,
                    b.block_hash,
                    tx.tx_hash,
                    txin.txin_pos,
                    -prevout.txout_value""" + (""",
                    prevout.txout_scriptPubKey""" if escrow else "") + """
                  FROM chain_candidate cc
                  JOIN block b ON (b.block_id = cc.block_id)
                  JOIN block_tx ON (block_tx.block_id = b.block_id)
                  JOIN tx ON (tx.tx_id = block_tx.tx_id)
                  JOIN txin ON (txin.tx_id = tx.tx_id)
                  JOIN txout prevout ON (txin.txout_id = prevout.txout_id)""" + ("""
                  JOIN multisig_pubkey mp ON (mp.multisig_id = prevout.pubkey_id)""" if escrow else "") + """
                  JOIN pubkey ON (pubkey.pubkey_id = """ + ("mp" if escrow else "prevout") + """.pubkey_id)
                 WHERE pubkey.pubkey_hash = ?
                   AND cc.in_longest = 1""" + ("" if max_rows < 0 else """
                 LIMIT ?"""),
                          (dbhash,)
                          if max_rows < 0 else
                          (dbhash, max_rows + 1))

        def get_sent(escrow):
            return store.selectall("""
                SELECT
                    b.block_nTime,
                    cc.chain_id,
                    b.block_height,
                    b.block_hash,
                    tx.tx_hash,
                    txout.txout_pos,
                    txout.txout_value""" + (""",
                    txout.txout_scriptPubKey""" if escrow else "") + """
                  FROM chain_candidate cc
                  JOIN block b ON (b.block_id = cc.block_id)
                  JOIN block_tx ON (block_tx.block_id = b.block_id)
                  JOIN tx ON (tx.tx_id = block_tx.tx_id)
                  JOIN txout ON (txout.tx_id = tx.tx_id)""" + ("""
                  JOIN multisig_pubkey mp ON (mp.multisig_id = txout.pubkey_id)""" if escrow else "") + """
                  JOIN pubkey ON (pubkey.pubkey_id = """ + ("mp" if escrow else "txout") + """.pubkey_id)
                 WHERE pubkey.pubkey_hash = ?
                   AND cc.in_longest = 1""" + ("" if max_rows < 0 else """
                 LIMIT ?"""),
                          (dbhash, max_rows + 1)
                          if max_rows >= 0 else
                          (dbhash,))

        if 'direct' in types:
            in_rows = get_received(False)
            if len(in_rows) > max_rows >= 0:
                return None  # XXX Could still show address basic data.
            txpoints += map(parse_direct_in, in_rows)

            out_rows = get_sent(False)
            if len(out_rows) > max_rows >= 0:
                return None
            txpoints += map(parse_direct_out, out_rows)

        if 'escrow' in types:
            in_rows = get_received(True)
            if len(in_rows) > max_rows >= 0:
                return None
            txpoints += map(parse_escrow_in, in_rows)

            out_rows = get_sent(True)
            if len(out_rows) > max_rows >= 0:
                return None
            txpoints += map(parse_escrow_out, out_rows)

        def cmp_txpoint(p1, p2):
            return cmp(p1['nTime'], p2['nTime']) \
                or cmp(p1['is_out'], p2['is_out']) \
                or cmp(p1['height'], p2['height']) \
                or cmp(p1['chain'].name, p2['chain'].name)

        txpoints.sort(cmp_txpoint)

        for txpoint in txpoints:
            adj_balance(txpoint)

        hist = {
            'binaddr':  binaddr,
            'version':  version,
            'chains':   chains,
            'txpoints': txpoints,
            'balance':  balance,
            'sent':     sent,
            'received': received,
            'counts':   counts
            }

        # Show P2SH address components, if known.
        # XXX With some more work, we could find required_signatures.
        for (subbinaddr,) in store.selectall("""
            SELECT sub.pubkey_hash
              FROM multisig_pubkey mp
              JOIN pubkey top ON (mp.multisig_id = top.pubkey_id)
              JOIN pubkey sub ON (mp.pubkey_id = sub.pubkey_id)
             WHERE top.pubkey_hash = ?""", (dbhash,)):
            if 'subbinaddr' not in hist:
                hist['subbinaddr'] = []
            hist['subbinaddr'].append(store.binout(subbinaddr))

        return hist

    # Called to indicate that the given block has the correct magic
    # number and policy for the given chains.  Updates CHAIN_CANDIDATE
    # and CHAIN.CHAIN_LAST_BLOCK_ID as appropriate.
    def offer_block_to_chains(store, b, chain_ids):
        b['top'] = store.adopt_orphans(b, 0, chain_ids, chain_ids)
        for chain_id in chain_ids:
            store._offer_block_to_chain(b, chain_id)

    def _offer_block_to_chain(store, b, chain_id):
        if b['chain_work'] is None:
            in_longest = 0
        else:
            # Do we produce a chain longer than the current chain?
            # Query whether the new block (or its tallest descendant)
            # beats the current chain_last_block_id.  Also check
            # whether the current best is our top, which indicates
            # this block is in longest; this can happen in database
            # repair scenarios.
            top = b['top'][chain_id][0]
            row = store.selectrow("""
                SELECT b.block_id, b.block_height, b.block_chain_work
                  FROM block b, chain c
                 WHERE c.chain_id = ?
                   AND b.block_id = c.chain_last_block_id""", (chain_id,))
            if row:
                loser_id, loser_height, loser_work = row
                if loser_id != top['block_id'] and \
                        store.binout_int(loser_work) >= top['chain_work']:
                    row = None
            if row:
                # New longest chain.
                in_longest = 1
                to_connect = []
                to_disconnect = []
                winner_id = top['block_id']
                winner_height = top['height']
                while loser_height > winner_height:
                    to_disconnect.insert(0, loser_id)
                    loser_id = store.get_prev_block_id(loser_id)
                    loser_height -= 1
                while winner_height > loser_height:
                    to_connect.insert(0, winner_id)
                    winner_id = store.get_prev_block_id(winner_id)
                    winner_height -= 1
                loser_height = None
                while loser_id != winner_id:
                    to_disconnect.insert(0, loser_id)
                    loser_id = store.get_prev_block_id(loser_id)
                    to_connect.insert(0, winner_id)
                    winner_id = store.get_prev_block_id(winner_id)
                    winner_height -= 1
                for block_id in to_disconnect:
                    store.disconnect_block(block_id, chain_id)
                for block_id in to_connect:
                    store.connect_block(block_id, chain_id)

            elif b['hashPrev'] == store.get_chain_by_id(chain_id).genesis_hash_prev:
                in_longest = 1  # Assume only one genesis block per chain.  XXX
            else:
                in_longest = 0

        store.sql("""
            INSERT INTO chain_candidate (
                chain_id, block_id, in_longest, block_height
            ) VALUES (?, ?, ?, ?)""",
                  (chain_id, b['block_id'], in_longest, b['height']))

        if in_longest > 0:
            store.sql("""
                UPDATE chain
                   SET chain_last_block_id = ?
                 WHERE chain_id = ?""", (top['block_id'], chain_id))

        if store.use_firstbits and b['height'] is not None:
            (addr_vers,) = store.selectrow("""
                SELECT chain_address_version
                  FROM chain
                 WHERE chain_id = ?""", (chain_id,))
            store.do_vers_firstbits(addr_vers, b['block_id'])

    def offer_existing_block(store, hash, chain_id):
        block_row = store.selectrow("""
            SELECT block_id, block_height, block_chain_work,
                   block_nTime, block_total_seconds,
                   block_total_satoshis, block_satoshi_seconds,
                   block_total_ss
              FROM block
             WHERE block_hash = ?
        """, (store.hashin(hash),))

        if not block_row:
            return False

        if chain_id is None:
            return True

        # Block header already seen.  Don't import the block,
        # but try to add it to the chain.

        b = {
            "block_id":   block_row[0],
            "height":     block_row[1],
            "chain_work": store.binout_int(block_row[2]),
            "nTime":      block_row[3],
            "seconds":    block_row[4],
            "satoshis":   block_row[5],
            "ss":         block_row[6],
            "total_ss":   block_row[7]}

        if store.selectrow("""
            SELECT 1
              FROM chain_candidate
             WHERE block_id = ?
               AND chain_id = ?""",
                        (b['block_id'], chain_id)):
            store.log.info("block %d already in chain %d",
                           b['block_id'], chain_id)
        else:
            if b['height'] == 0:
                b['hashPrev'] = store.get_chain_by_id(chain_id).genesis_hash_prev
            else:
                b['hashPrev'] = 'dummy'  # Fool adopt_orphans.
            store.offer_block_to_chains(b, frozenset([chain_id]))

        return True

    def find_next_blocks(store, block_id):
        ret = []
        for row in store.selectall(
            "SELECT next_block_id FROM block_next WHERE block_id = ?",
            (block_id,)):
            ret.append(row[0])
        return ret

    def find_chains_containing_block(store, block_id):
        ret = []
        for row in store.selectall(
            "SELECT chain_id FROM chain_candidate WHERE block_id = ?",
            (block_id,)):
            ret.append(row[0])
        return frozenset(ret)

    def get_prev_block_id(store, block_id):
        return store.selectrow(
            "SELECT prev_block_id FROM block WHERE block_id = ?",
            (block_id,))[0]

    def disconnect_block(store, block_id, chain_id):
        store.sql("""
            UPDATE chain_candidate
               SET in_longest = 0
             WHERE block_id = ? AND chain_id = ?""",
                  (block_id, chain_id))

    def connect_block(store, block_id, chain_id):
        store.sql("""
            UPDATE chain_candidate
               SET in_longest = 1
             WHERE block_id = ? AND chain_id = ?""",
                  (block_id, chain_id))

    def lookup_txout(store, tx_hash, txout_pos):
        row = store.selectrow("""
            SELECT txout.txout_id, txout.txout_value
              FROM txout, tx
             WHERE txout.tx_id = tx.tx_id
               AND tx.tx_hash = ?
               AND txout.txout_pos = ?""",
                  (store.hashin(tx_hash), txout_pos))
        return (None, None) if row is None else (row[0], int(row[1]))

# MULTICHAIN START
    def lookup_txout_scriptpubkey(store, tx_hash, txout_pos):
        row = store.selectrow("""
            SELECT txout_scriptPubKey
              FROM txout, tx
             WHERE txout.tx_id = tx.tx_id
               AND tx.tx_hash = ?
               AND txout.txout_pos = ?""",
                  (store.hashin(tx_hash), txout_pos))
        return None if row is None else row[0]
# MULTICHAIN END

    def script_to_pubkey_id(store, chain, script):
        """Extract address and script type from transaction output script."""
        script_type, data = chain.parse_txout_script(script)

        if script_type in (Chain.SCRIPT_TYPE_ADDRESS, Chain.SCRIPT_TYPE_P2SH):
            return store.pubkey_hash_to_id(data)

# MULTICHAIN START
        if script_type == Chain.SCRIPT_TYPE_MULTICHAIN_P2SH:
            return store.pubkey_hash_to_id(data, PUBKEY_FLAGS_P2SH)

        if script_type == Chain.SCRIPT_TYPE_MULTICHAIN:
            return store.pubkey_hash_to_id(data)

        if script_type == Chain.SCRIPT_TYPE_MULTICHAIN_ENTITY_PERMISSION:
            return store.pubkey_hash_to_id(data['pubkey_hash'])
# MULTICHAIN END

        if script_type == Chain.SCRIPT_TYPE_PUBKEY:
            return store.pubkey_to_id(chain, data)

        if script_type == Chain.SCRIPT_TYPE_MULTISIG:
            script_hash = chain.script_hash(script)
            multisig_id = store._pubkey_id(script_hash, script)

            if not store.selectrow("SELECT 1 FROM multisig_pubkey WHERE multisig_id = ?", (multisig_id,)):
                for pubkey in set(data['pubkeys']):
                    pubkey_id = store.pubkey_to_id(chain, pubkey)
                    store.sql("""
                        INSERT INTO multisig_pubkey (multisig_id, pubkey_id)
                        VALUES (?, ?)""", (multisig_id, pubkey_id))
            return multisig_id

        if script_type == Chain.SCRIPT_TYPE_BURN:
            return PUBKEY_ID_NETWORK_FEE

        return None

    def pubkey_hash_to_id(store, pubkey_hash, flags=0):
        return store._pubkey_id(pubkey_hash, None, flags)

    def pubkey_to_id(store, chain, pubkey, flags=0):
        pubkey_hash = chain.pubkey_hash(pubkey)
        return store._pubkey_id(pubkey_hash, pubkey, flags)

    def _pubkey_id(store, pubkey_hash, pubkey, flags=0):
        dbhash = store.binin(pubkey_hash)  # binin, not hashin for 160-bit
        row = store.selectrow("""
            SELECT pubkey_id
              FROM pubkey
             WHERE pubkey_hash = ?""", (dbhash,))
        if row:
            return row[0]
        pubkey_id = store.new_id("pubkey")

        if pubkey is not None and len(pubkey) > MAX_PUBKEY:
            pubkey = None

        store.sql("""
            INSERT INTO pubkey (pubkey_id, pubkey_hash, pubkey, pubkey_flags)
            VALUES (?, ?, ?, ?)""",
                  (pubkey_id, dbhash, store.binin(pubkey), flags ))
        return pubkey_id

    def flush(store):
        if store.bytes_since_commit > 0:
            store.commit()
            store.log.debug("commit")
            store.bytes_since_commit = 0

    def imported_bytes(store, size):
        store.bytes_since_commit += size
        if store.bytes_since_commit >= store.commit_bytes:
            store.flush()

    def catch_up(store):
        for dircfg in store.datadirs:
            try:
                loader = dircfg['loader'] or store.default_loader
                if loader == "blkfile":
                    store.catch_up_dir(dircfg)
                elif loader in ("rpc", "rpc,blkfile", "default"):
                    if not store.catch_up_rpc(dircfg):
                        if loader == "rpc":
                            raise Exception("RPC load failed")
                        store.log.debug("catch_up_rpc: abort")
                        store.catch_up_dir(dircfg)
                else:
                    raise Exception("Unknown datadir loader: %s" % loader)

                store.flush()

            except Exception, e:
                store.log.exception("Failed to catch up %s", dircfg)
                store.rollback()

    def catch_up_rpc(store, dircfg):
        """
        Load new blocks using RPC.  Requires running *coind supporting
        getblockhash, getblock, and getrawtransaction.  Bitcoind v0.8
        requires the txindex configuration option.  Requires chain_id
        in the datadir table.
        """

# MULTICHAIN START
        # Expand ~ in multichain folder to user home directory
        dircfg['dirname'] = os.path.expanduser(dircfg['dirname'])
        # Extract chain name from last path component of multichain folder
        chain_name = os.path.basename(dircfg['dirname'])
# MULTICHAIN END

        chain_id = dircfg['chain_id']
        if chain_id is None:
            store.log.error("no chain_id")
            return False
        chain = store.chains_by.id[chain_id]

        conffile = dircfg.get('conf') or chain.datadir_conf_file_name
        conffile = os.path.join(dircfg['dirname'], conffile)
        try:
            conf = dict([line.strip().split("=", 1)
                         if "=" in line
                         else (line.strip(), True)
                         for line in open(conffile)
                         if line != "" and line[0] not in "#\r\n"])
        except Exception, e:
            store.log.error("failed to load %s: %s", conffile, e)
            return False

        rpcuser     = conf.get("rpcuser", "")
        rpcpassword = conf["rpcpassword"]
        rpcconnect  = conf.get("rpcconnect", "127.0.0.1")
        rpcport     = conf.get("rpcport", chain.datadir_rpcport)
        url = "http://" + rpcuser + ":" + rpcpassword + "@" + rpcconnect \
            + ":" + str(rpcport)

# MULTICHAIN START
        def rpc(func, *params):
            store.rpclog.info("RPC>> %s %s %s", chain_name, func, params)
            ret = util.jsonrpc(chain_name, url, func, *params)
# MULTICHAIN END

            if (store.rpclog.isEnabledFor(logging.INFO)):
                store.rpclog.info("RPC<< %s",
                                  re.sub(r'\[[^\]]{100,}\]', '[...]', str(ret)))
            return ret

        def get_blockhash(height):
            try:
                return rpc("getblockhash", height)
            except util.JsonrpcException, e:
                if e.code in (-1, -5, -8, -711):
                    # Block number out of range...
                    #  -1 is legacy code (pre-10.0), generic error
                    #  -8 (RPC_INVALID_PARAMETER) first seen in bitcoind 10.x
                    #  -5 (RPC_NOT_FOUND): Been suggested in #bitcoin-dev as more appropriate
                    #-711 (RPC_BLOCK_NOT_FOUND): MultiChain block not found error
                    return None
                raise

        # Returns -1 on error, so we'll get 0 on empty chain
        height = store.get_block_number(chain.id) + 1
    
        def get_tx(rpc_tx_hash):
            try:
                rpc_tx_hex = rpc("getrawtransaction", rpc_tx_hash)
            except util.JsonrpcException, e:
                if e.code != -5 and e.code!= -710:  # -5 or -710: transaction not in index.
                    raise
                if height != 0:
                    return None

                # The genesis transaction is unavailable.  This is
                # normal.
                import genesis_tx
                rpc_tx_hex = genesis_tx.get(rpc_tx_hash)
                if rpc_tx_hex is None:
                    store.log.error("genesis transaction unavailable via RPC;"
                                    " see import-tx in abe.conf")
                    return None

            decoded_tx = rpc("decoderawtransaction", rpc_tx_hex)
            
            # Turn this on for debugs, trust me
            #print("Decoded Transaction = %s" % str(decoded_tx) )

            sdec_transaction_handler(decoded_tx, height)

            rpc_tx = rpc_tx_hex.decode('hex')
            
            tx_hash = rpc_tx_hash.decode('hex')[::-1]

            computed_tx_hash = chain.transaction_hash(rpc_tx)
            if tx_hash != computed_tx_hash:
                #raise InvalidBlock('transaction hash mismatch')
                store.log.debug('transaction hash mismatch: %r != %r', tx_hash, computed_tx_hash)

            tx = chain.parse_transaction(rpc_tx)
            tx['hash'] = tx_hash
            
            #print("tx after parsing = %s" % str(tx) ) 
            # obj = deserialize.deserialize_Transaction(tx)

            return tx

        ### SDEC HANDLERS ###    
        
        def sdec_invoice_fields(data):
            cnpj                    = data['cnpj']
            p                       = data['prestacao']
            substitutes             = p.get('substitutes', None)
            prefeituraIncidencia    = p.get('prefeituraIncidencia', None)
            baseCalculo             = p.get('baseCalculo', None)
            aliqServicos            = p.get('aliqServicos', None)
            valLiquiNfse            = p.get('valLiquiNfse', None)
            dataIncidencia          = p.get('dataIncidencia', None)
            valServicos             = p.get('valServicos', None)
            valDeducoes             = p.get('valDeducoes', None)
            valPis                  = p.get('valPis', None)
            valCofins               = p.get('valCofins', None)
            valInss                 = p.get('valInss', None)
            valIr                   = p.get('valIr', None)
            valCsll                 = p.get('valCsll', None)
            outrasRetencoes         = p.get('outrasRetencoes', None)
            valTotalTributos        = p.get('valTotalTributos', None)
            valIss                  = p.get('valIss', None)
            descontoIncond          = p.get('descontoIncond', None)
            descontoCond            = p.get('descontoCond', None)
            issRetido               = p.get('issRetido', None)
            respRetencao            = p.get('respRetencao', None)
            itemLista               = p.get('itemLista', None)
            codCnae                 = p.get('codCnae', None)
            codServico              = p.get('codServico', None)
            codNBS                  = p.get('codNBS', None)
            discriminacao           = p.get('discriminacao', None)
            exigibilidadeISS        = p.get('exigibilidadeISS', None)
            numProcesso             = p.get('numProcesso', None)
            regimeEspTribut         = p.get('regimeEspTribut', None)
            optanteSimplesNacional  = p.get('optanteSimplesNacional', None)
            incentivoFiscal         = p.get('incentivoFiscal', None)
            # Nested Optional Fields
            identificacaoIntermed   = None
            nomeRazaoIntermed       = None
            cidadeIntermed          = None
            codObra                 = None
            art                     = None
            tomadorEncriptado       = None
            identificacaoTomador    = None
            nif                     = None
            nomeRazaoTomador        = None
            logEnd                  = None
            numEnd                  = None
            compEnd                 = None
            bairroEnd               = None
            cidadeEnd               = None
            estadoEnd               = None
            paisEnd                 = None
            cepEnd                  = None
            email                   = None
            tel                     = None

            # Not returned, object
            tomador                 = data.get('tomador', None)

            if (data.get('intermediario', None) is not None):
                identificacaoIntermed   = data['intermediario'].get('identificacaoIntermed', None)
                nomeRazaoIntermed       = data['intermediario'].get('nomeRazaoIntermed', None)
                cidadeIntermed          = data['intermediario'].get('cidadeIntermed', None)
            if (data.get('constCivil', None) is not None):
                codObra                 = data['constCivil'].get('codObra', None)
                art                     = data['constCivil'].get('art', None)

            if (data.get('tomador', None) is not None):
                identificacaoTomador    = tomador.get('identificacaoTomador', None)
                nif                     = tomador.get('nif', None)
                nomeRazaoTomador        = tomador.get('nomeRazaoTomador', None)
                logEnd                  = tomador.get('logEnd', None)
                numEnd                  = tomador.get('numEnd', None)
                compEnd                 = tomador.get('compEnd', None)
                bairroEnd               = tomador.get('bairroEnd', None)
                cidadeEnd               = tomador.get('cidadeEnd', None)
                estadoEnd               = tomador.get('estadoEnd', None)
                paisEnd                 = tomador.get('paisEnd', None)
                cepEnd                  = tomador.get('cepEnd', None)
                email                   = tomador.get('email', None)
                tel                     = tomador.get('tel', None)
                if (identificacaoTomador is not None):
                    identificacaoTomador.replace('.','').replace('/','').replace('-','')
            else:
                tomadorEncriptado = data.get('tomadorEncriptado', None)
            
            return substitutes, prefeituraIncidencia, baseCalculo, aliqServicos, valLiquiNfse, \
                dataIncidencia, valServicos, valDeducoes, valPis, valCofins, valInss, valIr, valCsll, \
                outrasRetencoes, valTotalTributos, valIss, descontoIncond, descontoCond, issRetido, \
                respRetencao, itemLista, codCnae, codServico, codNBS, discriminacao, exigibilidadeISS, \
                numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, identificacaoIntermed, \
                nomeRazaoIntermed, cidadeIntermed, codObra, art, tomadorEncriptado, identificacaoTomador, nif, \
                nomeRazaoTomador, logEnd, numEnd, compEnd, bairroEnd, cidadeEnd, estadoEnd, paisEnd, cepEnd, email, tel, cnpj

        def sdec_transaction_handler(decoded_tx, height):
            meta = {
                'txid': decoded_tx['txid'],
                'blockhash': decoded_tx.get('blockhash', None),
                'blocktime': decoded_tx.get('blocktime', None),
                'height': height,
            }
            for transaction in decoded_tx['vout']:
                permissions = transaction.get('permissions', None)
                if (permissions is not None):
                    return
                items = transaction.get('items', None)
                if (items is not None):
                    for item in items:
                        if item['type'] == 'stream':
                            action = item['keys'][0].split('_')
                            data = item['data']['json']
                            meta['publishers'] = item['publishers']

                            if (action[0] == 'COMPANY'):
                                if (action[1] == 'REGISTRY'):
                                    bd_insert_company(data, meta)
                                elif (action[1] == 'UPDATE'):
                                    print('COMPANY_UPDATE: Ainda não implementado')
                            elif (action[0] == 'INVOICE'):
                                if (action[1] == 'REGISTRY'):
                                    bd_insert_invoice(data, meta)
                                elif (action[1] == 'UPDATE'):
                                    bd_update_and_insert_invoice(data, meta)
                            elif (action[0] == 'SETTLEMENT'):
                                if (action[1] == 'REGISTRY'):
                                    print('SETTLEMENT: Ainda não implementado')
                                elif (action[1] == 'UPDATE'):
                                    print('SETTLEMENT: Ainda não implementado')
                            return
                        return
                    return
                return

        def is_equal(x, y, epsilon=1*10**(-2) ):
            return abs(x - y) <= epsilon
        
        def bd_insert_invoice(data, meta, isReplacement = False):
            txId                    = meta['txid']	
            enderecoEmissor         = meta['publishers'][0]	
            blocoConfirmacaoId      = meta['height']

            substitutes, prefeituraIncidencia, baseCalculo, aliqServicos, valLiquiNfse, \
            dataIncidencia, valServicos, valDeducoes, valPis, valCofins, valInss, valIr, valCsll, \
            outrasRetencoes, valTotalTributos, valIss, descontoIncond, descontoCond, issRetido, \
            respRetencao, itemLista, codCnae, codServico, codNBS, discriminacao, exigibilidadeISS, \
            numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, identificacaoIntermed, \
            nomeRazaoIntermed, cidadeIntermed, codObra, art, tomadorEncriptado, identificacaoTomador, nif, \
            nomeRazaoTomador, logEnd, numEnd, compEnd, bairroEnd, cidadeEnd, estadoEnd, paisEnd, cepEnd, email, \
            tel, cnpj = sdec_invoice_fields(data)

            if (tomadorEncriptado is None):
                store.sql("""
                INSERT INTO invoice (
                    txId, enderecoEmissor, blocoConfirmacaoId, prefeituraIncidencia, baseCalculo,
                    aliqServicos, valLiquiNfse, dataIncidencia, valServicos, valDeducoes,
                    valPis, valCofins, valInss, valIr, valCsll, outrasRetencoes, valTotalTributos,
                    valIss, descontoIncond, descontoCond, issRetido, respRetencao, itemLista,
                    codCnae, codServico, codNBS, discriminacao, exigibilidadeISS,
                    numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, 
                    identificacaoIntermed, nomeRazaoIntermed, cidadeIntermed, codObra, art,
                    identificacaoTomador, nif, nomeRazaoTomador, logEnd, numEnd, compEnd, bairroEnd, cidadeEnd, 
                    estadoEnd, paisEnd, cepEnd, email, tel, substitutes
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                         ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?) 
                """, (txId, enderecoEmissor, blocoConfirmacaoId, prefeituraIncidencia, baseCalculo,
                    aliqServicos, valLiquiNfse, dataIncidencia, valServicos, valDeducoes,
                    valPis, valCofins, valInss, valIr, valCsll, outrasRetencoes, valTotalTributos,
                    valIss, descontoIncond, descontoCond, issRetido, respRetencao, itemLista,
                    codCnae, codServico, codNBS, discriminacao, exigibilidadeISS,
                    numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, 
                    identificacaoIntermed, nomeRazaoIntermed, cidadeIntermed, codObra, art, 
                    identificacaoTomador, nif, nomeRazaoTomador, logEnd, numEnd, compEnd, bairroEnd, cidadeEnd, 
                    estadoEnd, paisEnd, cepEnd, email, tel, substitutes
                    )
                )
                store.commit()

                print('nota nova: %s', txId)
                if isReplacement is True:
                    store.redis.publish('invoice:update', str(cnpj) + '|' + str(enderecoEmissor) + '|' + meta['txid'])
                else:
                    store.redis.publish('invoice:new', str(cnpj) + '|' + str(enderecoEmissor) + '|' + meta['txid'])

            else:
                store.sql("""
                INSERT INTO invoice (
                    txId, enderecoEmissor, blocoConfirmacaoId, prefeituraIncidencia, baseCalculo,
                    aliqServicos, valLiquiNfse, dataIncidencia, valServicos, valDeducoes,
                    valPis, valCofins, valInss, valIr, valCsll, outrasRetencoes, valTotalTributos,
                    valIss, descontoIncond, descontoCond, issRetido, respRetencao, itemLista,
                    codCnae, codServico, codNBS, discriminacao, exigibilidadeISS,
                    numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, 
                    identificacaoIntermed, nomeRazaoIntermed, cidadeIntermed, codObra, art, tomadorEncriptado, substitutes
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                         ?, ?, ?, ?, ?, ?, ?, ?) 
                """, (txId, enderecoEmissor, blocoConfirmacaoId, prefeituraIncidencia, baseCalculo,
                    aliqServicos, valLiquiNfse, dataIncidencia, valServicos, valDeducoes,
                    valPis, valCofins, valInss, valIr, valCsll, outrasRetencoes, valTotalTributos,
                    valIss, descontoIncond, descontoCond, issRetido, respRetencao, itemLista,
                    codCnae, codServico, codNBS, discriminacao, exigibilidadeISS,
                    numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, 
                    identificacaoIntermed, nomeRazaoIntermed, cidadeIntermed, codObra, art, tomadorEncriptado, substitutes)
                )
                store.commit()

                print('nota nova: %s', txId)
                if isReplacement is True:
                    store.redis.publish('invoice:update', str(cnpj) + '|' + str(enderecoEmissor) + '|' + meta['txid'])
                else:
                    store.redis.publish('invoice:new', str(cnpj) + '|' + str(enderecoEmissor) + '|' + meta['txid'])

        def bd_insert_company(company_data, meta):
            paisEndereco        = company_data.get('paisEnd', None)
            razaoSocial         = company_data.get('razao', None)
            cidadeEndereco      = company_data.get('cidadeEnd', None)
            nomeFantasia        = company_data.get('fantasia', None)
            enderecoBlockchain  = company_data.get('endBlock', None)
            bairroEndereco      = company_data.get('bairroEnd', None)
            unidadeFederacao    = company_data.get('estadoEnd', None)
            email               = company_data.get('email', None)
            complementoEndereco = company_data.get('compEnd', None)
            _cnpj                = company_data.get('cnpj', None)
            numeroEndereco      = company_data.get('numEnd', None)
            telefone            = company_data.get('tel', None)
            enderecoEmpresa     = company_data.get('logEnd', None)
            cep                 = company_data.get('cepEnd', None)

            cnpj = _cnpj.replace('.','').replace('/','').replace('-','')

            # Inserting new company on our database
            store.sql("""
                INSERT INTO empresa (
                paisEndereco, razaoSocial, cidadeEndereco, nomeFantasia, 
                enderecoBlockchain, bairroEndereco, unidadeFederacao, email, 
                complementoEndereco, cnpj, numeroEndereco, telefone, 
                enderecoEmpresa, cep
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, 
                (paisEndereco, razaoSocial, cidadeEndereco, nomeFantasia, 
                enderecoBlockchain, bairroEndereco, unidadeFederacao, email, 
                complementoEndereco, cnpj, numeroEndereco, telefone, 
                enderecoEmpresa, cep)
            )

            store.commit()

            store.redis.publish('company:new', str(_cnpj) + '|' + str(enderecoBlockchain) + '|' + meta['txid'])
            print('empresa nova: %s', str(enderecoBlockchain))

        def bd_update_and_insert_invoice(data, meta):
            txId                    = meta['txid']	
            enderecoEmissor         = meta['publishers'][0]	
            blocoConfirmacaoId      = meta['height']
            
            substitutes, prefeituraIncidencia, baseCalculo, aliqServicos, valLiquiNfse, \
            dataIncidencia, valServicos, valDeducoes, valPis, valCofins, valInss, valIr, valCsll, \
            outrasRetencoes, valTotalTributos, valIss, descontoIncond, descontoCond, issRetido, \
            respRetencao, itemLista, codCnae, codServico, codNBS, discriminacao, exigibilidadeISS, \
            numProcesso, regimeEspTribut, optanteSimplesNacional, incentivoFiscal, identificacaoIntermed, \
            nomeRazaoIntermed, cidadeIntermed, codObra, art, tomadorEncriptado, identificacaoTomador, nif, \
            nomeRazaoTomador, logEnd, numEnd, compEnd, bairroEnd, cidadeEnd, estadoEnd, paisEnd, cepEnd, email, \
            tel, cnpj = sdec_invoice_fields(data)

            store.sql("""
                UPDATE invoice
                SET
                    substitutedBy = ?
                WHERE
                    txId = ?;
                """, (txId, substitutes)
                )
            store.commit()
            bd_insert_invoice(data, meta, True)

        ### END SDEC HANDLERS ###

        def first_new_block(height, next_hash):
            """Find the first new block."""

            while height > 0:
                hash = get_blockhash(height - 1)

                if hash is not None and (1,) == store.selectrow("""
                    SELECT 1
                      FROM chain_candidate cc
                      JOIN block b ON (cc.block_id = b.block_id)
                     WHERE b.block_hash = ?
                       AND b.block_height IS NOT NULL
                       AND cc.chain_id = ?""", (
                        store.hashin_hex(str(hash)), chain.id)):
                    break

                next_hash = hash
                height -= 1

            return (height, next_hash)

        def catch_up_mempool(height):
            # imported tx cache, so we can avoid querying DB on each pass
            imported_tx = set()
            # Next height check time
            height_chk = time.time() + 1

            while store.rpc_load_mempool:
                # Import the memory pool.
                for rpc_tx_hash in rpc("getrawmempool"):
                    if rpc_tx_hash in imported_tx: continue

                    # Break loop if new block found
                    if height_chk < time.time():
                        rpc_hash = get_blockhash(height)
                        if rpc_hash:
                            return rpc_hash
                        height_chk = time.time() + 1

                    tx = get_tx(rpc_tx_hash)

                    if tx is None:
                        # NB: On new blocks, older mempool tx are often missing
                        # This happens some other times too, just get over with
                        store.log.info("tx %s gone from mempool" % rpc_tx_hash)
                        continue

                    # XXX Race condition in low isolation levels.
                    tx_id = store.tx_find_id_and_value(tx, False, check_only=True)
                    if tx_id is None:
                        tx_id = store.import_tx(tx, False, chain)
                        store.log.info("mempool tx %d", tx_id)
                        store.imported_bytes(tx['size'])
                    imported_tx.add(rpc_tx_hash)

                store.log.info("mempool load completed, starting over...")
                time.sleep(3)
            return None

        try:

            # Get block hash at height, and at the same time, test
            # bitcoind connectivity.
            try:
                next_hash = get_blockhash(height)
            except util.JsonrpcException, e:
                raise
            except Exception, e:
                # Connectivity failure.
                store.log.error("RPC failed: %s", e)
                return False

            # Get the first new block (looking backward until hash match)
            height, next_hash = first_new_block(height, next_hash)

            # Import new blocks.
            rpc_hash = next_hash or get_blockhash(height)
            if rpc_hash is None:
                rpc_hash = catch_up_mempool(height)
            while rpc_hash is not None:
                hash = rpc_hash.decode('hex')[::-1]
                hashString = rpc_hash

                if store.offer_existing_block(hash, chain.id):
                    rpc_hash = get_blockhash(height + 1)
                else:
                    rpc_block = rpc("getblock", rpc_hash)
                    assert rpc_hash == rpc_block['hash']

                    prev_hash = \
                        rpc_block['previousblockhash'].decode('hex')[::-1] \
                        if 'previousblockhash' in rpc_block \
                        else chain.genesis_hash_prev

                    block = {
                        'hash':     hash,
                        'hashString': hashString,
                        'version':  int(rpc_block['version']),
                        'hashPrev': prev_hash,
                        'hashMerkleRoot':
                            rpc_block['merkleroot'].decode('hex')[::-1],
                        'nTime':    int(rpc_block['time']),
                        'nBits':    int(rpc_block['bits'], 16),
                        'nNonce':   int(rpc_block['nonce']),
                        'transactions': [],
                        'size':     int(rpc_block['size']),
                        'height':   height,
                        }

                    if chain.block_header_hash(chain.serialize_block_header(
                            block)) != hash:
                        raise InvalidBlock('block hash mismatch')

                    for rpc_tx_hash in rpc_block['tx']:
                        tx = store.export_tx(tx_hash = str(rpc_tx_hash),
                                             format = "binary")
                        if tx is None:
                            tx = get_tx(rpc_tx_hash)
                            if tx is None:
                                store.log.error("RPC service lacks full txindex")
                                return False

                        block['transactions'].append(tx)

                    store.import_block(block, chain = chain)
                    store.imported_bytes(block['size'])
                    rpc_hash = rpc_block.get('nextblockhash')

                height += 1
                if rpc_hash is None:
                    rpc_hash = catch_up_mempool(height)
                    # Also look backwards in case we end up on an orphan block.
                    # NB: Call only when rpc_hash is not None, otherwise
                    #     we'll override catch_up_mempool's behavior.
                    if rpc_hash:
                        height, rpc_hash = first_new_block(height, rpc_hash)

        except util.JsonrpcMethodNotFound, e:
            store.log.error("bitcoind %s not supported", e.method)
            return False

        except InvalidBlock, e:
            store.log.error("RPC data not understood: %s", e)
            return False

        return True

    # Load all blocks starting at the current file and offset.
    def catch_up_dir(store, dircfg):
        def open_blkfile(number):
            store._refresh_dircfg(dircfg)
            blkfile = {
                'stream': BCDataStream.BCDataStream(),
                'name': store.blkfile_name(dircfg, number),
                'number': number
                }

            try:
                file = open(blkfile['name'], "rb")
            except IOError, e:
                # Early bitcoind used blk0001.dat to blk9999.dat.
                # Now it uses blocks/blk00000.dat to blocks/blk99999.dat.
                # Abe starts by assuming the former scheme.  If we don't
                # find the expected file but do see blocks/blk00000.dat,
                # switch to the new scheme.  Record the switch by adding
                # 100000 to each file number, so for example, 100123 means
                # blocks/blk00123.dat but 123 still means blk0123.dat.
                if blkfile['number'] > 9999 or e.errno != errno.ENOENT:
                    raise
                new_number = 100000
                blkfile['name'] = store.blkfile_name(dircfg, new_number)
                file = open(blkfile['name'], "rb")
                blkfile['number'] = new_number

            try:
                blkfile['stream'].map_file(file, 0)
            except Exception:
                # mmap can fail on an empty file, but empty files are okay.
                file.seek(0, os.SEEK_END)
                if file.tell() == 0:
                    blkfile['stream'].input = ""
                    blkfile['stream'].read_cursor = 0
                else:
                    blkfile['stream'].map_file(file, 0)
            finally:
                file.close()
            store.log.info("Opened %s", blkfile['name'])
            return blkfile

        def try_close_file(ds):
            try:
                ds.close_file()
            except Exception, e:
                store.log.info("BCDataStream: close_file: %s", e)

        try:
            blkfile = open_blkfile(dircfg['blkfile_number'])
        except IOError, e:
            store.log.warning("Skipping datadir %s: %s", dircfg['dirname'], e)
            return

        while True:
            dircfg['blkfile_number'] = blkfile['number']
            ds = blkfile['stream']
            next_blkfile = None

            try:
                store.import_blkdat(dircfg, ds, blkfile['name'])
            except Exception:
                store.log.warning("Exception at %d" % ds.read_cursor)
                try_close_file(ds)
                raise

            if next_blkfile is None:
                # Try another file.
                try:
                    next_blkfile = open_blkfile(dircfg['blkfile_number'] + 1)
                except IOError, e:
                    if e.errno != errno.ENOENT:
                        raise
                    # No more block files.
                    return
                except Exception, e:
                    if getattr(e, 'errno', None) == errno.ENOMEM:
                        # Assume 32-bit address space exhaustion.
                        store.log.warning(
                            "Cannot allocate memory for next blockfile: "
                            "skipping safety check")
                        try_close_file(ds)
                        blkfile = open_blkfile(dircfg['blkfile_number'] + 1)
                        dircfg['blkfile_offset'] = 0
                        continue
                    raise
                finally:
                    if next_blkfile is None:
                        try_close_file(ds)

                # Load any data written to the last file since we checked.
                store.import_blkdat(dircfg, ds, blkfile['name'])

                # Continue with the new file.
                blkfile = next_blkfile

            try_close_file(ds)
            dircfg['blkfile_offset'] = 0

    # Load all blocks from the given data stream.
    def import_blkdat(store, dircfg, ds, filename="[unknown]"):
        filenum = dircfg['blkfile_number']
        ds.read_cursor = dircfg['blkfile_offset']

        while filenum == dircfg['blkfile_number']:
            if ds.read_cursor + 8 > len(ds.input):
                break

            offset = ds.read_cursor
            magic = ds.read_bytes(4)

            # Assume no real magic number starts with a NUL.
            if magic[0] == "\0":
                if filenum > 99999 and magic == "\0\0\0\0":
                    # As of Bitcoin 0.8, files often end with a NUL span.
                    ds.read_cursor = offset
                    break
                # Skip NUL bytes at block end.
                ds.read_cursor = offset
                while ds.read_cursor < len(ds.input):
                    size = min(len(ds.input) - ds.read_cursor, 1000)
                    data = ds.read_bytes(size).lstrip("\0")
                    if (data != ""):
                        ds.read_cursor -= len(data)
                        break
                store.log.info("Skipped %d NUL bytes at block end",
                               ds.read_cursor - offset)
                continue

            # Assume blocks obey the respective policy if they get here.
            chain_id = dircfg['chain_id']
            chain = store.chains_by.id.get(chain_id, None)

            if chain is None:
                chain = store.chains_by.magic.get(magic, None)

            if chain is None:
                store.log.warning(
                    "Chain not found for magic number %s in block file %s at"
                    " offset %d.", magic.encode('hex'), filename, offset)

                not_magic = magic
                # Read this file's initial magic number.
                magic = ds.input[0:4]

                if magic == not_magic:
                    ds.read_cursor = offset
                    break

                store.log.info(
                    "Scanning for initial magic number %s.",
                    magic.encode('hex'))

                ds.read_cursor = offset
                offset = ds.input.find(magic, offset)
                if offset == -1:
                    store.log.info("Magic number scan unsuccessful.")
                    break

                store.log.info(
                    "Skipped %d bytes in block file %s at offset %d.",
                    offset - ds.read_cursor, filename, ds.read_cursor)

                ds.read_cursor = offset
                continue

            length = ds.read_int32()
            if ds.read_cursor + length > len(ds.input):
                store.log.debug("incomplete block of length %d chain %d",
                                length, chain.id)
                ds.read_cursor = offset
                break
            end = ds.read_cursor + length

            hash = chain.ds_block_header_hash(ds)

            # XXX should decode target and check hash against it to
            # avoid loading garbage data.  But not for merged-mined or
            # CPU-mined chains that use different proof-of-work
            # algorithms.

            if not store.offer_existing_block(hash, chain.id):
                b = chain.ds_parse_block(ds)
                b["hash"] = hash

                # We should decode/transform this hash to a viable string
                # because this function is called the first ~10 blocks
                # I'm not sure how to do it right now, so I'll leave a TODO
                # and implement it wrongly here
                b["hashString"] = str(hash)

                if (store.log.isEnabledFor(logging.DEBUG) and b["hashPrev"] == chain.genesis_hash_prev):
                    try:
                        store.log.debug("Chain %d genesis tx: %s", chain.id,
                                        b['transactions'][0]['__data__'].encode('hex'))
                    except Exception:
                        pass

                store.import_block(b, chain = chain)
                if ds.read_cursor != end:
                    store.log.debug("Skipped %d bytes at block end",
                                    end - ds.read_cursor)

            ds.read_cursor = end

            store.bytes_since_commit += length
            if store.bytes_since_commit >= store.commit_bytes:
                store.save_blkfile_offset(dircfg, ds.read_cursor)
                store.flush()
                store._refresh_dircfg(dircfg)

        if ds.read_cursor != dircfg['blkfile_offset']:
            store.save_blkfile_offset(dircfg, ds.read_cursor)

    def blkfile_name(store, dircfg, number=None):
        if number is None:
            number = dircfg['blkfile_number']
        if number > 9999:
            return os.path.join(dircfg['dirname'], "blocks", "blk%05d.dat"
                                % (number - 100000,))
        return os.path.join(dircfg['dirname'], "blk%04d.dat" % (number,))

    def save_blkfile_offset(store, dircfg, offset):
        store.sql("""
            UPDATE datadir
               SET blkfile_number = ?,
                   blkfile_offset = ?
             WHERE datadir_id = ?""",
                  (dircfg['blkfile_number'], store.intin(offset),
                   dircfg['id']))
        if store.rowcount() == 0:
            store.sql("""
                INSERT INTO datadir (datadir_id, dirname, blkfile_number,
                    blkfile_offset, chain_id)
                VALUES (?, ?, ?, ?, ?)""",
                      (dircfg['id'], dircfg['dirname'],
                       dircfg['blkfile_number'],
                       store.intin(offset), dircfg['chain_id']))
        dircfg['blkfile_offset'] = offset

    def _refresh_dircfg(store, dircfg):
        row = store.selectrow("""
            SELECT blkfile_number, blkfile_offset
              FROM datadir
             WHERE dirname = ?""", (dircfg['dirname'],))
        if row:
            number, offset = map(int, row)
            if (number > dircfg['blkfile_number'] or
                (number == dircfg['blkfile_number'] and
                 offset > dircfg['blkfile_offset'])):
                dircfg['blkfile_number'] = number
                dircfg['blkfile_offset'] = offset

    def get_block_number(store, chain_id):
        row = store.selectrow("""
            SELECT block_height
              FROM chain_candidate
             WHERE chain_id = ?
               AND in_longest = 1
             ORDER BY block_height DESC
             LIMIT 1""", (chain_id,))
        return int(row[0]) if row else -1

    def get_target(store, chain_id):
        rows = store.selectall("""
            SELECT b.block_nBits
              FROM block b
              JOIN chain c ON (b.block_id = c.chain_last_block_id)
             WHERE c.chain_id = ?""", (chain_id,))
        return util.calculate_target(int(rows[0][0])) if rows else None

    def get_received_and_last_block_id(store, chain_id, pubkey_hash,
                                       block_height = None):
        sql = """
            SELECT COALESCE(value_sum, 0), c.chain_last_block_id
              FROM chain c LEFT JOIN (
              SELECT cc.chain_id, SUM(txout.txout_value) value_sum
              FROM pubkey
              JOIN txout              ON (txout.pubkey_id = pubkey.pubkey_id)
              JOIN block_tx           ON (block_tx.tx_id = txout.tx_id)
              JOIN block b            ON (b.block_id = block_tx.block_id)
              JOIN chain_candidate cc ON (cc.block_id = b.block_id)
              WHERE
                  pubkey.pubkey_hash = ? AND
                  cc.chain_id = ? AND
                  cc.in_longest = 1""" + (
                  "" if block_height is None else """ AND
                  cc.block_height <= ?""") + """
              GROUP BY cc.chain_id
              ) a ON (c.chain_id = a.chain_id)
              WHERE c.chain_id = ?"""
        dbhash = store.binin(pubkey_hash)

        return store.selectrow(sql,
                               (dbhash, chain_id, chain_id)
                               if block_height is None else
                               (dbhash, chain_id, block_height, chain_id))

    def get_received(store, chain_id, pubkey_hash, block_height = None):
        return store.get_received_and_last_block_id(
            chain_id, pubkey_hash, block_height)[0]

    def get_sent_and_last_block_id(store, chain_id, pubkey_hash,
                                   block_height = None):
        sql = """
            SELECT COALESCE(value_sum, 0), c.chain_last_block_id
              FROM chain c LEFT JOIN (
              SELECT cc.chain_id, SUM(txout.txout_value) value_sum
              FROM pubkey
              JOIN txout              ON (txout.pubkey_id = pubkey.pubkey_id)
              JOIN txin               ON (txin.txout_id = txout.txout_id)
              JOIN block_tx           ON (block_tx.tx_id = txin.tx_id)
              JOIN block b            ON (b.block_id = block_tx.block_id)
              JOIN chain_candidate cc ON (cc.block_id = b.block_id)
              WHERE
                  pubkey.pubkey_hash = ? AND
                  cc.chain_id = ? AND
                  cc.in_longest = 1""" + (
                  "" if block_height is None else """ AND
                  cc.block_height <= ?""") + """
              GROUP BY cc.chain_id
              ) a ON (c.chain_id = a.chain_id)
              WHERE c.chain_id = ?"""
        dbhash = store.binin(pubkey_hash)

        return store.selectrow(sql,
                               (dbhash, chain_id, chain_id)
                               if block_height is None else
                               (dbhash, chain_id, block_height, chain_id))

    def get_sent(store, chain_id, pubkey_hash, block_height = None):
        return store.get_sent_and_last_block_id(
            chain_id, pubkey_hash, block_height)[0]

    def get_balance(store, chain_id, pubkey_hash):
        sent, last_block_id = store.get_sent_and_last_block_id(
            chain_id, pubkey_hash)
        received, last_block_id_2 = store.get_received_and_last_block_id(
            chain_id, pubkey_hash)

        # Deal with the race condition.
        for i in xrange(2):
            if last_block_id == last_block_id_2:
                break

            store.log.debug("Requerying balance: %d != %d",
                          last_block_id, last_block_id_2)

            received, last_block_id_2 = store.get_received(
                chain_id, pubkey_hash, store.get_block_height(last_block_id))

            if last_block_id == last_block_id_2:
                break

            store.log.info("Balance query affected by reorg? %d != %d",
                           last_block_id, last_block_id_2)

            sent, last_block_id = store.get_sent(
                chain_id, pubkey_hash, store.get_block_height(last_block_id_2))

        if last_block_id != last_block_id_2:
            store.log.warning("Balance query failed due to loader activity.")
            return None

        return received - sent


    def firstbits_full(store, version, hash):
        """
        Return the address in lowercase.  An initial substring of this
        will become the firstbits.
        """
        return util.hash_to_address(version, hash).lower()

    def insert_firstbits(store, pubkey_id, block_id, addr_vers, fb):
        store.sql("""
            INSERT INTO abe_firstbits (
                pubkey_id, block_id, address_version, firstbits
            )
            VALUES (?, ?, ?, ?)""",
                  (pubkey_id, block_id, addr_vers, fb))

    def cant_do_firstbits(store, addr_vers, block_id, pubkey_id):
        store.log.info(
            "No firstbits for pubkey_id %d, block_id %d, version '%s'",
            pubkey_id, block_id, store.binout_hex(addr_vers))
        store.insert_firstbits(pubkey_id, block_id, addr_vers, '')

    def do_firstbits(store, addr_vers, block_id, fb, ids, full):
        """
        Insert the firstbits that start with fb using addr_vers and
        are first seen in block_id.  Return the count of rows
        inserted.

        fb -- string, not a firstbits using addr_vers in any ancestor
        of block_id
        ids -- set of ids of all pubkeys first seen in block_id whose
        firstbits start with fb
        full -- map from pubkey_id to full firstbits
        """

        if len(ids) <= 1:
            for pubkey_id in ids:
                store.insert_firstbits(pubkey_id, block_id, addr_vers, fb)
            return len(ids)

        pubkeys = {}
        for pubkey_id in ids:
            s = full[pubkey_id]
            if s == fb:
                store.cant_do_firstbits(addr_vers, block_id, pubkey_id)
                continue
            fb1 = fb + s[len(fb)]
            ids1 = pubkeys.get(fb1)
            if ids1 is None:
                ids1 = set()
                pubkeys[fb1] = ids1
            ids1.add(pubkey_id)

        count = 0
        for fb1, ids1 in pubkeys.iteritems():
            count += store.do_firstbits(addr_vers, block_id, fb1, ids1, full)
        return count

    def do_vers_firstbits(store, addr_vers, block_id):
        """
        Create new firstbits records for block and addr_vers.  All
        ancestor blocks must have their firstbits already recorded.
        """

        address_version = store.binout(addr_vers)
        pubkeys = {}  # firstbits to set of pubkey_id
        full    = {}  # pubkey_id to full firstbits, or None if old

        for pubkey_id, pubkey_hash, oblock_id in store.selectall("""
            SELECT DISTINCT
                   pubkey.pubkey_id,
                   pubkey.pubkey_hash,
                   fb.block_id
              FROM block b
              JOIN block_tx bt ON (b.block_id = bt.block_id)
              JOIN txout ON (bt.tx_id = txout.tx_id)
              JOIN pubkey ON (txout.pubkey_id = pubkey.pubkey_id)
              LEFT JOIN abe_firstbits fb ON (
                       fb.address_version = ?
                   AND fb.pubkey_id = pubkey.pubkey_id)
             WHERE b.block_id = ?""", (addr_vers, block_id)):

            pubkey_id = int(pubkey_id)

            if (oblock_id is not None and
                store.is_descended_from(block_id, int(oblock_id))):
                full[pubkey_id] = None

            if pubkey_id in full:
                continue

            full[pubkey_id] = store.firstbits_full(address_version,
                                                   store.binout(pubkey_hash))

        for pubkey_id, s in full.iteritems():
            if s is None:
                continue

            # This is the pubkey's first appearance in the chain.
            # Find the longest match among earlier firstbits.
            longest, longest_id = 0, None
            substrs = [s[0:(i+1)] for i in xrange(len(s))]
            for ancestor_id, fblen, o_pubkey_id in store.selectall("""
                SELECT block_id, LENGTH(firstbits), pubkey_id
                  FROM abe_firstbits fb
                 WHERE address_version = ?
                   AND firstbits IN (?""" + (",?" * (len(s)-1)) + """
                       )""", tuple([addr_vers] + substrs)):
                if fblen > longest and store.is_descended_from(
                    block_id, int(ancestor_id)):
                    longest, longest_id = fblen, o_pubkey_id

            # If necessary, extend the new fb to distinguish it from
            # the longest match.
            if longest_id is not None:
                (o_hash,) = store.selectrow(
                    "SELECT pubkey_hash FROM pubkey WHERE pubkey_id = ?",
                    (longest_id,))
                o_fb = store.firstbits_full(
                    address_version, store.binout(o_hash))
                max_len = min(len(s), len(o_fb))
                while longest < max_len and s[longest] == o_fb[longest]:
                    longest += 1

            if longest == len(s):
                store.cant_do_firstbits(addr_vers, block_id, pubkey_id)
                continue

            fb = s[0 : (longest + 1)]
            ids = pubkeys.get(fb)
            if ids is None:
                ids = set()
                pubkeys[fb] = ids
            ids.add(pubkey_id)

        count = 0
        for fb, ids in pubkeys.iteritems():
            count += store.do_firstbits(addr_vers, block_id, fb, ids, full)
        return count

    def firstbits_to_addresses(store, fb, chain_id=None):
        dbfb = fb.lower()
        ret = []
        bind = [fb[0:(i+1)] for i in xrange(len(fb))]
        if chain_id is not None:
            bind.append(chain_id)

        for dbhash, vers in store.selectall("""
            SELECT pubkey.pubkey_hash,
                   fb.address_version
              FROM abe_firstbits fb
              JOIN pubkey ON (fb.pubkey_id = pubkey.pubkey_id)
              JOIN chain_candidate cc ON (cc.block_id = fb.block_id)
             WHERE fb.firstbits IN (?""" + (",?" * (len(fb)-1)) + """)""" + ( \
                "" if chain_id is None else """
               AND cc.chain_id = ?"""), tuple(bind)):
            address = util.hash_to_address(store.binout(vers),
                                           store.binout(dbhash))
            if address.lower().startswith(dbfb):
                ret.append(address)

        if len(ret) == 0 or (len(ret) > 1 and fb in ret):
            ret = [fb]  # assume exact address match

        return ret

    def get_firstbits(store, address_version=None, db_pubkey_hash=None,
                      chain_id=None):
        """
        Return address's firstbits, or the longest of multiple
        firstbits values if chain_id is not given, or None if address
        has not appeared, or the empty string if address has appeared
        but has no firstbits.
        """
        vers, dbhash = store.binin(address_version), db_pubkey_hash
        rows = store.selectall("""
            SELECT fb.firstbits
              FROM abe_firstbits fb
              JOIN pubkey ON (fb.pubkey_id = pubkey.pubkey_id)
              JOIN chain_candidate cc ON (fb.block_id = cc.block_id)
             WHERE cc.in_longest = 1
               AND fb.address_version = ?
               AND pubkey.pubkey_hash = ?""" + (
                "" if chain_id is None else """
               AND cc.chain_id = ?"""),
                               (vers, dbhash) if chain_id is None else
                               (vers, dbhash, chain_id))
        if not rows:
            return None

        ret = ""
        for (fb,) in rows:
            if len(fb) > len(ret):
                ret = fb
        return ret

# MULTICHAIN START
    def get_number_of_transactions(store, chain):
        """
        Add up the number of tx in each block which belongs to chain of chain_id
        :param chain_id:
        :return: number of tx, or -1 if there was an error
        """
        result = -1
        sumrow = store.selectrow("""
            SELECT SUM(block_num_tx) FROM chain_summary WHERE chain_id = ?
        """, (chain.id,))
        if sumrow:
            result = sumrow[0]
        return result

    def get_number_of_addresses(store, chain):
        """
        Count the number of unique pubkeys found in txouts for a chain_id
        :param chain_id:
        :return: number of addresses, or -1 if there was an error
        """
        result = -1
        countrow = store.selectrow("""
            SELECT COUNT(DISTINCT(pubkey_hash)) FROM txout_detail WHERE chain_id = ?
        """, (chain.id,))
        if countrow:
            result = countrow[0]
            if result > 0:
                result -= 1  # NULL_PUBKEY_HASH
        return result

    def get_number_of_assets(store, chain):
        """
        Get the number of assets issued in a chain
        :param chain:
        :return: integer number of assets
        """
        resp = store.get_assets(chain)
        if resp is not None:
            return len(resp)
        return 0

    def get_assets(store, chain):
        """
        Get the result of listassets json-rpc command as json object
        :param chain:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "listassets")
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_asset_by_name(store, chain, name):
        """
        Get the asset by name from listassets json-rpc command as json object
        :param chain:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "listassets", name)
            if len(resp) > 0 :
                resp = resp[0]
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_block_by_hash(store, chain, blockhash):
        """
        Get block info from getblock json-rpc command as json object
        :param chain:
        :param blockhash: hex string of block hash
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "getblock", blockhash)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_number_of_peers(store, chain):
        """
        Get the number of connected peers
        :param chain:
        :return: Integer number of nodes
        """
        resp = store.get_peerinfo(chain)
        if resp is not None:
            return len(resp)
        return 0

    def get_peerinfo(store, chain):
        """
        Get info about connected peers by invoking json-rpc command getpeerinfo
        :param chain:
        :return: JSON object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "getpeerinfo")
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_number_of_asset_holders(store, chain, assetref):
        """
        Get the number of addresses holding units of an asset
        :param chain:
        :param assetref:
        :return: int
        """
        chain_id = chain.id
        prefix = int( assetref.split('-')[-1] )
        row = store.selectrow("""
            SELECT count(DISTINCT pubkey_id)
            FROM asset_address_balance
            WHERE balance>0 AND asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
            """, (chain_id, prefix))
        if row is None:
            result = 0
        else:
            result = int(row[0])
        return result

    def get_asset_holders(store, chain, assetref):
        """
        Get a list of the addresses holding units of an asset
        :param chain:
        :param assetref:
        :return: List or None, where each list element is a dictionary storing the pubkey and balance.
        """
        def parse_row(row):
            pubkey, pubkey_hash, pubkey_flags, balance = row
            ret = {
                "pubkey": store.binout(pubkey),
                "pubkey_hash": store.binout(pubkey_hash),
                "pubkey_flags": pubkey_flags,
                "balance": balance
                }
            return ret

        chain_id = chain.id
        prefix = int( assetref.split('-')[-1] )
        rows = store.selectall("""
            SELECT p.pubkey, p.pubkey_hash, p.pubkey_flags, a.balance
            FROM asset_address_balance a
            JOIN pubkey p ON (a.pubkey_id = p.pubkey_id)
            WHERE balance>0 AND asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
            """, (chain_id, prefix))
        if rows is None:
            return None
        result = list(map(parse_row, rows))
        return result

    def get_recent_transactions_as_json(store, chain, limit=10):
        """
        Get a list of recent confirmed transactions, decoded to json
        :param chain:
        :param limit: the maxinmum number of transactions to return
        :return: list of strings or empty list.
        """
        # Ignore coinbase transactions where there is no native currency
        rows = store.selectall("""
            SELECT DISTINCT tx_hash
            FROM txout_detail
            WHERE chain_id=? AND pubkey_id != ?
            ORDER BY block_height DESC, tx_id DESC
            LIMIT ?
        """, (chain.id, NULL_PUBKEY_ID, limit))

        if rows is None:
             return []

        result = []
        for row in rows:
            try:
                txid = store.hashout_hex(row[0])
                json = store.get_rawtransaction_decoded(chain, txid)
                if json is not None and json['confirmations']>0:
                    result.append(json)
            except Exception:
                pass

        return result

    def get_transactions_for_asset(store, chain, assetref):
        """
        Get a list of transactions related to an asset.
        :param chain:
        :param assetref:
        :return: list of data (tx hash, height, blockhash) or None.
        """
        def parse_row(row):
            txhash, height, blockhash = row
            ret = {
#                "outpos": int(pos),
                "hash": store.hashout_hex(txhash),
                "height": int(height),
                "blockhash": store.hashout_hex(blockhash)
                }
            return ret

        prefix = int( assetref.split('-')[-1] )
        rows = store.selectall("""
            select DISTINCT t.tx_hash, bb.block_height, bb.block_hash from asset_txid a
            join block_tx b on (a.tx_id=b.tx_id)
            join tx t on (a.tx_id=t.tx_id)
            join block bb on (b.block_id=bb.block_id)
            where a.asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
            order by bb.block_height, b.tx_pos asc
        """, (chain.id, prefix))

        if rows is None:
            return None

        result = list(map(parse_row, rows))
        return result

    def get_transactions_for_asset_address(store, chain, assetref, address):
        """
        Get a list of transactions related to both an address and an assetref
        :param chain:
        :param assetref:
        :param address:
        :return: List of transactions or none.
        """
        def parse_row(row):
            txhash, height, blockhash = row
            ret = {
                #"outpos": int(pos),
                "hash": store.hashout_hex(txhash),
                "height": int(height),
                "blockhash": store.hashout_hex(blockhash)
                }
            return ret

        # get pubkey id
        version, pubkeyhash = util.decode_check_address_multichain(address)
        if pubkeyhash is None:
            return None
        row = store.selectrow("""select pubkey_id from pubkey where pubkey_hash = ?""",
                                    (store.binin(pubkeyhash),) )
        if row is None:
            return None
        pubkey_id = int(row[0])

        prefix = int( assetref.split('-')[-1] )
        # a.txout_pos,... , a.txout_pos asc
        rows = store.selectall("""
            select DISTINCT t.tx_hash, bb.block_height, bb.block_hash from asset_txid a
            join block_tx b on (a.tx_id=b.tx_id)
            join tx t on (a.tx_id=t.tx_id)
            join block bb on (b.block_id=bb.block_id)
            join txout o on (a.tx_id=o.tx_id)
            join txin_detail i on (a.tx_id=i.tx_id)
            where a.asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
            and (o.pubkey_id=? OR i.pubkey_id=?)
            order by bb.block_height, b.tx_pos asc
        """, (chain.id, prefix, pubkey_id, pubkey_id))

        if rows is None:
            return None

        result = list(map(parse_row, rows))
        return result

    def get_number_of_transactions_for_asset_address(store, chain, assetref, pubkey_id):
        """
        Get the number of transactions related to both an asset and an address.
        :param chain:
        :param assetref: human readable assetref e.g. 111-222-333
        :param pubkey_id:
        :return:
        """
        prefix = int( assetref.split('-')[-1] )
        row = store.selectrow("""
            select count(distinct a.tx_id) from asset_txid a join txout o on (a.tx_id=o.tx_id)
            where a.asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
            and o.pubkey_id=?
        """, (chain.id, prefix, pubkey_id))
        if row is None:
            return 0
        return int(row[0])

    def get_number_of_transactions_for_asset(store, chain, assetref):
        """
        Get the number of transactions related to an asset which are stored in the database.
        :param chain:
        :param assetref: human readable assetref e.g. 111-222-333
        :return: int
        """
        prefix = int( assetref.split('-')[-1] )
        row = store.selectrow("""
            select count(distinct a.tx_id) from asset_txid a
            where a.asset_id=( SELECT asset_id FROM asset WHERE chain_id=? AND prefix=?)
        """, (chain.id, prefix))
        if row is None:
            return 0
        return int(row[0])

    def does_transaction_exist(store, tx_hash):
        """
        Check to see if the database contains a transaction for a given tx hash.
        :param tx_hash:
        :return: boolean
        """
        if tx_hash is None:
            return False
        try:
            dbhash = store.hashin_hex(tx_hash)
        except TypeError:
            return False

        row = store.selectrow("""
            SELECT EXISTS (SELECT 1 FROM tx WHERE tx_hash = ?)
        """, (dbhash,))
        if row is None:
            return False
        result = int(row[0])
        return True if result==1 else False


    def list_transactions(store, chain, count):
        """
        Get the result of listtransactions json-rpc command as json object
        NOTE: This call does not work with MultiChain v2 scalable wallets.
        :param chain:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "listtransactions", "*", count)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_number_of_streams(store, chain):
        """
        Get the number of streams
        :param chain:
        :return: Integer number of streams
        """
        resp = store.list_streams(chain)
        if resp is not None:
            return len(resp)
        return 0

    def list_stream(store, chain, name):
        """
        Get the result of liststreams json-rpc command as json object.
        We ask for a specific stream and verbose data.
        :param chain:
        :param name:
        :return: None or json object for the stream
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "liststreams", name, True)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e

        if len(resp) < 1:
            return None
        return resp[0]

    def list_streams(store, chain, count=0):
        """
        Get the result of liststreams json-rpc command as json object.
        We ask for all streams and verbose data, such as the creators field.
        :param chain:
        :param count: by default all
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreans streamref verbose count start
            # e.g. liststreams "*" true 2 -2
            # display last two streams.
            # e.g. liststreams "*" true 2 0
            # display first two streams

            # all streams
            if count <= 0:
                resp = util.jsonrpc(multichain_name, url, "liststreams", "*", True)
            else:
                resp = util.jsonrpc(multichain_name, url, "liststreams", "*", True, count, -count)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_stream_items(store, chain, streamref, count=10, start=-10):
        """
        Get the result of liststreamitems json-rpc command as json object.
        We ask for all streams and verbose data, such as the creators field.
        :param chain:
        :param streamref:
        :param count:
        :param start:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreamitems streamref verbose count start localordering
            resp = util.jsonrpc(multichain_name, url, "liststreamitems", streamref, True, count, start)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_stream_publisher_items(store, chain, streamref, publisher, count=10, start=-10):
        """
        Get the result of liststreampublisheritems json-rpc command as json object.
        We ask for all streams and verbose data, such as the creators field.
        :param chain:
        :param streamref:
        :param publisher:
        :param count:
        :param start:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreampublisheritems streamref publisheraddress verbose count start localordering
            resp = util.jsonrpc(multichain_name, url, "liststreampublisheritems", streamref, publisher, True, count, start)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_stream_publishers(store, chain, streamref, publisher="*"):
        """
        Get the result of liststreampublisheritems json-rpc command as json object.
        We ask for all streams and verbose data, such as the creators field.
        :param chain:
        :param streamref:
        :param publisher:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreampublishers streamref publisheraddress
            resp = util.jsonrpc(multichain_name, url, "liststreampublishers", streamref, publisher)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_stream_keys(store, chain, streamref, keys="*"):
        """
        Get the result of liststreamkeys json-rpc command as json object.
        We ask for all keys and verbose data, such as the creators field.
        :param chain:
        :param streamref:
        :param keys:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreamkeys streamref keys
            resp = util.jsonrpc(multichain_name, url, "liststreamkeys", streamref, keys)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_stream_key_items(store, chain, streamref, streamkey, count=10, start=-10):
        """
        Get the result of liststreamkeyitems json-rpc command as json object.
        We ask for all streams and verbose data, such as the creators field.
        :param chain:
        :param streamref:
        :param key:
        :param count:
        :param start:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            # liststreamkeyitems streamref publisheraddress verbose count start localordering
            resp = util.jsonrpc(multichain_name, url, "liststreamkeyitems", streamref, streamkey, True, count, start)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def list_upgrades(store, chain):
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "listupgrades")
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_rawmempool(store, chain):
        """
        Get the result of getrawmempool json-rpc command as json object
        :param chain:
        :return: json object (key is txid, value is dict)
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "getrawmempool", True)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_rawtransaction_decoded(store, chain, tx_hash):
        """
        Get the result of getrawtransaction json-rpc command as json object
        :param chain:
        :return: json object
        """
        url = store.get_url_by_chain(chain)
        multichain_name = store.get_multichain_name_by_id(chain.id)
        resp = None
        try:
            resp = util.jsonrpc(multichain_name, url, "getrawtransaction", tx_hash, 1)
        except util.JsonrpcException as e:
            raise Exception("JSON-RPC error({0}): {1}".format(e.code, e.message))
        except IOError as e:
            raise e
        return resp

    def get_labels_for_tx(store, tx_hash, chain):
        """
        Get a list of labels describing a transaction
        :param tx_hash:
        :param chain:
        :return: list of string
        """
        labels = None
        try:
            mytx = store._export_tx_detail(tx_hash, chain)
        except MalformedHash:
            mytx = None

        if mytx is not None:
            d = set()
            for txout in mytx['out']:
                tmp = store.get_labels_for_scriptpubkey(chain, txout['binscript'])
                d |= set(tmp)
            labels = list(d)
        return labels

    def get_labels_for_scriptpubkey(store, chain, scriptpubkey):
        """
        Get labels describing the scriptpubkey of a txout.
        :param chain:
        :param scriptpubkey:
        :return: labels as list, or empty list if not a recognized MultiChain OP_DROP or OP_RETURN.
        """
        label = []
        script_type, data = chain.parse_txout_script(scriptpubkey)
        if script_type is Chain.SCRIPT_TYPE_MULTICHAIN_P2SH:
            label.append('P2SH')
        if script_type in [Chain.SCRIPT_TYPE_MULTICHAIN_STREAM, Chain.SCRIPT_TYPE_MULTICHAIN_STREAM_ITEM]:
            label.append('Stream')
        if script_type == Chain.SCRIPT_TYPE_MULTICHAIN_FILTER:
            label.append('Filter')
        if script_type in [Chain.SCRIPT_TYPE_MULTICHAIN, Chain.SCRIPT_TYPE_MULTICHAIN_P2SH]:
            data = util.get_multichain_op_drop_data(scriptpubkey)
            if data is not None:
                opdrop_type, val = util.parse_op_drop_data(data, chain)
                if opdrop_type==util.OP_DROP_TYPE_ISSUE_ASSET:
                    label.append('Issue Asset')
                elif opdrop_type==util.OP_DROP_TYPE_SEND_ASSET:
                    label.append('Asset')
                elif opdrop_type==util.OP_DROP_TYPE_PERMISSION:
                    label.append('Permissions')
                elif opdrop_type==util.OP_DROP_TYPE_ISSUE_MORE_ASSET:
                    label.append('Reissue Asset')
                else:
                    label.append('OP_DROP')
            else:
                label.append('Unknown')
        elif script_type is Chain.SCRIPT_TYPE_MULTICHAIN_OP_RETURN:
            opreturn_type, val = util.parse_op_return_data(data, chain)
            if opreturn_type==util.OP_RETURN_TYPE_ISSUE_ASSET:
                label.append('Issue Asset')
            elif opreturn_type == util.OP_RETURN_TYPE_MINER_BLOCK_SIGNATURE:
                label.append("Miner Sig")
            else:
                label.append('Metadata')
        # Protocol 10007
        elif script_type in [Chain.SCRIPT_TYPE_MULTICHAIN_SPKN, Chain.SCRIPT_TYPE_MULTICHAIN_SPKU]:
            data = util.get_multichain_op_drop_data(scriptpubkey)
            if data is not None:
                opdrop_type, val = util.parse_op_drop_data(data, chain)
                if opdrop_type==util.OP_DROP_TYPE_FOLLOW_ON_ISSUANCE_METADATA:
                    label.append('Asset')
                elif opdrop_type==util.OP_DROP_TYPE_SPKN_NEW_ISSUE:
                    label.append('Issue Asset')
                elif opdrop_type==util.OP_DROP_TYPE_SPKN_CREATE_STREAM:
                    label.append('Create Stream')
                elif opdrop_type == util.OP_DROP_TYPE_SPKN_CREATE_FILTER:
                    label.append('Create Filter')
                elif opdrop_type == util.OP_DROP_TYPE_SPKN_CREATE_UPGRADE:
                    label.append("Create Upgrade")
                elif opdrop_type == util.OP_DROP_TYPE_SPKN_APPROVE_UPGRADE:
                    label.append("Approve Upgrade")
                elif opdrop_type==util.OP_DROP_TYPE_SPKE:
                    pass
                    #label.append('SPKE')
            else:
                label.append('Unknown')
        elif script_type is Chain.SCRIPT_TYPE_MULTICHAIN_ENTITY_PERMISSION:
            label.append('Permissions')
        elif script_type is Chain.SCRIPT_TYPE_MULTICHAIN_APPROVE:
            label.append("Approve Upgrade")
        elif script_type is Chain.SCRIPT_TYPE_MULTICHAIN_SPKF:
            label.append("Inline Data")
        if "spkd" in scriptpubkey:
            label.append("Inline Data")

        return label

def new(args):
    return DataStore(args)
