
from typing import (
    Iterable, NamedTuple, Dict, Mapping, Union, get_type_hints, Tuple,
    Callable)


class Params:
    # The infamous max block size.
    MAX_BLOCK_SERIALIZED_SIZE = int(1000000)  # bytes = 1MB


    COINBASE_MATURITY = int(2)

    # Accept blocks timestamped as being from the future, up to this amount.
    MAX_FUTURE_BLOCK_TIME = int(60 * 60 * 2)

    # The number of LET per coin. #realname COIN
    LET_PER_COIN = int(100e6)

    TOTAL_COINS = int(21_000_000)

    # The maximum number of Lets that will ever be found.
    MAX_MONEY = LET_PER_COIN * TOTAL_COINS

    # The duration we want to pass between blocks being found, in seconds.
    # This is lower than Bitcoin's configuation (10 * 60).
    #
    # #realname PowTargetSpacing
    TIME_BETWEEN_BLOCKS_IN_SECS_TARGET = int(60)

    # The number of seconds we want a difficulty period to last.
    #
    # Note that this differs considerably from the behavior in Bitcoin, which
    # is configured to target difficulty periods of (10 * 2016) minutes.
    #
    # #realname PowTargetTimespan
    DIFFICULTY_PERIOD_IN_SECS_TARGET = int(60 * 60 * 10)

    # After this number of blocks are found, adjust difficulty.
    #
    # #realname DifficultyAdjustmentInterval
    DIFFICULTY_PERIOD_IN_BLOCKS = int(
        DIFFICULTY_PERIOD_IN_SECS_TARGET / TIME_BETWEEN_BLOCKS_IN_SECS_TARGET)

    # The number of right-shifts applied to 2 ** 256 in order to create the
    # initial difficulty target necessary for mining a block.
    INITIAL_DIFFICULTY_BITS = int(24)

    # The number of blocks after which the mining subsidy will halve.
    #
    # #realname SubsidyHalvingInterval
    HALVE_SUBSIDY_AFTER_BLOCKS_NUM = int(210_000)
    ACTIVE_CHAIN_IDX = int(0)

    TRIES_MAXIMUM = 1

    # list of peers
    CHUNK_SIZE = int(50)
    SAVE_PER_SIZE = int(37)
    MAXIMUM_ALLOWABLE_HEIGHT_DIFF = 15
    MAXIMUM_FAILURE_PEER = 50

    PUBLIC_IP = ''
    PORT_CURRENT = int(9996)
    PEERS_FILE =  'seeds.node'
    CHAIN_FILE = 'chain.dat'
    WALLET_FILE = 'mywallet.dat'
    PEERS: Iterable[Tuple] = list([('47.102.41.81', 9996),
                     ('39.97.166.176', 9996),
                     ('47.92.85.186', 10000),
                    ('47.111.168.213', 9996),
                     ('47.88.63.126', 9996),
                     ('161.117.84.146', 9996)
                     ])


