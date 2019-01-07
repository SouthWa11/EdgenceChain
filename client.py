#!/usr/bin/env python3
"""
⛼  edgencechain client

Usage:
  client.py balance [options] [--raw]
  client.py send [options] <addr> <val>
  client.py status [options] <txid> [--csv]

Options:
  -h --help            Show help
  -w, --wallet PATH    Use a particular wallet file (e.g. `-w ./wallet2.dat`)
  -n, --node HOSTNAME  The hostname of node to use for RPC (default: localhost)
  -p, --port PORT      Port node is listening on (default: 9999)

"""

# options参数用-h而非--help，其它三个参数也一样
# 尖括号括起来的是必选参数，如<addr>表示此处填写目的地址，<val>表示金额，，<txid>表示交易ID
# --raw表示直接显示金额的原始数字，--csv表示将采用csv格式将结果打印出来。这两个可选参数不需关注。

import logging
import os
import socket

from docopt import docopt

import edgencechain as t


logging.basicConfig(
    level=getattr(logging, os.environ.get('TC_LOG_LEVEL', 'INFO')),
    format='[%(asctime)s][%(module)s:%(lineno)d] %(levelname)s %(message)s')
logger = logging.getLogger(__name__)


def main(args):
    # args本身是个包含了命令行参数的字典，此处再添加三条关于钱包信息的内容。
    args['signing_key'], args['verifying_key'], args['my_addr'] = (
        t.init_wallet(args.get('--wallet'))) #t.init_wallet()有默认钱包wallet.dat

    #当--port和--node参数在命令行参数里被指定，或者有值，则将函数send_msg的对应内置成员赋值。
    if args['--port']:
        send_msg.port = args['--port']
    if args['--node']:
        send_msg.node_hostname = args['--node']

    if args['balance']:  #如果args字典里有balance，则执行get_balance函数
        get_balance(args) # get_balance以args字典为参数，该函数内部有对args的解析，以获得addr参数。
    elif args['send']:
        send_value(args)
    elif args['status']:
        txn_status(args)


def get_balance(args):
    """
    Get the balance of a given address.
    """
    val = sum(i.value for i in find_utxos_for_address(args))
    print(val if args['--raw'] else f"{val / t.Params.LET_PER_COIN} ⛼ ")


def txn_status(args):
    """
    Get the status of a transaction.

    Prints [status],[containing block_id],[height mined]
    """
    txid = args['<txid>']  #获得<txid>位置的参数
    as_csv = args['--csv']
    mempool = send_msg(t.GetMempoolMsg())

    if txid in mempool: #如果txid在mempool里，说明该交易尚未打包确认
        print(f'{txid}:in_mempool,,' if as_csv else 'Found in mempool')
        return

    chain = send_msg(t.GetActiveChainMsg())

    for tx, block, height in t.txn_iterator(chain): #在主链中查找该交易
        if tx.id == txid:
            print(
                f'{txid}:mined,{block.id},{height}' if as_csv else
                f'Mined in {block.id} at height {height}')
            return

    print(f'{txid}:not_found,,' if as_csv else 'Not found')


def send_value(args: dict):  #发送交易
    """
    Send value to some address.
    """
    val, to_addr, sk = int(args['<val>']), args['<addr>'], args['signing_key']
    selected = set()
    my_coins = list(sorted(
        find_utxos_for_address(args), key=lambda i: (i.value, i.height)))  #按utxo的value和height两个属性排序

    for coin in my_coins:   #相当于贪心算法选择utxo集合
        selected.add(coin)
        if sum(i.value for i in selected) > val:
            break

    txout = t.TxOut(value=val, to_address=to_addr)

    txn = t.Transaction(
        txins=[make_txin(sk, coin.outpoint, txout) for coin in selected], #.outpoint是utxo的一个属性函数，返回OutPoint(self.txid, self.txout_idx)
        txouts=[txout])

    logger.info(f'built txn {txn}')
    logger.info(f'broadcasting txn {txn.id}')
    send_msg(txn)


def send_msg(data: bytes, node_hostname=None, port=None):  #可以指定对方的IP和端口
    node_hostname = getattr(send_msg, 'node_hostname', 'localhost')
    port = getattr(send_msg, 'port', 9999)

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((node_hostname, port))
        s.sendall(t.encode_socket_data(data))
        return t.read_all_from_socket(s)


def find_utxos_for_address(args: dict):
    utxo_set = dict(send_msg(t.GetUTXOsMsg())) #让全节点运行GetUTXOsMsg函数，返回utxo_set
    return [u for u in utxo_set.values() if u.to_address == args['my_addr']] #从参数里解析出to_address，并查出对应的utxo


def make_txin(signing_key, outpoint: t.OutPoint, txout: t.TxOut) -> t.TxIn:
    sequence = 0
    pk = signing_key.verifying_key.to_string()
    spend_msg = t.build_spend_message(outpoint, pk, sequence, [txout])

    return t.TxIn(
        to_spend=outpoint, unlock_pk=pk,
        unlock_sig=signing_key.sign(spend_msg), sequence=sequence)


if __name__ == '__main__':
    main(docopt(__doc__, version='edgencechain client 0.1'))
