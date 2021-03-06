from typing import (
    Iterable, NamedTuple, Dict, Mapping, Union, Tuple,
    Callable)

from utils.Errors import TxUnlockError
from utils.Errors import TxnValidationError
from utils.Errors import ChainFileLostError

from utils.Utils import Utils
from params.Params import Params
from wallet.Wallet import Wallet
from ds.UnspentTxOut import UnspentTxOut
from ds.BaseUTXO_Set import BaseUTXO_Set
from ds.TxIn import TxIn
from ds.TxOut import TxOut
from ds.BaseMemPool import BaseMemPool
from ds.BaseBlockChain import BaseBlockChain



import binascii
import ecdsa
import logging
import os



logging.basicConfig(
    level=getattr(logging, os.environ.get('TC_LOG_LEVEL', 'INFO')),
    format='[%(asctime)s][%(module)s:%(lineno)d] %(levelname)s %(message)s')
logger = logging.getLogger(__name__)

# Used to represent the specific output within a transaction.

class Transaction(NamedTuple):
    txins: Iterable[TxIn]
    txouts: Iterable[TxOut]


    locktime: int = None

    @property
    def is_coinbase(self) -> bool:
        return len(self.txins) == 1 and self.txins[0].to_spend is None

    @classmethod
    def create_coinbase(cls, pay_to_addr, value, height):
        return cls(
            txins=[TxIn(
                to_spend=None,
                # Push current block height into unlock_sig so that this
                # transaction's ID is unique relative to other coinbase txns.
                unlock_sig=str(height).encode(),
                unlock_pk=None,
                sequence=0)],
            txouts=[TxOut(
                value=value,
                to_address=pay_to_addr)],
        )

    @property
    def id(self) -> str:
        return Utils.sha256d(Utils.serialize(self))

    def validate_basics(self, as_coinbase=False):
        if not self.txouts:
            raise TxnValidationError('Missing txouts')
        if not as_coinbase and not self.txins:
            raise TxnValidationError('MIssing txins for not coinbase transation')
        if not as_coinbase:
            if None in [txin.to_spend for txin in self.txins]:
                raise TxnValidationError('None to spend for not coinbase transation')
        if as_coinbase and len(self.txins)>1:
            raise TxnValidationError('Coinbase transaction has more than one TxIns')
        if as_coinbase and self.txins[0].to_spend is not None:
            raise TxnValidationError('Coinbase transaction should not have valid to_spend in txins')

        if len(Utils.serialize(self)) > Params.MAX_BLOCK_SERIALIZED_SIZE:
            raise TxnValidationError('Too large')

        if sum(t.value for t in self.txouts) > Params.MAX_MONEY:
            raise TxnValidationError('Spend value too high')


    def validate_txn(self,
                     utxo_set: BaseUTXO_Set,
                     mempool: BaseMemPool = None,
                     active_chain: BaseBlockChain = None,
                     as_coinbase: bool = False,
                     siblings_in_block: Iterable[NamedTuple] = None,  #object
                     allow_utxo_from_mempool: bool = True,
                     ) -> bool:
        """
        Validate a single transaction. Used in various contexts, so the
        parameters facilitate different uses.
        """
        def validate_signature_for_spend(txin, utxo: UnspentTxOut):
            def build_spend_message(to_spend, pk, sequence, txouts) -> bytes:
                """This should be ~roughly~ equivalent to SIGHASH_ALL."""
                return Utils.sha256d(
                    Utils.serialize(to_spend) + str(sequence) +
                    binascii.hexlify(pk).decode() + Utils.serialize(txouts)).encode()

            pubkey_as_addr = Wallet.pubkey_to_address(txin.unlock_pk)
            verifying_key = ecdsa.VerifyingKey.from_string(
                txin.unlock_pk, curve=ecdsa.SECP256k1)

            if pubkey_as_addr != utxo.to_address:
                raise TxUnlockError("Pubkey doesn't match")

            try:
                spend_msg = build_spend_message(
                    txin.to_spend, txin.unlock_pk, txin.sequence, self.txouts)
                verifying_key.verify(txin.unlock_sig, spend_msg)
            except Exception:
                logger.exception(f'[ds] Key verification failed')
                raise TxUnlockError("Signature doesn't match")
            return True        


        self.validate_basics(as_coinbase=as_coinbase)

        available_to_spend = 0

        for idx, txin in enumerate(self.txins):
            utxo = utxo_set.get().get(txin.to_spend)

            if siblings_in_block:
                from ds.UTXO_Set import UTXO_Set
                utxo = utxo or UTXO_Set.find_utxo_in_list(txin, siblings_in_block)

            if allow_utxo_from_mempool:
                utxo = utxo or mempool.find_utxo_in_mempool(txin)

            if not utxo:
                raise TxnValidationError(
                    f'Could find no UTXO for TxIn [{idx}] for txn: {self.id}',
                    to_orphan=self)

            if active_chain is not None:
                if utxo.is_coinbase and \
                        (active_chain.height - utxo.height) < \
                        Params.COINBASE_MATURITY:
                    raise TxnValidationError(f'Coinbase UTXO not ready for spend')

            try:
                validate_signature_for_spend(txin, utxo)
            except TxUnlockError:
                raise TxnValidationError(f'{txin} is not a valid spend of {utxo}')

            available_to_spend += utxo.value

        if available_to_spend < sum(o.value for o in self.txouts):
            raise TxnValidationError('Spend value is more than available')

        return True




