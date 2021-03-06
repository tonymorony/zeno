
module Zeno.Notariser.UTXO where

import Control.Monad.Reader

import Network.Bitcoin
import Network.Komodo
import Network.ZCash.Sapling
import qualified Haskoin as H

import Zeno.Data.Aeson
import Zeno.Prelude
import Zeno.Process


-- TODO: Should be a single "Has Komodo r"
forkMonitorUTXOs :: (Has KomodoIdent r, Has BitcoinConfig r)
                 => Word64 -> Int -> Int -> Zeno r ()
forkMonitorUTXOs amount minimum nsplit = do
  KomodoIdent{..} <- asks has
  run $ do
    available <- isRightAmount <$> komodoUtxos [kmdAddress]

    when (length available < minimum) do
      logInfo $ printf "Creating %i UTXOs of %i" nsplit amount
      makeSplits amount nsplit
      threadDelay $ 5 * 60 * 1000000

    threadDelay $ 30 * 1000000
  where
    isRightAmount = filter ((==amount) . utxoAmount)
    onError e = do
      logError $ show e
      threadDelay $ 30 * 1000000
    run act = do
      _ <- spawn "monitor UTXOs" $ \_ -> do
        forever $ act `catchAny` onError
      pure ()


makeSplits :: (Has BitcoinConfig r, Has KomodoIdent r) => Word64 -> Int -> Zeno r ()
makeSplits amount nsplits = do
  KomodoIdent{..} <- asks has

  let outs = replicate nsplits (H.PayPK kmdPubKeyI, amount)
      fee = 10000
      total = (sum $ snd <$> outs) + fee
      viable = reverse . sortOn (\c -> ( utxoConfirmations c * (-1)
                                       , utxoTxid c
                                       ))
                       . filter (\c -> utxoAmount c > total)
                       . filter utxoSpendable
      buildSplit x =
        let changeSats = utxoAmount x - total
            changeAddr = getAddrHash $ utxoAddress x
            change = if changeSats >= fee
                        then [(H.PayPKHash changeAddr, changeSats)]
                        else []  -- avoid dust
         in saplingFromLegacy <$> H.buildTx [getOutPoint x] (outs ++ change)

      fromSats :: Word64 -> String
      fromSats sats = printf "%f" $ (fromIntegral sats :: Double) / (10e7)
   in do
     utxos <- viable <$> komodoUtxos []
     case utxos of
          [] -> do
            logWarn $ "No funds! Need a spendable input of at least " ++ fromSats total ++ " KMD"
          (x:_) -> do
            logDebug $ "Chose input: " ++ show (getOutPoint x)
            case buildSplit x of
                 Left err -> do
                   logError $ "Could not build transaction: " <> err
                 Right mtx -> do
                   signed <- queryBitcoin "signrawtransaction" [mtx]
                   case signed .? "{hex}" :: Maybe SaplingTx of
                     Just tx -> do
                       splitId <- queryBitcoin "sendrawtransaction" [tx]
                       logInfo $ "Sent split tx: " ++ splitId
                     Nothing -> do
                       logError $ "Could not sign transaction: " <> show signed
