{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes, GADTs #-}

module Zeno.Consensus.Round
  ( ConsensusException(..)
  , step
  , stepWithTopic
  , propose
  , say
  , collectMembers
  , collectMajority
  , collectThreshold
  , haveMajority
  , collectGeneric
  , runConsensus
  , inventoryIndex
  , prioritiseRemoteInventory
  , dedupeInventoryQueries
  , majorityThreshold
  ) where

import           Control.Monad.Reader
import           Control.Monad.State

import           Control.Distributed.Process
import           Control.Distributed.Process.Node
import           Control.Distributed.Process.Serializable (Serializable)

import qualified Data.ByteString as BS
import qualified Data.Binary as Bin
import qualified Data.Map as Map

import           Network.Ethereum.Crypto

import           Zeno.Prelude
import           Zeno.Prelude.Lifted
import qualified Zeno.Consensus.P2P as P2P
import           Zeno.Consensus.Step
import           Zeno.Consensus.Types
import           Zeno.Consensus.Utils

import           Control.Monad.Free


data RoundF a where
  GetTopic     :: (Msg -> a) -> RoundF a
  GetParams    :: (ConsensusParams -> a) -> RoundF a
  LogSay       :: String -> RoundF a
  WithTimeout2 :: Serializable b => Int -> Round b -> (b -> a) -> RoundF a
  RunStep2     :: Serializable o => Msg -> Ballot o -> [Address] -> Collect o -> Int -> (StepResult o -> a) -> RoundF a

instance Functor RoundF where
  fmap f = go where
    go (GetTopic g) = GetTopic $ f . g
    go (GetParams g) = GetParams $ f . g
    go (LogSay s) = LogSay s
    go (WithTimeout2 t act g) = WithTimeout2 t act $ f . g
    go (RunStep2 m b a c i g) = RunStep2 m b a c i $ f . g

type Round = Free RoundF

getTopic = liftF (GetTopic id)
getParams = liftF (GetParams undefined)
logSay s = liftF (LogSay s)
withTimeout2 t act = liftF (WithTimeout2 t act undefined)
runStep2 m b ms x i = liftF (RunStep2 m b ms x i undefined)

runRoundConsensus :: forall a. Serializable a => Round a -> Consensus a
runRoundConsensus = iterM run where
  run :: RoundF (Consensus a) -> Consensus a
  run (GetTopic f) = get >>= f
  run (GetParams f) = ask >>= f
  run (WithTimeout2 t act f) = do
    withTimeout t $ runRoundConsensus act >>= f
  run (RunStep2 topic ballot members collect timeout f) = do
    r <- 
      lift $ lift $ do
        (send, recv) <- newChan
        _ <- spawnLocalLink $ runStep topic ballot members $ sendChan send
        collect recv timeout members
    f r






-- Run round ------------------------------------------------------------------

runConsensus :: (Serializable a, Has ConsensusNode r) => ConsensusParams
             -> a -> Round b -> Zeno r b
runConsensus params topicData act = do
  let topic = hashMsg $ toStrict $ Bin.encode topicData
      act' = evalStateT (runReaderT (runRoundConsensus act) params) topic
  ConsensusNode node <- asks $ has
  liftIO $ do
    handoff <- newEmptyMVar
    runProcess node $ do
      _ <- spawnLocalLink P2P.peerNotifier
      act' >>= putMVar handoff
    takeMVar handoff


-- Coordinate Round -----------------------------------------------------------

-- | step initiates the procedure of exchanging signed messages.
--   The messages contain a signature which is based on 
--   
step' :: Serializable a => Collect a -> a -> Round (StepResult a)
step' collect obj = do
  topic <- getTopic
  ConsensusParams members (EthIdent sk myAddr) timeout <- getParams
  let sig = sign sk topic
  let ballot = Ballot myAddr sig obj
  runStep2 topic ballot members collect timeout

stepWithTopic :: Serializable a => Topic -> Collect a -> a -> Round (StepResult a)
stepWithTopic topic collect o = putTopic topic >> step' collect o

step :: Serializable a => Collect a -> a -> Round (StepResult a)
step collect o = permuteTopic >> step' collect o
 
-- 1. Determine a starting proposer
-- 2. Try to get a proposal from them
-- 3. If there's a timeout, move to the next proposer
proposeWithRound :: forall a. Serializable a => Consensus a -> Round (StepResult a)
proposeWithRound mObj =
  determineProposers >>= withTimeout2 (5 * 1000000) . go
    where
    go :: [(Address, Bool)] -> Round (StepResult a)
    go [] = pure $ Left $ ConsensusTimeout "Ran out of proposers"
    go ((pAddr, isMe):xs) = do
      obj <- if isMe then Just <$> (undefined :: Round a) else pure Nothing
      stepWithRound (collectMembers [pAddr]) obj >>=
        \case
          Right results ->
            case Map.lookup pAddr results of
                 Just (_, Just obj2) -> pure $ Right obj2
                 _ -> pure $ Left $
                   ConsensusMischief $ printf "Missing proposal from %s" $ show pAddr
          Left (ConsensusTimeout _) -> do
            logSay $ "Timeout collecting for proposer: " ++ show pAddr
            go xs
          Left e -> pure $ Left e


propose :: forall a. Serializable a => Consensus a -> Consensus (StepResult a)
propose = runRoundConsensus . proposeWithRound

determineProposers :: Round [(Address, Bool)]
determineProposers = do
  {- This gives fairly good distribution:
  import hashlib
  dist = [0] * 64
  for i in xrange(100000):
      m = hashlib.sha256(str(i))
      d = sum(map(ord, m.digest()))
      dist[d%64] += 1
  print dist
  -}
  ConsensusParams members (EthIdent _ myAddr)  _ <- getParams
  let msg2sum = sum . map fromIntegral . BS.unpack . getMsg
  topic <- getTopic
  let i = mod (msg2sum topic) (length members)
      proposers = take 3 $ drop i $ cycle members
  pure $ [(p, p == myAddr) | p <- proposers]

permuteTopic :: Consensus Topic
permuteTopic = do
  out <- get
  put $ hashMsg $ getMsg out
  pure out


-- Check Majority -------------------------------------------------------------

-- | Collects a majority
collectMajority :: Serializable a => Collect a
collectMajority = collectGeneric haveMajority

-- | Wait for results from specific members
collectMembers :: Serializable a => [Address] -> Collect a
collectMembers addrs = collectGeneric $ \_ -> allSigned
  where allSigned inv = all id [Map.member a inv | a <- addrs]

collectThreshold :: Serializable a => Int -> Collect a
collectThreshold t = collectGeneric $ \_ inv -> length inv == t

collectGeneric :: Serializable a => ([Address] -> Inventory a -> Bool) -> Collect a
collectGeneric test recv timeout members = do
  startTime <- getCurrentTime
  fix $ \f -> do
    d <- timeDelta startTime
    let us = max 0 $ timeout - d
    minv <- receiveChanTimeout us recv
    case minv of
         Nothing -> pure $ Left (ConsensusTimeout "collect timeout")
         Just inv | test members inv -> pure $ Right inv
         _ -> f

haveMajority :: [Address] -> Inventory a -> Bool
haveMajority members inv =
   length inv >= majorityThreshold (length members)

majorityThreshold :: Int -> Int
majorityThreshold m = floor $ (fromIntegral m) / 2 + 1
