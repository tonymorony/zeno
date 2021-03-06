{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Network.Ethereum.Crypto
  ( module ALL
  , EthIdent(..)
  , Address(..)
  , Key(..)
  , deriveEthIdent
  , deriveEthAddress
  , genSecKey
  , sign
  , recoverAddr
  ) where


import           Crypto.Secp256k1 as ALL
                 (CompactRecSig(..), Msg, PubKey, SecKey, secKey, derivePubKey)
import qualified Crypto.Secp256k1 as Secp256k1

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import           Data.Monoid
import           Zeno.Data.FixedBytes

import           Network.Ethereum.Crypto.Address as ALL
import           Network.Ethereum.Crypto.Hash as ALL
import           Network.Ethereum.Crypto.Trie as ALL
import           Zeno.Data.Aeson hiding (Key)
import           Zeno.Prelude
import           Zeno.Data.Hex

import           System.Entropy


data EthIdent = EthIdent 
  { ethSecKey :: SecKey
  , ethAddress :: Address
  }
  deriving (Show)

deriveEthIdent :: SecKey -> EthIdent
deriveEthIdent sk = EthIdent sk $ deriveEthAddress $ derivePubKey sk

deriveEthAddress :: PubKey -> Address
deriveEthAddress = Address . PrefixedHex . toFixedR . sha3' . BS.drop 1 . Secp256k1.exportPubKey False

type ToBytes32 s = StringConv s Bytes32
toBytes32 :: ToBytes32 s => s -> Bytes32
toBytes32 = toS

recoverAddr :: ToBytes32 s => s -> CompactRecSig -> Maybe Address
recoverAddr bs crs = deriveEthAddress <$> recover crs m
  where m = fromJust $ Secp256k1.msg $ unFixed $ toBytes32 bs

genSecKey :: IO SecKey
genSecKey = do
  bytes <- getEntropy 32
  case secKey bytes of
       Just sk -> pure sk
       Nothing -> fail "IO error generating secret key"


-- TODO: Return Either here
recover :: CompactRecSig -> Msg -> Maybe PubKey
recover crs message = do
  rs <- Secp256k1.importCompactRecSig crs
  let s = Secp256k1.convertRecSig rs
      (_, bad) = Secp256k1.normalizeSig s
   in if bad then Nothing
             else Secp256k1.recover rs message


sign :: ToBytes32 s => SecKey -> s -> CompactRecSig
sign sk b = Secp256k1.exportCompactRecSig $ Secp256k1.signRecMsg sk m
  where m = fromJust $ Secp256k1.msg $ unFixed $ toBytes32 b


instance ToJSON CompactRecSig where
  toJSON (CompactRecSig r s v) = toJsonHex $
    fromShort r <> fromShort s <> (if v == 0 then "\0" else "\1")

instance FromJSON CompactRecSig where
  parseJSON val = do
    bs <- unHex <$> parseJSON val
    let (r, rest) = BS8.splitAt 32 bs
        (s, v)    = BS8.splitAt 32 rest
        f = pure . CompactRecSig (toShort r) (toShort s)
    case v of "\0" -> f 0
              "\1" -> f 1
              _      -> fail "Sig invalid"

newtype Key a = Key a

instance (Show a) => ToJSON (Key a) where
  toJSON (Key a) = toJSON $ init $ drop 8 $ show a
