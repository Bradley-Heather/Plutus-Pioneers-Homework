{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Week04.Homework where

import Data.Aeson            (FromJSON, ToJSON)
import Data.Functor          (void)
import Data.Void             (Void)
import Data.Text             (Text)
import GHC.Generics          (Generic)
import Ledger
import Ledger.Ada            as Ada
import Ledger.Constraints    as Constraints
import Plutus.Contract       as Contract
import Plutus.Trace.Emulator as Emulator
import Wallet.Emulator.Wallet

data PayParams = PayParams
    { ppRecipient :: PubKeyHash
    , ppLovelace  :: Integer
    } deriving (Show, Generic, FromJSON, ToJSON)

type PaySchema = Endpoint "pay" PayParams

payContract :: Contract () PaySchema Text ()
payContract = do
    pp <- endpoint @"pay"
    let tx = mustPayToPubKey (ppRecipient pp) $ lovelaceValueOf $ ppLovelace pp
    void $ submitTx tx
    -- payContract -- Recursion now handled by payContractError

payContractErrHandle :: Contract () PaySchema Void ()
payContractErrHandle = do 
    Contract.handleError Contract.logError payContract
    payContractErrHandle

payTrace :: Integer -> Integer -> EmulatorTrace ()
payTrace p1 p2 = do
    h1 <- activateContractWallet (Wallet 1) payContractErrHandle
    
    callEndpoint @"pay" h1 $ PayParams
        { ppRecipient = pubKeyWallet2, ppLovelace  = p1 }
    void $ Emulator.waitNSlots 1
    
    callEndpoint @"pay" h1 $ PayParams 
        { ppRecipient = pubKeyWallet2, ppLovelace  = p2 }
    void $ Emulator.waitNSlots 1

    where pubKeyWallet2 = pubKeyHash $ walletPubKey $ Wallet 2


payTest1 :: IO ()
payTest1 = runEmulatorTraceIO $ payTrace 1000000 2000000

payTest2 :: IO ()
payTest2 = runEmulatorTraceIO $ payTrace 1000000000 2000000
