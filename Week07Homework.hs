{-# LANGUAGE DataKinds             #-} -- prevents untyped functional programming at type level
{-# LANGUAGE DeriveAnyClass        #-} -- Derive any other class
{-# LANGUAGE DeriveGeneric         #-} -- Automatically derive generic Instances
{-# LANGUAGE FlexibleContexts      #-} -- Remove the type-variable restriction on class contexts
{-# LANGUAGE MultiParamTypeClasses #-} -- Allow the definition of typeclasses with more than one parameter
{-# LANGUAGE NoImplicitPrelude     #-} -- Don't import Prelude by Default
{-# LANGUAGE OverloadedStrings     #-} -- Give a string literal a type (IsString a) => a
{-# LANGUAGE ScopedTypeVariables   #-} -- Enable lexical scoping of type variables explicitly introduced with forall
{-# LANGUAGE TemplateHaskell       #-} -- Enable Template Haskell’s splice and quotation syntax.
{-# LANGUAGE TypeApplications      #-} -- Allows you to use visible type application in expressions (preceded by an @)
{-# LANGUAGE TypeFamilies          #-} -- Allow use and definition of indexed type and data families.
{-# LANGUAGE TypeOperators         #-} -- Allows you to use infix operators in types.

module Week07.RockPaperScissors 
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , Last (..)
    , ThreadToken
    , Text
    , endpoints 
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)  -- Types and functions for working efficiently with JSON data.
import           Data.Monoid                   (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
-- The following are Plutus specific
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import           Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts         as Scripts
import           Plutus.Contract              as Contract
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Playground.Contract          (ToSchema)
-- Import required Prelude as it was not imported due to NoImplicitPrelude Language extension 
import           Prelude                      (Semigroup(..), Show (..), String)
import qualified Prelude

data Game = Game 
    { gFirst          :: !PubKeyHash
    , gSecond         :: !PubKeyHash
    , gStake          :: !Integer
    , gPlayDeadline   :: !POSIXTime
    , gRevealDeadline :: !POSIXTime
    , gToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq)

PlutusTx.makeLift ''Game -- makeLift :: Name -> Q [Dec]

data GameChoice = Rock | Paper | Scissors
   deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Rock     == Rock     = True
    Paper    == Paper    = True
    Scissors == Scissors = True
    _        == _        = False

{-# INLINABLE beats #-}
beats :: GameChoice -> GameChoice -> Bool
beats Rock     Scissors  = True
beats Scissors Paper     = True
beats Paper    Rock      = True
beats _        _         = False

PlutusTx.unstableMakeIsData ''GameChoice

data GameDatum = GameDatum ByteString (Maybe GameChoice) | Finished  -- ByteString is the hash the first player submits, (Maybe GameChoice) is the possible move by the second player, Finished represents final state of the StateMachine
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc') -- bs = ByteString,  mc = Maybe GameChoice
    Finished        == Finished          = True
    _               == _                 = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | RevealWin ByteString GameChoice | RevealDraw ByteString GameChoice | ClaimFirst | ClaimSecond  -- Play is when the second player moves (GameChoice as an argument), ClaimFirst for when the second player doesn't play
      deriving Show 

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum  -- Maybe Monad
gameDatum o f = do
    dh        <- txOutDatum o   -- o is the TxOut (Maybe as TxOut may not have a datum) 
    Datum d   <- f dh           -- Use second argument function to get datum. Datum is a type wrapper around builtInData 
    PlutusTx.fromBuiltinData d  -- Maybe turn d into a GameDatum

{-# INLINABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)
transition game s r = case (stateValue s, stateData s, r) of -- s = State Datum (pair consisting of datum and value), r = Game Redeemer
    (v, GameDatum bs Nothing, Play c)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gSecond game)         <>
                                                       Constraints.mustValidateIn (to $ gPlayDeadline game)       
                                                     , State (GameDatum bs $ Just c) (lovelaceValueOf $ 2 * gStake game)
                                                     )
    (v, GameDatum _ (Just _), RevealWin _ _)
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)
                                                     , State Finished mempty
                                                     )

    (v, GameDatum _ (Just _), RevealDraw _ _)
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gFirst game)                                   <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)                     <>
                                                       Constraints.mustPayToPubKey (gFirst game) (lovelaceValueOf $ gStake game)  <>
                                                       Constraints.mustPayToPubKey (gSecond game) (lovelaceValueOf $ gStake game)
                                                     , State Finished mempty
                                                     )                                               

    (v, GameDatum _ Nothing, ClaimFirst)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)
                                                     , State Finished mempty
                                                     )
    (v, GameDatum _ (Just _), ClaimSecond)
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
                                                     , State Finished mempty
                                                     )
    _                                        -> Nothing

{-# INLINABLE final #-}
final :: GameDatum -> Bool
final Finished = True
final _        = False

{-# INLINABLE check #-}
check :: ByteString -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
check bsRock' bsPaper' bsScissors' (GameDatum bs (Just c)) (RevealDraw nonce _) _ =
    sha2_256 (nonce `concatenate`  if c == Rock then bsRock' else if c == Paper then bsPaper' else bsScissors') ==  bs 
    
check bsRock' bsPaper' bsScissors' (GameDatum bs (Just _)) (RevealDraw nonce c) _ =
    sha2_256 (nonce `concatenate`  if c == Rock then bsRock' else if c == Paper then bsPaper' else bsScissors') ==  bs 

check _       _       _            _                       _                _     = True


 
{-# INLINABLE gameStateMachine #-}
gameStateMachine :: Game -> ByteString -> ByteString -> ByteString -> StateMachine GameDatum GameRedeemer
gameStateMachine game bsRock' bsPaper' bsScissors' = StateMachine
    { smTransition  = transition game
    , smFinal       = final
    , smCheck       = check bsRock' bsPaper' bsScissors'
    , smThreadToken = Just $ gToken game
    }

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsRock' bsPaper' bsScissors' = mkValidator $ gameStateMachine game bsRock' bsPaper' bsScissors'

type Gaming = StateMachine GameDatum GameRedeemer

bsRock, bsPaper, bsScissors :: ByteString
bsRock     = "0"
bsPaper    = "1"
bsScissors = "2"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer
gameStateMachine' game = gameStateMachine game bsRock bsPaper bsScissors

typedGameValidator :: Game -> Scripts.TypedValidator Gaming
typedGameValidator game = Scripts.mkTypedValidator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsRock
        `PlutusTx.applyCode` PlutusTx.liftCode bsPaper
        `PlutusTx.applyCode` PlutusTx.liftCode bsScissors)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . typedGameValidator

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

gameClient :: Game -> StateMachineClient GameDatum GameRedeemer
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (typedGameValidator game)

data FirstParams = FirstParams
    { fpSecond         :: !PubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !POSIXTime
    , fpRevealDeadline :: !POSIXTime
    , fpNonce          :: !ByteString
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

mapError' :: Contract w s SMContractError a -> Contract w s Text a  -- In order to use Text as the error message
mapError' = mapError $ pack . show

waitUntilTimeHasPassed :: AsContractError e => POSIXTime -> Contract w s e ()
waitUntilTimeHasPassed t = void $ awaitTime t >> waitNSlots 1

firstGame :: forall s. FirstParams -> Contract (Last ThreadToken) s Text ()
firstGame fp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    tt  <- mapError' getThreadToken
    let game   = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = tt
            }
        client = gameClient game
        v      = lovelaceValueOf (fpStake fp)
        c      = fpChoice fp
        bs     = sha2_256 $ fpNonce fp `concatenate` if c == Rock then bsRock else if c == Paper then bsPaper else bsScissors
    void $ mapError' $ runInitialise client (GameDatum bs Nothing) v
    logInfo @String $ "made first move: " ++ show (fpChoice fp)
    tell $ Last $ Just tt

    waitUntilTimeHasPassed $ fpPlayDeadline fp

    m <- mapError' $ getOnChainState client
    case m of
        Nothing             -> throwError "game output not found"
        Just ((o, _), _) -> case tyTxOutData o of

            GameDatum _ Nothing -> do
                logInfo @String "second player did not play"
                void $ mapError' $ runStep client ClaimFirst
                logInfo @String "first player reclaimed stake"

            GameDatum _ (Just c') | beats c c' -> do
                logInfo @String "second player played and lost"
                void $ mapError' $ runStep client $ RevealWin (fpNonce fp) (fpChoice fp)
                logInfo @String "first player revealed and won"

            GameDatum _ (Just c') | c' == c -> do
                logInfo @String "second player played and drew"
                void $ mapError' $ runStep client $ RevealDraw (fpNonce fp) (fpChoice fp)
                logInfo @String "first player revealed and drew"

            _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
    { spFirst          :: !PubKeyHash
    , spStake          :: !Integer
    , spPlayDeadline   :: !POSIXTime
    , spRevealDeadline :: !POSIXTime
    , spChoice         :: !GameChoice
    , spToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON)

secondGame :: forall w s. SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game   = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = spToken sp
            }
        client = gameClient game
    m <- mapError' $ getOnChainState client
    case m of
        Nothing          -> logInfo @String "no running game found"
        Just ((o, _), _) -> case tyTxOutData o of
            GameDatum _ Nothing -> do
                logInfo @String "running game found"
                void $ mapError' $ runStep client $ Play $ spChoice sp
                logInfo @String $ "made second move: " ++ show (spChoice sp)

                waitUntilTimeHasPassed $ spRevealDeadline sp

                m' <- mapError' $ getOnChainState client
                case m' of
                    Nothing -> logInfo @String "Second player didn't win"

                    Just _  -> do
                        logInfo @String "first player didn't reveal"
                        void $ mapError' $ runStep client ClaimSecond
                        logInfo @String "second player Won"

            _ -> throwError "unexpected datum"

type GameSchema = Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract (Last ThreadToken) GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  >>= firstGame
    second = endpoint @"second" >>= secondGame
