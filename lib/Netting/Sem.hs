module Netting.Sem where

import qualified Data.Map as M
import qualified Data.Sequence as S
import qualified Data.List as L

data AtomicToken
  = T0
  | T1
  | T2
  deriving (Eq, Ord)

instance Show AtomicToken where 
  show T0 = "t0"
  show T1 = "t1"
  show T2 = "t2"

data MintedToken a
  = MT (a, a)
  deriving (Ord)

instance (Show a) => Show (MintedToken a) where
  show (MT (t0, t1)) = "{" ++ (show t0) ++ ", " ++ (show t1) ++ "}"

instance (Eq a) => Eq (MintedToken a) where
  MT (t0, t1) == MT (t2, t3)
    | (t0 == t2 && t1 == t3) || (t0 == t3 && t1 == t2) = True
    | otherwise                                        = False
  mtok1 /= mtok2 = not $ mtok1 == mtok2

type MintedTokenT = MintedToken AtomicToken

-- sort of like "Either", just for tokens
data Token a b = AtomTok a | MintTok b
  deriving (Eq, Ord)

instance (Show a, Show b) => Show (Token a b) where
  show (AtomTok t) = show t
  show (MintTok t) = show t

type TokenT = Token AtomicToken MintedTokenT 

type Balance = M.Map TokenT Rational

data User = User 
  { wallet  :: Balance,
    name    :: String }
    deriving Eq
  
instance Show User where 
  show (User w n) = n ++ "[" ++ (show_bal w) ++ "]"
    where 
      show_bal = unwords . L.intersperse ", " . map (\(t, v) -> (show $ fromRational v) ++ ": " ++ (show t)) . M.toList

type TokenAmt = (AtomicToken, Rational)

type MintedTokenAmt = (MintedTokenT, Rational)

data AMM = AMM 
  { r0 :: TokenAmt,
    r1 :: TokenAmt }

instance Show AMM where 
  show (AMM (t0, r0) (t1, r1)) = "{" ++ (show $ fromRational r0) ++ ": " ++ (show t0) ++ ", "
                                     ++ (show $ fromRational r1) ++ ": " ++ (show t1) ++ "}"

instance Eq AMM where
  AMM r0 r1 == AMM r2 r3 
    | (r0 == r2 && r1 == r3) || (r0 == r3 && r1 == r2) = True
    | otherwise                                        = False
  amm1 /= amm2 = not $ amm1 == amm2

type State = ([AMM], [User])

data Transaction a b c
  = Swp a | Dep b | Rdm c
  deriving Eq

instance (Show a, Show b, Show c) => Show (Transaction a b c) where 
  show (Swp swp) = show swp
  show (Dep dep) = show dep
  show (Rdm rdm) = show rdm

type TransactionT
  = Transaction Swap Deposit Redeem

data Swap
  = Swap
  { sender :: String,
    from   :: TokenAmt,
    to     :: TokenAmt }
    deriving (Eq)

instance Show Swap where 
  show (Swap n (t0, v0) (t1, v1)) = n ++ ": swap(" ++ (show $ fromRational v0) ++ ": " ++ (show t0) ++ ", " 
                                      ++ (show $ fromRational v1) ++ ": " ++ (show t1) ++ ")"

data Deposit
  = Deposit
  { depositor :: String,
    v0        :: TokenAmt,
    v1        :: TokenAmt }
    deriving Eq

instance Show Deposit where 
  show (Deposit n (t0, v0) (t1, v1)) = n ++ ": deposit(" ++ (show $ fromRational v0) ++ ": " ++ (show t0) ++ ", " 
                                         ++ (show $ fromRational v1) ++ ": " ++ (show t1) ++ ")"

data Redeem
  = Redeem
  { redeemer :: String,
    v        :: MintedTokenAmt }
    deriving Eq

instance Show Redeem where 
  show (Redeem n (mt, v)) = n ++ ": redeem(" ++ (show $ fromRational v) ++ ": " ++ (show mt) ++ ")"

type Queue = S.Seq TransactionT

type QLength = Int

data Configuration = Configuration
  { lastGreen :: State,
    simulated :: State,
    queue     :: Queue }
    deriving (Show, Eq)