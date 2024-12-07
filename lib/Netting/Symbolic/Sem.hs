{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Sem where

import Netting.Symbolic.Utils

import Text.Read
import Data.List.Extra
import Data.Char
import Data.Ratio
import Data.Maybe
import Data.Tuple
import qualified Data.Map as M

import qualified GHC.Utils.Misc as Util

data DeclType
    = TReal
    | TToken
    | TString
    | TAmm
    | TArray DeclType DeclType
    deriving (Eq, Ord)

instance Show DeclType where
    show = \case
        TReal -> "Real"
        TToken -> "Token"
        TString -> "String"
        TAmm -> "Amm"
        TArray t1 t2 -> "(Array " ++ show t1 ++ " " ++ show t2 ++ ")"

data Decl
    = DeclVar String DeclType
    | DeclFun String DeclType DeclType

instance Show Decl where
    show = \case
        DeclVar s t -> "(declare-const " ++ s ++ " " ++ show t ++ ")"
        DeclFun s t1 t2 -> "(declare-fun " ++ s ++ " (" ++ show t1 ++ ") " ++ show t2 ++ ")"
        --TODO: DeclData s...

data UnOp
    = Not
    | R0 | R1
    | T  | V
    | Fee
    deriving (Eq, Ord)

instance Show UnOp where
    show = \case
        Not -> "not"
        R0  -> "r0"
        R1  -> "r1"
        T   -> "t"
        V   -> "v"
        Fee -> "fee"

data BinOp
    = Add | Mul | Sub | Div
    | Lt | Gt | Eq | Gteq | Or | And | Distinct
    | Xor | Implies
    | Select
    deriving (Eq, Ord)

instance Show BinOp where
    show = \case
        Add -> "+"
        Mul -> "*"
        Sub -> "-"
        Div -> "/"
        Lt -> "<"
        Gt -> ">"
        Gteq -> ">="
        Eq -> "="
        Or -> "or"
        And -> "and"
        Distinct -> "distinct"
        Xor -> "xor"
        Implies -> "=>"
        Select -> "select"

    
data TerOp
    = Store | Ite
    deriving (Eq, Ord)

instance Show TerOp where
    show = \case
        Store -> "store"
        Ite -> "ite"
        
lnot, getr0, getr1, gett, getv, gfee :: Expr -> Expr
lnot   = UnOp Not
getr0  = UnOp R0
getr1  = UnOp R1
gett   = UnOp T
getv   = UnOp V
gfee   = UnOp Fee

add, mul, sub, div, lt, gt, eq, lor, land, xor, implies, distinct, select :: Expr -> Expr -> Expr
add   = BinOp Add
mul   = BinOp Mul
sub   = BinOp Sub
div   = BinOp Div
lt    = BinOp Lt
gt    = BinOp Gt
eq    = BinOp Eq
gteq  = BinOp Gteq
land  = BinOp And
lor   = BinOp Or
xor   = BinOp Xor
implies  = BinOp Implies
distinct = BinOp Distinct
select   = BinOp Select

store, ite :: Expr -> Expr -> Expr -> Expr
store = TerOp Store
ite   = TerOp Ite

        
data Expr
    = Var String
    | LReal Rational
    | LTok String
    | LBool Bool
    | UnOp  UnOp  Expr
    | BinOp BinOp Expr Expr
    | TerOp TerOp Expr Expr Expr
    | ForAll String DeclType Expr
    | Exists String DeclType Expr
    | Let String Expr Expr
    deriving (Eq, Ord)
    
makeExp :: [String] -> String
makeExp ss = "(" ++ unwords ss ++ ")"

instance Show Expr where
    show = \case
        Var s                   -> s
        LReal r                 -> makeExp [show Div, show $ numerator r, show $ denominator r]
        LTok t                  -> t
        LBool b                 -> lower $ show b
        UnOp  op e1             -> makeExp [show op, show e1]
        BinOp op e1 e2          -> makeExp [show op, show e1, show e2]
        TerOp op e1 e2 e3       -> makeExp [show op, show e1, show e2, show e3]
        ForAll v t b            -> makeExp ["forall", makeExp [makeExp [v, show t]], show b]
        Exists v t b            -> makeExp ["exists", makeExp [makeExp [v, show t]], show b]
        Let v t e               -> makeExp ["let", makeExp [makeExp [v, show t]], show e]

-- Parses our text into either a nullary, unary or binary expression
data ParseHelper a b c = Done a | UnO b | BinO c

prec :: (ParseHelper Expr UnOp BinOp) -> Maybe Int
prec (Done _)        = return (-1)
prec (BinO Implies)  = return 1
prec (BinO Or  )     = return 2
prec (BinO And )     = return 3
prec (BinO Distinct) = return 4
prec (BinO Eq  )     = return 4 
prec (UnO Not)       = return 5
prec (BinO Lt  )     = return 6
prec (BinO Gt  )     = return 6
prec (BinO Gteq)     = return 6
prec (BinO Add )     = return 7
prec (BinO Sub )     = return 7
prec (BinO Mul )     = return 8
prec (BinO Div )     = return 8
prec (BinO Xor)      = Nothing -- These operators are not currently supported (some are implicitly)
prec (UnO R0 )       = Nothing 
prec (UnO R1 )       = Nothing
prec (UnO T  )       = Nothing
prec (UnO V  )       = Nothing
prec (BinO Select)   = Nothing

data Assert = Assert Expr

instance Show Assert where
    show (Assert e) = makeExp ["assert", show e]

data SMTStmt a b = Dec a | Ass b

data SType = DTok | DAmm | DUser | DUsers | Symval deriving (Eq, Ord, Show)

data TFee r = Conc r | Sym | None deriving (Show, Eq)

-- we only provide input for t, v, and wallet if those are to be "named" and constrained, otherwise leave unconstrained
data SAMM = SAMM
    { ammName :: String
    , r0      :: (Maybe Rational, String)
    , r1      :: (Maybe Rational, String)
    , fee     :: TFee Rational}
    deriving (Show, Eq)
    
data SToks = SToks [String] deriving (Show)

data SUser = SUser
    { wallet :: [(String, (Maybe Rational))]
    , name   ::  String }
    deriving (Show)

instance Read SUser where
    readsPrec _ ('U':'S':'E':'R':input) = 
        let (name, rest1) = readTokUntil '(' input in if name == "!" then [] else
        let (wal, rest)   = readUntil    ')' rest1 in if wal  == "!" then [] else
        let wal'  = Util.split ',' wal
            wal'' = map parsePair wal'
        in
        if (not . null) name && all (\c -> isAlphaNum c || c == '_') name 
                             && all isJust wal'' 
        then let wal''' = map swap (Util.mapFst toR (map fromJust wal''))
             in [( SUser wal''' name, rest)]
        else []
            where
                toR s = readMaybe s :: Maybe Rational
                parsePair s | all (flip elem " \n\t") s = Nothing
                parsePair s  = 
                    case Util.split ':' s of
                        (v:t:[]) -> 
                            let v' = concat $ words v
                                t' = concat $ words t in 
                                    if isToken t' && isRatio v' then Just (v', t')
                                    else Nothing
                        otherwise -> Nothing
                    where 
                        isRatio "" = False
                        isRatio r  = 
                            if all ((==) '_') r then True else -- TODO: we allow sym vals for the values of token balance?
                            case Util.split '%' r of 
                                (num:den:[]) | all isNumber num && all isNumber den -> True
                                _ -> False
                        isToken "" = False
                        isToken s  = all isAlphaNum s -- TODO: allow symbolic tokens in the wallet? or ludacris
    readsPrec _ _ = []