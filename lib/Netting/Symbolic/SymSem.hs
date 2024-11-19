{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.SymSem where

import Data.List.Extra
import Data.Char

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

data UnOp
    = Not
    | R0 | R1
    | T  | V
    deriving (Eq, Ord)

instance Show UnOp where
    show = \case
        Not -> "not"
        R0  -> "r0"
        R1  -> "r1"
        T   -> "t"
        V   -> "v"

data BinOp
    = Add | Mul | Sub | Div
    | Lt | Gt | Eq | Or | And | Distinct
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
        
lnot, getr0, getr1, gett, getv :: Expr -> Expr
lnot   = UnOp Not
getr0  = UnOp R0
getr1  = UnOp R1
gett   = UnOp T
getv   = UnOp V

add, mul, sub, div, lt, gt, eq, lor, land, xor, implies, distinct, select :: Expr -> Expr -> Expr
add   = BinOp Add
mul   = BinOp Mul
sub   = BinOp Sub
div   = BinOp Div
lt    = BinOp Lt
gt    = BinOp Gt
eq    = BinOp Eq
land  = BinOp And
lor   = BinOp Or
xor   = BinOp Xor
implies  = BinOp Implies
distinct = BinOp Distinct
select   = BinOp Select

        
data Expr
    = Var String
    | LReal Rational -- TODO: check
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

-- TODO: look at concretize and normalize

instance Show Expr where
    show = \case
        Var s                   -> s
        LReal n                 -> show n -- TODO: show how? division or decimal
        LBool b                 -> lower $ show b
        UnOp  op e1             -> makeExp [show op, show e1]
        BinOp op e1 e2          -> makeExp [show op, show e1, show e2]
        TerOp op e1 e2 e3       -> makeExp [show op, show e1, show e2, show e3]
        ForAll v t b            -> makeExp ["forall", makeExp [makeExp [v, show t]], show b]
        Exists v t b            -> makeExp ["exists", makeExp [makeExp [v, show t]], show b]
        Let v t e               -> makeExp ["let", makeExp [makeExp [v, show t]], show e]

data Assert = Assert Expr

instance Show Assert where
    show (Assert e) = makeExp ["assert", show e]

data SMTStmt a b = Dec a | Ass b

-- we only provide input for t, v, and wallet if those are to be "named" and constrained, otherwise leave unconstrained
data SAMM = SAMM
    { ammName :: String
    , r0      :: (Maybe String, Maybe String)
    , r1      :: (Maybe String, Maybe String) }
    
instance Read SAMM where
    readsPrec _ ('A':'M':'M':input) = 
        let (name, _:rest1) = span (/= '(') input
            (t0, _:rest2) = span (/= ':') rest1
            (v0, _:rest3) = span (/= ',') rest2
            (t1, _:rest4) = span (/= ':') rest3
            (v1, _:rest)  = span (/= ')') rest4
        in 
            if (not . null) name && all (\c -> isAlpha c || elem c "\'_") name
                                 && all isValid [t0, v0, t1, v1]
            then [(SAMM name (toName t0, toName v0) (toName t1, toName v1), rest)]
            else []
        where 
            isValid s = --we allow either blank (for Nothing) or alphanumeric names for (Just) variables
                s == "" || s == "_" || all (\c -> isAlpha c || c == '\'') s
            toName ""  = Nothing
            toName "_" = Nothing
            toName x = pure x
    readsPrec _ _ = [] -- no parse 
    
data SUser = SUser
    { wallet :: Maybe String
    , name   :: String }
    
data STxn = STxn
    { sender :: Maybe String
    , from   :: (Maybe String, Maybe String)
    , to     :: (Maybe String, Maybe String)
    }