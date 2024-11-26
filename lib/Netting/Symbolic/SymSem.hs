{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.SymSem where

import Netting.Symbolic.Utils

import Text.Read
import Data.List.Extra
import Data.Char
import Debug.Trace
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
    deriving (Eq, Ord)

instance Show UnOp where
    show = \case
        Not -> "not"
        R0  -> "r0"
        R1  -> "r1"
        T   -> "t"
        V   -> "v"

instance Read UnOp where
    readsPrec _ ('n':'o':'t':[]) = [(Not, "")]
    readsPrec _ ('r':'0':[])     = [(R0, "")]
    readsPrec _ ('r':'1':[])     = [(R1, "")]
    readsPrec _ ('t':[])         = [(T, "")]
    readsPrec _ ('v':[])         = [(V, "")]
    readsPrec _ _ = []

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

instance Read BinOp where
    readsPrec _ ('+':[])     = [(Add, "")]
    readsPrec _ ('*':[])     = [(Mul, "")]
    readsPrec _ ('-':[])     = [(Sub, "")]
    readsPrec _ ('/':[])     = [(Div, "")]
    readsPrec _ ('<':[])     = [(Lt, "")]
    readsPrec _ ('>':[])     = [(Gt, "")]
    readsPrec _ ('=':[])     = [(Eq, "")]
    readsPrec _ ('>':'=':[]) = [(Gteq, "")]
    readsPrec _ ('|':'|':[]) = [(Or, "")]
    readsPrec _ ('&':'&':[]) = [(And, "")]
    readsPrec _ ('/':'=':[]) = [(Distinct, "")]
    readsPrec _ ('=':'>':[]) = [(Implies, "")]
    readsPrec _ _ = []

    
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
gteq  = BinOp Gteq
land  = BinOp And
lor   = BinOp Or
xor   = BinOp Xor
implies  = BinOp Implies
distinct = BinOp Distinct
select   = BinOp Select

        
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

--instance Read Expr where
--    readsPrec _ input = 
--        let tokenize = map Todo input in
--            []
--        where
--            readParens acc []       ctr = acc
--            readParens acc ('(':[]) ctr = [] -- error wrong parenthesis... What TODO?
--            readParens acc ('(':cs) ctr = readParens acc cs (ctr + 1)
--            readParens acc (')':cs) ctr = readParens acc cs (ctr - 1)
--            readParens acc (c : cs) ctr = readParens ((c, ctr):acc) cs ctr

data Assert = Assert Expr

instance Show Assert where
    show (Assert e) = makeExp ["assert", show e]

data Assertion = EF Expr | EU Expr Expr

instance Read Assertion where
    readsPrec _ ('E':'F':input) = undefined -- Finally
    readsPrec _ ('E':input) = undefined --Until
    readsPrec _ _ = []

data SMTStmt a b = Dec a | Ass b

-- we only provide input for t, v, and wallet if those are to be "named" and constrained, otherwise leave unconstrained
data SAMM = SAMM
    { ammName :: String
    , r0      :: (Maybe Rational, Maybe String)
    , r1      :: (Maybe Rational, Maybe String) }
    deriving (Show)

readUntil :: Char -> String -> (String, String)
readUntil c input = 
    case span (/= c) input of
        (h, _:rest) -> (h, rest)
        _           -> ("!", "")

-- like ReadUntil, but will return an error if it reads more than two words before encountering the breaker
readTokUntil :: Char -> String -> (String, String)
readTokUntil c input = 
    case span (/= c) input of
        (h, _:rest) ->
            if ((>1) . length . words) h then ("!", "") else (concat $ words h, rest)
        _           -> ("!", "")

instance Read SAMM where
    readsPrec _ ('A':'M':'M':input) = 
        let (name, rest1) = readTokUntil '(' input in if name == "!" then [] else
        let (v0,   rest2) = readTokUntil ':' rest1 in if v0   == "!" then [] else
        let (t0,   rest3) = readTokUntil ',' rest2 in if t0   == "!" then [] else
        let (v1,   rest4) = readTokUntil ':' rest3 in if v1   == "!" then [] else
        let (t1,   rest)  = readTokUntil ')' rest4 in if t1   == "!" then [] else
        if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                             && all isToken [t0, t1]
                             && all isRatio [v0, v1]
        then [(SAMM name (toVal v0, toName t0) (toVal v1, toName t1), rest)]
        else []
        where 
            isRatio "" = False
            isRatio r  = 
                if all ((==) '_') r then True else -- TODO: we allow sym vals for the values of token balance?
                case Util.split '%' r of 
                    (num:den:[]) | all isNumber num && all isNumber den -> True
                    _ -> False
            isToken "" = False
            isToken s  = s == "_" || all isAlphaNum s
            toName "_" = Nothing
            toName x   = pure x
            toVal  "_" = Nothing
            toVal  v   = readMaybe v :: Maybe Rational
    readsPrec _ _ = [] -- no parse 
    
data SToks = SToks [String] deriving (Show)

instance Read SToks where
    readsPrec _ ('T':'O':'K':'E':'N':'S':input) = 
        let (h, rest1  ) = readUntil '(' input in if h    == "!" then [] else
        let (toks, rest) = readUntil ')' rest1 in if toks == "!" then [] else
        let toks'  = Util.split ',' toks
            toks'' = map (filter (\c -> c /= ' ')) toks'
        in 
            if (any (\x -> ((> 1) . length) $ words x) toks') then [] else 
            if any (\s -> null s || all (\c -> c == ' ') s) toks'' then [] else
        [(SToks $ toks'', rest)]
    readsPrec _ _ = []
    
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
    

--data Stmt = SU SUser | SA SAMM | ST SToks | NO String deriving (Show)
--
--instance Read Stmt where
--    readsPrec _ input =
--        case readMaybe input :: Maybe SToks of
--            Just toks -> [(ST toks, "")]
--            Nothing -> 
--                case readMaybe input :: Maybe SAMM of
--                    Just samm -> [(SA samm, "")]
--                    Nothing   -> 
--                        case readMaybe input :: Maybe SUser of 
--                            Just suser -> [(SU suser, "")]
--                            Nothing    -> [(NO "No Parse", input)]
--    readsPrec _ _ = []
   
data STxn = STxn
    { sender :: Maybe String
    , from   :: (Maybe String, Maybe String)
    , to     :: (Maybe String, Maybe String)
    }