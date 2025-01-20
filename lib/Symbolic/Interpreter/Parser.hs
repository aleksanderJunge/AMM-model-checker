{-# LANGUAGE LambdaCase #-}

module Symbolic.Interpreter.Parser where

import Data.Maybe
import Symbolic.Sem
import Symbolic.Utils
import Symbolic.Interpreter.SymTab
import Data.List.Split
import Data.List
import qualified Data.Map as M
import Data.List.Extra
import qualified GHC.Utils.Misc as Util
import Data.Either
import Data.Either.Extra
import Data.Char
import Text.Read hiding (prec)

parse :: Env String SType -> String -> Either String (Expr, ExpType)
parse stab input = 
  let string_depth = mergeToks . splitWhen' . reverse $ readParens [] input 0
  in if isLeft string_depth then Left "failed to parse string depth" else
    let string_depth' = Util.mapFst (tokenize stab) (fromRight [] string_depth)
    in if any isLeft (map fst string_depth') then Left . concat . intersperse "\n" $ lefts (map fst string_depth') else 
    let tokens_depth = Util.mapFst fromRight' string_depth'
    in case parseRec tokens_depth of
      Right [(Done (exp, t), _)] -> Right (exp, t)
      Right _ -> Left "parsing didn't result in single exp"
      Left e  -> Left $ e ++ "\nin expression:\n" ++ input
  where 
    parseRec :: [(ToParse, Int)] -> Either String [(ToParse, Int)]
    parseRec [single] = Right [single]
    parseRec inp = 
      let max_depth = foldl (\acc (exp, i) -> case exp of {Done _ -> acc; _ -> max i acc}) 0 inp
          toParse = takeWhile (\(_, i) -> i == max_depth) (dropWhile (\(_, i)-> i /= max_depth) inp) -- parses leftmost 'deepest' exp (based on parenthesis), might be 0 if no ()
          front   = takeWhile (\(_, i) -> i /= max_depth) inp
          back   = drop (length front + length toParse) inp
      in case parse' (map fst toParse) of 
            Right exp -> parseRec (front ++ [(Done exp, max_depth - 1)] ++ back)
            Left e    -> Left e

    parse' :: [ToParse] -> Either String (Expr, ExpType) -- assumes a flat structure with no parenthesis
    parse' [(Done exp)] = Right exp
    parse' a        = 
      let precs     = map prec a
      in if (>0) . length $ (filter isNothing precs) then Left "trying to parse op whose precedence is unspecified" else
      let max_prec  =  foldl (\hi i -> max hi i) 0 (map fromJust precs)
          idx       = fromJust $ findIndex (\exp -> (fromJust $ prec exp) == max_prec) a
      in case a !? idx of
          Nothing       -> Left "out of bounds idx access when looking for operator"
          Just (UnO u)  -> let operand = get_adj_exp a (idx + 1)
                           in if isLeft operand then operand else 
                           let (exp, t) = fromRight' operand in
                           case u of
                            Not ->  if t == TRational then Left "error: expected boolean argument to 'not'"
                                    else let (exp', t') = (UnOp u (exp), TBool)
                                         in parse' $ (take idx a) ++ [Done (exp', t')] ++ (drop ( idx + 2) a)
          Just (BinO b) -> let operand1 = get_adj_exp a (idx - 1)
                           in if isLeft operand1 then operand1 else 
                           let operand2 = get_adj_exp a (idx + 1) 
                           in if isLeft operand2 then operand2 else 
                           let (exp1, t1) = fromRight' operand1
                               (exp2, t2) = fromRight' operand2
                           in case b of
                                b' | elem b' [Or, And, Implies] -> -- bools input & output
                                  if t1 == TRational then Left $ "left argument of "  ++ (show b) ++ " is rational, but expected bool" else
                                  if t2 == TRational then Left $ "right argument of " ++ (show b) ++ " is rational, but expected bool"
                                  else let done_exp = (BinOp b exp1 exp2, TBool) 
                                       in parse' $ (take (idx - 1) a) ++ [Done done_exp] ++ (drop ( idx + 2) a)
                                b' | elem b' [Add, Sub, Mul, Div] -> -- real inputs & real output
                                  if t1 == TBool then Left $ "left argument of "  ++ (show b) ++ " is bool, but expected rational" else
                                  if t2 == TBool then Left $ "right argument of " ++ (show b) ++ " is bool, but expected rational"
                                  else let done_exp = (BinOp b exp1 exp2, TRational) 
                                       in parse' $ (take (idx - 1) a) ++ [Done done_exp] ++ (drop ( idx + 2) a)
                                b' | elem b' [Lt, Gt, Gteq] -> -- real input & bool output 
                                  if t1 == TBool then Left $ "left argument of "  ++ (show b) ++ " is bool, but expected rational" else
                                  if t2 == TBool then Left $ "right argument of " ++ (show b) ++ " is bool, but expected rational"
                                  else let done_exp = (BinOp b exp1 exp2, TBool) 
                                       in parse' $ (take (idx - 1) a) ++ [Done done_exp] ++ (drop ( idx + 2) a)
                                b' | elem b' [Distinct, Eq] -> -- any input & bool output
                                  if t1 /= t2 then Left $ "mismatching types for the arguments of " ++ (show b) else 
                                  let done_exp = (BinOp b exp1 exp2, TBool) 
                                  in parse' $ (take (idx - 1) a) ++ [Done done_exp] ++ (drop ( idx + 2) a)
          _             -> error "Trying to re-eval an already evaled exp"

    get_adj_exp a i =
        case a !? i of 
          Nothing         -> Left "adjacent expr was not accessible"
          Just (UnO _)    -> Left "unop (unop expr): not supported (not necessary so far)"
          Just (BinO _)   -> Left "Found 2 operands next to each other"
          Just (Done (exp, t)) -> Right (exp, t)

    tokenize :: Env String SType -> String -> Either String ToParse
    tokenize stab s =
      case readMaybe s :: Maybe UnOp of
        Just uno -> Right . UnO $ uno
        Nothing  -> do
          case readMaybe s :: Maybe BinOp of
            Just bino -> Right . BinO $ bino
            Nothing   -> do
              case toVal s :: Maybe Rational of 
                Just r -> Right . Done $ (LReal r, TRational)
                Nothing -> 
                  case toVar stab s of
                    Right exp -> return . Done $ (exp, TRational)
                    Left err  -> Left err
    toVar stab "" = Left "indexing empty string"
    toVar stab n = 
        case Util.split '.' n of 
            (name:[])       | all (\c -> isAlphaNum c || c == '_') name  -> Right $ Var (name)
            (name:field:[]) | all (\c -> isAlphaNum c || c == '_') name &&
                              all (\c -> isAlphaNum c || c == '_') field ->
                                case M.lookup name stab of 
                                  Just DUser ->  Right . Var $ name +@ field
                                  Just (DAmm t0 t1) | field == t0    ->  Right . Var $ "l" +@ name
                                  Just (DAmm t0 t1) | field == t1    ->  Right . Var $ "r" +@ name
                                  Just (DAmm t0 t1) | field == "fee" ->  Right . Var $ field +@ name
                                  Just (DAmm _ _)  ->  Left $ "field of AMM: " ++ name ++ " being indexed isn't a token on this AMM!"
                                  Just DTok->  Left $ "Tried to index a token"
                                  _ -> Left $ "field indexing: " ++ name ++ " failed."
            _ -> Left $ "failed to read: " ++ n
    readParens :: [(Char, Int)] -> String -> Int -> [(Char, Int)]
    readParens acc []       ctr 
        | ctr > 0               = [] -- error wrong parenthesis
    readParens acc []       ctr = acc
    readParens acc ('(':[]) ctr = [] -- error wrong parenthesis
    readParens acc ('(':cs) ctr = readParens acc cs (ctr + 1)
    readParens acc (')':cs) ctr = readParens acc cs (ctr - 1)
    readParens acc (c : cs) ctr = readParens ((c, ctr):acc) cs ctr

    mergeToks :: Maybe [[(Char,Int)]] -> Either String [(String, Int)]
    mergeToks Nothing = Left " mismatching parenthesis or tried to parse empty string "
    mergeToks (Just ts) =
        let ts' = filter (not . null) ts
            is  = map (map snd) ts'
            sum1 = map sum is
            sum2 = map (\s -> (length s) * (case listToMaybe s of {Nothing -> 0; Just i -> i})) is in
        if sum1 /= sum2 then Left "Couldn't split a token due to parenthesis" else
        Right $ map (\l -> foldl (\(acc, j) (c, i) -> (acc ++ [c], i)) ("", 0) l) ts'

    splitWhen' :: [(Char, Int)] -> Maybe [[(Char, Int)]]
    splitWhen' a
        | null a    = Nothing
        | otherwise = Just $ splitWhen (\(c,i) -> elem c " \t\n") a 

instance Read Opt where
    readsPrec _ ('S':'E':'T':'O':'P':'T':input) = 
      let tokens = words input in
      case tokens of
        ("TEX":rem) -> [(Tex, unwords rem)]
        ("RATIONAL":rem) -> [(Precision Nothing, unwords rem)]
        ("DECIMAL":v:rem) | all isNumber v -> 
          case readMaybe v :: Maybe Int of
            Just i -> [(Precision $ Just i, unwords rem)]
            _      -> []
        ("DECIMAL":rem) -> [(Precision $ Just 3, unwords rem)] --defaults to 3 digits of precision
        _ -> []
    readsPrec _ _ = []

instance Read SToks where
    readsPrec _ ('T':'O':'K':'E':'N':'S':input) = 
        let (h, rest1  ) = readUntil '(' input in if h    == "!" then [] else
        let (toks, rest) = readUntil ')' rest1 in if toks == "!" then [] else
        let toks'  = Util.split ',' toks
            toks'' = map (filter (\c -> c /= ' ')) toks'
        in 
            if (any (\x -> ((> 1) . length) $ words x) toks') ||
                any (\s -> null s || all (\c -> c == ' ') s) toks'' then [] else
        [(SToks $ toks'', rest)]
    readsPrec _ _ = []


instance Read TxFree where
    readsPrec _ ('F':'R':'E':'E':input) = 
        let (blank, rest1) = readUntil '(' input in if blank == "!" then [] else
        let (users, rest) = readUntil ')' rest1 in if users == "!" then [] else
        let users'  = Util.split ',' users
            users'' = map (filter (\c -> c /= ' ')) users'
        in 
            if (any (\x -> ((> 1) . length) $ words x) users') ||
                any (\s -> null s || all (\c -> c == ' ') s) users'' then [] else
        [(TxFree $ users'', rest)]
    readsPrec _ _ = []

instance Read UnOp where
    readsPrec _ ('n':'o':'t':[]) = [(Not, "")]
    readsPrec _ _ = []

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

instance Read TxCon where
    readsPrec _ input =
      let (blank, rest1) = readUntil '(' input in if blank == "!" then [] else
      let (name, rest2) = readTokUntil ',' rest1 in if name == "!" then [] else
      let (v0,   rest3) = readTokUntil ':' rest2 in if v0   == "!" then [] else
      let (t0,   rest4) = readTokUntil ',' rest3 in if t0   == "!" then [] else
      let (v1,   rest5) = readTokUntil ':' rest4 in if v1   == "!" then [] else
      let (t1,   rest6) = readTokUntil ')' rest5 in if t1   == "!" then [] else
      let v0' = toVal v0
          v1' = toVal v1 in
      if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                           && all (all isAlphaNum) [t0, t1]
                           && (isJust v0' || all (=='_') v0)
                           && (isJust v1' || all (=='_') v1)
      then [(TxCon name t0 t1 v0' v1', rest6)] else []


instance Read SAMM where
    readsPrec _ ('A':'M':'M':input) = 
        let (name, rest1) = readTokUntil '(' input in if name == "!" then [] else
        let (v0,   rest2) = readTokUntil ':' rest1 in if v0   == "!" then [] else
        let (t0,   rest3) = readTokUntil ',' rest2 in if t0   == "!" then [] else
        let (v1,   rest4) = readTokUntil ':' rest3 in if v1   == "!" then [] else
        let v0' = toVal v0
            v1' = toVal v1 in
        case Util.split ':' rest4 of -- TODO: clean this up too much duplicated 
          [_] -> 
            let (t1,   rest)  = readTokUntil ')' rest4 in if t1   == "!" then [] else
            if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                                 && all (all isAlphaNum) [take 1 t0, take 1 t1]
                                 && all (all (\c -> isAlphaNum c || c =='_')) [t0, t1]
                                 && (isJust v0' || all (=='_') v0)
                                 && (isJust v1' || all (=='_') v1)
            then [(SAMM name (v0', t0) (v1', t1) None, rest)]
            else []
          t_and_val : fee : [] -> 
            let (t1,  rest5)  = readTokUntil ',' rest4 in if t1   == "!" then [] else
            let (vFee, rest6) = readTokUntil ':' rest5 in if vFee == "!" then [] else
            let vFee'         = toValFee vFee
                (tFee, rest)  = readTokUntil ')' rest6 in if tFee == "!" then [] else
            if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                                && all (all isAlphaNum) [take 1 t0, take 1 t1]
                                && all (all (\c -> isAlphaNum c || c =='_')) [t0, t1]
                                && (isJust v0' || all (=='_') v0)
                                && (isJust v1' || all (=='_') v1)
                                && (isJust (toVal vFee) || all (=='_') vFee)
                                && (==) "fee" tFee
            then [(SAMM name (v0', t0) (v1', t1) (toValFee vFee), rest)]
            else []
          _ -> []
        where 
            toValFee  "_" = Sym
            toValFee  v   = 
              case readMaybe v :: Maybe Int of
                Just i -> Conc $ toRational i
                Nothing ->
                  case readMaybe v :: Maybe Rational of
                    Just r -> Conc r
                    Nothing -> 
                      case stringToRational v of 
                        Just r -> Conc r
                        Nothing -> None
    readsPrec _ _ = [] -- no parse 

instance Read SUser where
    readsPrec _ ('U':'S':'E':'R':input) = 
        let (name, rest1) = readTokUntil '(' input in if name == "!" then [] else
        let (wal, rest)   = readUntil    ')' rest1 in if wal  == "!" then [] else
        let wal'  = Util.split ',' wal
            wal'' = map parsePair wal'
        in
        if (not . null) name && all (\c -> isAlphaNum c || c == '_') name 
                             && all isJust wal'' 
        then let wal''' = map fromJust wal''
             in [( SUser wal''' name, rest)]
        else []
            where
                parsePair s | all (flip elem " \n\t") s = Nothing
                parsePair s  = 
                    case Util.split ':' s of
                        (v:t:[]) -> 
                            let v' = concat $ words v
                                t' = concat $ words t 
                                v'' = toVal v'
                            in if (all isAlphaNum (take 1 t')) && (all (\c -> isAlphaNum c || c=='_') (drop 1 t')) && isJust v'' then Just (t', v'')
                               else if all isAlphaNum t' && isNothing v'' then Just (t', Nothing)
                               else Nothing
                        otherwise -> Nothing
    readsPrec _ _ = []