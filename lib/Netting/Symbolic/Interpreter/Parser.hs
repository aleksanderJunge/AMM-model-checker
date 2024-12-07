module Netting.Symbolic.Interpreter.Parser where

import Data.Maybe
import Netting.Sem
import Netting.AmmFuns
import Netting.Symbolic.Sem
import Netting.Symbolic.Utils
import Netting.Symbolic.Interpreter.SymTab
import Data.List.Split
import Data.List
import qualified GHC.Utils.Misc as Util
import Data.Either
import Data.Either.Extra
import Data.Char
import Text.Read hiding (prec)
import Debug.Trace

type ToParse = ParseHelper Expr UnOp BinOp
--parse :: String -> Either String Expr
--parse input = 
--  let string_depth = mergeToks . splitWhen' . reverse $ readParens [] input 0
--  in if isLeft string_depth then Left "failed to parse string depth" else
--    let string_depth' = Util.mapFst tokenize (fromRight [] string_depth)
--    in if (>0) . length $ filter (\(exp, _) -> isNothing exp) string_depth' then Left "Tokenization failed" else 
--    let tokens_depth = Util.mapFst fromJust string_depth'
--    in parse' tokens_depth
--  where 
--    parse' :: [(ToParse, Int)] -> Either String Expr
--    parse' [(Done exp, _)] = Right exp
--    parse' a        = 
--      let max_depth = foldl (\acc (exp, i) -> case exp of {Done _ -> acc; _ -> max i acc}) 0 a
--          toParse   = takeWhile (\(_, i) -> i == max_depth) (dropWhile (\(_, i)-> i /= max_depth) a) -- parses leftmost 'deepest' exp (based on parenthesis), might be 0 if no ()
--          precs     = map prec ( map fst toParse )
--      in if (>0) . length $ (filter isNothing precs) then Left "trying to parse op whose precedence is unspecified" else
--      let max_prec  =  foldl (\hi i -> max hi i) 0 (map fromJust precs)
--          idx       = (fromJust $ findIndex (\(exp, i) -> (fromJust $ prec exp) == max_prec && i == max_depth) a)
--      in case a !? idx of
--          Nothing            -> Left "out of bounds idx access when looking for operator"
--          Just (UnO u, i)  -> let operand = get_adj_exp a (idx + 1)
--                              in if isLeft operand then operand else 
--                              let exp     = UnOp u (fromRight' operand)
--                                  depth'   = if i == 0 then i else i - 1
--                              in parse' $ (take idx a) ++ [(Done $ exp, depth')] ++ (drop ( idx + 2) a)
--          Just (BinO b, i) -> let operand1 = get_adj_exp a (idx - 1)
--                              in if isLeft operand1 then operand1 else 
--                              let operand2 = get_adj_exp a (idx + 1) 
--                              in if isLeft operand2 then operand2 else 
--                              let exp      = BinOp b (fromRight' operand1) (fromRight' operand2)
--                                  depth'   = if i == 0 then i else i - 1
--                              in parse' $ (take (idx - 1) a) ++ [(Done $ exp, depth')] ++ (drop ( idx + 2) a)
--          _                  -> error "Trying to re-eval an already evaled exp"
--
parse :: String -> Either String Expr
parse input = 
  let string_depth = mergeToks . splitWhen' . reverse $ readParens [] input 0
  in if isLeft string_depth then Left "failed to parse string depth" else
    let string_depth' = Util.mapFst tokenize (fromRight [] string_depth)
    in if (>0) . length $ filter (\(exp, _) -> isNothing exp) string_depth' then Left "Tokenization failed" else 
    let tokens_depth = Util.mapFst fromJust string_depth'
    in case parseRec tokens_depth of
      Right [(Done exp, _)] -> Right exp
      Right _ -> Left "parsing didn't result in single exp"
      Left e  -> Left e
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

    parse' :: [ToParse] -> Either String Expr -- assumes a flat structure with no parenthesis
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
                           let exp     = UnOp u (fromRight' operand)
                           in parse' $ (take idx a) ++ [Done exp] ++ (drop ( idx + 2) a)
          Just (BinO b) -> let operand1 = get_adj_exp a (idx - 1)
                           in if isLeft operand1 then operand1 else 
                           let operand2 = get_adj_exp a (idx + 1) 
                           in if isLeft operand2 then operand2 else 
                           let exp      = BinOp b (fromRight' operand1) (fromRight' operand2)
                           in parse' $ (take (idx - 1) a) ++ [Done exp] ++ (drop ( idx + 2) a)
          _             -> error "Trying to re-eval an already evaled exp"

    get_adj_exp a i =
        case a !? i of 
          Nothing         -> Left "adjacent expr was not accessible"
          Just (UnO _)    -> Left "unop (unop expr): not supported (not necessary so far)"
          Just (BinO _)   -> Left "Found 2 operands next to each other"
          Just (Done exp) -> Right exp

    tokenize :: String -> Maybe ToParse
    tokenize s =
      case readMaybe s :: Maybe UnOp of
        Just uno -> return . UnO $ uno
        Nothing  -> do
          case readMaybe s :: Maybe BinOp of
            Just bino -> return . BinO $ bino
            Nothing   -> do
              case readMaybe s :: Maybe Rational of 
                Just r -> return . Done $ LReal r
                Nothing -> 
                  case toVar s of
                    Just exp -> return . Done $ exp
                    Nothing  -> Nothing
    isRatio "" = False
    isRatio r  = 
        if all ((==) '_') r then True else -- TODO: we allow sym vals for the values of token balance?
        case Util.split '%' r of 
            (num:den:[]) | all isNumber num && all isNumber den -> True
            _ -> False
    toVar "" = Nothing
    toVar n = 
        case Util.split '.' n of 
            (name:[])       | all (\c -> isAlphaNum c || c == '_') name  -> Just $ Var (name)
            (name:field:[]) | all (\c -> isAlphaNum c || c == '_') name &&
                              all (\c -> isAlphaNum c || c == '_') field ->
                                case readMaybe field :: Maybe UnOp of
                                  Just Fee -> Just $ gfee (Var name) 
                                  Just _   -> Nothing -- other unary field operations are not permitted. (except indexing for tokens, see below)
                                  Nothing  -> Just $ select (Var name) (Var field) -- TODO: assert later that this is a legal operation (i.e. check for existing token)
            (name:field1:field2:[]) | all (\c -> isAlphaNum c || c == '_') name   &&
                                      all (\c -> isAlphaNum c || c == '_') field1 &&
                                      all (\c -> isAlphaNum c || c == '_') field2 ->
                                        case readMaybe field1 :: Maybe UnOp of
                                          Just R0 -> case readMaybe field2 :: Maybe UnOp of
                                            Just T -> Just $ gett (getr0 $ (Var name))
                                            Just V -> Just $ getv (getr0 $ (Var name))
                                            _      -> Nothing 
                                          Just R1 -> case readMaybe field2 :: Maybe UnOp of
                                            Just T -> Just $ gett (getr1 $ (Var name))
                                            Just V -> Just $ getv (getr1 $ (Var name))
                                            _      -> Nothing 
                                          _       -> Nothing 
            _ -> Nothing
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

instance Read UnOp where
    readsPrec _ ('f':'e':'e':[]) = [(Fee, "")]
    readsPrec _ ('n':'o':'t':[]) = [(Not, "")]
    readsPrec _ ('r':'0':[])     = [(R0, "")]
    readsPrec _ ('r':'1':[])     = [(R1, "")]
    readsPrec _ ('t':[])         = [(T, "")]
    readsPrec _ ('v':[])         = [(V, "")]
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

instance Read SAMM where
    readsPrec _ ('A':'M':'M':input) = 
        let (name, rest1) = readTokUntil '(' input in if name == "!" then [] else
        let (v0,   rest2) = readTokUntil ':' rest1 in if v0   == "!" then [] else
        let (t0,   rest3) = readTokUntil ',' rest2 in if t0   == "!" then [] else
        let (v1,   rest4) = readTokUntil ':' rest3 in if v1   == "!" then [] else
        case Util.split ':' rest4 of -- TODO: clean this up too much duplicated 
          [_] -> 
            let (t1,   rest)  = readTokUntil ')' rest4 in if t1   == "!" then [] else
            if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                                && all (all isAlphaNum) [t0, t1]
                                && all isRatio [v0, v1]
            then [(SAMM name (toVal v0, t0) (toVal v1, t1) None, rest)]
            else []
          t_and_val : fee : [] -> 
            let (t1,  rest5)  = readTokUntil ',' rest4 in if t1   == "!" then [] else
            let (vFee, rest6) = readTokUntil ':' rest5 in if vFee == "!" then [] else
            let (tFee, rest)  = readTokUntil ')' rest6 in if tFee == "!" then [] else
            if (not . null) name && all (\c -> isAlphaNum c || c == '_') name
                                && all (all isAlphaNum) [t0, t1]
                                && all isRatio [v0, v1]
                                && isRatio vFee
                                && (==) "fee" tFee
            then [(SAMM name (toVal v0, t0) (toVal v1, t1) (toValFee vFee), rest)]
            else []
          _ -> []
        where 
            isRatio "" = False
            isRatio r  = 
                if all ((==) '_') r then True else -- TODO: we allow sym vals for the values of token balance?
                case Util.split '%' r of 
                    (num:den:[]) | all isNumber num && all isNumber den -> True
                    _ -> False
            toVal  "_" = Nothing
            toVal  v   = readMaybe v :: Maybe Rational
            toValFee  "_" = Sym
            toValFee  v   = 
              case readMaybe v :: Maybe Rational of
                Just r -> Conc r
                Nothing -> None
    readsPrec _ _ = [] -- no parse 