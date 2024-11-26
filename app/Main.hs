{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad
--import Data.Map
import Data.Maybe
import Netting.Sem
import Netting.AmmFuns
--import qualified Data.Sequence as S
--import Netting.Symbolic.SMT_opt
import Netting.Symbolic.Basics
import Netting.Symbolic.SymSem
import Netting.SymTab
import Data.List.Split
import Data.List
import qualified GHC.Utils.Misc as Util
import Data.Either
import Data.Either.Extra
import Data.Char
import Text.Read hiding (prec)

readParens :: [(Char, Int)] -> String -> Int -> [(Char, Int)]
readParens acc []       ctr 
  | ctr > 0                 = [] -- error wrong parenthesis
readParens acc []       ctr = acc
readParens acc ('(':[]) ctr = [] -- error wrong parenthesis
readParens acc ('(':cs) ctr = readParens acc cs (ctr + 1)
readParens acc (')':cs) ctr = readParens acc cs (ctr - 1)
readParens acc (c : cs) ctr = readParens ((c, ctr):acc) cs ctr

splitWhen' :: [(Char, Int)] -> Maybe [[(Char, Int)]]
splitWhen' a
  | null a    = Nothing
  | otherwise = Just $ splitWhen (\(c,i) -> elem c " \t\n") a 

--splitWhen :: [(Char, Int)] -> [[(Char, Int)]]
--splitWhen a = 
--  reverse $ go [[]] ([], a)
--  where 
--    go acc ([], [])      = acc
--    go acc ([(c, _)], [])
--      | elem c "\t\n "   = acc
--    go acc ([], todo)    = go acc (cutSpace todo)
--    go acc ([(c, _)], todo) 
--      | elem c "\t\n "   = go acc (consume todo)
--    go acc (front, todo) = go (front : acc) (cutSpace todo)
--    cutSpace = span (\(c, i) -> elem c " \t\n")
--    consume  = span (\(c, i) -> not $ elem c " \t\n")

mergeToks :: Maybe [[(Char,Int)]] -> Either String [(String, Int)]
mergeToks Nothing = Left " mismatching parenthesis or tried to parse empty string "
mergeToks (Just ts) =
  let ts' = filter (not . null) ts
      is  = map (map snd) ts'
      sum1 = map sum is
      sum2 = map (\s -> (length s) * (case listToMaybe s of {Nothing -> 0; Just i -> i})) is in
  if sum1 /= sum2 then Left "Couldn't split a token due to parenthesis" else
  Right $ map (\l -> foldl (\(acc, j) (c, i) -> (acc ++ [c], i)) ("", 0) l) ts'

--data ParseHelper a b c = Done a | UnO b | BinO c

type ParseHelper2 = ParseHelper Expr UnOp BinOp

parse :: String -> Either String Expr
parse input = 
  let string_depth = mergeToks . splitWhen' . reverse $ readParens [] input 0
  in if isLeft string_depth then Left "failed to parse string depth" else
    let string_depth' = Util.mapFst tokenize (fromRight [] string_depth)
    in if (>0) . length $ filter (\(exp, _) -> isNothing exp) string_depth' then Left "Tokenization failed" else 
    let tokens_depth = Util.mapFst fromJust string_depth'
    in parse' tokens_depth
  where 
    -- TODO: IMPORTANT!!!  lower depth by 1 after parsing exp!!! and modify code to take into account
    parse' :: [(ParseHelper2, Int)] -> Either String Expr
    parse' [(Done exp, _)] = Right exp
    parse' a        = 
      let max_depth = foldl (\acc (exp, i) -> case exp of {Done _ -> acc; _ -> max i acc}) 0 a
          --prefixLen = takeWhile (\(_, i)-> i /= max_depth) a
          toParse   = takeWhile (\(_, i) -> i == max_depth) (dropWhile (\(_, i)-> i /= max_depth) a) -- parses leftmost 'deepest' exp (based on parenthesis), might be 0 if no ()
          precs     = map prec ( map fst toParse )
      in if (>0) . length $ (filter isNothing precs) then Left "trying to parse op whose precedence is unspecified" else
      let max_prec  = foldl (\hi i -> max hi i) 0 (map fromJust precs)
          idx       = (fromJust $ findIndex (\(exp, i) -> (fromJust $ prec exp) == max_prec && i == max_depth) a)
      in case a !? idx of
          Nothing            -> Left "out of bounds idx access when looking for operator"
          Just (UnO u, i)  -> let operand = get_adj_exp a (idx + 1)
                              in if isLeft operand then operand else 
                              let exp     = UnOp u (fromRight' operand) in
                                parse' $ (take idx a) ++ [(Done $ exp, i - 1)] ++ (drop ( idx + 2) a) -- TODO: double check this i - 1
          Just (BinO b, i) -> let operand1 = get_adj_exp a (idx - 1)
                              in if isLeft operand1 then operand1 else 
                              let operand2 = get_adj_exp a (idx + 1) 
                              in if isLeft operand2 then operand2 else 
                              let exp      = BinOp b (fromRight' operand1) (fromRight' operand2)
                              in parse' $ (take (idx - 1) a) ++ [(Done $ exp, i - 1)] ++ (drop ( idx + 2) a) -- TODO: double check this i - 1
          _                  -> error "Trying to re-eval an already evaled exp"

    get_adj_exp a i =
      let exp = a !? i in
        case exp of 
          Nothing            -> Left "adjacent expr was not accessible"
          Just (UnO _, i)    -> Left "unop (unop expr): not supported (not necessary so far)"
          Just (BinO _, i)   -> Left "Found 2 operands next to each other"
          Just (Done exp, i) -> Right exp

    tokenize :: String -> Maybe ParseHelper2
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
                                  Just uno -> Nothing -- Doesn't make sense, unless there's two fields
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

main :: IO ()
main = do
  putStrLn . show $ parse "alberto.t1 >= aleks.t1 && aleks.t1 >= roberto.t1 => alberto.t1 >= roberto.t1"
  putStrLn . show $ parse "not (aleks.t0 = ((3%1 + 992%1) / 41%1))"
  putStrLn . show $ parse "((aleks.t0 > 4%1) && (alberto.t1 < aleks.t0))"
  putStrLn . show $ parse "aleks.t0 > 4%1 && alberto.t1 < aleks.t0"
  putStrLn . show $ parse "testamm.r0.t = t1"
  repl 
  return ()

    --  case read line :: Stmt of
    --    ST toks -> do 
    --      case declToks of
    --        Left e           -> do {putStrLn e; repl stab}
    --        Right (r, stab') -> do {putStrLn r; repl stab'}
    --    SA samm -> 
    --      case makeAmm samm stab of
    --        Left e           -> do {putStrLn e; repl stab}
    --        Right (r, stab') -> do {putStrLn $ showStmts r; repl stab'}
    --    SU suser ->
    --      case makeUser suser stab of
    --        Left e           -> do {putStrLn e; repl stab}
    --        Right (r, stab') -> do {putStrLn $ showStmts r; repl stab'}
    --    st -> do {putStrLn st; repl stab}

    

    --let ex1_amms = 
    --      [(AMM (T0, 8) (T1, 18)),
    --       (AMM (T1, 8) (T2, 18)),
    --       (AMM (T2, 8) (T0, 18)) ]

    --    ex1_q_len      = 2
    --    ex1_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 0)]) "A"
    --    ex1_init_state = (ex1_amms, [ex1_a])
    --    ex1_init_conf  = Configuration ex1_init_state ex1_init_state S.Empty
    --    ex5_amms =
    --      [(AMM (T0, 12) (T1, 12)), 
    --        (AMM (T1, 18) (T2,  8)),
    --        (AMM (T2, 12) (T0, 12))]
    --    ex5_q_len      = 2
    --    ex5_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 6)]) "A"
    --    ex5_a'         = User (fromList [(AtomTok T0, 4), (AtomTok T1, 0), (AtomTok T2, 0)]) "A"
    --    ex5_init_state = (ex5_amms, [ex5_a])
    --    ex5_init_conf  = Configuration ex5_init_state ex5_init_state S.Empty
    --    ex3_amms =
    --      [(AMM (T0, 12) (T1, 12)), 
    --        (AMM (T1, 12) (T2, 12))]
    --    ex3_q_len      = 3
    --    ex3_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
    --    ex3_b          = User (fromList [(AtomTok T0, 4), (AtomTok T1, 0), (AtomTok T2, 0)]) "B"
    --    ex3_init_state = (ex3_amms, [ex3_a, ex3_b])
    --    ex3_init_conf  = Configuration ex3_init_state ex3_init_state S.Empty       

    ----res' <- checkGoal ex1_init_conf 3 [(U ("A", [(T0, 2), (T1, 2), (T2, 2)])) ]
    ----res' <- checkGoal ex1_init_conf 3 [(U ("A", [(T0, 2), (T1, 2), (T2, 2)])) ]
    --res  <- checkGoal ex3_init_conf 4 [(U ("A", [(T0, 4)])), (U ("B", [(T2, 4)]))]
    --return ()