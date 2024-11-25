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
import qualified GHC.Utils.Misc as Util
import Data.Either
import Data.Char
import Text.Read

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

tokenize :: String -> IO ()
tokenize input = 
  let string_depth = mergeToks . splitWhen' . reverse $ readParens [] input 0
  in do
    putStrLn $ show string_depth
    --mapM try_print ((map fst . (fromRight [])) string_depth)
    mapM (\(s, i) -> putStrLn $ show (toVar s)) (fromRight [] string_depth)
    return ()
  where 
    try_print s =
      case readMaybe s :: Maybe UnOp of
        Just uno -> putStrLn $ show uno
        Nothing  -> do
          case readMaybe s :: Maybe BinOp of
            Just bino -> putStrLn $ show bino
            Nothing   -> do
              case readMaybe s :: Maybe Rational of 
                Just r -> putStrLn $ show r
                Nothing -> putStrLn $ show (Var (s))
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

-- Overall idea for parsing this:
-- Firstly, we represent the list of tokens as a sequnce of 'TODOS'
-- (Either, Done Exp   or   Todo (String, Int))
-- 
-- Secondly, we do a sequnce of traversals through this list, at each traversal we parse
--   the deepest unparsed part of the list. (Meaning the part with highest snd component, which might be equal)
--
-- As an expression, might likely rely on a bordering expression that is either not parsed or parsed we have to
--   be considerate of "border" issues between Done Exp and Todo (String, Int)
--
-- As an example consider:
--   [Done (UnOp Not (Something)), Todo ("=>", i), Todo ("aleks.t0", i), Todo (">", i), Todo ("12%1", i)]
--
-- In this case, we search for the operator of highest precedence and consume the necessary tokens surrounding to parse it as an expression
--   in this case, giving:
--
-- As an example consider:
--   [Done (UnOp Not (Something)), Todo ("=>", i), Done (BinOp Gt (Var "aleks.t0") (LReal 12%1))]
--
-- Before proceeding to parse the implication, which is now surrounded by "Done" expressions, and can be readily parsed.
-- 
-- We should consider augmenting the "Done" data constructor with type information, such that we can check the types of ">" are 
--   e.g. "Real" Or "Int " on both sides, and similarly that the outermost-expression has type bool!
--
-- This gives rise to the following data decl:
-- data Todo a b = DoneB a | DoneR a | Todo b
--
-- where DoneB denotes that 'a' has type bool, and DoneR that 'a' has type Rational
-- But this might prove impossible to do, as our parser doesn't have access to our symbol table
--
-- a = Real/Var/Single (Also Exp? e.g. LReal and Var, so maybe just Done?), b = UnOp, c = BinOp, d = Exp
-- data Todo a b c d = TodoNu a | TodoUn b | TudoBi c | Done d

main :: IO ()
main = do
  --putStrLn $ show . reverse $ readParens [] " aleks.t0 = ((3 + 9) / 4)" 0
  --putStrLn $ show . splitWhen . reverse $ readParens [] "not( aleks.t0 = ((3%1 + 992%1) / 41%1))" 0
  tokenize "not (aleks.t0 = ((3%1 + 992%1) / 41%1))"
  tokenize "((aleks.t0 > 4%1) && (alberto.t1 < aleks.t0))"
  tokenize "aleks.t0 > 4%1 && alberto.t1 < aleks.t0"
  tokenize "testamm.r0.t = t1"
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