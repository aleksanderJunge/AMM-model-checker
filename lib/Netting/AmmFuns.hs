{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
module Netting.AmmFuns where

import qualified Data.Map as M
import Netting.Sem
import Data.Sequence (Seq ((:|>), (:<|))) -- explicit import of insertion operators
import qualified Data.Sequence as S      -- qualified import of rest of lib
import Data.List
import Data.Either
import Data.Foldable
import Data.Maybe
import Control.Monad

-- May result in a negative balance of the user
swap :: AMM -> Swap -> Balance -> Either String (AMM, User)
swap amm@(AMM (t0, r0) (t1, r1)) txn@(Swap name (t2, v0) (t3, v1)) bal =
  if t0 /= t2 then
    swap (AMM (t1, r1) (t0, r0)) txn bal
  else
    if (0 <= payout) && (payout >= v1) then 
      let bal'  = updateBal t1 payout
                . updateBal t0 (- v0) $ bal
      in
      Right (AMM (t0, r0 + v0) (t1, r1 - payout), User bal' name)
    else 
      Left $ name ++ " couldn't swap " ++ (show $ fromRational v0) ++ " " ++ (show t0) ++ " for " 
                  ++ (show $ fromRational v1) ++ " " ++ (show t1) ++ ", AMM payout for this input would be: " 
                  ++ (show $ fromRational payout) ++ " " ++ (show t1) ++ ". "
  where 
    payout = (r1 * v0) / (r0 + v0) -- preserves CFMM properties
    updateBal t v bal = M.insert (AtomTok t) (getBal (AtomTok t) bal + v) bal

-- this executes a swap on the provided state and returns a new state
executeSwap :: State -> Swap -> Either String State
executeSwap s@(amms, users) txn@(Swap name (t0, _) (t1, _)) =
  case findAMMIdx amms t0 t1 of
    Nothing -> Left "no AMM matches this swap token pair"
    Just i  -> -- AMM at index i matches token pair
      case findUserIdx users name of 
        Nothing -> Left "no User's name matched txn sender"
        Just j  -> -- User at index j matches name
          let (head_amms, amm:tail_amms )              = splitAt i amms
              (head_users, (User wal name):tail_users) = splitAt j users
          in
            case swap amm txn wal of
              Left message              -> Left message
              Right (new_amm, new_user) -> Right $ (head_amms ++ new_amm : tail_amms, head_users ++ new_user : tail_users)

executeDeposit :: State -> Deposit -> Either String State
executeDeposit s@(amms, users) dep@(Deposit name (t0, v0) (t1, v1))
  | v0 <= 0 || v1 <= 0 = Left "Must deposit > 0"
  | canAfford          = 
      case findUserIdx users name of 
        Nothing -> Left "User depositing doesn't exist in state"
        Just i  -> 
          let (head_users, u@(User w _):tail_users) = splitAt i users
              supply = tokenSupply s (MintTok $ MT (t0, t1)) 
          in
            if supply == 0 then -- [deposit0]
              let amm    = AMM (t0, v0) (t1, v1)
                  bal'   = updateBal (AtomTok t0) (-v0)
                         . updateBal (AtomTok t1) (-v1)
                         . updateBal (MintTok $ MT (t0, t1)) v0 $ w
              in Right (amms ++ [amm], head_users ++ (User bal' name) : tail_users)
            else -- [deposit1]
              case findAMMIdx amms t0 t1 of 
                Nothing -> Left $ " AMM for: " ++ (show t0) ++ " " ++ (show t1) ++ " doesn't exist.(shouldn't be possible)"
                Just j  -> 
                  let (head_amms, (AMM (t0', r0) (t1', r1)):tail_amms ) = splitAt j amms in
                    if not (r0 * v1 == r1 * v0) then -- TODO: these are floats ... what is the precision of this equality?
                      Left $ "Deposit doesn't preserve ratio between reserves " ++ (show dep)
                    else 
                      let payout = v0 / r0 * supply -- look into this one as well
                          amm'   = (AMM (t0, r0 + v0) (t1, r1 + v1))
                          bal'   = updateBal (AtomTok t0) (-v0) 
                                 . updateBal (AtomTok t1) (- v1)
                                 . updateBal (MintTok $ MT (t0, t1)) payout $ w
                      in Right (head_amms ++ amm' : tail_amms, head_users ++ (User bal' name) : tail_users)
  | otherwise = Left $ "User " ++ name ++ " can't afford to execute " ++ (show dep)
  where 
    updateBal t v bal = M.insert t ((getBal t bal) + v) bal
    canAfford =
      let userBal = fromMaybe M.empty (liftM (\(User w _) -> w) (findUser name users))
          v0Bal   = getBal (AtomTok t0) userBal
          v1Bal   = getBal (AtomTok t1) userBal 
      in v0Bal >= v0 && v1Bal >= v1

executeRedeem :: State -> Redeem -> Either String State
executeRedeem s@(amms, users) rdm@(Redeem name (mt@(MT (t0, t1)), v))
  | v <= 0    = Left $ "Must redeem > 0 " ++ (show mt)
  | canAfford = 
      case findUserIdx users name of 
        Nothing -> Left "User redeeming doesn't exist in state"
        Just i  -> 
          case findAMMIdx amms t0 t1 of 
            Nothing -> Left $ " AMM for: " ++ (show t0) ++ " " ++ (show t1) ++ " doesn't exist.(shouldn't be possible)"
            Just j  -> 
              let (head_users, u@(User w _):tail_users)             = splitAt i users
                  (head_amms, (AMM (t0', r0) (t1', r1)):tail_amms ) = splitAt j amms
                  supply = tokenSupply s (MintTok $ mt) 
                  v0     = v * r0 / supply
                  v1     = v * r1 / supply
                  amm'   = (AMM (t0, r0 - v0) (t1, r1 - v1))
                  bal'   = updateBal (MintTok mt) (-v)
                         . updateBal (AtomTok t0) v0
                         . updateBal (AtomTok t1) v1 $ w
              in Right (head_amms ++ amm' : tail_amms, head_users ++ (User bal' name) : tail_users)
  | otherwise = Left $ "User " ++ name ++ " can't afford to execute " ++ (show rdm)
  where
    updateBal t v bal = M.insert t ((getBal t bal) + v) bal
    canAfford =
      let userBal = fromMaybe M.empty (liftM (\(User w _) -> w) (findUser name users))
          vBal    = getBal (MintTok mt) userBal
      in vBal >= v

-- Takes a state and a queue of txns and finds a solution to the 'netting-problem'
net :: (Queue -> State -> Int) -> State -> (Queue, String) -> (Queue, String)
net findOverdraft s (q@(txn :<| txns), log) = 
  let q' = runAndDrop q s 
      s' = runQueue q' s in 
    if isGreen s' then (q', log)
    else
      let violating_idx = findOverdraft q' s
          q''           = S.deleteAt violating_idx q'
          log_msg       = "removed idx " ++ (show violating_idx)
                          ++ ", queue now consists of\n" ++ (show . toList $ q'') ++ "\n"
      in
        net findOverdraft s (q'', log ++ log_msg)
net _ _ (S.Empty, log) = (S.Empty, log)

takeStep :: (Configuration, Int, [String]) -> TransactionT -> QLength -> Bool -> (Configuration, Int, [String])
takeStep (conf@(Configuration green sim queue), i, log) txn maxqlen runInMaxOverdraftMode =
  case txn of 
    Swp swp -> second_lvl_sem $ executeSwap    sim swp
    Dep dep -> second_lvl_sem $ executeDeposit sim dep
    Rdm rdm -> second_lvl_sem $ executeRedeem  sim rdm
  where 
    second_lvl_sem =
      \case
        Left message -> (conf, i + 1, (add_to_log (" not executed becase " ++ message) sim i) : log)
        Right s'     -> 
          if isGreen s' then (Configuration s' s' S.Empty, i + 1, (add_to_log " applied cover rule " s' i) : log)
          else 
            if S.length queue < maxqlen then
              (Configuration green s' (queue :|> txn), i + 1, (add_to_log " applied overdraft rule" s' i) : log)
            else
              let nettingAlgo = if runInMaxOverdraftMode then findLargestOverdraft else findFirstOverdraft
                  (q', net_log) = net nettingAlgo green (queue :|> txn, "")
                  s''           = runQueue q' green 
              in
                (Configuration s'' s'' S.Empty, i + 1, 
                  (add_to_log (" applied netting rule, as the state:\n" ++ (show s') ++ "\nis red, and queue is full:\n"
                                ++ (show . toList $ queue :|> txn) ++ "\n" ++ net_log) s'' i) : log)
    add_to_log message s' i = 
      "txn " ++ (show i) ++ ":\n " ++ (show txn) ++ message ++ " resulting in state:\n" ++ (show s') ++ "\n"


-- used to run a sequence of transactions on a configuration
-- outputs (the configuration after executing txns, a log with a brief summary of each txn)
runTransactions :: Bool -> Configuration -> [TransactionT] -> QLength -> (Configuration, [String])
runTransactions runNetInMaxOverdraftMode conf@(Configuration lg sim q) txns maxqlen =
  let (conf', _, log) = foldl' (\acc txn -> takeStep acc txn maxqlen runNetInMaxOverdraftMode) (conf, 1, []) txns
      log' = ("Starting state:\n" ++ (show lg) ++ "\nExecution Log:") : reverse log
  in (conf', log')


--- More auxillary functions follows below ---

isGreen :: State -> Bool
isGreen (_, users) = 
  (==0) . length $ filter (\(User w _) -> is_neg w) users
  where is_neg = not . M.null . M.filter (< 0.0)

getBal :: TokenT -> Balance -> Rational
getBal t bal = snd $ fromMaybe (t, 0.0) (find (\(t', _) -> t == t') (M.toList bal))

-- Runs all the transactions in the queue and returns a new state
runQueue :: Queue -> State -> State
runQueue (txn :<| txns) s =
  let s' = case txn of
            Swp swp -> fromRight s (executeSwap    s swp)
            Dep dep -> fromRight s (executeDeposit s dep)
            Rdm rdm -> fromRight s (executeRedeem  s rdm)
  in runQueue txns s'
runQueue S.Empty s = s

-- returns the queue after running and discarding any transactions whose premise is unsat
runAndDrop :: Queue -> State -> Queue
runAndDrop q s =
  let (states :|> _) = S.scanl (\s' tx -> fromRight s' (exec_txn s' tx)) s q
      maybeTxns      = S.zipWith check_txn states q
  in S.fromList . catMaybes . toList $ maybeTxns
    where exec_txn s txn =
            case txn of 
              Swp swp -> executeSwap    s swp
              Dep dep -> executeDeposit s dep
              Rdm rdm -> executeRedeem  s rdm
          check_txn s txn = if isRight $ exec_txn s txn then Just txn else Nothing

-- takes a queue and a state, and finds the first transaction in the queue that results in a red state
findFirstOverdraft :: Queue -> State -> Int
findFirstOverdraft q s =
  find_idx q s 0
  where 
    find_idx (txn :<| txns) s i =
      case txn of 
        Swp swp -> check_res $ executeSwap    s swp 
        Dep dep -> check_res $ executeDeposit s dep
        Rdm rdm -> check_res $ executeRedeem  s rdm
      where 
        check_res = 
          \case
            Left _   -> i
            Right s' -> if isGreen s' then find_idx txns s' (i+1) else i

-- takes a queue and a state, discards a transaction in queue that enlarges the biggest overdraft in the final state
findLargestOverdraft :: Queue -> State -> Int
findLargestOverdraft q s =
  let (_, usrs) = runQueue q s 
      (a', t')  = find_max_overdraft usrs -- finds max overdraft after running queue in the t' balance of a'
  in
    find_idx q s 0 0 0 a' t'
  where 
    find_max_overdraft users = 
      let minVal  = foldr min 0 $ map ((M.foldr min 0) . wallet) users -- identify biggest overdraft
          usr     = (!! 0) $ filter (\(User w _) -> (>= 1) . M.size $ M.filter (\v -> v == minVal) w) users 
          (t, v)  = (!! 0) $ dropWhile (\(t, v) -> v /= minVal) (M.toList $ wallet usr)
      in
        (usr, t)
    find_idx S.Empty _ _ idx_lo _ _ _ = idx_lo
    find_idx (txn :<| txns) s i idx_lo lo u@(User w n) t =
      case txn of 
        Swp swp@(Swap name _ _)    | name == n -> check_a  $ executeSwap    s swp 
        Swp swp                                -> continue $ executeSwap    s swp 
        Dep dep@(Deposit name _ _) | name == n -> check_a  $ executeDeposit s dep
        Dep dep                                -> continue $ executeDeposit s dep
        Rdm rdm@(Redeem name _)    | name == n -> check_a  $ executeRedeem  s rdm
        Rdm rdm                                -> continue $ executeRedeem  s rdm
      where 
        continue =  -- Txn not sent by user with biggest overdraft, keep looking
          \case
            Left _   -> i
            Right s' -> find_idx txns s' (i+1) idx_lo lo u t
        check_a =  -- Txn sent by user with biggest overdraft, check if bal is lower than lo
          \case
            Left _              -> i
            Right s'@(_, users) -> 
              case findUserIdx users n of
                Nothing  -> i
                Just idx -> let bal       = wallet $ users !! idx
                                overdraft = getBal t bal
                                idx_lo'   = if overdraft < lo then i else idx_lo
                            in
                              find_idx txns s' (i+1) idx_lo' (min lo overdraft) u t


-- returns the index of the AMM corresponding to the AtomicToken pair (or Nothing)
findAMMIdx :: [AMM] -> AtomicToken -> AtomicToken -> Maybe Int
findAMMIdx amms t0 t1 =
  find_amm amms t0 t1 0
  where 
    find_amm [] _ _ _ = Nothing
    find_amm (amm@(AMM (t0, r0) (t1, r1)):amms) t2 t3 i =
      if (t0 == t2 && t1 == t3) || (t1==t2 && t0 == t3) then
        Just i
      else
        find_amm amms t2 t3 (i + 1)
    
-- returns the index of the User corresponding to the name (or Nothing)
findUserIdx :: [User] -> String -> Maybe Int
findUserIdx users lfName =
  find_user users lfName 0
  where 
    find_user [] _ _ = Nothing
    find_user ((User _ name):users) lfName i = 
      if name == lfName then
        Just i
      else
        find_user users lfName (i + 1)

findUser :: String -> [User] -> Maybe User
findUser name = find (\(User _ n) -> (n == name))

tokenSupply :: State -> TokenT -> Rational
tokenSupply (amms, users) (AtomTok t) = 
  let amm_supply = sum $ map (\(AMM (t0, v0) (t1, v1)) -> 
                              if
                              | t0 == t   -> v0 
                              | t1 == t   -> v1
                              | otherwise -> 0 ) amms
      user_supply = sum $ map (\(User w _) -> getBal (AtomTok t) w) users
  in amm_supply + user_supply

tokenSupply (_, users) mt@(MintTok t) =
  sum $ map (\(User w _) -> getBal mt w) users
