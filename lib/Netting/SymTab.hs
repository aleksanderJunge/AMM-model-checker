module Netting.SymTab where

import Data.Maybe
--import Data.Composition
import Data.Function
import Data.List
--import Control.Monad.State.Class

import qualified Data.Map.Strict as M

data SType = DTok | DAmm | DUser deriving (Eq, Ord, Show)

type Env a b = M.Map a b

empty :: Env a b 
empty = M.empty

bind :: (Ord a, Ord b) => Env a b -> (a, b) -> Env a b
bind d (k,v) = M.insert k v d

get :: (Ord a, Ord b) => Env a b -> a -> Maybe b 
get = flip M.lookup

domain :: Eq a => Env a b -> [a]
domain = map fst . M.toList

codomain :: Eq b => Env a b -> [b]
codomain = map snd . M.toList
--data SymTab = SymT (Env String SType)



--getDefault :: (Ord a, Ord b) => b -> Env a b -> a -> b 
--getDefault x = fromMaybe x .* get 

-- our simple symtab just maps var names to their type

--instance SymTab MonadState 

--toList :: Env a b -> [(a,b)]
--toList = M.toList
