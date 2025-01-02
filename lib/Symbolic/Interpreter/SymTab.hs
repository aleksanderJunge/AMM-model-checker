module Symbolic.Interpreter.SymTab where

import Data.Maybe
import Data.Function
import Data.List

import qualified Data.Map.Strict as M

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