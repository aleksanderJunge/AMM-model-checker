module Symbolic.Utils where 

import Data.Char
import Text.Read
import Debug.Trace

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

(+@) :: String -> String -> String
s +@ s' = s ++ "_" ++ s'

stringToRational :: String -> Maybe Rational
stringToRational s =
    go s [] 1
    where 
        go (i:[]) acc ctr | isNumber i  = readMaybe (acc ++ [i] ++ "%" ++ (show ctr)) :: Maybe Rational
        go (i:s) acc ctr  | isNumber i && ctr >  1 = if (take 1 s) == "?" then readMaybe (acc ++ [i] ++ "%" ++ (show ctr)) :: Maybe Rational else go s (acc ++ [i]) (ctr * 10)
        go (i:s) acc ctr  | isNumber i && ctr == 1 = go s (acc ++ [i]) ctr
        go ('.':s) acc ctr = go s acc (ctr * 10)
        go (i:s) acc ctr  | not (isNumber i) =  Nothing
        go _ acc _ = Nothing