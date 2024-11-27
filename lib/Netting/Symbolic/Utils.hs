module Netting.Symbolic.Utils where 

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