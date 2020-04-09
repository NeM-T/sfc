import System.IO
import Data.Char

anyChar (x: xs) = (x, xs)

apply f (x: xs) | f x = (x, xs)

-- between :: String -> String -> String
-- between t1 t2= do
  
char t = apply (== t)

end st = do
  let (x, xs) = anyChar st 
      in if xs == [] then [x]
		     else [] ++ [x] ++ (end xs)

string :: [Char] -> [Char] -> [Char]
string str target = do
  let x1 = take (length str) target 
      in if str == x1 then x1
		      else "Error"

main = do 
    handle <- openFile "config.toml" ReadMode
    text <- hGetLine handle
    putStr $ text ++ "\n"
    line2 <- hGetLine handle
    putStr $ line2 ++ "\n"
    print $ anyChar text
    print $ end text
    print $ string "[ro" text

