import Text.Parsec
import Text.Parsec.String

data Term = TmTrue
    | TmFalse 
    | TmIf Term Term Term
    | TmZero
    | TmSucc Term
    | TmPred Term
    | TmIsZero Term
    | TmErro
    deriving (Show)


isval :: Term -> Bool
isval TmTrue  = True 
isval TmFalse = True
isval t       = isnumericval t

isnumericval :: Term -> Bool
isnumericval TmZero      = True
isnumericval (TmSucc t1) = isnumericval t1
_                        = False

eval :: Term -> Term
eval t = if isval t 
	   then t
	   else eval1 t

eval1 :: Term -> Term
eval1 t = case t of
	      TmIf TmTrue t2 _      ->  t2
	      TmIf TmFalse _ t3     ->  t3
	      TmIf t1 t2 t3         -> TmIf (eval t1) t2 t3
	      TmPred TmZero 	    ->  TmZero
	      TmPred (TmSucc nv1)   -> if isnumericval nv1 then  nv1 
					    else TmPred (eval1 nv1)
	      TmIsZero TmZero 	    ->  TmTrue
	      TmIsZero (TmSucc nv1) -> if isnumericval nv1 then  TmFalse else TmErro



----------------------------------------------------

parseTrue :: Parser Term 
parseTrue =  string "True" >> return TmTrue

parseFalse :: Parser Term 
parseFalse =  string "False" >> return TmFalse

parseInt :: Parser Term 
parseInt =  do
  x <- many1 digit
  return (num2Tm (read x :: Int))

num2Tm :: Int -> Term
num2Tm n = 
       if n > 0 then (TmSucc (num2Tm (n - 1)))
		else TmZero

parseIsZero :: Parser Term 
parseIsZero =  do
  string "zero?" 
  many space
  t <- parseTerm
  return $ TmIsZero t

parseIf :: Parser Term
parseIf = do
  string "if"
  space
  t1 <- parseTerm
  space
  string "then"
  space
  t2 <- parseTerm
  space
  string "else"
  space
  t3 <- parseTerm
  return $ TmIf t1 t2 t3


parsePred :: Parser Term 
parsePred =  do
  string "pred" 
  space
  t <- parseTerm
  return $ TmPred t


parseTerm :: Parser Term
parseTerm = 
    parseTrue  <|>
    parseFalse <|>
    parsePred  <|>
    parseInt   <|>
    parseIf    <|>
    parseIsZero<|>
     between (string "(") (string ")") parseTerm

-------------------------------------------


interp = do
  tm <- getLine
  if tm == "" then return TmErro
	     else do
		parseTest parseTerm tm
		interp

main =do 
  parseTest parseTerm "True"
  parseTest parseTerm "False"
  parseTest parseTerm "3"
  parseTest parseTerm "pred 3"
  parseTest parseTerm "if 3 then True else False"
  parseTest parseTerm "zero? 0"
  parseTest parseTerm "zero? pred (3)"
  interp
