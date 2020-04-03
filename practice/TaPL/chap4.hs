(|>) a f = f a

data Term = TmTrue
    | TmFalse 
    | TmIf Term Term Term
    | TmZero
    | TmSucc Term
    | TmPred Term
    | TmIsZero Term
    | TmErro


isval :: Term -> Bool
isval TmTrue  = True 
isval TmFalse = True
isval t       = isnumericval t

isnumericval :: Term -> Bool
isnumericval TmZero      = True
isnumericval (TmSucc t1) = isnumericval t1
_ 		       = False

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


