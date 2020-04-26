module lambda where

postulate A : Set
postulate B : Set
postulate f : A -> B
postulate a : A

b : B
b = f a

id : A -> A
id = \x -> x

id2 : A -> A
id2 a = a

postulate P : ( A -> A ) -> Set

k : P id -> P id2
k x = x

A2 : Set
A2 = A -> A
A3 : Set
A3 = A2 -> A2
a2 : A2
a2 = \x -> x

