module Typecheck where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

pred :: Nat -> Nat
pred n =
  case n of {
   O -> n;
   S u -> u}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x ->
    case x of {
     True -> Right;
     False -> Left}) b1 b2

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ h x ->
    case x of {
     EmptyString -> Right;
     String0 a0 s0 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (h s0))
        (\_ -> Right) (ascii_dec a a0)}) s1 s2

eqb_string :: String -> String -> Bool
eqb_string x y =
  case string_dec x y of {
   Left -> True;
   Right -> False}

type Total_map a = String -> a

t_update :: (Total_map a1) -> String -> a1 -> String -> a1
t_update m x v x' =
  case eqb_string x x' of {
   True -> v;
   False -> m x'}

type Partial_map a = Total_map (Option a)

update :: (Partial_map a1) -> String -> a1 -> String -> Option a1
update m x v =
  t_update m x (Some v)

data Ty =
   Arrow Ty Ty
 | Nat0
 | Sum Ty Ty
 | List Ty
 | Unit
 | Prod Ty Ty

data Tm =
   Var String
 | App Tm Tm
 | Abs String Ty Tm
 | Const Nat
 | Scc Tm
 | Prd Tm
 | Mlt Tm Tm
 | Test0 Tm Tm Tm
 | Tinl Ty Tm
 | Tinr Ty Tm
 | Tcase Tm String Tm String Tm
 | Tnil Ty
 | Tcons Tm Tm
 | Tlcase Tm Tm String String Tm
 | Unit0
 | Pair Tm Tm
 | Fst Tm
 | Snd Tm
 | Tlet String Tm Tm
 | Tfix Tm

subst :: String -> Tm -> Tm -> Tm
subst x s t =
  case t of {
   Var y -> case eqb_string x y of {
             True -> s;
             False -> t};
   App t1 t2 -> App (subst x s t1) (subst x s t2);
   Abs y t0 t1 -> Abs y t0
    (case eqb_string x y of {
      True -> t1;
      False -> subst x s t1});
   Const n -> Const n;
   Scc t1 -> Scc (subst x s t1);
   Prd t1 -> Prd (subst x s t1);
   Mlt t1 t2 -> Mlt (subst x s t1) (subst x s t2);
   Test0 t1 t2 t3 -> Test0 (subst x s t1) (subst x s t2) (subst x s t3);
   Tinl t0 t1 -> Tinl t0 (subst x s t1);
   Tinr t0 t1 -> Tinr t0 (subst x s t1);
   Tcase t0 y1 t1 y2 t2 -> Tcase (subst x s t0) y1
    (case eqb_string x y1 of {
      True -> t1;
      False -> subst x s t1}) y2
    (case eqb_string x y2 of {
      True -> t2;
      False -> subst x s t2});
   Tnil t0 -> Tnil t0;
   Tcons t1 t2 -> Tcons (subst x s t1) (subst x s t2);
   Tlcase t1 t2 y1 y2 t3 -> Tlcase (subst x s t1) (subst x s t2) y1 y2
    (case eqb_string x y1 of {
      True -> t3;
      False -> case eqb_string x y2 of {
                True -> t3;
                False -> subst x s t3}});
   Unit0 -> Unit0;
   _ -> t}

type Context = Partial_map Ty

eqb_ty :: Ty -> Ty -> Bool
eqb_ty t1 t2 =
  case t1 of {
   Arrow t11 t12 ->
    case t2 of {
     Arrow t21 t22 -> andb (eqb_ty t11 t21) (eqb_ty t12 t22);
     _ -> False};
   Nat0 -> case t2 of {
            Nat0 -> True;
            _ -> False};
   Sum t11 t12 ->
    case t2 of {
     Sum t21 t22 -> andb (eqb_ty t11 t21) (eqb_ty t12 t22);
     _ -> False};
   List t11 -> case t2 of {
                List t21 -> eqb_ty t11 t21;
                _ -> False};
   Unit -> case t2 of {
            Unit -> True;
            _ -> False};
   Prod t11 t12 ->
    case t2 of {
     Prod t21 t22 -> andb (eqb_ty t11 t21) (eqb_ty t12 t22);
     _ -> False}}

type_check :: Context -> Tm -> Option Ty
type_check gamma t =
  case t of {
   Var x -> gamma x;
   App t1 t2 ->
    case type_check gamma t1 of {
     Some t3 ->
      case type_check gamma t2 of {
       Some t4 ->
        case t3 of {
         Arrow t11 t12 ->
          case eqb_ty t11 t4 of {
           True -> Some t12;
           False -> None};
         _ -> None};
       None -> None};
     None -> None};
   Abs x1 t1 t2 ->
    case type_check (update gamma x1 t1) t2 of {
     Some t3 -> Some (Arrow t1 t3);
     None -> None};
   Const _ -> Some Nat0;
   Scc t1 ->
    case type_check gamma t1 of {
     Some t2 -> case t2 of {
                 Nat0 -> Some Nat0;
                 _ -> None};
     None -> None};
   Prd t1 ->
    case type_check gamma t1 of {
     Some t2 -> case t2 of {
                 Nat0 -> Some Nat0;
                 _ -> None};
     None -> None};
   Mlt t1 t2 ->
    case type_check gamma t1 of {
     Some t3 ->
      case type_check gamma t2 of {
       Some t4 ->
        case t3 of {
         Nat0 -> case t4 of {
                  Nat0 -> Some Nat0;
                  _ -> None};
         _ -> None};
       None -> None};
     None -> None};
   Test0 guard t0 f ->
    case type_check gamma guard of {
     Some tguard ->
      case type_check gamma t0 of {
       Some t1 ->
        case type_check gamma f of {
         Some t2 ->
          case tguard of {
           Nat0 -> case eqb_ty t1 t2 of {
                    True -> Some t1;
                    False -> None};
           _ -> None};
         None -> None};
       None -> None};
     None -> None};
   Tinl t2 t1 ->
    case type_check gamma t1 of {
     Some t3 -> Some (Sum t3 t2);
     None -> None};
   Tinr t1 t2 ->
    case type_check gamma t2 of {
     Some t3 -> Some (Sum t1 t3);
     None -> None};
   Tcase t0 x1 t1 x2 t2 ->
    case type_check gamma t0 of {
     Some t3 ->
      case t3 of {
       Sum t4 t5 ->
        case type_check (update gamma x1 t4) t1 of {
         Some t6 ->
          case type_check (update gamma x2 t5) t2 of {
           Some t7 -> case eqb_ty t6 t7 of {
                       True -> Some t6;
                       False -> None};
           None -> None};
         None -> None};
       _ -> None};
     None -> None};
   Tnil t0 -> Some (List t0);
   Tcons t1 t2 ->
    case type_check gamma t1 of {
     Some t3 ->
      case type_check gamma t2 of {
       Some t4 ->
        case t4 of {
         List t5 ->
          case eqb_ty t3 t5 of {
           True -> Some (List t3);
           False -> None};
         _ -> None};
       None -> None};
     None -> None};
   Tlcase t0 t1 x21 x22 t2 ->
    case type_check gamma t0 of {
     Some t3 ->
      case t3 of {
       List t4 ->
        case type_check gamma t1 of {
         Some t1' ->
          case type_check (update (update gamma x22 (List t4)) x21 t4) t2 of {
           Some t2' ->
            case eqb_ty t1' t2' of {
             True -> Some t1';
             False -> None};
           None -> None};
         None -> None};
       _ -> None};
     None -> None};
   Unit0 -> Some Unit;
   Pair t1 t2 ->
    case type_check gamma t1 of {
     Some t3 ->
      case type_check gamma t2 of {
       Some t4 -> Some (Prod t3 t4);
       None -> None};
     None -> None};
   Fst t0 ->
    case type_check gamma t0 of {
     Some t1 -> case t1 of {
                 Prod t2 _ -> Some t2;
                 _ -> None};
     None -> None};
   Snd t0 ->
    case type_check gamma t0 of {
     Some t1 -> case t1 of {
                 Prod _ t2 -> Some t2;
                 _ -> None};
     None -> None};
   Tlet x t1 t2 ->
    case type_check gamma t1 of {
     Some t3 -> type_check (update gamma x t3) t2;
     None -> None};
   Tfix t0 ->
    case type_check gamma t0 of {
     Some t1 ->
      case t1 of {
       Arrow t2 t3 -> case eqb_ty t2 t3 of {
                       True -> Some t2;
                       False -> None};
       _ -> None};
     None -> None}}

value_bool :: Tm -> Bool
value_bool t =
  case t of {
   Abs _ _ _ -> True;
   Const _ -> True;
   Tinl _ v -> value_bool v;
   Tinr _ v -> value_bool v;
   Tnil _ -> True;
   Tcons v1 v2 -> andb (value_bool v1) (value_bool v2);
   Unit0 -> True;
   Pair v1 v2 -> andb (value_bool v1) (value_bool v2);
   _ -> False}

stepf :: Tm -> Option Tm
stepf t =
  case t of {
   App t1 t2 ->
    case stepf t1 of {
     Some t1' -> Some (App t1' t2);
     None ->
      case value_bool t1 of {
       True ->
        case stepf t2 of {
         Some t2' -> Some (App t1 t2');
         None ->
          case value_bool t2 of {
           True ->
            case t1 of {
             Abs x _ t12 -> Some (subst x t2 t12);
             _ -> None};
           False -> None}};
       False -> None}};
   Scc t1 ->
    case t1 of {
     Const n -> Some (Const (S n));
     _ -> case stepf t1 of {
           Some t1' -> Some (Scc t1');
           None -> None}};
   Prd t1 ->
    case t1 of {
     Const n -> Some (Const (pred n));
     _ -> case stepf t1 of {
           Some t1' -> Some (Prd t1');
           None -> None}};
   Mlt t1 t2 ->
    case stepf t1 of {
     Some t1' -> Some (Mlt t1' t2);
     None ->
      case value_bool t1 of {
       True ->
        case stepf t2 of {
         Some t2' -> Some (Mlt t1 t2');
         None ->
          case t1 of {
           Const n1 ->
            case t2 of {
             Const n2 -> Some (Const (mul n1 n2));
             _ -> None};
           _ -> None}};
       False -> None}};
   Test0 t1 t2 t3 ->
    case t1 of {
     Const n0 -> case n0 of {
                  O -> Some t2;
                  S _ -> Some t3};
     _ ->
      case stepf t1 of {
       Some t1' -> Some (Test0 t1' t2 t3);
       None -> None}};
   Tinl t0 t1 ->
    case stepf t1 of {
     Some t1' -> Some (Tinl t0 t1');
     None -> None};
   Tinr t0 t1 ->
    case stepf t1 of {
     Some t1' -> Some (Tinr t0 t1');
     None -> None};
   Tcase t0 x1 t1 x2 t2 ->
    case stepf t0 of {
     Some t0' -> Some (Tcase t0' x1 t1 x2 t2);
     None ->
      case t0 of {
       Tinl _ v0 ->
        case value_bool v0 of {
         True ->
          case stepf v0 of {
           Some _ -> None;
           None -> Some (subst x1 v0 t1)};
         False -> None};
       Tinr _ v0 ->
        case value_bool v0 of {
         True ->
          case stepf v0 of {
           Some _ -> None;
           None -> Some (subst x2 v0 t2)};
         False -> None};
       _ -> None}};
   Tcons t1 t2 ->
    case stepf t1 of {
     Some t1' -> Some (Tcons t1' t2);
     None ->
      case value_bool t1 of {
       True ->
        case stepf t2 of {
         Some t2' -> Some (Tcons t1 t2');
         None -> None};
       False -> None}};
   Tlcase t1 t2 x1 x2 t3 ->
    case stepf t1 of {
     Some t1' -> Some (Tlcase t1' t2 x1 x2 t3);
     None ->
      case t1 of {
       Tnil _ -> Some t2;
       Tcons v1 vl ->
        case andb (value_bool v1) (value_bool vl) of {
         True -> Some (subst x2 vl (subst x1 v1 t3));
         False -> None};
       _ -> None}};
   Pair t1 t2 ->
    case stepf t1 of {
     Some t1' -> Some (Pair t1' t2);
     None ->
      case value_bool t1 of {
       True ->
        case stepf t2 of {
         Some t2' -> Some (Pair t1 t2');
         None -> None};
       False -> None}};
   Fst t0 ->
    case stepf t0 of {
     Some t' -> Some (Fst t');
     None ->
      case value_bool t0 of {
       True -> case t0 of {
                Pair t1 _ -> Some t1;
                _ -> None};
       False -> None}};
   Snd t0 ->
    case stepf t0 of {
     Some t' -> Some (Snd t');
     None ->
      case value_bool t0 of {
       True -> case t0 of {
                Pair _ t2 -> Some t2;
                _ -> None};
       False -> None}};
   Tlet x t1 t2 ->
    case stepf t1 of {
     Some t1' -> Some (Tlet x t1' t2);
     None ->
      case value_bool t1 of {
       True -> Some (subst x t1 t2);
       False -> None}};
   Tfix t0 ->
    case stepf t0 of {
     Some t' -> Some (Tfix t');
     None ->
      case t0 of {
       Abs x _ t1 -> Some (subst x (Tfix t0) t1);
       _ -> None}};
   _ -> None}

