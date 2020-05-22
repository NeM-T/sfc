
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (x, x0, x1, x2, x3, x4, x5, x6) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec x b8 with
   | Left ->
     (match bool_dec x0 b9 with
      | Left ->
        (match bool_dec x1 b10 with
         | Left ->
           (match bool_dec x2 b11 with
            | Left ->
              (match bool_dec x3 b12 with
               | Left ->
                 (match bool_dec x4 b13 with
                  | Left -> (match bool_dec x5 b14 with
                             | Left -> bool_dec x6 b15
                             | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> Left
                    | String (_, _) -> Right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Right
     | String (a0, s1) -> (match ascii_dec a a0 with
                           | Left -> string_dec s0 s1
                           | Right -> Right))

(** val eqb_string : string -> string -> bool **)

let eqb_string x y =
  match string_dec x y with
  | Left -> True
  | Right -> False

type 'a total_map = string -> 'a

(** val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1 **)

let t_update m x v x' =
  match eqb_string x x' with
  | True -> v
  | False -> m x'

type 'a partial_map = 'a option total_map

(** val update : 'a1 partial_map -> string -> 'a1 -> string -> 'a1 option **)

let update m x v =
  t_update m x (Some v)

module STLCExtended =
 struct
  type ty =
  | Arrow of ty * ty
  | Nat
  | Sum of ty * ty
  | List of ty
  | Unit
  | Prod of ty * ty

  type tm =
  | Coq_var of string
  | Coq_app of tm * tm
  | Coq_abs of string * ty * tm
  | Coq_const of nat
  | Coq_scc of tm
  | Coq_prd of tm
  | Coq_mlt of tm * tm
  | Coq_test0 of tm * tm * tm
  | Coq_tinl of ty * tm
  | Coq_tinr of ty * tm
  | Coq_tcase of tm * string * tm * string * tm
  | Coq_tnil of ty
  | Coq_tcons of tm * tm
  | Coq_tlcase of tm * tm * string * string * tm
  | Coq_unit
  | Coq_pair of tm * tm
  | Coq_fst of tm
  | Coq_snd of tm
  | Coq_tlet of string * tm * tm
  | Coq_tfix of tm

  (** val subst : string -> tm -> tm -> tm **)

  let rec subst x s t = match t with
  | Coq_var y -> (match eqb_string x y with
                  | True -> s
                  | False -> t)
  | Coq_app (t1, t2) -> Coq_app ((subst x s t1), (subst x s t2))
  | Coq_abs (y, t0, t1) -> Coq_abs (y, t0, (match eqb_string x y with
                                            | True -> t1
                                            | False -> subst x s t1))
  | Coq_const n -> Coq_const n
  | Coq_scc t1 -> Coq_scc (subst x s t1)
  | Coq_prd t1 -> Coq_prd (subst x s t1)
  | Coq_mlt (t1, t2) -> Coq_mlt ((subst x s t1), (subst x s t2))
  | Coq_test0 (t1, t2, t3) -> Coq_test0 ((subst x s t1), (subst x s t2), (subst x s t3))
  | Coq_tinl (t0, t1) -> Coq_tinl (t0, (subst x s t1))
  | Coq_tinr (t0, t1) -> Coq_tinr (t0, (subst x s t1))
  | Coq_tcase (t0, y1, t1, y2, t2) ->
    Coq_tcase ((subst x s t0), y1, (match eqb_string x y1 with
                                    | True -> t1
                                    | False -> subst x s t1), y2,
      (match eqb_string x y2 with
       | True -> t2
       | False -> subst x s t2))
  | Coq_tnil t0 -> Coq_tnil t0
  | Coq_tcons (t1, t2) -> Coq_tcons ((subst x s t1), (subst x s t2))
  | Coq_tlcase (t1, t2, y1, y2, t3) ->
    Coq_tlcase ((subst x s t1), (subst x s t2), y1, y2,
      (match eqb_string x y1 with
       | True -> t3
       | False -> (match eqb_string x y2 with
                   | True -> t3
                   | False -> subst x s t3)))
  | Coq_unit -> Coq_unit
  | _ -> t

  type context = ty partial_map
 end

(** val eqb_ty : STLCExtended.ty -> STLCExtended.ty -> bool **)

let rec eqb_ty t1 t2 =
  match t1 with
  | STLCExtended.Arrow (t11, t12) ->
    (match t2 with
     | STLCExtended.Arrow (t21, t22) -> (match eqb_ty t11 t21 with
                                         | True -> eqb_ty t12 t22
                                         | False -> False)
     | _ -> False)
  | STLCExtended.Nat -> (match t2 with
                         | STLCExtended.Nat -> True
                         | _ -> False)
  | STLCExtended.Sum (t11, t12) ->
    (match t2 with
     | STLCExtended.Sum (t21, t22) -> (match eqb_ty t11 t21 with
                                       | True -> eqb_ty t12 t22
                                       | False -> False)
     | _ -> False)
  | STLCExtended.List t11 -> (match t2 with
                              | STLCExtended.List t21 -> eqb_ty t11 t21
                              | _ -> False)
  | STLCExtended.Unit -> (match t2 with
                          | STLCExtended.Unit -> True
                          | _ -> False)
  | STLCExtended.Prod (t11, t12) ->
    (match t2 with
     | STLCExtended.Prod (t21, t22) -> (match eqb_ty t11 t21 with
                                        | True -> eqb_ty t12 t22
                                        | False -> False)
     | _ -> False)

(** val type_check : STLCExtended.context -> STLCExtended.tm -> STLCExtended.ty option **)

let rec type_check gamma = function
| STLCExtended.Coq_var x -> gamma x
| STLCExtended.Coq_app (t1, t2) ->
  (match type_check gamma t1 with
   | Some t3 ->
     (match type_check gamma t2 with
      | Some t4 ->
        (match t3 with
         | STLCExtended.Arrow (t11, t12) -> (match eqb_ty t11 t4 with
                                             | True -> Some t12
                                             | False -> None)
         | _ -> None)
      | None -> None)
   | None -> None)
| STLCExtended.Coq_abs (x1, t1, t2) ->
  (match type_check (update gamma x1 t1) t2 with
   | Some t3 -> Some (STLCExtended.Arrow (t1, t3))
   | None -> None)
| STLCExtended.Coq_const _ -> Some STLCExtended.Nat
| STLCExtended.Coq_scc t1 ->
  (match type_check gamma t1 with
   | Some t2 -> (match t2 with
                 | STLCExtended.Nat -> Some STLCExtended.Nat
                 | _ -> None)
   | None -> None)
| STLCExtended.Coq_prd t1 ->
  (match type_check gamma t1 with
   | Some t2 -> (match t2 with
                 | STLCExtended.Nat -> Some STLCExtended.Nat
                 | _ -> None)
   | None -> None)
| STLCExtended.Coq_mlt (t1, t2) ->
  (match type_check gamma t1 with
   | Some t3 ->
     (match type_check gamma t2 with
      | Some t4 ->
        (match t3 with
         | STLCExtended.Nat -> (match t4 with
                                | STLCExtended.Nat -> Some STLCExtended.Nat
                                | _ -> None)
         | _ -> None)
      | None -> None)
   | None -> None)
| STLCExtended.Coq_test0 (guard, t0, f) ->
  (match type_check gamma guard with
   | Some tguard ->
     (match type_check gamma t0 with
      | Some t1 ->
        (match type_check gamma f with
         | Some t2 ->
           (match tguard with
            | STLCExtended.Nat -> (match eqb_ty t1 t2 with
                                   | True -> Some t1
                                   | False -> None)
            | _ -> None)
         | None -> None)
      | None -> None)
   | None -> None)
| STLCExtended.Coq_tinl (t2, t1) ->
  (match type_check gamma t1 with
   | Some t3 -> Some (STLCExtended.Sum (t3, t2))
   | None -> None)
| STLCExtended.Coq_tinr (t1, t2) ->
  (match type_check gamma t2 with
   | Some t3 -> Some (STLCExtended.Sum (t1, t3))
   | None -> None)
| STLCExtended.Coq_tcase (t0, x1, t1, x2, t2) ->
  (match type_check gamma t0 with
   | Some t3 ->
     (match t3 with
      | STLCExtended.Sum (t4, t5) ->
        (match type_check (update gamma x1 t4) t1 with
         | Some t6 ->
           (match type_check (update gamma x2 t5) t2 with
            | Some t7 -> (match eqb_ty t6 t7 with
                          | True -> Some t6
                          | False -> None)
            | None -> None)
         | None -> None)
      | _ -> None)
   | None -> None)
| STLCExtended.Coq_tnil t0 -> Some (STLCExtended.List t0)
| STLCExtended.Coq_tcons (t1, t2) ->
  (match type_check gamma t1 with
   | Some t3 ->
     (match type_check gamma t2 with
      | Some t4 ->
        (match t4 with
         | STLCExtended.List t5 -> (match eqb_ty t3 t5 with
                                    | True -> Some (STLCExtended.List t3)
                                    | False -> None)
         | _ -> None)
      | None -> None)
   | None -> None)
| STLCExtended.Coq_tlcase (t0, t1, x21, x22, t2) ->
  (match type_check gamma t0 with
   | Some t3 ->
     (match t3 with
      | STLCExtended.List t4 ->
        (match type_check gamma t1 with
         | Some t1' ->
           (match type_check (update (update gamma x22 (STLCExtended.List t4)) x21 t4) t2 with
            | Some t2' -> (match eqb_ty t1' t2' with
                           | True -> Some t1'
                           | False -> None)
            | None -> None)
         | None -> None)
      | _ -> None)
   | None -> None)
| STLCExtended.Coq_unit -> Some STLCExtended.Unit
| STLCExtended.Coq_pair (t1, t2) ->
  (match type_check gamma t1 with
   | Some t3 -> (match type_check gamma t2 with
                 | Some t4 -> Some (STLCExtended.Prod (t3, t4))
                 | None -> None)
   | None -> None)
| STLCExtended.Coq_fst t0 ->
  (match type_check gamma t0 with
   | Some t1 -> (match t1 with
                 | STLCExtended.Prod (t2, _) -> Some t2
                 | _ -> None)
   | None -> None)
| STLCExtended.Coq_snd t0 ->
  (match type_check gamma t0 with
   | Some t1 -> (match t1 with
                 | STLCExtended.Prod (_, t2) -> Some t2
                 | _ -> None)
   | None -> None)
| STLCExtended.Coq_tlet (x, t1, t2) ->
  (match type_check gamma t1 with
   | Some t3 -> type_check (update gamma x t3) t2
   | None -> None)
| STLCExtended.Coq_tfix t0 ->
  (match type_check gamma t0 with
   | Some t1 ->
     (match t1 with
      | STLCExtended.Arrow (t2, t3) -> (match eqb_ty t2 t3 with
                                        | True -> Some t2
                                        | False -> None)
      | _ -> None)
   | None -> None)

(** val value_bool : STLCExtended.tm -> bool **)

let rec value_bool = function
| STLCExtended.Coq_abs (_, _, _) -> True
| STLCExtended.Coq_const _ -> True
| STLCExtended.Coq_tinl (_, v) -> value_bool v
| STLCExtended.Coq_tinr (_, v) -> value_bool v
| STLCExtended.Coq_tnil _ -> True
| STLCExtended.Coq_tcons (v1, v2) -> (match value_bool v1 with
                                      | True -> value_bool v2
                                      | False -> False)
| STLCExtended.Coq_unit -> True
| STLCExtended.Coq_pair (v1, v2) -> (match value_bool v1 with
                                     | True -> value_bool v2
                                     | False -> False)
| _ -> False

(** val stepf : STLCExtended.tm -> STLCExtended.tm option **)

let rec stepf = function
| STLCExtended.Coq_app (t1, t2) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_app (t1', t2))
   | None ->
     (match value_bool t1 with
      | True ->
        (match stepf t2 with
         | Some t2' -> Some (STLCExtended.Coq_app (t1, t2'))
         | None ->
           (match value_bool t2 with
            | True ->
              (match t1 with
               | STLCExtended.Coq_abs (x, _, t12) -> Some (STLCExtended.subst x t2 t12)
               | _ -> None)
            | False -> None))
      | False -> None))
| STLCExtended.Coq_scc t1 ->
  (match t1 with
   | STLCExtended.Coq_const n -> Some (STLCExtended.Coq_const (S n))
   | _ -> (match stepf t1 with
           | Some t1' -> Some (STLCExtended.Coq_scc t1')
           | None -> None))
| STLCExtended.Coq_prd t1 ->
  (match t1 with
   | STLCExtended.Coq_const n -> Some (STLCExtended.Coq_const (pred n))
   | _ -> (match stepf t1 with
           | Some t1' -> Some (STLCExtended.Coq_prd t1')
           | None -> None))
| STLCExtended.Coq_mlt (t1, t2) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_mlt (t1', t2))
   | None ->
     (match value_bool t1 with
      | True ->
        (match stepf t2 with
         | Some t2' -> Some (STLCExtended.Coq_mlt (t1, t2'))
         | None ->
           (match t1 with
            | STLCExtended.Coq_const n1 ->
              (match t2 with
               | STLCExtended.Coq_const n2 -> Some (STLCExtended.Coq_const (mul n1 n2))
               | _ -> None)
            | _ -> None))
      | False -> None))
| STLCExtended.Coq_test0 (t1, t2, t3) ->
  (match t1 with
   | STLCExtended.Coq_const n0 -> (match n0 with
                                   | O -> Some t2
                                   | S _ -> Some t3)
   | _ -> (match stepf t1 with
           | Some t1' -> Some (STLCExtended.Coq_test0 (t1', t2, t3))
           | None -> None))
| STLCExtended.Coq_tinl (t0, t1) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_tinl (t0, t1'))
   | None -> None)
| STLCExtended.Coq_tinr (t0, t1) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_tinr (t0, t1'))
   | None -> None)
| STLCExtended.Coq_tcase (t0, x1, t1, x2, t2) ->
  (match stepf t0 with
   | Some t0' -> Some (STLCExtended.Coq_tcase (t0', x1, t1, x2, t2))
   | None ->
     (match t0 with
      | STLCExtended.Coq_tinl (_, v0) ->
        (match value_bool v0 with
         | True -> (match stepf v0 with
                    | Some _ -> None
                    | None -> Some (STLCExtended.subst x1 v0 t1))
         | False -> None)
      | STLCExtended.Coq_tinr (_, v0) ->
        (match value_bool v0 with
         | True -> (match stepf v0 with
                    | Some _ -> None
                    | None -> Some (STLCExtended.subst x2 v0 t2))
         | False -> None)
      | _ -> None))
| STLCExtended.Coq_tcons (t1, t2) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_tcons (t1', t2))
   | None ->
     (match value_bool t1 with
      | True -> (match stepf t2 with
                 | Some t2' -> Some (STLCExtended.Coq_tcons (t1, t2'))
                 | None -> None)
      | False -> None))
| STLCExtended.Coq_tlcase (t1, t2, x1, x2, t3) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_tlcase (t1', t2, x1, x2, t3))
   | None ->
     (match t1 with
      | STLCExtended.Coq_tnil _ -> Some t2
      | STLCExtended.Coq_tcons (v1, vl) ->
        (match match value_bool v1 with
               | True -> value_bool vl
               | False -> False with
         | True -> Some (STLCExtended.subst x2 vl (STLCExtended.subst x1 v1 t3))
         | False -> None)
      | _ -> None))
| STLCExtended.Coq_pair (t1, t2) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_pair (t1', t2))
   | None ->
     (match value_bool t1 with
      | True -> (match stepf t2 with
                 | Some t2' -> Some (STLCExtended.Coq_pair (t1, t2'))
                 | None -> None)
      | False -> None))
| STLCExtended.Coq_fst t0 ->
  (match stepf t0 with
   | Some t' -> Some (STLCExtended.Coq_fst t')
   | None ->
     (match value_bool t0 with
      | True -> (match t0 with
                 | STLCExtended.Coq_pair (t1, _) -> Some t1
                 | _ -> None)
      | False -> None))
| STLCExtended.Coq_snd t0 ->
  (match stepf t0 with
   | Some t' -> Some (STLCExtended.Coq_snd t')
   | None ->
     (match value_bool t0 with
      | True -> (match t0 with
                 | STLCExtended.Coq_pair (_, t2) -> Some t2
                 | _ -> None)
      | False -> None))
| STLCExtended.Coq_tlet (x, t1, t2) ->
  (match stepf t1 with
   | Some t1' -> Some (STLCExtended.Coq_tlet (x, t1', t2))
   | None -> (match value_bool t1 with
              | True -> Some (STLCExtended.subst x t1 t2)
              | False -> None))
| STLCExtended.Coq_tfix t0 ->
  (match stepf t0 with
   | Some t' -> Some (STLCExtended.Coq_tfix t')
   | None ->
     (match t0 with
      | STLCExtended.Coq_abs (x, _, t1) -> Some (STLCExtended.subst x (STLCExtended.Coq_tfix t0) t1)
      | _ -> None))
| _ -> None
