
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

val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val bool_dec : bool -> bool -> sumbool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

val eqb_string : string -> string -> bool

type 'a total_map = string -> 'a

val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1

type 'a partial_map = 'a option total_map

val update : 'a1 partial_map -> string -> 'a1 -> string -> 'a1 option

module STLCExtended :
 sig
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

  val subst : string -> tm -> tm -> tm

  type context = ty partial_map
 end

val eqb_ty : STLCExtended.ty -> STLCExtended.ty -> bool

val type_check : STLCExtended.context -> STLCExtended.tm -> STLCExtended.ty option

val value_bool : STLCExtended.tm -> bool

val stepf : STLCExtended.tm -> STLCExtended.tm option
