Set Implicit Arguments.

Require Import List.
Remove Hints Bool.trans_eq_bool.


(* 等価継続 *)
Ltac idcont tt :=
  idtac.

(* タクティックの型付けされない引数 *)

(* 任意のCoqの値は型Boxerに収めることができます。 これは、タクティックを実装するためのCoqの計算に便利です。 *)
Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.

(* タクティックのオプショナルな引数 *)
(* ltac_no_argは、タクティックの定義の中で、オプショナルな引数をシミュレートするのに使うことができる定数です。 タクティックの呼び出しには mytactic ltac_no_arg とします。 また、引数が与えられたかどうかをテストするためには match arg with ltac_no_arg => .. または match type of arg with ltac_No_arg => .. とします。 *)
Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.

(* タクティックのワイルドカード引数 *)
(* ltac_wildは、タクティックの定義の中で、ワイルドカード引数をシミュレートするのに使うことができる定数です。 記法は __ です。 *)
Inductive ltac_Wild : Set :=
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(* ltac_wildsは、典型的にはN個のワイルドカードの列をシミュレートするのに使う定数です。 ここでNはコンテキストに依存して適切に選ばれます。記法は ___ です。 *)

Inductive ltac_Wilds : Set :=
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.

(* ポジションマーカ *)

(* ltac_Markとltac_markは、コンテキストまたはゴールにおいて、特定のポジションにマークをつけるために、タクティックが使う標識のダミーの定義です。 *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(* gen_until_markはコンテキストの一番下の仮定から型Markの仮定に逹するまでgeneralizeを繰り返します。 コンテキストにMarkが現れないときは失敗します。 *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.


Ltac gen_until_mark_with_processing cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H; generalize H; clear H;
         gen_until_mark_with_processing cont
  end end.

(* intro_until_markは型Markの仮定に逹するまでintroを繰り返します。 そしてその仮定Markを廃棄します。 ゴールの仮定にMarkが現れないときには失敗します。 *)

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.



(* タクティックの引数のリスト *)

(* 型list Boxerの datatype は ltac でCoqの値のリストを扱うために使われます。 記法は >> v1 v2 ... vN で値v1からvNまでを含むリストを作ります。 *)

Notation "'>>'" :=
  (@nil Boxer)
  (at level 0)
  : ltac_scope.
Notation "'>>' v1" :=
  ((boxer v1)::nil)
  (at level 0, v1 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2" :=
  ((boxer v1)::(boxer v2)::nil)
  (at level 0, v1 at level 0, v2 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, v13 at level 0)
  : ltac_scope.

(*
タクティックlist_boxer_ofは項Eを入力し、次の規則に従って型 "list boxer" の項を返します:
もしEが既に型"list Boxer"ならばEを返す;
そうでなければリスト (boxer E)::nil を返す。
 *)

Ltac list_boxer_of E :=
  match type of E with
  | List.list Boxer => constr:(E)
  | _ => constr:((boxer E)::nil)
  end.

(* 補題のデータベース *)
(* 項を項へマップするデータベースを実装するために、ヒント機構を使います。 新しいデータベースを宣言するには定義 Definition mydatabase := True. を使います。
そして、mykeyをmyvalueにマップするには、次のヒントを記述します: Hint Extern 1 (Register mydatabase mykey) => Provide myvalue. 
最後に、キーに関連付けられた値を問合わせるには、タクティックltac_database_get mydatabase mykeyを走らせます。 そうするとゴールの先頭に項myvalueが置かれます。 するとintroによって指名し利用できます。 *)

Inductive Ltac_database_token : Prop := ltac_database_token.

Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.

Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
  (at level 69, D at level 0, T at level 0).

Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer),
  ltac_database D T A.
Proof using. split. Qed.

Ltac Provide T := apply (@ltac_database_provide (boxer T)).

Ltac ltac_database_get D T :=
  let A := fresh "TEMP" in evar (A:Boxer);
  let H := fresh "TEMP" in
  assert (H : ltac_database (boxer D) (boxer T) A);
  [ subst A; auto
  | subst A; match type of H with ltac_database _ _ (boxer ?L) =>
               generalize L end; clear H ].


(* その場での仮定の除去 *)
(* lets、applys、forwards、specializesなどのタクティックに渡される引数のリスト >> H1 H2 .. HN において、 恒等関数である項rmを消去すべき仮定の名前の前に置くことができます。 *)

Definition rm (A:Type) (X:A) := X.

(* rm_term E はEと同じ型と認められる仮定を除去します。 *)

Ltac rm_term E :=
  let T := type of E in
  match goal with H: T |- _ => try clear H end.

(* rm_inside E は rm Ei という形のEの任意の部分項に対して rm_term Ei を呼びます。 *)
Ltac rm_inside E :=
  let go E := rm_inside E in
  match E with
  | rm ?X => rm_term X
  | ?X1 ?X2 =>
     go X1; go X2
  | ?X1 ?X2 ?X3 =>
     go X1; go X2; go X3
  | ?X1 ?X2 ?X3 ?X4 =>
     go X1; go X2; go X3; go X4
  | ?X1 ?X2 ?X3 ?X4 ?X5 =>
     go X1; go X2; go X3; go X4; go X5
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 =>
     go X1; go X2; go X3; go X4; go X5; go X6
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9; go X10
  | _ => idtac
  end.

(* パフォーマンスを上げるためにrm_insideを非アクティブ化するには、次の定義の本体をidtacに置換してください。 *)
Ltac fast_rm_inside E :=
  rm_inside E.

(* 引数としての数値 *)

(* タクティックが自然数を引数としてとるとき、自然数として構文解析される可能性と相対値として構文解析される可能性があります。 タクティックが引数を自然数に変換するために、変換タクティックを提供します。 *)
Require BinPos Coq.ZArith.BinInt.

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
  match x with
  | BinInt.Z0 => 0%nat
  | BinInt.Zpos p => BinPos.nat_of_P p
  | BinInt.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.

(* ltac_pattern E at Kは pattern E at K と同様ですが、K が Ltac の整数ではなく Coq の数（natかZ）である点が違います。 構文 ltac_pattern E as K in H も可能です。 *)

Tactic Notation "ltac_pattern" constr(E) "at" constr(K) :=
  match number_to_nat K with
  | 1 => pattern E at 1
  | 2 => pattern E at 2
  | 3 => pattern E at 3
  | 4 => pattern E at 4
  | 5 => pattern E at 5
  | 6 => pattern E at 6
  | 7 => pattern E at 7
  | 8 => pattern E at 8
  | _ => fail "ltac_pattern: arity not supported"
  end.

Tactic Notation "ltac_pattern" constr(E) "at" constr(K) "in" hyp(H) :=
  match number_to_nat K with
  | 1 => pattern E at 1 in H
  | 2 => pattern E at 2 in H
  | 3 => pattern E at 3 in H
  | 4 => pattern E at 4 in H
  | 5 => pattern E at 5 in H
  | 6 => pattern E at 6 in H
  | 7 => pattern E at 7 in H
  | 8 => pattern E at 8 in H
  | _ => fail "ltac_pattern: arity not supported"
  end.

(* ltac_set (x := E) at K is the same as set (x := E) at K except that K is a Coq number (nat or Z) rather than a Ltac integer. *)

Tactic Notation "ltac_set" "(" ident(X) ":=" constr(E) ")" "at" constr(K) :=
  match number_to_nat K with
  | 1%nat => set (X := E) at 1
  | 2%nat => set (X := E) at 2
  | 3%nat => set (X := E) at 3
  | 4%nat => set (X := E) at 4
  | 5%nat => set (X := E) at 5
  | 6%nat => set (X := E) at 6
  | 7%nat => set (X := E) at 7
  | 8%nat => set (X := E) at 8
  | 9%nat => set (X := E) at 9
  | 10%nat => set (X := E) at 10
  | 11%nat => set (X := E) at 11
  | 12%nat => set (X := E) at 12
  | 13%nat => set (X := E) at 13
  | _ => fail "ltac_set: arity not supported"
  end.



(* タクティックをテストする *)

(* show tac はタクティックtacを実行し、その結果を表示します。 *)
Tactic Notation "show" tactic(tac) :=
  let R := tac in pose R.

(* dup N は現在のゴールのN個のコピーを作ります。 これは、タクティックのふるまいを示す例を作るのに便利です。 dupは dup 2 の略記法です。 *)
Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match number_to_nat N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.
Tactic Notation "dup" :=
  dup 2.


Ltac is_not_evar E :=
  first [ is_evar E; fail 1
        | idtac ].

(* is_evar_as_bool E evaluates to true if E is an evar and to false otherwise. *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).

(* ゴールにやり残しがないことのチェック *)
Ltac check_noevar M :=
  first [ has_evar M; fail 2 | idtac ].

Ltac check_noevar_hyp H :=
  let T := type of H in check_noevar T.

Ltac check_noevar_goal :=
  match goal with |- ?G => check_noevar G end.

(* Evarを導入する補助関数 *)

(* with_evar T (fun M => tac)はtacに与えたタクティック内で、新しいT型のEvarをMという変数名で使えるようにします。 *)

Ltac with_evar_base T cont :=
  let x := fresh "TEMP" in evar (x:T); cont x; subst x.

Tactic Notation "with_evar" constr(T) tactic(cont) :=
  with_evar_base T cont.

(* 仮定のタグ付け *)

(* get_last_hyp tt はコンテキストの一番下の最後の仮定を返す関数です。 仮定に付けられたデフォルトの名前を得るのに便利です。例えば: intro; let H := get_last_hyp tt in let H' := fresh "P" H in ... *)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

(* 仮定のタグ付けをさらに *)

(* ltac_tag_substは置換対象の等式である仮定にタグ付けするのに使われる特別なマーカです。 *)
Definition ltac_tag_subst (A:Type) (x:A) := x.

(* ltac_to_generalizeは一般化する仮定のための特別なマーカです。 *)
Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
  repeat match goal with
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
  let T := type of H in
  change T with (ltac_to_generalize T) in H.


(* 項を解体する *)

(* get_head E は項Eの冒頭の定数を返すタクティックです。 つまり、P x1 ... xN という形の項に適用されるとPを返します。 Eが適用の形ではないときには、Eを返します。 注意: このタクティックは、ゴールが積で、この関数の結果を使う処理がある場合にループすることがあります。 （訳注: このファイル中での積(product)は、直積のことではなく Coq のマニュアルの product のことです。 含意または全称限量のことを指します。） ） *)
Ltac get_head E :=
  match E with
  | ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ => constr:(P)
  | ?P _ _ _ => constr:(P)
  | ?P _ _ => constr:(P)
  | ?P _ => constr:(P)
  | ?P => constr:(P)
  end.

(* get_fun_arg E は適用項Eの分解をするタクティックです。 つまり、X1 ... XN という形の項に適用されると X1 .. X(N-1) と XN の対を返します。 *)
Ltac get_fun_arg E :=
  match E with
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6 X7,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4 X5,X))
  | ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3 X4,X))
  | ?X1 ?X2 ?X3 ?X => constr:((X1 X2 X3,X))
  | ?X1 ?X2 ?X => constr:((X1 X2,X))
  | ?X1 ?X => constr:((X1,X))
  end.


(* 出現場所でのアクションと出現場所以外でのアクション *)

(* ltac_action_at K of E do Tac はゴールにおけるEのK番目の出現を区別し、それを指定されたパターンPによって P E の形にセットしてタクティックTacを呼び、最後にPを unfold します。 構文 ltac_action_at K of E in H do Tac も可能です。 *)
Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "do" tactic(Tac) :=
  let p := fresh "TEMP" in ltac_pattern E at K;
  match goal with |- ?P _ => set (p:=P) end;
  Tac; unfold p; clear p.

Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "in" hyp(H) "do" tactic(Tac) :=
  let p := fresh "TEMP" in ltac_pattern E at K in H;
  match type of H with ?P _ => set (p:=P) in H end;
  Tac; unfold p in H; clear p.

(* protects E do Tac は式Eに一時的に名前を与えることで、タクティックTacの実行がEを変更しないようにします。 これは例えばsimplのアクションを制限するのに便利です。 *)
Tactic Notation "protects" constr(E) "do" tactic(Tac) :=
  
  let x := fresh "TEMP" in let H := fresh "TEMP" in
  set (X := E) in *; assert (H : X = E) by reflexivity;
  clearbody X; Tac; subst x.

Tactic Notation "protects" constr(E) "do" tactic(Tac) "/" :=
  protects E do Tac.


(* eqの別名 *)
(* eq'は帰納的定義の等式で使うためのeqの別名で、 これにより、inversionによって生成される等式と混ざるのを防ぐことができます。 *)

Definition eq' := @eq.

Hint Unfold eq'.

Notation "x '='' y" := (@eq' _ x y)
  (at level 70, y at next level).


(* intuitionのようにゴールを簡約するタクティック *)
Ltac jauto_set_hyps :=
  repeat match goal with H: ?T |- _ =>
    match T with
    | _ /\ _ => destruct H
    | exists a, _ => destruct H
    | _ => generalize H; clear H
    end
  end.

Ltac jauto_set_goal :=
  repeat match goal with
  | |- exists a, _ => esplit
  | |- _ /\ _ => split
  end.

Ltac jauto_set :=
  intros; jauto_set_hyps;
  intros; jauto_set_goal;
  unfold not in *.


(* 後方/前方連鎖 *)

(* 適用(Application) *)
Ltac old_refine f :=
  refine f.
(* rapplyはeapplyと同様のタクティックですが、refine タクティックに基づいている点が違います。 そしてこのために、（少なくとも理論的には）より強力です。 簡単に言うと、引数がマッチするために必要となる変換をその場で行うことができます。 また必要なときに存在変数を具体化できます。 *)

Tactic Notation "rapply" constr(t) :=
  first
  [ eexact (@t)
  | old_refine (@t)
  | old_refine (@t _)
  | old_refine (@t _ _)
  | old_refine (@t _ _ _)
  | old_refine (@t _ _ _ _)
  | old_refine (@t _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  | old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  ].

(* 自然数Nについて、タクティック applys_N T は applys T をより効果的に使う方法を提供します。 関数Tの引数の数(アリティ、arity)を明示的に指定することで、すべての可能なアリティを試してみることを避けます。 *)

Tactic Notation "rapply_0" constr(t) :=
  old_refine (@t).
Tactic Notation "rapply_1" constr(t) :=
  old_refine (@t _).
Tactic Notation "rapply_2" constr(t) :=
  old_refine (@t _ _).
Tactic Notation "rapply_3" constr(t) :=
  old_refine (@t _ _ _).
Tactic Notation "rapply_4" constr(t) :=
  old_refine (@t _ _ _ _).
Tactic Notation "rapply_5" constr(t) :=
  old_refine (@t _ _ _ _ _).
Tactic Notation "rapply_6" constr(t) :=
  old_refine (@t _ _ _ _ _ _).
Tactic Notation "rapply_7" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _).
Tactic Notation "rapply_8" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _).
Tactic Notation "rapply_9" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _ _).
Tactic Notation "rapply_10" constr(t) :=
  old_refine (@t _ _ _ _ _ _ _ _ _ _).

(* lets_base H E は仮定 H : T をコンテキストに追加します。 ここでTは項Eの型です。 もしHが導入パターンなら、パターンに従ってHを分解します。 *)

Ltac lets_base I E := generalize E; intros I.

(* applys_to H E は、仮定Hを、項EをHに適用した結果で置換することで、仮定の型を変換します。 直観的には、lets H: (E H) と同値です。 *)

Tactic Notation "applys_to" hyp(H) constr(E) :=
  let H' := fresh "TEMP" in rename H into H';
  (first [ lets_base H (E H')
         | lets_base H (E _ H')
         | lets_base H (E _ _ H')
         | lets_base H (E _ _ _ H')
         | lets_base H (E _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ _ H') ]
  ); clear H'.


Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
  applys_to H1 E; applys_to H2 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E; applys_to H4 E.

(* constructorsはconstructorまたはeconstructorを呼びます。 *)

Tactic Notation "constructors" :=
  first [ constructor | econstructor ]; unfold eq'.

(* 表明(Assertions) *)

(* asserts H: T は assert (H : T) の別構文です。 これは同様に導出パターンについてはたらきます。 例えば、次のように書くことができます: asserts \[x P\] (exists n, n = 3)、あるいは asserts \[H|H\] (n = 0 \/ n = 1)。 *)
Tactic Notation "asserts" simple_intropattern(I) ":" constr(T) :=
  let H := fresh "TEMP" in assert (H : T);
  [ | generalize H; clear H; intros I ].

(* asserts H1 .. HN: T は asserts \[H1 \[H2 \[.. HN\]\]\]: T の略記法です。 *)

Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) ":" constr(T) :=
  asserts [I1 I2]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
  asserts [I1 [I2 I3]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) ":" constr(T) :=
  asserts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
  asserts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) ":" constr(T) :=
  asserts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.

(* asserts: T は自動的に選択されたHについて asserts H: T をします。 *)

Tactic Notation "asserts" ":" constr(T) :=
  let H := fresh "TEMP" in asserts H : T.

(* cuts H: T は asserts H: T と同様ですが、生成される2つのサブゴールの順番が逆になる点が違います。 サブゴールTが二番目に来ます。 なお、cutと対照的に仮定を導入します。 *)

Tactic Notation "cuts" simple_intropattern(I) ":" constr(T) :=
  cut (T); [ intros I | idtac ].

(* cuts: T は自動的に選択されたHについて cuts H: T をします。 *)

Tactic Notation "cuts" ":" constr(T) :=
  let H := fresh "TEMP" in cuts H: T.

(* cuts H1 .. HN: T は cuts \[H1 \[H2 \[.. HN\]\]\]: T の略記法です。 *)

Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) ":" constr(T) :=
  cuts [I1 I2]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
  cuts [I1 [I2 I3]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) ":" constr(T) :=
  cuts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
  cuts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3)
 simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) ":" constr(T) :=
  cuts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.



(* 具体化と前方連鎖 *)

(* 具体化タクティックは補題E（その型は積）をある引数について具体化するために使います。 Eの型は含意と全称限量から成ります。 例えば forall x, P x -> forall y z, Q x y z -> R z です。 *)

(* 最初の可能性は引数を順番に与えることです。 最初にx、次にP xの証明、次にy... このやり方をとることは"Args"モードと呼ばれますが、すべての引数を与えることが必要です。 もしワイルドカード（__と書かれる）が与えられると、引数の場所に存在変数が導入されます。 *)
(* 補題の具体化するべき引数を与え、アンダースコアが入るべき場所をタクティックに自動的に発見させることはとても便利です。 アンダースコア引数 __ は次のように解釈されます: アンダースコアは引数をスキップしたいことを意味します。 ただしその引数の型は次に与えられる実際の引数（ここで「実際の」とはアンダースコアでないこと）と同じになります。 アンダースコアの後で実際の引数が与えられない場合、アンダースコアは最初の可能な引数に使われます。 *)
(* 一般構文は tactic (>> E1 .. EN) です。 ここでtacticはタクティック（いくつかの引数を伴うこともある）の名前で、Eiは引数です。 さらに、いくつかのタクティックは、5以下のNについて tactic (>> E1 .. EN) の略記法として構文 tactic E1 .. EN を使うことができます。 *)
(* 最後に、与えられた引数ENが三連アンダースコア ___ のときは、適切な数のワイルドカードのリストを与えるのと同値です。 これは、補題の残りのすべての引数が具体化されることを意味します。 この場合、帰結部の定義は展開されません。 *)


Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac build_app_alls t final :=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ => app_evar t A go
    | _ => final t
    end in
  go t.

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.


Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont' | fail 3 ]
             end
           | _ =>
             match T with
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first [ app_evar t U cont' | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.



(* 新バージョン：型クラスのサポート *)
Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac build_app_alls t final ::=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ =>
        first [ app_evar t A go
              | app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in
  go t.

Ltac build_app_hnts t vs final ::=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont'
                                       | fail 3 ]
             end
           | _ =>
             match T with
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first
                 [ app_typeclass t cont'
                 | app_evar t U cont'
                 | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first
                 [ app_typeclass t cont
                 | app_evar t A cont
                 | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.


Ltac build_app args final :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      fast_rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
  eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs =>
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end.

Ltac args_unfold_head_if_not_product_but_params args :=
  match args with
  | (boxer ?t)::(boxer ?v)::?vs =>
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.

(* lets H: (>> E0 E1 .. EN) は補題E0を各引数Ei（これはワイルドカード __ のこともあります）について具体化し、結果の項に名前Hを付けます。 Hは導出パターンか、導出パターンの列 I1 I2 IN か、空です。 構文 lets H: E0 E1 .. EN も可能です。 もし最後の引数ENが ___ （三連アンダースコア）ならば、Hのすべての引数が具体化されます。 *)

Ltac lets_build I Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in

  build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E) :=
  lets_build I E.
Tactic Notation "lets" ":" constr(E) :=
  let H := fresh in lets H: E.
Tactic Notation "lets" ":" constr(E0)
 constr(A1) :=
  lets: (>> E0 A1).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: (>> E0 A1 A2).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: (>> E0 A1 A2 A3).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  lets [I1 I2]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  lets [I1 [I2 I3]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  lets [I1 [I2 [I3 I4]]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  lets [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: (>> E0 A1 A2 A3).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) :=
  lets [I1 I2]: E0 A1.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets [I1 I2]: E0 A1 A2.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets [I1 I2]: E0 A1 A2 A3.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets [I1 I2]: E0 A1 A2 A3 A4.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets [I1 I2]: E0 A1 A2 A3 A4 A5.

(* forwards H: (>> E0 E1 .. EN) は forwards H: (>> E0 E1 .. EN ___) の略記法です。 各引数 Ei（E0 を除く）はワイルドカード __ でも構いません。 H は導入パターンか、導入パターンの列か、空です。 構文 forwards H: E0 E1 .. EN も可能です。 *)

Ltac forwards_build_app_arg Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product args in
  args.

Ltac forwards_then Ei cont :=
  let args := forwards_build_app_arg Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args cont.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(Ei) :=
  let args := forwards_build_app_arg Ei in
  lets I: args.

Tactic Notation "forwards" ":" constr(E) :=
  let H := fresh in forwards H: E.
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) :=
  forwards: (>> E0 A1).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: (>> E0 A1 A2).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: (>> E0 A1 A2 A3).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  forwards [I1 I2]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  forwards [I1 [I2 I3]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  forwards [I1 [I2 [I3 I4]]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  forwards [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: (>> E0 A1 A2).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: (>> E0 A1 A2 A3).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: (>> E0 A1 A2 A3 A4 A5).



Tactic Notation "forwards_nounfold" simple_intropattern(I) ":" constr(Ei) :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args ltac:(fun R => lets_base I R).

(* forwards_nounfold_then E ltac:(fun K => ..) is like forwards: E but it provides the resulting term to a continuation, under the name K. *)

Ltac forwards_nounfold_then Ei cont :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args cont.

(* applys (>> E0 E1 .. EN) は補題E0を各引数 Ei （ワイルドカード __ でも良い）について具体化し、その結果を、前述のapplysを使って現在のゴールに適用します。 applys E0 E1 E2 .. EN も可能です。 *)

Ltac applys_build Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R =>
   first [ apply R | eapply R | rapply R ]).

Ltac applys_base E :=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ rapply E | applys_build E ]
  end; fast_rm_inside E.

Tactic Notation "applys" constr(E) :=
  applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
  applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
  applys (>> E0 A1 A2).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys (>> E0 A1 A2 A3).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys (>> E0 A1 A2 A3 A4).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys (>> E0 A1 A2 A3 A4 A5).

(* fapplys (>> E0 E1 .. EN) は補題E0を各引数Eiについて具体化します。 引数が ___ のときは、すべての存在変数が明示的に具体化されます。 そして結果の項を現在のゴールに適用します。 fapplys E0 E1 E2 .. EN も可能です。 *)

Ltac fapplys_build Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R => apply R).

Tactic Notation "fapplys" constr(E0) :=
  match type of E0 with
  | list Boxer => fapplys_build E0
  | _ => fapplys_build (>> E0)
  end.
Tactic Notation "fapplys" constr(E0) constr(A1) :=
  fapplys (>> E0 A1).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) :=
  fapplys (>> E0 A1 A2).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  fapplys (>> E0 A1 A2 A3).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  fapplys (>> E0 A1 A2 A3 A4).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  fapplys (>> E0 A1 A2 A3 A4 A5).

(* specializes H (>> E1 E2 .. EN) は仮定Hを各引数Ei（ワイルドカード __ も可）について具体化します。 もし最後の引数ENが ___ （三連アンダースコア）ならば、Hのすべての引数が具体化されます。 *)

Ltac specializes_build H Ei :=
  let H' := fresh "TEMP" in rename H into H';
  let args := list_boxer_of Ei in
  let args := constr:((boxer H')::args) in
  let args := args_unfold_head_if_not_product args in
  build_app args ltac:(fun R => lets H: R);
  clear H'.

Ltac specializes_base H Ei :=
  specializes_build H Ei; fast_rm_inside Ei.

Tactic Notation "specializes" hyp(H) :=
  specializes_base H (___).
Tactic Notation "specializes" hyp(H) constr(A) :=
  specializes_base H A.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H (>> A1 A2).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H (>> A1 A2 A3).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H (>> A1 A2 A3 A4).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H (>> A1 A2 A3 A4 A5).

(* specializes_vars H is equivalent to specializes H __ .. __ with as many double underscore as the number of dependent arguments visible from the type of H. Note that no unfolding is currently being performed (this behavior might change in the future). The current implementation is restricted to the case where H is an existing hypothesis -- TODO: generalize. *)

Ltac specializes_var_base H :=
  match type of H with
  | ?P -> ?Q => fail 1
  | forall _:_, _ => specializes H __
  end.

Ltac specializes_vars_base H :=
  repeat (specializes_var_base H).

Tactic Notation "specializes_var" hyp(H) :=
  specializes_var_base H.

Tactic Notation "specializes_vars" hyp(H) :=
  specializes_vars_base H.



(* 適用(application)の実験的タクティック *)

(* fapplyはapplyのforwardsにもとづくバージョンです。 *)

Tactic Notation "fapply" constr(E) :=
  let H := fresh "TEMP" in forwards H: E;
  first [ apply H | eapply H | rapply H | hnf; apply H
        | hnf; eapply H | applys H ].

(* sapplyは"super apply"の意味です。 apply、eapply、applys、fapplyを試し、さらに最初にゴールの頭正規化(head-nomalize)をしようとします。 *)

Tactic Notation "sapply" constr(H) :=
  first [ apply H | eapply H | rapply H | applys H
        | hnf; apply H | hnf; eapply H | hnf; applys H
        | fapply H ].

(* 仮定を追加する *)

(* lets_simpl H: E は lets H: E と同様ですが、仮定 H について simplを呼ぶ点が違います。 lets_simpl: E という使い方もできます。 *)

Tactic Notation "lets_simpl" ident(H) ":" constr(E) :=
  lets H: E; try simpl in H.

Tactic Notation "lets_simpl" ":" constr(T) :=
  let H := fresh "TEMP" in lets_simpl H: T.

(* lets_hnf H: E は lets H: E と同様ですが、hnfを呼んで定義を頭正規形(head normal form)にする点が違います。 lets_hnf: E という使い方もできます。 *)

Tactic Notation "lets_hnf" ident(H) ":" constr(E) :=
  lets H: E; hnf in H.

Tactic Notation "lets_hnf" ":" constr(T) :=
  let H := fresh "TEMP" in lets_hnf H: T.

(* puts X: E は pose (X := E) と同義です。 別の構文として puts: E というものもあります。 *)

Tactic Notation "puts" ident(X) ":" constr(E) :=
  pose (X := E).
Tactic Notation "puts" ":" constr(E) :=
  let X := fresh "X" in pose (X := E).

(* トートロジーの適用 *)

(* Eが事実とするとき、logic Eは assert H:E; [tauto | eapply H; clear H] と同値です。 例えば連言（AND式） A /\ B を証明するとき、最初に A を示し、次に A -> B を示すのに、コマンド logic (foral A B, A -> (A -> B) -> A /\ B) を使うのが便利です。 *)

Ltac logic_base E cont :=
  assert (H:E); [ cont tt | eapply H; clear H ].

Tactic Notation "logic" constr(E) :=
  logic_base E ltac:(fun _ => tauto).

(* 等式を法とした適用 *)

(* タクティックequatesは P x y z の形のゴールを P x ?a z に置き換え、サブゴール ?a = y を作ります。 存在変数?aが導入されることで、もとのゴールに適用できなかった補題が適用できるようになることがあります。 例えば、forall n m, P n n m という形の補題です。 なぜなら、xとyは等しかったかもしれませんが、変換可能ではないからです。 *)
(* 使用法は equates i1 ... ik です。 ここで各インデックスは存在変数に置き換える引数の場所を、左端から数えたものです。 もし0が引数に与えられたら、ゴール全体が存在変数に置き換えられます。 *)

Section equatesLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall (P Q:Prop),
  P -> P = Q -> Q.
Proof. intros. subst. auto. Qed.

Lemma equates_1 :
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof. intros. subst. auto. Qed.

Lemma equates_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof. intros. subst. auto. Qed.

Lemma equates_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof. intros. subst. auto. Qed.

End equatesLemma.

Ltac equates_lemma n :=
  match number_to_nat n with
  | 0 => constr:(equates_0)
  | 1 => constr:(equates_1)
  | 2 => constr:(equates_2)
  | 3 => constr:(equates_3)
  | 4 => constr:(equates_4)
  | 5 => constr:(equates_5)
  | 6 => constr:(equates_6)
  end.

Ltac equates_one n :=
  let L := equates_lemma n in
  eapply L.

Ltac equates_several E cont :=
  let all_pos := match type of E with
    | List.list Boxer => constr:(E)
    | _ => constr:((boxer E)::nil)
    end in
  let rec go pos :=
     match pos with
     | nil => cont tt
     | (boxer ?n)::?pos' => equates_one n; [ instantiate; go pos' | ]
     end in
  go all_pos.

Tactic Notation "equates" constr(E) :=
  equates_several E ltac:(fun _ => idtac).
Tactic Notation "equates" constr(n1) constr(n2) :=
  equates (>> n1 n2).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) :=
  equates (>> n1 n2 n3).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates (>> n1 n2 n3 n4).

(* applys_eq H i1 .. iK は equates i1 .. iK の後最初のサブゴールに対して apply H を行ったのと同じです。 *)

Tactic Notation "applys_eq" constr(H) constr(E) :=
  equates_several E ltac:(fun _ => sapply H).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) :=
  applys_eq H (>> n1 n2).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H (>> n1 n2 n3).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H (>> n1 n2 n3 n4).

(* Absurd Goals *)

(* false_goalは任意のゴールをFalseで置換します。 タクティックfalse（後述）と対照的に、特に何もしようとしません。 *)

Tactic Notation "false_goal" :=
  elimtype False.

(* false_postはFalseの形のゴールを証明するときに背後で使われるタクティックです。 デフォルトの実装ではコンテキストがFalseか、またはC x1 .. xN = D y1 .. yMという形の仮定を含む場合、あるいはcongruenceタクティックがあるxについて x <> x の証明を見つけた場合にゴールを証明します。 *)

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(* falseは任意のゴールをFalseに置換し、false_postを呼びます。 *)

Tactic Notation "false" :=
  false_goal; try false_post.

(* tryfalseは矛盾によってゴールを解こうとします。 そして解けなかった場合にはゴールを変更しないまま残します。 これは try solve \[ false \] と同値です。 *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(* false E tries to exploit lemma E to prove the goal false. false E1 .. EN is equivalent to false (>> E1 .. EN), which tries to apply applys (>> E1 .. EN) and if it does not work then tries forwards H: (>> E1 .. EN) followed with false *)

Ltac false_then E cont :=
  false_goal; first
  [ applys E; instantiate
  | forwards_then E ltac:(fun M =>
      pose M; jauto_set_hyps; intros; false) ];
  cont tt.

Tactic Notation "false" constr(E) :=
  false_then E ltac:(fun _ => idtac).
Tactic Notation "false" constr(E) constr(E1) :=
  false (>> E E1).
Tactic Notation "false" constr(E) constr(E1) constr(E2) :=
  false (>> E E1 E2).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) :=
  false (>> E E1 E2 E3).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false (>> E E1 E2 E3 E4).

(* false_invert Hは、inversion Hかfalseによって不合理(absurd)であると示せるときに証明します。 *)

Ltac false_invert_for H :=
  let M := fresh "TEMP" in pose (M := H); inversion H; false.

Tactic Notation "false_invert" constr(H) :=
  try solve [ false_invert_for H | false ].

(* false_invertは、コンテキストに少なくとも1つの仮定H（またはゴールの先頭に全称限量でつながった仮定）があって、inversion HによってHが不合理(absurd)であることが証明されるとき、任意のゴールを証明します。 *)

Ltac false_invert_iter :=
  match goal with H:_ |- _ =>
    solve [ inversion H; false
          | clear H; false_invert_iter
          | fail 2 ] end.

Tactic Notation "false_invert" :=
  intros; solve [ false_invert_iter | false ].

(* tryfalse_invert Hとtryfalse_invertは上と同様ですが、失敗するときは、ゴールを変えずに残します。 *)

Tactic Notation "tryfalse_invert" constr(H) :=
  try (false_invert H).

Tactic Notation "tryfalse_invert" :=
  try false_invert.

(* false_neq_self_hyp proves any goal if the context contains an hypothesis of the form E <> E. It is a restricted and optimized version of false. It is intended to be used by other tactics only. *)

Ltac false_neq_self_hyp :=
  match goal with H: ?x <> ?x |- _ =>
    false_goal; apply H; reflexivity end.



(* 導入と一般化 *)

(* 導入(Introduction) 

introvは依存性のない(non-dependent)仮定のみを指名するのに使います。
introvが forall x, H という形のゴールに対して呼ばれると、ゴールの頭部のforallに限量されたすべての変数が導入されます。 しかし、P -> Q のような矢印コンストラクタの前の仮定は導入されません。
introvが forall x, H でも P -> Q でもない形のゴールに対して呼ばれると、forall x, H または P -> Q. の形になるまで、定義を展開(unfold)します。 展開してもゴールが上記の形にならなかったとき、タクティックintrovは何もしません。
*)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.


Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

  Ltac introv_noarg_not_optimized :=
    intro; match goal with H:_|-_ => revert H end; introv_rec.


Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.


Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* intros_all は intro を可能な限り繰り返します。 introsと対照的に、定義を途中で unfold します。 否定の定義も unfold するので、intros_allを forall x, P x -> ~Q の形のゴールに適用すると、 x、P x、Qを導入し、ゴールにFalseを残すことに注意します。 *)

Tactic Notation "intros_all" :=
  repeat intro.

(* intros_hnf は仮定を導入し、頭正規形にします。 *)

Tactic Notation "intro_hnf" :=
  intro; match goal with H: _ |- _ => hnf in H end.

(* Introduction using => and =>> *)


Ltac ltac_intros_post := idtac.

Tactic Notation "=>" :=
  intros.
Tactic Notation "=>" simple_intropattern(I1) :=
  intros I1.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2) :=
  intros I1 I2.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  intros I1 I2 I3.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  intros I1 I2 I3 I4.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  intros I1 I2 I3 I4 I5.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.


Ltac intro_nondeps_aux_special_intro G :=
  fail.

Ltac intro_nondeps_aux is_already_hnf :=
  match goal with
  | |- (?P -> ?Q) => idtac
  | |- ?G -> _ => intro_nondeps_aux_special_intro G;
                  intro; intro_nondeps_aux true
  | |- (forall _,_) => intros ?; intro_nondeps_aux true
  | |- _ =>
     match is_already_hnf with
     | true => idtac
     | false => hnf; intro_nondeps_aux true
     end
  end.

Ltac intro_nondeps tt := intro_nondeps_aux false.

Tactic Notation "=>>" :=
  intro_nondeps tt.
Tactic Notation "=>>" simple_intropattern(I1) :=
  =>>; intros I1.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2) :=
  =>>; intros I1 I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  =>>; intros I1 I2 I3.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  =>>; intros I1 I2 I3 I4.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  =>>; intros I1 I2 I3 I4 I5.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  =>>; intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  =>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.



(* 一般化(Generalization) *)

(* gen X1 .. XN は、変数 XN...X1 に対して generalize dependent を呼ぶことの略記法です。 なお、generalizeタクティックの慣習にならって、変数は逆順で一般化(generalize)されます。 つまり、X1が結果のゴールの最初の束縛変数になるということです。 *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) :=
  gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) :=
  gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) :=
  gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) :=
  gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
 ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
  gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.

(* generalizes X は generalize X; clear X の略記法です。 これは依存性をサポートしないため、タクティック gen X より弱いです。 主にタクティック記述に利用することを意図したものです。 *)

Tactic Notation "generalizes" hyp(X) :=
  generalize X; clear X.
Tactic Notation "generalizes" hyp(X1) hyp(X2) :=
  generalizes X1; generalizes X2.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) :=
  generalizes X1 X2; generalizes X3.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) hyp(X4) :=
  generalizes X1 X2 X3; generalizes X4.



(* 名前付け(Naming) *)

(* sets X: E は set (X := E) in * と同じです。つまり、 Eのすべての出現を新しいメタ変数Xに置換します。Xの定義はEになります。 *)

Tactic Notation "sets" ident(X) ":" constr(E) :=
  set (X := E) in *.

(* def_to_eq E X H は、X := E がローカルな定義のとき適用できます。 適用されると仮定 H: X = E が追加され、Xの定義がクリアされます。 def_to_eq_sym も同様ですが、違いは、この場合、等式 H: E = X が生成されることです。 *)

Ltac def_to_eq X HX E :=
  assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

(* set_eq X H: E は新しい名前Xについての等式 H: X = E を生成し、現在のゴールの E を X で置換します。 構文 set_eq X: E および set_eq: E も可能です。 同様に、 set_eq <- X H: E は等式 H: E = X を生成します。 *)
(* sets_eq X HX: E も同様ですが、ゴールのすべてのEをXで置換します。 sets_eq X HX: E in H は H 内を置換します。 set_eq X HX: E in |- は何も置換しません。 *)

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq X HX: E.
Tactic Notation "set_eq" ":" constr(E) :=
  let X := fresh "X" in set_eq X: E.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq <- X HX: E.
Tactic Notation "set_eq" "<-" ":" constr(E) :=
  let X := fresh "X" in set_eq <- X: E.

Tactic Notation "sets_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E) in *; def_to_eq X HX E.
Tactic Notation "sets_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in sets_eq X HX: E.
Tactic Notation "sets_eq" ":" constr(E) :=
  let X := fresh "X" in sets_eq X: E.

Tactic Notation "sets_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
  set (X := E) in *; def_to_eq_sym X HX E.
Tactic Notation "sets_eq" "<-" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in sets_eq <- X HX: E.
Tactic Notation "sets_eq" "<-" ":" constr(E) :=
  let X := fresh "X" in sets_eq <- X: E.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
  set (X := E) in H; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" hyp(H) :=
  let HX := fresh "EQ" X in set_eq X HX: E in H.
Tactic Notation "set_eq" ":" constr(E) "in" hyp(H) :=
  let X := fresh "X" in set_eq X: E in H.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
  set (X := E) in H; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" hyp(H) :=
  let HX := fresh "EQ" X in set_eq <- X HX: E in H.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" hyp(H) :=
  let X := fresh "X" in set_eq <- X: E in H.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
  set (X := E) in |-; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" "|-" :=
  let HX := fresh "EQ" X in set_eq X HX: E in |-.
Tactic Notation "set_eq" ":" constr(E) "in" "|-" :=
  let X := fresh "X" in set_eq X: E in |-.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
  set (X := E) in |-; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" "|-" :=
  let HX := fresh "EQ" X in set_eq <- X HX: E in |-.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" "|-" :=
  let X := fresh "X" in set_eq <- X: E in |-.

(* inductionタクティックは通常、情報を失いますが、gen_eq X: E は、 inductionのこの限界を避けて等式を導入することを目的としたタクティックです。 gen_eq E as X 項Eのすべての出現を新しい変数Xで置換し、等式 X = E を現在の結論の追加の仮定とします。 言い換えると、結論Cは (X = E) -> C になります。 gen_eq: E および gen_eq: E as X も可能です。 *)

Tactic Notation "gen_eq" ident(X) ":" constr(E) :=
  let EQ := fresh "EQ" X in sets_eq X EQ: E; revert EQ.
Tactic Notation "gen_eq" ":" constr(E) :=
  let X := fresh "X" in gen_eq X: E.
Tactic Notation "gen_eq" ":" constr(E) "as" ident(X) :=
  gen_eq X: E.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
  ident(X2) ":" constr(E2) :=
  gen_eq X2: E2; gen_eq X1: E1.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
  ident(X2) ":" constr(E2) "," ident(X3) ":" constr(E3) :=
  gen_eq X3: E3; gen_eq X2: E2; gen_eq X1: E1.

(* sets_let X はゴールの最初の let-式を見つけ出し、その本体をXと名付けます。 sets_eq_let X も同様ですが、明示的に等式を作ることが違います。 タクティック sets_let X in H と sets_eq_let X in H により特定の仮定を指定することができます（デフォルトでは、letを含む最初のものが対象となります）。 *)
(* 既知の限界: ltac で項内の複数の let-in コンストラクタに対する名前付けのサポートをすることは不可能なようです。 *)

Ltac sets_let_base tac :=
  match goal with
  | |- context[let _ := ?E in _] => tac E; cbv zeta
  | H: context[let _ := ?E in _] |- _ => tac E; cbv zeta in H
  end.

Ltac sets_let_in_base H tac :=
  match type of H with context[let _ := ?E in _] =>
    tac E; cbv zeta in H end.

Tactic Notation "sets_let" ident(X) :=
  sets_let_base ltac:(fun E => sets X: E).
Tactic Notation "sets_let" ident(X) "in" hyp(H) :=
  sets_let_in_base H ltac:(fun E => sets X: E).
Tactic Notation "sets_eq_let" ident(X) :=
  sets_let_base ltac:(fun E => sets_eq X: E).
Tactic Notation "sets_eq_let" ident(X) "in" hyp(H) :=
  sets_let_in_base H ltac:(fun E => sets_eq X: E).



(* 書き換え(Rewriting) *)
(* rewrites E is similar to rewrite except that it supports the rm directives to clear hypotheses on the fly, and that it supports a list of arguments in the form rewrites (>> E1 E2 E3) to indicate that forwards should be invoked first before rewrites is called. *)

Ltac rewrites_base E cont :=
  match type of E with
  | List.list Boxer => forwards_then E cont
  | _ => cont E; fast_rm_inside E
  end.

Tactic Notation "rewrites" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite M ).
Tactic Notation "rewrites" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite M in H).
Tactic Notation "rewrites" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite M in *).
Tactic Notation "rewrites" "<-" constr(E) :=
  rewrites_base E ltac:(fun M => rewrite <- M ).
Tactic Notation "rewrites" "<-" constr(E) "in" hyp(H) :=
  rewrites_base E ltac:(fun M => rewrite <- M in H).
Tactic Notation "rewrites" "<-" constr(E) "in" "*" :=
  rewrites_base E ltac:(fun M => rewrite <- M in *).


(* rewrite_all E は rewrite E を可能な限り繰り返します。 注意: このタクティックは簡単に無限ループに陥ります。 右から左への書き換えや仮定への適用の構文はrewriteと同様です。 *)

Tactic Notation "rewrite_all" constr(E) :=
  repeat rewrite E.
Tactic Notation "rewrite_all" "<-" constr(E) :=
  repeat rewrite <- E.
Tactic Notation "rewrite_all" constr(E) "in" ident(H) :=
  repeat rewrite E in H.
Tactic Notation "rewrite_all" "<-" constr(E) "in" ident(H) :=
  repeat rewrite <- E in H.
Tactic Notation "rewrite_all" constr(E) "in" "*" :=
  repeat rewrite E in *.
Tactic Notation "rewrite_all" "<-" constr(E) "in" "*" :=
  repeat rewrite <- E in *.

(* asserts_rewrite E は等式Eの成立を主張し（対応するサブゴールを生成します）、現在のゴールの対応する部分をすぐに書き換えます。 これによって、等式に名前を付けて後でそれを消すことを避けることができます。 右から左への書き換えや仮定への適用の構文はrewriteと同様です。 なお、タクティックreplacesも同様のはたらきをします。 *)

Ltac asserts_rewrite_tactic E action :=
  let EQ := fresh "TEMP" in (assert (EQ : E);
  [ idtac | action EQ; clear EQ ]).

Tactic Notation "asserts_rewrite" constr(E) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "asserts_rewrite" "<-" constr(E) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "asserts_rewrite" constr(E) "in" hyp(H) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).
Tactic Notation "asserts_rewrite" constr(E) "in" "*" :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in *).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" "*" :=
  asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in *).

(* cuts_rewrite E は asserts_rewrite E と同様ですが、サブゴールの順番が変わります。 *)

Ltac cuts_rewrite_tactic E action :=
  let EQ := fresh "TEMP" in (cuts EQ: E;
  [ action EQ; clear EQ | idtac ]).

Tactic Notation "cuts_rewrite" constr(E) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "cuts_rewrite" "<-" constr(E) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "cuts_rewrite" constr(E) "in" hyp(H) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "cuts_rewrite" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).

(* rewrite_except H EQ は、仮定H以外のすべての部分で等式 EQ を書き換えます。 他のタクティックにおいて便利です。 *)

Ltac rewrite_except H EQ :=
  let K := fresh "TEMP" in let T := type of H in
  set (K := T) in H;
  rewrite EQ in *; unfold K in H; clear K.

(* rewrites E at K は E が T1 = T2 の形のときに、現在のゴールにおける T1 の K 番目の出現を T2 に書き換えます。 構文 rewrites <- E at K と rewrites E at K in H も可能です。 *)

Tactic Notation "rewrites" constr(E) "at" constr(K) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T1 do (rewrites E) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T2 do (rewrites <- E) end.
Tactic Notation "rewrites" constr(E) "at" constr(K) "in" hyp(H) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T1 in H do (rewrites E in H) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) "in" hyp(H) :=
  match type of E with ?T1 = ?T2 =>
    ltac_action_at K of T2 in H do (rewrites <- E in H) end.


(* 置き換え(Replace) *)

(* replaces E with F は replace E with F と同様ですが、等式 E = F が最初のサブゴールとして生成される点が違います。 構文 replaces E with F in H も可能です。 replaceと対照的に、replacesはassumptionによって等式を解こうとはしません。 なお、replaces E with F は asserts_rewrite (E = F) と同様です。 *)

Tactic Notation "replaces" constr(E) "with" constr(F) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F; clear T ].

Tactic Notation "replaces" constr(E) "with" constr(F) "in" hyp(H) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F in H; clear T ].

(* replaces E at K with F は現在のゴールの EのK番目の出現をFに置き換えます。 構文 replaces E at K with F in H も可能です。 *)

Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K; clear T ].

Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) "in" hyp(H) :=
  let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K in H; clear T ].

(* Change 
changes is like change except that it does not silently fail to perform its task. (Note that, changes is implemented using rewrite, meaning that it might perform additional beta-reductions compared with the original change tactic.*)

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" hyp(H) :=
  asserts_rewrite (E1 = E2) in H; [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) :=
  asserts_rewrite (E1 = E2); [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" "*" :=
  asserts_rewrite (E1 = E2) in *; [ reflexivity | ].


(* 名前変え(リネーム、Renaming) *)

(* renames X1 to Y1, ..., XN to YN はリネーム操作 rename Xi into Yi の列の略記法です。 *)

Tactic Notation "renames" ident(X1) "to" ident(Y1) :=
  rename X1 into Y1.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) :=
  renames X1 to Y1; renames X2 to Y2.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
 ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
 ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) ","
 ident(X6) "to" ident(Y6) :=
  renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5, X6 to Y6.


(* 定義の展開(Unfolding) *)

(* unfolds はゴールの先頭の定義を展開します。 つまり、ゴールが P x1 ... xN の形のとき、unfold P を呼びます。 ゴールが等式のとき、左辺の先頭の定数を展開しようとします。 それができないとき、右辺について試みます。 ゴールが積のとき、最初にintrosを呼びます。 注意：このタクティックはLibReflectの中で上書きされます。 *)

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.

(* unfolds in H は仮定Hの冒頭の定義を展開します。 つまりHが型 P x1 ... xN ならば、unfold P in H を呼びます。 *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H.

(* unfolds in H1,H2,..,HN allows unfolding the head constant in several hypotheses at once. *)

Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
  unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
  unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
  unfolds in H1; unfolds in H2 H3 H4 H5.

(* unfolds P1,..,PN は unfold P1,..,PN in * の略記法です。 *)

Tactic Notation "unfolds" constr(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2) :=
  unfold F1,F2 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) :=
  unfold F1,F2,F3 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) :=
  unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5) "," constr(F6) :=
  unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) :=
  unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) "," constr(F5)
 "," constr(F6) "," constr(F7) "," constr(F8) :=
  unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.

(* folds P1,..,PN は fold P1 in *; ..; fold PN in * の略記法です。 *)

Tactic Notation "folds" constr(H) :=
  fold H in *.
Tactic Notation "folds" constr(H1) "," constr(H2) :=
  folds H1; folds H2.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3) :=
  folds H1; folds H2; folds H3.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) :=
  folds H1; folds H2; folds H3; folds H4.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
 "," constr(H4) "," constr(H5) :=
  folds H1; folds H2; folds H3; folds H4; folds H5.


(* 単純化(Simplification) *)

(* simpls は simpl in * の略記法です。 *)

Tactic Notation "simpls" :=
  simpl in *.

(* simpls P1,..,PN は simpl P1 in *; ..; simpl PN in * の略記法です。 *)

Tactic Notation "simpls" constr(F1) :=
  simpl F1 in *.
Tactic Notation "simpls" constr(F1) "," constr(F2) :=
  simpls F1; simpls F2.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) :=
  simpls F1; simpls F2; simpls F3.
Tactic Notation "simpls" constr(F1) "," constr(F2)
 "," constr(F3) "," constr(F4) :=
  simpls F1; simpls F2; simpls F3; simpls F4.

(* unsimpl E はXのすべての出現をEに置き換えます。 ここでXはEにsimplを適用すると得られるであろう結果です。 simplが単純化し過ぎたときに undo をするのに便利です。 *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(* unsimpl E in H は unsimpl E と同様ですが、 特定の仮定Hの中だけに適用されます。 *)

Tactic Notation "unsimpl" constr(E) "in" hyp(H) :=
  let F := (eval simpl in E) in change F with E in H.

(* unsimpl E in * は unsimpl E を可能なすべての場所に適用します。 unsimpls E はその別名です。 *)

Tactic Notation "unsimpl" constr(E) "in" "*" :=
  let F := (eval simpl in E) in change F with E in *.
Tactic Notation "unsimpls" constr(E) :=
  unsimpl E in *.

(* nosimpl t はCoqの項tについて、ある形の単純化が適用されないようにします。 このからくりの詳細は Gonthier の仕事を見てください。 *)

Notation "'nosimpl' t" := (match tt with tt => t end)
  (at level 10).



(* 簡約(Reduction) *)

Tactic Notation "hnfs" := hnf in *.


(* 置換(Substitution) *)

(* substsはsubstは同様にはたらきますが、違いは、substsはコンテキストに循環する等式があっても失敗しないことです。 *)

Tactic Notation "substs" :=
  repeat (match goal with H: ?x = ?y |- _ =>
            first [ subst x | subst y ] end).

(* 次はsubsts belowの実装です。 これは、証明コンテキストの指定されたポジションより下のすべての仮定にsubstを呼ぶことを可能にするものです。 *)

Ltac substs_below limit :=
  match goal with H: ?T |- _ =>
  match T with
  | limit => idtac
  | ?x = ?y =>
    first [ subst x; substs_below limit
          | subst y; substs_below limit
          | generalizes H; substs_below limit; intro ]
  end end.

(* substs below body E は、コンテキストの中で本体がEである最初の仮定より下に現れるすべての等式にsubstを適用します。 もしコンテキストにそのような仮定がないときには、substと同値です。 例えば、Hが仮定のとき、substs below H は仮定Hより下のすべての等式を置換します。 *)

Tactic Notation "substs" "below" "body" constr(M) :=
  substs_below M.

(* substs below H はコンテキストでHで指定された仮定より下に現れるすべての等式にsubstを適用します。 なお、現在の実装は技術的に間違いがあります。 それは、同じ本体を持つ違う仮定を区別できないからです。 *)

Tactic Notation "substs" "below" hyp(H) :=
  match type of H with ?M => substs below body M end.

(* subst_hyp H substitutes the equality contained in the first hypothesis from the context. *)

Ltac intro_subst_hyp := fail.
(* subst_hyp H はHに含まれる等式を置換します。 *)

Ltac subst_hyp_base H :=
  match type of H with
  | (_,_,_,_,_) = (_,_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
  | (_,_,_,_) = (_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
  | (_,_,_) = (_,_,_) => injection H; clear H; do 3 intro_subst_hyp
  | (_,_) = (_,_) => injection H; clear H; do 2 intro_subst_hyp
  | ?x = ?x => clear H
  | ?x = ?y => first [ subst x | subst y ]
  end.

Tactic Notation "subst_hyp" hyp(H) := subst_hyp_base H.

Ltac intro_subst_hyp ::=
  let H := fresh "TEMP" in intros H; subst_hyp H.

(* intro_substは intro H; subst_hyp H の略記法です。 現在のゴールの先頭の等式を導入し置換します。 *)

Tactic Notation "intro_subst" :=
  let H := fresh "TEMP" in intros H; subst_hyp H.

(* subst_localはコンテキストのすべてのローカル定義を置換します。 *)

Ltac subst_local :=
  repeat match goal with H:=_ |- _ => subst H end.

(* subst_eq E は等式 x = t をとり、ゴールのすべての場所でxをtに置き換えます。 *)

Ltac subst_eq_base E :=
  let H := fresh "TEMP" in lets H: E; subst_hyp H.

Tactic Notation "subst_eq" constr(E) :=
  subst_eq_base E.



(* proof irrelevance を扱うタクティック *)

Require Import ProofIrrelevance.

(* pi_rewrite E は型PropのEを新しい単一化変数に置き換えます。 これから、proof irrelevance を利用する現実的な方法になります。 明示的に rewrite (proof_irrelevance E E') と書く必要はありません。 E'が大きな式であるとき特に有効です。 （訳注: Proof Irrelevance は、言ってみれば、同じ命題の証明を同一視することです。） *)

Ltac pi_rewrite_base E rewrite_tac :=
  let E' := fresh "TEMP" in let T := type of E in evar (E':T);
  rewrite_tac (@proof_irrelevance _ E E'); subst E'.

Tactic Notation "pi_rewrite" constr(E) :=
  pi_rewrite_base E ltac:(fun X => rewrite X).
Tactic Notation "pi_rewrite" constr(E) "in" hyp(H) :=
  pi_rewrite_base E ltac:(fun X => rewrite X in H).

(* 等式を証明する *)
(* Note: current implementation only supports up to arity 5 *)

(* fequalはf_equalの変種で、n個組の間の等式をよりうまく扱います。 *)

Ltac fequal_base :=
  let go := f_equal; [ fequal_base | ] in
  match goal with
  | |- (_,_,_) = (_,_,_) => go
  | |- (_,_,_,_) = (_,_,_,_) => go
  | |- (_,_,_,_,_) = (_,_,_,_,_) => go
  | |- (_,_,_,_,_,_) = (_,_,_,_,_,_) => go
  | |- _ => f_equal
  end.

Tactic Notation "fequal" :=
  fequal_base.

(* fequalsはfequalと同様ですが、違う点は、すべての簡単なサブゴールをreflexivityとcongruence（および proof-irrelevance 原理）を使って解こうとします。 fequalsは f x1 .. xN = f y1 .. yN という形のゴールに適用することができ、 xi = yi という形のサブゴールをいくつか生成します。 *)

Ltac fequal_post :=
  first [ reflexivity | congruence | apply proof_irrelevance | idtac ].

Tactic Notation "fequals" :=
  fequal; fequal_post.

(* fequals_recはfequalsを再帰的に呼び出します。 これは repeat (progress fequals) と同値です。 *)

Tactic Notation "fequals_rec" :=
  repeat (progress fequals).



(* 反転(Inversion) *)

(* 基本反転(Basic Inversion) *)

(* invert keep H は inversion H と同様ですが、得られた事実をすべてゴールに置く点が違います。 キーワードkeepは仮定Hを除去しないでおくことを意味します。 *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

(* invert keep H as X1 .. XN は inversion H as ... と同様ですが、明示的に名前を付けなければならないのが変数ではない仮定だけである点が違います。 これは、introvが仮定だけに名前を付けるのと同じ流儀です。 *)

Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) :=
  invert keep H; introv I1.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert keep H; introv I1 I2.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert keep H; introv I1 I2 I3.

(* invert H は inversion H と同様ですが、得られた事実をすべてゴールに置き、仮定Hをクリアする点が違います。 言い換えると、これは invert keep H; clear H と同値です。 *)

Tactic Notation "invert" hyp(H) :=
  invert keep H; clear H.

(* invert H as X1 .. XN は invert keep H as X1 .. XN と同様ですが、仮定Hもクリアする点が違います。 *)

Tactic Notation "invert_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => invert keep H as I1).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => invert keep H as I1 I2).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => invert keep H as I1 I2 I3).

(* 置換(substitution)を伴う反転(inversion) *)

(* ここで定義する反転タクティックは、inversionによって生成される依存等式を proof irrelevance を使って除去できます。 *)


Axiom inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
  existT P p x = existT P p y -> x = y.

Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 :=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go i1 i2 i3 i4 i5 i6
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go i1 i2 i3 i4 i5 i6
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

(* inverts keep H は invert keep H と同様ですが、 inversion によって生成されたすべての等式にsubstを適用する点が違います。 *)

Tactic Notation "inverts" "keep" hyp(H) :=
  inverts_tactic H ltac:(intro) ltac:(intro) ltac:(intro)
                   ltac:(intro) ltac:(intro) ltac:(intro).

(* inverts keep H as X1 .. XN は invert keep H as X1 .. XN と同様ですが、inversion によって生成されたすべての等式にsubstを適用する点が違います。 *)

Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) :=
  inverts_tactic H ltac:(intros I1)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intros I6).

(* inverts H は inverts keep H と同様ですが、仮定Hをクリアする点が違います。 *)

Tactic Notation "inverts" hyp(H) :=
  inverts keep H; try clear H.

(* inverts H as X1 .. XN は inverts keep H as X1 .. XN と同様ですが、仮定Hもクリアする点が違います。 *)

Tactic Notation "inverts_tactic" hyp(H) tactic(tac) :=
  let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => inverts keep H as I1).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  invert_tactic H (fun H => inverts keep H as I1 I2).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5 I6).

(* inverts H as は仮定Hに対して inversion を行い、生成された等式を置換し、そして、別の新しく生成された仮定を、ユーザが明示的に名前を付けられるようにゴールに置きます。 inverts keep H as は同様ですが、Hをクリアしない点が違います。 TODO: 上述のinvertsをこれを使って再実装すること *)

Ltac inverts_as_tactic H :=
  let rec go tt :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh "TEMP" in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) =>
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H;
  generalize ltac_mark; gen_until_mark;
  go tt; gen_to_generalize; unfolds ltac_to_generalize;
  unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) "as" :=
  inverts_as_tactic H.

Tactic Notation "inverts" hyp(H) "as" :=
  inverts_as_tactic H; clear H.

Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7)
 simple_intropattern(I8) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7 I8.

(* lets_inverts E as I1 .. IN is intuitively equivalent to inverts E, with the difference that it applies to any expression and not just to the name of an hypothesis. *)

Ltac lets_inverts_base E cont :=
  let H := fresh "TEMP" in lets H: E; try cont H.

Tactic Notation "lets_inverts" constr(E) :=
  lets_inverts_base E ltac:(fun H => inverts H).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3 I4).


(* 置換を伴う注入(Injection) *)

(* injectsの背後の実装 *)

Ltac injects_tactic H :=
  let rec go _ :=
    match goal with
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y | idtac ];
                           go tt
    end in
  generalize ltac_mark; injection H; go tt.

(* injects keep H は C a1 .. aN = C b1 .. bN の形の仮定Hをとって、生成されたすべての等式 ai = bi を置換します。 *)

Tactic Notation "injects" "keep" hyp(H) :=
  injects_tactic H.

(* injects H は injects keep H と同様ですが、仮定Hをクリアする点が違います。 *)

Tactic Notation "injects" hyp(H) :=
  injects_tactic H; clear H.

(* inject H as X1 .. XN はinjectionに続けて intros X1 .. XN を行うのと同様です。 *)

Tactic Notation "inject" hyp(H) :=
  injection H.
Tactic Notation "inject" hyp(H) "as" ident(X1) :=
  injection H; intros X1.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) :=
  injection H; intros X1 X2.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3) :=
  injection H; intros X1 X2 X3.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) :=
  injection H; intros X1 X2 X3 X4.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
 ident(X4) ident(X5) :=
  injection H; intros X1 X2 X3 X4 X5.



(* 置換を伴う反転と注入 -- おおざっぱな実装 *)

(* この節で提供するタクティックinversionsおよびinjectionsはそれぞれinvertsおよびinjectsと同様ですが、 置換する等式は、新しく生成されたものに限らずすべてのコンテキストの等式である点が違います。 対応する実装は、より簡単になっています。 *)
(* 非推奨：これらはもう使ってはいけません。 *)

(* inversions keep H は inversions H と同様ですが、仮定Hをクリアしません。 *)

Tactic Notation "inversions" "keep" hyp(H) :=
  inversion H; subst.

(* inversions H は inversion H に続いて subst と clear H を行うことの略記法です。 これは inverts H のおおざっぱな実装で、証明コンテキストが既に等式を含んでいるときには、問題のある振る舞いをします。 これは、より良い実装（inverts H）が遅すぎる場合のために用意してあります。 *)

Tactic Notation "inversions" hyp(H) :=
  inversion H; subst; try clear H.

(* injections keep H は injection H に続いて intros と subst を行うことの略記法です。 これは injects keep H のおおざっぱな実装で、証明コンテキストが既に等式を含んでいるとき、あるいはゴールがforallまたは含意で始まるときには、問題のある振る舞いをします。 *)

Tactic Notation "injections" "keep" hyp(H) :=
  injection H; intros; subst.

(* injections H は injection H に続いて clear H、intros、substを順に行うのと同じです。 これは injects H のおおざっぱな実装で、証明コンテキストが既に等式を含んでいるとき、あるいはゴールがforallまたは含意で始まるときには、問題のある振る舞いをします。 *)

Tactic Notation "injections" "keep" hyp(H) :=
  injection H; clear H; intros; subst.



(* 場合分け *)

(* cases は case_eq E と同様ですが、等式をゴールではなくコンテキストに作る点と、作る等式の右辺と左辺が逆であることが違います。 構文 cases E as H が可能で、仮定の名前Hを特定します。 *)

Tactic Notation "cases" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq_sym X H E;
  destruct X.

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.

(* case_if_postはゴールをかたづけるタクティックとして後で定義されるものです。 デフォルトでは明らかな矛盾を探します。 現状では、LibReflectでブール命題を片付けるように拡張されます。 *)

Ltac case_if_post H :=
  tryfalse.

(* case_ifはゴール内の if ?B then ?E1 else ?E2 という形のパターンを探し、Bについて destruct B を呼んで場合分けをします。 矛盾を含むようなサブゴールになったら自動で片付けられます。 case_ifは最初にゴールから探しますが、そこにifがなければifを含む最初の仮定を見ます。 case_if in H は考慮対象の仮定を指定するのに使えます。 構文 case_if as Eq と case_if in H as Eq は、場合分けによって生成される仮定に名前を付けるのに使えます。 *)

Ltac case_if_on_tactic_core E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq | Eq]
  | _ => let X := fresh "TEMP" in
         sets_eq <- X Eq: E;
         destruct X
  end.

Ltac case_if_on_tactic E Eq :=
  case_if_on_tactic_core E Eq; case_if_post Eq.

Tactic Notation "case_if_on" constr(E) "as" simple_intropattern(Eq) :=
  case_if_on_tactic E Eq.

Tactic Notation "case_if" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => case_if_on B as Eq
  | K: context [if ?B then _ else _] |- _ => case_if_on B as Eq
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  match type of H with context [if ?B then _ else _] =>
    case_if_on B as Eq end.

Tactic Notation "case_if" :=
  let Eq := fresh "C" in case_if as Eq.

Tactic Notation "case_if" "in" hyp(H) :=
  let Eq := fresh "C" in case_if in H as Eq.

(* cases_if は case_if と同様ですが、主に2つの違いがあります: もし x = y という形の等式が生成されたなら、ゴールでこの等式にもとづく置換をします。 *)

Ltac cases_if_on_tactic_core E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
  | _ => let X := fresh "TEMP" in
         sets_eq <- X Eq: E;
         destruct X
  end.

Ltac cases_if_on_tactic E Eq :=
  cases_if_on_tactic_core E Eq; tryfalse; case_if_post Eq.

Tactic Notation "cases_if_on" constr(E) "as" simple_intropattern(Eq) :=
  cases_if_on_tactic E Eq.

Tactic Notation "cases_if" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => cases_if_on B as Eq
  | K: context [if ?B then _ else _] |- _ => cases_if_on B as Eq
  end.

Tactic Notation "cases_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  match type of H with context [if ?B then _ else _] =>
    cases_if_on B as Eq end.

Tactic Notation "cases_if" :=
  let Eq := fresh "C" in cases_if as Eq.

Tactic Notation "cases_if" "in" hyp(H) :=
  let Eq := fresh "C" in cases_if in H as Eq.

(* case_ifs is like repeat case_if *)

Ltac case_ifs_core :=
  repeat case_if.

Tactic Notation "case_ifs" :=
  case_ifs_core.

(* destruct_if はゴールから if ?B then ?E1 else ?E2 という形のパターンを探し、Bについて destruct B を呼ぶことで場合分けをします。 最初にゴールから探しますが、そこにifがなければifを含む最初の仮定を見ます。 *)

Ltac destruct_if_post := tryfalse.

Tactic Notation "destruct_if"
 "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  match goal with
  | |- context [if ?B then _ else _] => destruct B as [Eq1|Eq2]
  | K: context [if ?B then _ else _] |- _ => destruct B as [Eq1|Eq2]
  end;
  destruct_if_post.

Tactic Notation "destruct_if" "in" hyp(H)
 "as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
  match type of H with context [if ?B then _ else _] =>
    destruct B as [Eq1|Eq2] end;
  destruct_if_post.

Tactic Notation "destruct_if" "as" simple_intropattern(Eq) :=
  destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
  destruct_if in H as Eq Eq.

Tactic Notation "destruct_if" :=
  let Eq := fresh "C" in destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) :=
  let Eq := fresh "C" in destruct_if in H as Eq Eq.

(* v8.5beta2から動きません。 TODO: 要掃除。 *)
(* destruct_head_matchは、ゴールが match ?E with ... または match ?E with ... = _ または _ = match ?E with ... という形のとき、先頭パターンマッチの引数で場合分けをします。 Ltacの制約により、マッチするものがないときでもこのタクティックは失敗しません。 その代わり、ゴールの不特定の部分項について、場合分けします。 注意: 実験的です。 *)

Ltac find_head_match T :=
  match T with context [?E] =>
    match T with
    | E => fail 1
    | _ => constr:(E)
    end
  end.

Ltac destruct_head_match_core cont :=
  match goal with
  | |- ?T1 = ?T2 => first [ let E := find_head_match T1 in cont E
                          | let E := find_head_match T2 in cont E ]
  | |- ?T1 => let E := find_head_match T1 in cont E
  end;
  destruct_if_post.

Tactic Notation "destruct_head_match" "as" simple_intropattern(I) :=
  destruct_head_match_core ltac:(fun E => destruct E as I).

Tactic Notation "destruct_head_match" :=
  destruct_head_match_core ltac:(fun E => destruct E).


(* cases' E は case_eq E と同様ですが、等式をゴールではなくコンテキストに作ります。 構文 cases' E as H も可能で、その仮定の名前 H を指定します。 *)

Tactic Notation "cases'" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq X H E;
  destruct X.

Tactic Notation "cases'" constr(E) :=
  let x := fresh "Eq" in cases' E as H.

(* cases_if'はcases_ifと同様ですが、生成される等式が左右逆になっている点が違います。 *)

Ltac cases_if_on' E Eq :=
  match type of E with
  | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
  | _ => let X := fresh "TEMP" in
         sets_eq X Eq: E;
         destruct X
  end; case_if_post Eq.

Tactic Notation "cases_if'" "as" simple_intropattern(Eq) :=
  match goal with
  | |- context [if ?B then _ else _] => cases_if_on' B Eq
  | K: context [if ?B then _ else _] |- _ => cases_if_on' B Eq
  end.

Tactic Notation "cases_if'" :=
  let Eq := fresh "C" in cases_if' as Eq.


(* 帰納法(Induction) *)
(* inductions E は dependent induction E の略記法です。 inductions E gen X1 .. XN は dependent induction E generalizing X1 .. XN の略記法です。 *)

From Coq Require Import Program.Equality.

Ltac inductions_post :=
  unfold eq' in *.

Tactic Notation "inductions" ident(E) :=
  dependent induction E; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) :=
  dependent induction E generalizing X1; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2) :=
  dependent induction E generalizing X1 X2; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) :=
  dependent induction E generalizing X1 X2 X3; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) :=
  dependent induction E generalizing X1 X2 X3 X4; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) :=
  dependent induction E generalizing X1 X2 X3 X4 X5; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
 ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) :=
  dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7 X8; inductions_post.

(* induction_wf IH: E X は、与えられた整礎関係(well-founded relation) についての整礎帰納法原理(well-founded induction principle) を適用するために使われます。 これはゴールPXに対して適用されます。ここでPXはXの上の命題です。 最初に、pattern X を使って (fun a => P a) X という形のゴールを用意します。 そして次に、Eについて具体化された整礎帰納法原理を適用します。 *)
(* ここでEは次のうちのどれかです： 
 A->A->Prop型のRについてwf Rの証明
二項関係A->A->Prop
尺度関数 A -> nat // LibWf 利用時のみ
構文は induction_wf: E X と induction_wf E X です。*)


Ltac induction_wf_core_then IH E X cont :=
  let T := type of E in
  let T := eval hnf in T in
  let clearX tt :=
    first [ clear X | fail 3 "the variable on which the induction is done appears in the hypotheses" ] in
  match T with
  
  | ?A -> ?A -> Prop =>
     pattern X;
     first [
       applys well_founded_ind E;
       clearX tt;
       [
       | intros X IH; cont tt ]
     | fail 2 ]
  | _ =>
    pattern X;
    applys well_founded_ind E;
    clearX tt;
    intros X IH;
    cont tt
  end.

Ltac induction_wf_core IH E X :=
  induction_wf_core_then IH E X ltac:(fun _ => idtac).

Tactic Notation "induction_wf" ident(IH) ":" constr(E) ident(X) :=
  induction_wf_core IH E X.
Tactic Notation "induction_wf" ":" constr(E) ident(X) :=
  let IH := fresh "IH" in induction_wf IH: E X.
Tactic Notation "induction_wf" ":" constr(E) ident(X) :=
  induction_wf: E X.

(* Induction on the height of a derivation: the helper tactic induct_height helps proving the equivalence of the auxiliary judgment that includes a counter for the maximal height (see LibTacticsDemos for an example) *)

From Coq Require Import Arith.Compare_dec.
From Coq Require Import omega.Omega.

Lemma induct_height_max2 : forall n1 n2 : nat,
  exists n, n1 < n /\ n2 < n.
Proof using.
  intros. destruct (lt_dec n1 n2).
  exists (S n2). omega.
  exists (S n1). omega.
Qed.

Ltac induct_height_step x :=
  match goal with
  | H: exists _, _ |- _ =>
     let n := fresh "n" in let y := fresh "x" in
     destruct H as [n ?];
     forwards (y&?&?): induct_height_max2 n x;
     induct_height_step y
  | _ => exists (S x); eauto
 end.

Ltac induct_height := induct_height_step O.

(* Coinduction *)
(* Tactic cofixs IH is like cofix IH except that the coinduction hypothesis is tagged in the form IH: COIND P instead of being just IH: P. This helps other tactics clearing the coinduction hypothesis using clear_coind *)

Definition COIND (P:Prop) := P.

Tactic Notation "cofixs" ident(IH) :=
  cofix IH;
  match type of IH with ?P => change P with (COIND P) in IH end.

(* Tactic clear_coind clears all the coinduction hypotheses, assuming that they have been tagged *)

Ltac clear_coind :=
  repeat match goal with H: COIND _ |- _ => clear H end.

(* Tactic abstracts tac is like abstract tac except that it clears the coinduction hypotheses so that the productivity check will be happy. For example, one can use abstracts omega to obtain the same behavior as omega but with an auxiliary lemma being generated. *)

Tactic Notation "abstracts" tactic(tac) :=
  clear_coind; tac.



(* 決定可能な等式 *)

(* decides_equality は decide equality と同様ですが、現在のゴールの先頭の定義を展開できる点が違います。 *)

Ltac decides_equality_tactic :=
  first [ decide equality | progress(unfolds); decides_equality_tactic ].

Tactic Notation "decides_equality" :=
  decides_equality_tactic.



(* 同値(Equivalence) *)

(* iff H は同値 P <-> Q を証明し、それぞれの場合に得られる仮定に名前Hを付けることができます。 構文 iff と iff H1 H2 も可能で、それぞれ0個、2個の名前を付けます。 タクティック iff <- H は2つのサブゴールを交換します。 つまり、(Q -> P) が最初のゴールになります。 *)

Lemma iff_intro_swap : forall (P Q : Prop),
  (Q -> P) -> (P -> Q) -> (P <-> Q).
Proof using. intuition. Qed.

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
  split; [ intros H1 | intros H2 ].
Tactic Notation "iff" simple_intropattern(H) :=
  iff H H.
Tactic Notation "iff" :=
  let H := fresh "H" in iff H.

Tactic Notation "iff" "<-" simple_intropattern(H1) simple_intropattern(H2) :=
  apply iff_intro_swap; [ intros H1 | intros H2 ].
Tactic Notation "iff" "<-" simple_intropattern(H) :=
  iff <- H H.
Tactic Notation "iff" "<-" :=
  let H := fresh "H" in iff <- H.



(* N個の連言と選言 *)

(* ゴールに分割されるN-連言 *)

(* splits の背後の実装。 *)

Ltac splits_tactic N :=
  match N with
  | O => fail
  | S O => idtac
  | S ?N' => split; [| splits_tactic N']
  end.

Ltac unfold_goal_until_conjunction :=
  match goal with
  | |- _ /\ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_conjunction
  end.

Ltac get_term_conjunction_arity T :=
  match T with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
  | _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
  | _ /\ _ /\ _ /\ _ => constr:(4)
  | _ /\ _ /\ _ => constr:(3)
  | _ /\ _ => constr:(2)
  | _ -> ?T' => get_term_conjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_conjunction_arity T'
         end
         
  end.

Ltac get_goal_conjunction_arity :=
  match goal with |- ?T => get_term_conjunction_arity T end.

(* splits は (T1 /\ .. /\ TN) という形のゴールに適用され、N個のサブゴール T1 .. TN に分解します。 ゴールが連言ではない場合、先頭の定義を展開します。 *)

Tactic Notation "splits" :=
  unfold_goal_until_conjunction;
  let N := get_goal_conjunction_arity in
  splits_tactic N.

(* splits N はsplitsと同様ですが、N-連言を得るのに必要なだけ定義を展開する点が違います。 *)

Tactic Notation "splits" constr(N) :=
  let N := number_to_nat N in
  splits_tactic N.



(* N-連言の分解 *)

(* destructsの背後の実装。 *)

Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
| 4 => destruct T as [? [? [? ?]]]
| 5 => destruct T as [? [? [? [? ?]]]]
| 6 => destruct T as [? [? [? [? [? ?]]]]]
| 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
end.

(* destructs T は N-連言の項Tを分解します。 destruct T as (H1 .. HN) と同様ですが、N個の異なる名前を手動で指定しなくて良い点が違います。 *)

Tactic Notation "destructs" constr(T) :=
  let TT := type of T in
  let N := get_term_conjunction_arity TT in
  destructs_conjunction_tactic N T.

(* destructs N T は destruct T as (H1 .. HN) と同様ですが、N個の異なる名前を手動で指定しなくて良い点が違います。 N-引数の連言に限らないことに注意します。 *)

Tactic Notation "destructs" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_conjunction_tactic N T.

(* N-選言であるゴールを証明する *)

(* branchの背後の実装。 *)

Ltac branch_tactic K N :=
  match constr:((K,N)) with
  | (_,0) => fail 1
  | (0,_) => fail 1
  | (1,1) => idtac
  | (1,_) => left
  | (S ?K', S ?N') => right; branch_tactic K' N'
  end.

Ltac unfold_goal_until_disjunction :=
  match goal with
  | |- _ \/ _ => idtac
  | _ => progress(unfolds); unfold_goal_until_disjunction
  end.

Ltac get_term_disjunction_arity T :=
  match T with
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(8)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(7)
  | _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(6)
  | _ \/ _ \/ _ \/ _ \/ _ => constr:(5)
  | _ \/ _ \/ _ \/ _ => constr:(4)
  | _ \/ _ \/ _ => constr:(3)
  | _ \/ _ => constr:(2)
  | _ -> ?T' => get_term_disjunction_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_disjunction_arity T'
         end
  end.

Ltac get_goal_disjunction_arity :=
  match goal with |- ?T => get_term_disjunction_arity T end.

(* branch N は P1 \/ ... \/ PK \/ ... \/ PN という形のゴールに適用され、ゴールPKを残します。 これは先頭の定義（もし存在すれば）だけを展開することができます。 より複雑な展開のためには、タクティック branch K of N を使うべきです。 *)

Tactic Notation "branch" constr(K) :=
  let K := number_to_nat K in
  unfold_goal_until_disjunction;
  let N := get_goal_disjunction_arity in
  branch_tactic K N.

(* branch K of N は branch K と同様ですが、選言の数Nが手動で与えられ、このため定義を展開できます。 言い換えると、P1 \/ ... \/ PK \/ ... \/ PNという形のゴールに適用され、ゴールPKを残します。 *)

Tactic Notation "branch" constr(K) "of" constr(N) :=
  let N := number_to_nat N in
  let K := number_to_nat K in
  branch_tactic K N.

(* N-選言の分解 *)

(* branches の背後の実装。 *)

Ltac destructs_disjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? | ?]
  | 3 => destruct T as [? | [? | ?]]
| 4 => destruct T as [? | [? | [? | ?]]]
| 5 => destruct T as [? | [? | [? | [? | ?]]]]
end.

(* branches T はN-選言である項Tを分解します。 これは destruct T as [ H1 | .. | HN ] と同値で、N個の可能な場合に対応するN個のサブゴールを生成します。 *)

Tactic Notation "branches" constr(T) :=
  let TT := type of T in
  let N := get_term_disjunction_arity TT in
  destructs_disjunction_tactic N T.

(* branches N T は branches T と同様ですが、選言の個数がNに強制される点が違います。この形は定義をその場で展開したいときに便利です。 *)

Tactic Notation "branches" constr(N) constr(T) :=
  let N := number_to_nat N in
  destructs_disjunction_tactic N T.

(* branches automatically finds a hypothesis h that is a disjunction and destructs it. *)

Tactic Notation "branches" :=
  match goal with h: _ \/ _ |- _ => branches h end.



(* N-変数存在限量 *)


Ltac get_term_existential_arity T :=
  match T with
  | exists x1 x2 x3 x4 x5 x6 x7 x8, _ => constr:(8)
  | exists x1 x2 x3 x4 x5 x6 x7, _ => constr:(7)
  | exists x1 x2 x3 x4 x5 x6, _ => constr:(6)
  | exists x1 x2 x3 x4 x5, _ => constr:(5)
  | exists x1 x2 x3 x4, _ => constr:(4)
  | exists x1 x2 x3, _ => constr:(3)
  | exists x1 x2, _ => constr:(2)
  | exists x1, _ => constr:(1)
  | _ -> ?T' => get_term_existential_arity T'
  | _ => let P := get_head T in
         let T' := eval unfold P in T in
         match T' with
         | T => fail 1
         | _ => get_term_existential_arity T'
         end
  end.

Ltac get_goal_existential_arity :=
  match goal with |- ?T => get_term_existential_arity T end.

(* exists T1 ... TN は exists T1; ...; exists TN の略記法です。 これは exist X1 .. XN, P という形のゴールを証明することを意図したものです。 もし与えられた引数が __ （二連アンダースコア）ならば、存在変数が導入されます。 exists T1 .. TN ___ は、任意個の __ についての exists T1 .. TN __ __ __ と同値です。 *)

Tactic Notation "exists_original" constr(T1) :=
  exists T1.
Tactic Notation "exists" constr(T1) :=
  match T1 with
  | ltac_wild => esplit
  | ltac_wilds => repeat esplit
  | _ => exists T1
  end.
Tactic Notation "exists" constr(T1) constr(T2) :=
  exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
  exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1; exists T2; exists T3; exists T4.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1; exists T2; exists T3; exists T4; exists T5.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1; exists T2; exists T3; exists T4; exists T5; exists T6.

(* For compatibility with Coq syntax, exists T1, .., TN is also provided. *)

Tactic Notation "exists" constr(T1) "," constr(T2) :=
  exists T1 T2.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) :=
  exists T1 T2 T3 T4.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) :=
  exists T1 T2 T3 T4 T5.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
 constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6.

(* タクティック exists___ N は N個の二連アンダースコアの exists __ ... __ の略記法です。 タクティック exists は、ゴールの先頭に存在限量が N 個ある場合 exists___ N を呼ぶのと同値です。 exists の振る舞いが exists ___ と違うのは、ゴールの定義を展開してはじめて存在限量になる場合です。 *)

Tactic Notation "exists___" constr(N) :=
  let rec aux N :=
    match N with
    | 0 => idtac
    | S ?N' => esplit; aux N'
    end in
  let N := number_to_nat N in aux N.

Tactic Notation "exists___" :=
  let N := get_goal_existential_arity in
  exists___ N.

Tactic Notation "exists" :=
  exists___.

Tactic Notation "exists_all" := exists___.

(* 仮定内の存在限量と連言 *)
(* unpack or unpack H destructs conjunctions and existentials in all or one hypothesis. *)

Ltac unpack_core :=
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: exists (varname: _), _ |- _ =>
      
      let name := fresh varname in
      destruct H as [name ?]
  end.

Ltac unpack_hypothesis H :=
  try match type of H with
  | _ /\ _ =>
      let h1 := fresh "TEMP" in
      let h2 := fresh "TEMP" in
      destruct H as [ h1 h2 ];
      unpack_hypothesis h1;
      unpack_hypothesis h2
  | exists (varname: _), _ =>
      
      let name := fresh varname in
      let body := fresh "TEMP" in
      destruct H as [name body];
      unpack_hypothesis body
  end.

Tactic Notation "unpack" :=
  unpack_core.
Tactic Notation "unpack" constr(H) :=
  unpack_hypothesis H.



(* タイプクラスのインスタンスを証明するためのタクティック *)

(* typeclass はタイプクラスのインスタンスを発見することに特化された自動化タクティックです。 *)

Tactic Notation "typeclass" :=
  let go _ := eauto with typeclass_instances in
  solve [ go tt | constructor; go tt ].

(* solve_typeclassはtypeclassの簡易版です。 インスタンスを再度解くヒントタクティックで使われます。 *)

Tactic Notation "solve_typeclass" :=
  solve [ eauto with typeclass_instances ].

(* 自動化起動のタクティック *)

(* Definitions for Parsing Compatibility *)

Tactic Notation "f_equal" :=
  f_equal.
Tactic Notation "constructor" :=
  constructor.
Tactic Notation "simple" :=
  simpl.

Tactic Notation "split" :=
  split.

Tactic Notation "right" :=
  right.
Tactic Notation "left" :=
  left.

(* hint to Add Hints Local to a Lemma *)
(* hint E adds E as an hypothesis so that automation can use it. Syntax hint E1,..,EN is available *)

Tactic Notation "hint" constr(E) :=
  let H := fresh "Hint" in lets H: E.
Tactic Notation "hint" constr(E1) "," constr(E2) :=
  hint E1; hint E2.
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) :=
  hint E1; hint E2; hint(E3).
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hint E1; hint E2; hint(E3); hint(E4 ).


(* jauto, 新しい自動化タクティック *)

(* jauto は intuition eauto と比べて、コンテキストから存在限量を展開できる点が優れています。 同時に、jauto はコンテキストから選言を分解しないため、 intuition eauto より速い場合があります。 jautoの戦略は以下のようにまとめられます: *)
(* コンテキストからすべての存在限量と連言を開きます *)
(* ゴールの存在限量と連言に対して esplit と split を呼びます *)
(* eauto を呼びます。 *)

Tactic Notation "jauto" :=
  try solve [ jauto_set; eauto ].

Tactic Notation "jauto_fast" :=
  try solve [ auto | eauto | jauto ].

(* iautoは intuition eauto の略記法です *)

Tactic Notation "iauto" := try solve [intuition eauto].

(* 自動化タクティックの定義 *)

(* 以下の2つのタクティックは、「軽い自動化」("light automation")と「強力な自動化」("strong automation")のデフォルトの振る舞いを定義します。 これらのタクティックは、構文 Ltac .. ::= .. を使うことでいつでも再定義できます。 *)

(* auto_tilde は、タクティックの後に記号~が使われたときにいつでも呼ばれるタクティックです。 *)

Ltac auto_tilde_default := auto.
Ltac auto_tilde := auto_tilde_default.

(* auto_star は、タクティックの後に記号*が使われたときにいつでも呼ばれるタクティックです。 *)

Ltac auto_star_default := try solve [ jauto ].
Ltac auto_star := auto_star_default.

(* autos~はタクティックauto_tildeの記法です。 この後に、ゴールを解くために auto が使う補題（または証明項）を付記することができます。 *)
(* autosはautos~と同じです。 *)

Tactic Notation "autos" :=
  auto_tilde.
Tactic Notation "autos" "~" :=
  auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
  lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) :=
  lets: E1; lets: E2; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) :=
  lets: E1; lets: E2; lets: E3; auto_tilde.

(* autos*はタクティックauto_starの記法です。 この後に、ゴールを解くために auto が使う補題（または証明項）を付記することができます。 *)

Tactic Notation "autos" "*" :=
  auto_star.
Tactic Notation "autos" "*" constr(E1) :=
  lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) :=
  lets: E1; lets: E2; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) :=
  lets: E1; lets: E2; lets: E3; auto_star.

(* auto_falseは、ある種の矛盾を発見できるautoの一種です。 <->を見つけるとsplitを呼ぶというアドホックなサポートが入っています。 auto_false~ および auto_false* も可能です。 *)

Ltac auto_false_base cont :=
  try solve [
    intros_all; try match goal with |- _ <-> _ => split end;
    solve [ cont tt | intros_all; false; cont tt ] ].

Tactic Notation "auto_false" :=
   auto_false_base ltac:(fun tt => auto).
Tactic Notation "auto_false" "~" :=
   auto_false_base ltac:(fun tt => auto_tilde).
Tactic Notation "auto_false" "*" :=
   auto_false_base ltac:(fun tt => auto_star).

Tactic Notation "dauto" :=
  dintuition eauto.

(* 軽い自動化の構文解析 *)

(* 任意のタクティックに記号~を付けると、すべてのサブゴールに対してauto_tildeが呼ばれます。 例外が3つあります: *)
(* cutsとassertsは最初のサブゴールにautoだけを呼びます *)
(* apply~はapplyではなくsapplyを使います *)
(* tryfalse~は tryfalse by auto_tilde と定義されています。 *)
(* いくつかのビルトイン・タクティックはタクティック記法を使って定義されていないため、拡張できません。 例えばsimplとunfoldです。 これらに対して、simpl~のような記法は使えません。 *)

Tactic Notation "equates" "~" constr(E) :=
   equates E; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) :=
  equates n1 n2; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) :=
  equates n1 n2 n3; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates n1 n2 n3 n4; auto_tilde.

Tactic Notation "applys_eq" "~" constr(H) constr(E) :=
  applys_eq H E; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) :=
  applys_eq H n1 n2; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H n1 n2 n3; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H n1 n2 n3 n4; auto_tilde.

Tactic Notation "apply" "~" constr(H) :=
  sapply H; auto_tilde.

Tactic Notation "destruct" "~" constr(H) :=
  destruct H; auto_tilde.
Tactic Notation "destruct" "~" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto_tilde.
Tactic Notation "f_equal" "~" :=
  f_equal; auto_tilde.
Tactic Notation "induction" "~" constr(H) :=
  induction H; auto_tilde.
Tactic Notation "inversion" "~" constr(H) :=
  inversion H; auto_tilde.
Tactic Notation "split" "~" :=
  split; auto_tilde.
Tactic Notation "subst" "~" :=
  subst; auto_tilde.
Tactic Notation "right" "~" :=
  right; auto_tilde.
Tactic Notation "left" "~" :=
  left; auto_tilde.
Tactic Notation "constructor" "~" :=
  constructor; auto_tilde.
Tactic Notation "constructors" "~" :=
  constructors; auto_tilde.

Tactic Notation "false" "~" :=
  false; auto_tilde.
Tactic Notation "false" "~" constr(E) :=
  false_then E ltac:(fun _ => auto_tilde).
Tactic Notation "false" "~" constr(E0) constr(E1) :=
  false~ (>> E0 E1).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) :=
  false~ (>> E0 E1 E2).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) :=
  false~ (>> E0 E1 E2 E3).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false~ (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "~" :=
  try solve [ false~ ].

Tactic Notation "asserts" "~" simple_intropattern(H) ":" constr(E) :=
  asserts H: E; [ auto_tilde | idtac ].
Tactic Notation "asserts" "~" ":" constr(E) :=
  let H := fresh "H" in asserts~ H: E.
Tactic Notation "cuts" "~" simple_intropattern(H) ":" constr(E) :=
  cuts H: E; [ auto_tilde | idtac ].
Tactic Notation "cuts" "~" ":" constr(E) :=
  cuts: E; [ auto_tilde | idtac ].

Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E) :=
  lets I: E; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: E0 A1; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "lets" "~" ":" constr(E) :=
  lets: E; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) :=
  lets: E0 A1; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E) :=
  forwards I: E; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" ":" constr(E) :=
  forwards: E; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) :=
  forwards: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "applys" "~" constr(H) :=
  sapply H; auto_tilde. Tactic Notation "applys" "~" constr(E0) constr(A1) :=
  applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) :=
  applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) :=
  applys E0 A1 A2; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys E0 A1 A2 A3; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "specializes" "~" hyp(H) :=
  specializes H; auto_tilde.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
  specializes H A1; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H A1 A2; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H A1 A2 A3; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H A1 A2 A3 A4; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "fapply" "~" constr(E) :=
  fapply E; auto_tilde.
Tactic Notation "sapply" "~" constr(E) :=
  sapply E; auto_tilde.

Tactic Notation "logic" "~" constr(E) :=
  logic_base E ltac:(fun _ => auto_tilde).

Tactic Notation "intros_all" "~" :=
  intros_all; auto_tilde.

Tactic Notation "unfolds" "~" :=
  unfolds; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) :=
  unfolds F1; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) :=
  unfolds F1, F2; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) :=
  unfolds F1, F2, F3; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) ","
 constr(F4) :=
  unfolds F1, F2, F3, F4; auto_tilde.

Tactic Notation "simple" "~" :=
  simpl; auto_tilde.
Tactic Notation "simple" "~" "in" hyp(H) :=
  simpl in H; auto_tilde.
Tactic Notation "simpls" "~" :=
  simpls; auto_tilde.
Tactic Notation "hnfs" "~" :=
  hnfs; auto_tilde.
Tactic Notation "hnfs" "~" "in" hyp(H) :=
  hnf in H; auto_tilde.
Tactic Notation "substs" "~" :=
  substs; auto_tilde.
Tactic Notation "intro_hyp" "~" hyp(H) :=
  subst_hyp H; auto_tilde.
Tactic Notation "intro_subst" "~" :=
  intro_subst; auto_tilde.
Tactic Notation "subst_eq" "~" constr(E) :=
  subst_eq E; auto_tilde.

Tactic Notation "rewrite" "~" constr(E) :=
  rewrite E; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) :=
  rewrite <- E; auto_tilde.
Tactic Notation "rewrite" "~" constr(E) "in" hyp(H) :=
  rewrite E in H; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  rewrite <- E in H; auto_tilde.

Tactic Notation "rewrites" "~" constr(E) :=
  rewrites E; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" hyp(H) :=
  rewrites E in H; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" "*" :=
  rewrites E in *; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) :=
  rewrites <- E; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" hyp(H) :=
  rewrites <- E in H; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" "*" :=
  rewrites <- E in *; auto_tilde.

Tactic Notation "rewrite_all" "~" constr(E) :=
  rewrite_all E; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) :=
  rewrite_all <- E; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" ident(H) :=
  rewrite_all E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" ident(H) :=
  rewrite_all <- E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" "*" :=
  rewrite_all E in *; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" "*" :=
  rewrite_all <- E in *; auto_tilde.

Tactic Notation "asserts_rewrite" "~" constr(E) :=
  asserts_rewrite E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) :=
  asserts_rewrite <- E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" hyp(H) :=
  asserts_rewrite E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite <- E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" "*" :=
  asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" "*" :=
  asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "~" constr(E) :=
  cuts_rewrite E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) :=
  cuts_rewrite <- E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" constr(E) "in" hyp(H) :=
  cuts_rewrite E in H; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite <- E in H; auto_tilde.

Tactic Notation "erewrite" "~" constr(E) :=
  erewrite E; auto_tilde.

Tactic Notation "fequal" "~" :=
  fequal; auto_tilde.
Tactic Notation "fequals" "~" :=
  fequals; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) :=
  pi_rewrite E; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) "in" hyp(H) :=
  pi_rewrite E in H; auto_tilde.

Tactic Notation "invert" "~" hyp(H) :=
  invert H; auto_tilde.
Tactic Notation "inverts" "~" hyp(H) :=
  inverts H; auto_tilde.
Tactic Notation "inverts" "~" hyp(E) "as" :=
  inverts E as; auto_tilde.
Tactic Notation "injects" "~" hyp(H) :=
  injects H; auto_tilde.
Tactic Notation "inversions" "~" hyp(H) :=
  inversions H; auto_tilde.

Tactic Notation "cases" "~" constr(E) "as" ident(H) :=
  cases E as H; auto_tilde.
Tactic Notation "cases" "~" constr(E) :=
  cases E; auto_tilde.
Tactic Notation "case_if" "~" :=
  case_if; auto_tilde.
Tactic Notation "case_ifs" "~" :=
  case_ifs; auto_tilde.
Tactic Notation "case_if" "~" "in" hyp(H) :=
  case_if in H; auto_tilde.
Tactic Notation "cases_if" "~" :=
  cases_if; auto_tilde.
Tactic Notation "cases_if" "~" "in" hyp(H) :=
  cases_if in H; auto_tilde.
Tactic Notation "destruct_if" "~" :=
  destruct_if; auto_tilde.
Tactic Notation "destruct_if" "~" "in" hyp(H) :=
  destruct_if in H; auto_tilde.
Tactic Notation "destruct_head_match" "~" :=
  destruct_head_match; auto_tilde.

Tactic Notation "cases'" "~" constr(E) "as" ident(H) :=
  cases' E as H; auto_tilde.
Tactic Notation "cases'" "~" constr(E) :=
  cases' E; auto_tilde.
Tactic Notation "cases_if'" "~" "as" ident(H) :=
  cases_if' as H; auto_tilde.
Tactic Notation "cases_if'" "~" :=
  cases_if'; auto_tilde.

Tactic Notation "decides_equality" "~" :=
  decides_equality; auto_tilde.

Tactic Notation "iff" "~" :=
  iff; auto_tilde.
Tactic Notation "iff" "~" simple_intropattern(I) :=
  iff I; auto_tilde.
Tactic Notation "splits" "~" :=
  splits; auto_tilde.
Tactic Notation "splits" "~" constr(N) :=
  splits N; auto_tilde.

Tactic Notation "destructs" "~" constr(T) :=
  destructs T; auto_tilde.
Tactic Notation "destructs" "~" constr(N) constr(T) :=
  destructs N T; auto_tilde.

Tactic Notation "branch" "~" constr(N) :=
  branch N; auto_tilde.
Tactic Notation "branch" "~" constr(K) "of" constr(N) :=
  branch K of N; auto_tilde.

Tactic Notation "branches" "~" :=
  branches; auto_tilde.
Tactic Notation "branches" "~" constr(T) :=
  branches T; auto_tilde.
Tactic Notation "branches" "~" constr(N) constr(T) :=
  branches N T; auto_tilde.

Tactic Notation "exists" "~" :=
  exists; auto_tilde.
Tactic Notation "exists___" "~" :=
  exists___; auto_tilde.
Tactic Notation "exists" "~" constr(T1) :=
  exists T1; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) :=
  exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) :=
  exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_tilde.

Tactic Notation "exists" "~" constr(T1) "," constr(T2) :=
  exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) :=
  exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_tilde.


(* 強力な自動化の構文解析 *)

(* 任意のタクティックに記号*を付けると、すべてのサブゴールに対してauto*が呼ばれます。 例外は、軽い自動化と同じです。 *)
(* 例外: ライブラリ Coq.Classes.Equivalence を import したいときは、 subst*ではなくsubs*を使ってください。 *)

Tactic Notation "equates" "*" constr(E) :=
   equates E; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) :=
  equates n1 n2; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) :=
  equates n1 n2 n3; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) constr(n4) :=
  equates n1 n2 n3 n4; auto_star.

Tactic Notation "applys_eq" "*" constr(H) constr(E) :=
  applys_eq H E; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) :=
  applys_eq H n1 n2; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) :=
  applys_eq H n1 n2 n3; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
  applys_eq H n1 n2 n3 n4; auto_star.

Tactic Notation "apply" "*" constr(H) :=
  sapply H; auto_star.

Tactic Notation "destruct" "*" constr(H) :=
  destruct H; auto_star.
Tactic Notation "destruct" "*" constr(H) "as" simple_intropattern(I) :=
  destruct H as I; auto_star.
Tactic Notation "f_equal" "*" :=
  f_equal; auto_star.
Tactic Notation "induction" "*" constr(H) :=
  induction H; auto_star.
Tactic Notation "inversion" "*" constr(H) :=
  inversion H; auto_star.
Tactic Notation "split" "*" :=
  split; auto_star.
Tactic Notation "subs" "*" :=
  subst; auto_star.
Tactic Notation "subst" "*" :=
  subst; auto_star.
Tactic Notation "right" "*" :=
  right; auto_star.
Tactic Notation "left" "*" :=
  left; auto_star.
Tactic Notation "constructor" "*" :=
  constructor; auto_star.
Tactic Notation "constructors" "*" :=
  constructors; auto_star.

Tactic Notation "false" "*" :=
  false; auto_star.
Tactic Notation "false" "*" constr(E) :=
  false_then E ltac:(fun _ => auto_star).
Tactic Notation "false" "*" constr(E0) constr(E1) :=
  false* (>> E0 E1).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) :=
  false* (>> E0 E1 E2).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) :=
  false* (>> E0 E1 E2 E3).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false* (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "*" :=
  try solve [ false* ].

Tactic Notation "asserts" "*" simple_intropattern(H) ":" constr(E) :=
  asserts H: E; [ auto_star | idtac ].
Tactic Notation "asserts" "*" ":" constr(E) :=
  let H := fresh "H" in asserts* H: E.
Tactic Notation "cuts" "*" simple_intropattern(H) ":" constr(E) :=
  cuts H: E; [ auto_star | idtac ].
Tactic Notation "cuts" "*" ":" constr(E) :=
  cuts: E; [ auto_star | idtac ].

Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E) :=
  lets I: E; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: E0 A1; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "lets" "*" ":" constr(E) :=
  lets: E; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) :=
  lets: E0 A1; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E) :=
  forwards I: E; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: E0 A1; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" ":" constr(E) :=
  forwards: E; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) :=
  forwards: E0 A1; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "applys" "*" constr(H) :=
  sapply H; auto_star. Tactic Notation "applys" "*" constr(E0) constr(A1) :=
  applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) :=
  applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) :=
  applys E0 A1 A2; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys E0 A1 A2 A3; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys E0 A1 A2 A3 A4; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "specializes" "*" hyp(H) :=
  specializes H; auto_star.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
  specializes H A1; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
  specializes H A1 A2; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
  specializes H A1 A2 A3; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
  specializes H A1 A2 A3 A4; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  specializes H A1 A2 A3 A4 A5; auto_star.

Tactic Notation "fapply" "*" constr(E) :=
  fapply E; auto_star.
Tactic Notation "sapply" "*" constr(E) :=
  sapply E; auto_star.

Tactic Notation "logic" constr(E) :=
  logic_base E ltac:(fun _ => auto_star).

Tactic Notation "intros_all" "*" :=
  intros_all; auto_star.

Tactic Notation "unfolds" "*" :=
  unfolds; auto_star.
Tactic Notation "unfolds" "*" constr(F1) :=
  unfolds F1; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) :=
  unfolds F1, F2; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) :=
  unfolds F1, F2, F3; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) ","
 constr(F4) :=
  unfolds F1, F2, F3, F4; auto_star.

Tactic Notation "simple" "*" :=
  simpl; auto_star.
Tactic Notation "simple" "*" "in" hyp(H) :=
  simpl in H; auto_star.
Tactic Notation "simpls" "*" :=
  simpls; auto_star.
Tactic Notation "hnfs" "*" :=
  hnfs; auto_star.
Tactic Notation "hnfs" "*" "in" hyp(H) :=
  hnf in H; auto_star.
Tactic Notation "substs" "*" :=
  substs; auto_star.
Tactic Notation "intro_hyp" "*" hyp(H) :=
  subst_hyp H; auto_star.
Tactic Notation "intro_subst" "*" :=
  intro_subst; auto_star.
Tactic Notation "subst_eq" "*" constr(E) :=
  subst_eq E; auto_star.

Tactic Notation "rewrite" "*" constr(E) :=
  rewrite E; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) :=
  rewrite <- E; auto_star.
Tactic Notation "rewrite" "*" constr(E) "in" hyp(H) :=
  rewrite E in H; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  rewrite <- E in H; auto_star.

Tactic Notation "rewrites" "*" constr(E) :=
  rewrites E; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" hyp(H):=
  rewrites E in H; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" "*":=
  rewrites E in *; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) :=
  rewrites <- E; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" hyp(H):=
  rewrites <- E in H; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" "*":=
  rewrites <- E in *; auto_star.

Tactic Notation "rewrite_all" "*" constr(E) :=
  rewrite_all E; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) :=
  rewrite_all <- E; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" ident(H) :=
  rewrite_all E in H; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" ident(H) :=
  rewrite_all <- E in H; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" "*" :=
  rewrite_all E in *; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" "*" :=
  rewrite_all <- E in *; auto_star.

Tactic Notation "asserts_rewrite" "*" constr(E) :=
  asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) :=
  asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" hyp(H) :=
  asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" "*" :=
  asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" "*" :=
  asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "*" constr(E) :=
  cuts_rewrite E; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) :=
  cuts_rewrite <- E; auto_star.
Tactic Notation "cuts_rewrite" "*" constr(E) "in" hyp(H) :=
  cuts_rewrite E in H; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
  cuts_rewrite <- E in H; auto_star.

Tactic Notation "erewrite" "*" constr(E) :=
  erewrite E; auto_star.

Tactic Notation "fequal" "*" :=
  fequal; auto_star.
Tactic Notation "fequals" "*" :=
  fequals; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) :=
  pi_rewrite E; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) "in" hyp(H) :=
  pi_rewrite E in H; auto_star.

Tactic Notation "invert" "*" hyp(H) :=
  invert H; auto_star.
Tactic Notation "inverts" "*" hyp(H) :=
  inverts H; auto_star.
Tactic Notation "inverts" "*" hyp(E) "as" :=
  inverts E as; auto_star.
Tactic Notation "injects" "*" hyp(H) :=
  injects H; auto_star.
Tactic Notation "inversions" "*" hyp(H) :=
  inversions H; auto_star.

Tactic Notation "cases" "*" constr(E) "as" ident(H) :=
  cases E as H; auto_star.
Tactic Notation "cases" "*" constr(E) :=
  cases E; auto_star.
Tactic Notation "case_if" "*" :=
  case_if; auto_star.
Tactic Notation "case_ifs" "*" :=
  case_ifs; auto_star.
Tactic Notation "case_if" "*" "in" hyp(H) :=
  case_if in H; auto_star.
Tactic Notation "cases_if" "*" :=
  cases_if; auto_star.
Tactic Notation "cases_if" "*" "in" hyp(H) :=
  cases_if in H; auto_star.
 Tactic Notation "destruct_if" "*" :=
  destruct_if; auto_star.
Tactic Notation "destruct_if" "*" "in" hyp(H) :=
  destruct_if in H; auto_star.
Tactic Notation "destruct_head_match" "*" :=
  destruct_head_match; auto_star.

Tactic Notation "cases'" "*" constr(E) "as" ident(H) :=
  cases' E as H; auto_star.
Tactic Notation "cases'" "*" constr(E) :=
  cases' E; auto_star.
Tactic Notation "cases_if'" "*" "as" ident(H) :=
  cases_if' as H; auto_star.
Tactic Notation "cases_if'" "*" :=
  cases_if'; auto_star.

Tactic Notation "decides_equality" "*" :=
  decides_equality; auto_star.

Tactic Notation "iff" "*" :=
  iff; auto_star.
Tactic Notation "iff" "*" simple_intropattern(I) :=
  iff I; auto_star.
Tactic Notation "splits" "*" :=
  splits; auto_star.
Tactic Notation "splits" "*" constr(N) :=
  splits N; auto_star.

Tactic Notation "destructs" "*" constr(T) :=
  destructs T; auto_star.
Tactic Notation "destructs" "*" constr(N) constr(T) :=
  destructs N T; auto_star.

Tactic Notation "branch" "*" constr(N) :=
  branch N; auto_star.
Tactic Notation "branch" "*" constr(K) "of" constr(N) :=
  branch K of N; auto_star.

Tactic Notation "branches" "*" constr(T) :=
  branches T; auto_star.
Tactic Notation "branches" "*" constr(N) constr(T) :=
  branches N T; auto_star.

Tactic Notation "exists" "*" :=
  exists; auto_star.
Tactic Notation "exists___" "*" :=
  exists___; auto_star.
Tactic Notation "exists" "*" constr(T1) :=
  exists T1; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) :=
  exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) :=
  exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
 constr(T5) constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_star.

Tactic Notation "exists" "*" constr(T1) "," constr(T2) :=
  exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) :=
  exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
  constr(T4) :=
  exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) :=
  exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
 constr(T4) "," constr(T5) "," constr(T6) :=
  exists T1 T2 T3 T4 T5 T6; auto_star.



(* 証明コンテキストを整理するためのタクティック *)

(* 仮定の隠蔽 *)


Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof using. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof using. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof using. auto. Qed.

(* hide_def x と show_def x によって、定義xの本体を隠蔽/明示化できます。 *)

Tactic Notation "hide_def" hyp(x) :=
  let x' := constr:(x) in
  let T := eval unfold x in x' in
  change T with (@ltac_something _ T) in x.

Tactic Notation "show_def" hyp(x) :=
  let x' := constr:(x) in
  let U := eval unfold x in x' in
  match U with @ltac_something _ ?T =>
    change U with T in x end.

(* show_def はゴールの Something を展開します *)

Tactic Notation "show_def" :=
  unfold ltac_something.
Tactic Notation "show_def" "in" hyp(H) :=
  unfold ltac_something in H.
Tactic Notation "show_def" "in" "*" :=
  unfold ltac_something in *.

(* hide_defs と show_defs はすべての定義に適用されます *)

Tactic Notation "hide_defs" :=
  repeat match goal with H := ?T |- _ =>
    match T with
    | @ltac_something _ _ => fail 1
    | _ => change T with (@ltac_something _ T) in H
    end
  end.

Tactic Notation "show_defs" :=
  repeat match goal with H := (@ltac_something _ ?T) |- _ =>
    change (@ltac_something _ T) with T in H end.

(* hide_hyp H はHの型の表記を Something に変え、 show_hyp H は仮定の型を明示します。 なお、Hの隠された型でもHの実際の型と同様にはたらきます。 *)

Tactic Notation "show_hyp" hyp(H) :=
  apply ltac_something_show in H.

Tactic Notation "hide_hyp" hyp(H) :=
  apply ltac_something_hide in H.

(* hide_hyps と show_hyps は、型Propのすべての仮定を隠蔽/明示化します。 *)

Tactic Notation "show_hyps" :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Tactic Notation "hide_hyps" :=
  repeat match goal with H: ?T |- _ =>
    match type of T with
    | Prop =>
      match T with
      | @ltac_something _ _ => fail 2
      | _ => hide_hyp H
      end
    | _ => fail 1
    end
  end.

(* hide H と show H はそれぞれ、hide_hyp または hide_def を、あるいは、show_hyp または show_def を自動的に選択します。 同様に、hide_all と show_all はすべてに適用されます。 *)

Tactic Notation "hide" hyp(H) :=
  first [hide_def H | hide_hyp H].

Tactic Notation "show" hyp(H) :=
  first [show_def H | show_hyp H].

Tactic Notation "hide_all" :=
  hide_hyps; hide_defs.

Tactic Notation "show_all" :=
  unfold ltac_something in *.

(* hide_term E はゴールから項を隠すのに使います。 show_term または show_term E は隠された項を明示化するために使います。 hide_term E in H は仮定を指定するときに使います。 *)

Tactic Notation "hide_term" constr(E) :=
  change E with (@ltac_something _ E).
Tactic Notation "show_term" constr(E) :=
  change (@ltac_something _ E) with E.
Tactic Notation "show_term" :=
  unfold ltac_something.

Tactic Notation "hide_term" constr(E) "in" hyp(H) :=
  change E with (@ltac_something _ E) in H.
Tactic Notation "show_term" constr(E) "in" hyp(H) :=
  change (@ltac_something _ E) with E in H.
Tactic Notation "show_term" "in" hyp(H) :=
  unfold ltac_something in H.

(* show_unfold R unfolds the definition of R and reveals the hidden definition of R. --todo:test, and implement using unfold simply *)

Tactic Notation "show_unfold" constr(R1) :=
  unfold R1; show_def.
Tactic Notation "show_unfold" constr(R1) "," constr(R2) :=
  unfold R1, R2; show_def.

(* 仮定のソーティング *)

(* sort はコンテキストの仮定を並び変えて、すべての命題（型 Prop の仮定）がコンテキストの下部に来るようにします。 *)

Ltac sort_tactic :=
  try match goal with H: ?T |- _ =>
  match type of T with Prop =>
    generalizes H; (try sort_tactic); intro
  end end.

Tactic Notation "sort" :=
  sort_tactic.


(* 仮定のクリア *)

(* clears X1 ... XN はclearの変種で、変数 X1..XN とそれらに依存するすべての仮定をクリアします。 clearと対照的に、失敗することはありません。 *)

Tactic Notation "clears" ident(X1) :=
  let rec doit _ :=
  match goal with
  | H:context[X1] |- _ => clear H; try (doit tt)
  | _ => clear X1
  end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
  clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
  clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
  clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) :=
  clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) ident(X6) :=
  clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.

(* clears （引数なし）は使われていないすべての変数をコンテキストからクリアします。 言い換えると、命題（型 Prop を持つもの）でもなく、別の仮定にもゴールにも現れないすべての変数を除去します。 *)

Ltac clears_tactic :=
  match goal with H: ?T |- _ =>
  match type of T with
  | Prop => generalizes H; (try clears_tactic); intro
  | ?TT => clear H; (try clears_tactic)
  | ?TT => generalizes H; (try clears_tactic); intro
  end end.

Tactic Notation "clears" :=
  clears_tactic.

(* clears_allは消すことができるすべての仮定をゴールからクリアします。 残るのは、ゴールで言及されている仮定だけです。 *)

Ltac clears_or_generalizes_all_core :=
  repeat match goal with H: _ |- _ =>
           first [ clear H | generalizes H] end.

Tactic Notation "clears_all" :=
  generalize ltac_mark;
  clears_or_generalizes_all_core;
  intro_until_mark.

(* clears_but H1 H2 .. HN clears all hypotheses except the one that are mentioned and those that cannot be cleared. *)

Ltac clears_but_core cont :=
  generalize ltac_mark;
  cont tt;
  clears_or_generalizes_all_core;
  intro_until_mark.

Tactic Notation "clears_but" :=
  clears_but_core ltac:(fun _ => idtac).
Tactic Notation "clears_but" ident(H1) :=
  clears_but_core ltac:(fun _ => gen H1).
Tactic Notation "clears_but" ident(H1) ident(H2) :=
  clears_but_core ltac:(fun _ => gen H1 H2).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3 H4).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) :=
  clears_but_core ltac:(fun _ => gen H1 H2 H3 H4 H5).

Lemma demo_clears_all_and_clears_but :
  forall x y:nat, y < 2 -> x = x -> x >= 2 -> x < 3 -> True.
Proof using.
  introv M1 M2 M3. dup 6.
  clears_all. auto.
  clears_but M3. auto.
  clears_but y. auto.
  clears_but x. auto.
  clears_but M2 M3. auto.
  clears_but x y. auto.
Qed.

(* clears_lastはコンテキストから最後の仮定をクリアします。 clears_last N は最後のN個の仮定をコンテキストからクリアします。 *)

Tactic Notation "clears_last" :=
  match goal with H: ?T |- _ => clear H end.

Ltac clears_last_base N :=
  match number_to_nat N with
  | 0 => idtac
  | S ?p => clears_last; clears_last_base p
  end.

Tactic Notation "clears_last" constr(N) :=
  clears_last_base N.

(* 開発目的のタクティック *)

(* サブゴールのスキップ *)


Tactic Notation "skip" :=
  admit.

(* demo is like admit but it documents the fact that admit is intended *)

Tactic Notation "demo" :=
  skip.

(* admits H: T は現在のコンテキストに型Tの仮定Hを追加します。 このときにHは無批判に真と仮定されます。 admit: T も構文として可能です。 なお、H は intro パターンでも構いません。 *)

Tactic Notation "admits" simple_intropattern(I) ":" constr(T) :=
  asserts I: T; [ skip | ].
Tactic Notation "admits" ":" constr(T) :=
  let H := fresh "TEMP" in admits H: T.
Tactic Notation "admits" "~" ":" constr(T) :=
  admits: T; auto_tilde.
Tactic Notation "admits" "*" ":" constr(T) :=
  admits: T; auto_star.

(* admit_cuts T は単に現在のゴールをTに置きかえます。 *)

Tactic Notation "admit_cuts" constr(T) :=
  cuts: T; [ skip | ].

(* admit_goal H は任意のゴールに適用できます。 単に現在のゴールを真と仮定します。 その仮定に "H" という名前を付けます。 帰納法(induction)や余帰納法(coinduction)による証明の準備のときに便利です。 構文 admit_goal も可能です。 *)

Tactic Notation "admit_goal" ident(H) :=
  match goal with |- ?G => admits H: G end.

Tactic Notation "admit_goal" :=
  let IH := fresh "IH" in admit_goal IH.

(* admit_rewrite T はTが等式のときに適用できます。 この等式を無批判に成立するものとし、ゴールをこの等式について書き換えします。 *)

Tactic Notation "admit_rewrite" constr(T) :=
  let M := fresh "TEMP" in admits M: T; rewrite M; clear M.

(* admit_rewrite T in H はadmit_rewriteと同様ですが、仮定Hを書き換える点が違います。 *)

Tactic Notation "admit_rewrite" constr(T) "in" hyp(H) :=
  let M := fresh "TEMP" in admits M: T; rewrite M in H; clear M.

(* admit_rewrites_all T は admit_rewrite と同様ですが、すべての場所（ゴールとすべての仮定）を書き換える点が違います。 *)

Tactic Notation "admit_rewrite_all" constr(T) :=
  let M := fresh "TEMP" in admits M: T; rewrite_all M; clear M.

(* forwards_nounfold_admit_sides_then E ltac:(fun K => ..) is like forwards: E but it provides the resulting term to a continuation, under the name K, and it admits any side-condition produced by the instantiation of E, using the skip tactic. *)

Inductive ltac_goal_to_discard := ltac_goal_to_discard_intro.

Ltac forwards_nounfold_admit_sides_then S cont :=
  let MARK := fresh "TEMP" in
  generalize ltac_goal_to_discard_intro;
  intro MARK;
  forwards_nounfold_then S ltac:(fun K =>
    clear MARK;
    cont K);
  match goal with
  | MARK: ltac_goal_to_discard |- _ => skip
  | _ => idtac
  end.



(* 標準ライブラリとのコンパチビリティ *)

(* モジュール Program は現在のモジュールと衝突する定義を含んでいます。 Program を直接または間接的に import するときには（Program を間接的に import するのは、例えば Setoid や ZArith を利用するときです）、トップレベルのコマンド Import LibTacticsCompatibility を行って、コンパチビリティの定義を import する必要があります。 *)

Module LibTacticsCompatibility.
  Tactic Notation "apply" "*" constr(H) :=
    sapply H; auto_star.
  Tactic Notation "subst" "*" :=
    subst; auto_star.
End LibTacticsCompatibility.

Open Scope nat_scope.
