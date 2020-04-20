# Coq
[論理の基礎](https://www.chiguri.info/sfja/lf/)をやる。  
CoqIDEおよび、neovimに[coqpit.vim](https://github.com/LumaKernel/coqpit.vim)を入れて用いている。  
~~coqpitはrewriteがうまくいかないので該当する部分がある場合にCoqIDEをつかいます。~~  
できるようになったのでCoqIDEを使う必要はないかもしれないが、coqpitは`From LF Require Export`ができず、`Require Import`にする必要があるが、色々面倒なのでCoqIDEを使う。  
coqpitディレクトリにはMAPS以降の章で以前の章との依存関係のないcoqpitで動くものを入れていきます。。  
spacemacsとProof Generalでやりはじめました。いい感じだったらこっちにします。  


intros: 仮説や変数をゴールからコンテキストに移動させる  
reflexivity: 反射的に証明を終わらせる（ゴールがe=eのように見えるとき  
apply: 仮説、リーマ、コンストラクターを使って目標を証明する。  
apply... in H: 文脈の中で仮説、リーマ、コンストラクターを仮説に適用する (前方推論)  
apply... with... : パターンマッチングでは決定できない変数の値を明示的に指定します。  
simpl: ゴールでの計算を単純化します。  
simpl in H: ... or a hypothesis  
rewrite: 等価仮説(またはリーマ)を使用して、ゴールを書き換えます。  
rewrite in H  
symmetry: t=u の形のゴールを u=t に変更します。  
symmetry in H: t=u の形式の仮説を u=t に変える  
unfold: 定義された定数をゴールの右辺に置き換えます。  
unfold... in H ：...または仮説  
destruct... as...：帰納的に定義された型の値の場合の解析  
destruct... eqn:...：コンテキストに追加する方程式の名前を指定し、ケース分析の結果を記録します。  
induction... as...：帰納的に定義された型の値に対する帰納法  
injection: 帰納的に定義された型の値の間の等質性に対する注入性による推論  
discriminate: 帰納的に定義された型の値の間の等質性に関するコンストラクタの不連続性による推論  
assert(H: e) (あるいは(eをHとしてアサート) : "ローカル・レンマ" eを導入してHと呼ぶ  
generalize dependent x:：変数x（およびそれに依存する他のすべてのもの）をコンテキストからゴール式の明示的な仮説に戻す。
