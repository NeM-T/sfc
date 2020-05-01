# Coq
~~[論理の基礎](https://www.chiguri.info/sfja/lf/)~~ [Software Foundations](https://www.chiguri.info/sfja/index.html)をやる。  
spacemacs+PG+company-coqの環境がすごくいい感じです。おすすめ  


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


clear H: 仮定Hをコンテキストから消去します。  
subst x: 変数xについて、コンテキストから仮定 x = e または e = x を発見し、xをコンテキストおよび現在のゴールのすべての場所でeに置き換え、この仮定を消去します。  
subst: x = e および e = x の形（xは変数）のすべての仮定を置換します。  
rename... into...: 証明コンテキストの仮定の名前を変更します。 例えば、コンテキストがxという名前の変数を含んでいるとき、rename x into y は、すべてのxの出現をyに変えます。  
assumption: ゴールにちょうどマッチする仮定Hをコンテキストから探そうとします。 発見されたときは apply H と同様に振る舞います。   
contradiction: Falseと同値の仮定Hをコンテキストから探そうとします。 発見されたときはゴールを解きます。  
constructor: 現在のゴールを解くのに使えるコンストラクタcを（現在の環境のInductiveによる定義から）探そうとします。 発見されたときは apply c と同様に振る舞います。  
