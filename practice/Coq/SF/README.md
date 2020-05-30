# Coq
~~[論理の基礎](https://www.chiguri.info/sfja/lf/)~~ [Software Foundations](https://www.chiguri.info/sfja/index.html)をやる。  
spacemacs+PG+company-coqの環境がすごくいい感じです。おすすめ  

Coqはversion 8.11.0 を使用しています。  

### tactics
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


## 拡張tactics
SSReflect は強力なタクティックを提供する別のパッケージです。 ライブラリ"LibTactics"は"SSReflect"と次の2点で異なります:  
* "SSReflect"は主として数学の定理を証明するために開発されました。 一方、"LibTactics"は主としてプログラミング言語の定理の証明のために開発されました。 特に"LibTactics"は、"SSReflect"パッケージには対応するものがない、 いくつもの有用なタクティックを提供します。
* "SSReflect"はタクティックの提示方法を根底から考え直しています。 一方、"LibTactics"はCoqタクティックの伝統的提示方法をほとんど崩していません。 このことからおそらく"LibTactics"の方が"SSReflect"よりとっつきやすいと思われます。

[ソフトウェアの基礎](https://www.chiguri.info/sfja/plf/UseTactics.html)からLibTacticsの概要を転載  
* inversionの名前付けをよりよくするintrovとinverts。
* 証明できないゴールを捨てやすくするfalseとtryfalse。
* 先頭の定義を展開する（unfoldする）unfolds。
* 帰納法の状況を整えやすくするgen。
* 場合分けをよりよくするcasesとcases_if。
* n-引数コンストラクタを扱うsplitsとbranch。
* 等価性を扱いやすくするasserts_rewrite、cuts_rewrite、substs、fequals。
* 補題の具体化と使用方法を表現するlets、forwards、specializes、applys。
* 補題を適用する前に行う書き換えを自動化するapplys_eq。
* 柔軟に集中、無視するサブゴールを選ぶadmits、admit_rewrite、admit_goal。

もし LibTactics.v を自分の作る証明に使いたい場合は、 http://www.chargueraud.org/softs/tlc/ から最新版を取得してください。  

## 自動化tactics
* auto は reflexivity、assumption、apply を自動で適用します。
* eauto は eapply を使い、また途中で得られた存在限量を具体化しようとします。
* iauto は eauto を拡張して、論理否定、論理積、論理和に対応したものです。 ただし、論理和に対しては指数的に遅くなりえます。
* jauto は eauto を拡張して、論理否定、論理積、仮定の先頭に来る存在限量に対応したものです。
* congruence は等式や不等式の解決に役立ちます。
* omega は算術式と等式や不等式によるゴールを証明しますが、乗算には対応していません。
* ring は乗算を含む算術式の等式について証明しますが、不等式には対応していません。


自動化を調整するために、以下の大まかなルールを気にとめておいてください。
* 自動化はバランスが大事です。 自動化が不十分だと証明が変更に弱くなりますが、自動化しすぎると壊れたときに直せなくなります。
* 補題がゴール指向でない（帰結に出現しないような変数がある）場合、変数の具体化する対象を示す前提が必要です。 このとき、より適切に具体化しそうな前提から順に書きましょう。
* False が帰結であるような補題は、現在のセクションだけのヒント（local hint）として利用しましょう。
* 推移律の補題はヒントとして使わないようにしましょう。 どうしても必要ならば、Extern Hintを設定しましょう。
* 定義には一緒に Hint Unfold を付けましょう。

