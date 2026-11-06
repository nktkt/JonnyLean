# v4の数学を使う

Lean側の入口は `JonnyLean.lean`、個々の主張の入口は `specs/` と `contracts/` です。
必要な分野のモジュールだけをimportすることもできます。各課題は主定理に加え、再利用する定義と補題を持ちます。

## 自然数上の有限線形代数

`JonnyLean.LinearAlgebra` は `Fin n → Nat` のベクトルと `Fin m → Fin n → Nat` の矩形行列を扱います。
次元を型に含めるため、行列積の内側の次元が一致することをLeanが確認します。次元0も許します。
有限和の交換から行列積の結合則を導き、単位行列、転置、行列とベクトルの積、対角行列、trace、冪、外積までつなぎます。

```lean
import JonnyLean.LinearAlgebra.Multiplication
open JonnyLean.LinearAlgebra

example {m n p q : Nat} (A : Mat m n) (B : Mat n p) (C : Mat p q) :
    mulMat (mulMat A B) C = mulMat A (mulMat B C) :=
  mulMat_assoc A B C
```

係数は自然数です。加法逆元・一般の行列逆・実ベクトル空間の基底理論はこの実装の対象外です。
ブロック行列は四つの矩形行列を持つ構造として表し、ベクトル対に作用します。

## 正規表現から実行できる照合器へ

`JonnyLean.RegularExpressions.Regex` は空言語、空語、1文字、和、連結、Kleene閉包を表します。
言語としての意味 `denotes` と、実行可能なBoolean関数 `accepts` を別々に定義しています。
文字を一つ読むごとに正規表現の微分を計算し、最後に空語を受理するかを調べます。
`accepts_correct` は任意の正規表現と任意長の語について、照合結果と意味が一致することを証明します。

```lean
import JonnyLean.RegularExpressions.Matcher
open JonnyLean.RegularExpressions

#eval accepts (.star (.atom 'a')) ['a', 'a'] -- true
#eval accepts (.star (.atom 'a')) ['a', 'b'] -- false

example {α : Type} [DecidableEq α] (r : Regex α) (w : List α) :
    accepts r w = true ↔ denotes r w := accepts_correct r w
```

正しさの証明は実行時間の上限を与えません。正規表現の微分が大きくなる場合の状態共有やDFA最小化は別の課題です。
`JonnyLean.Parsing` は値と未消費の接尾辞を返すパーサーを合成し、接尾辞保存や固定回数・燃料付き反復を証明します。
`many` の燃料は繰り返し回数の上限で、入力を消費しないパーサーにも定義できます。

## 命令型プログラムを仕様と結び付ける

`JonnyLean.Imperative` の状態は自然数の変数番号から自然数値への関数です。
代入・順次実行・条件分岐・whileを、終了する実行の導出 `Exec` と燃料付き関数 `run` で表します。
`run_sound` と `run_complete` により、成功する実行器と終了する意味論の関係を双方向に証明しています。
燃料は導出の高さを制限し、逐次命令の両側にはそれぞれ減らした燃料を渡します。
燃料切れは、そのプログラムが無限ループするという判定ではありません。

```lean
import JonnyLean.Imperative.Examples
open JonnyLean.Imperative

example (x : Nat) (s : State) :
    Exec (countdown x) s (update s x 0) ∧
      ∀ t, Exec (countdown x) s t → t = update s x 0 :=
  countdown_correct x s
```

Hoare論理は部分正当性です。「事前条件を満たし、終了したなら事後条件を満たす」と述べます。
代入・順次実行・分岐・while不変条件・非更新変数の保存に対応する規則があります。
カウントダウン、変数間の値の移送、累積和では、終了する導出の存在も別途構成して証明しています。

## 証明と契約をたどる

```sh
python3 tools/jonnylean.py catalog search 行列
python3 tools/jonnylean.py catalog search 正規表現
python3 tools/jonnylean.py library show JonnyLean.RegularExpressions.accepts_correct
python3 tools/jonnylean.py library search "run_sound" --kind theorem
python3 tools/jonnylean.py plan JL-300 --include-dependencies
```

`library` は現在の全体機械検証がある場合に実際のLeanの型を表示します。
自然言語仕様、契約、主定理、補助定理、公理監査を合わせて読み、課題が保証する範囲を確認できます。
