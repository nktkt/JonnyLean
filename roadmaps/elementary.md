# JonnyLean v2 数学ライブラリ

60課題を実装。各課題に日本語仕様、Leanの名前付き定理、独立した契約を備える。機械検証とAIレビューの実結果は生成レポートを参照。

| ID | 内容 | Lean実装 | 契約 |
| --- | --- | --- | --- |
| [JL-001](../specs/JL-001.md) | 偶数どうしの和は偶数 | [証明](../JonnyLean/NumberTheory/Parity.lean) | [契約](../contracts/JL001.lean) |
| [JL-002](../specs/JL-002.md) | 連続する自然数の積は偶数 | [証明](../JonnyLean/NumberTheory/Consecutive.lean) | [契約](../contracts/JL002.lean) |
| [JL-003](../specs/JL-003.md) | 三角数の和の公式 | [証明](../JonnyLean/NumberTheory/Triangular.lean) | [契約](../contracts/JL003.lean) |
| [JL-004](../specs/JL-004.md) | 交わらない有限集合の和集合の要素数 | [証明](../JonnyLean/FiniteSet/Basic.lean) | [契約](../contracts/JL004.lean) |
| [JL-005](../specs/JL-005.md) | 冪集合の要素数 | [証明](../JonnyLean/FiniteSet/Powerset.lean) | [契約](../contracts/JL005.lean) |
| [JL-006](../specs/JL-006.md) | 自然数の偶奇分解 | [証明](../JonnyLean/NumberTheory/OddSums.lean) | [契約](../contracts/JL006.lean) |
| [JL-007](../specs/JL-007.md) | 平方の偶数性と元の偶数性 | [証明](../JonnyLean/NumberTheory/ParityProducts.lean) | [契約](../contracts/JL007.lean) |
| [JL-008](../specs/JL-008.md) | 整除の積への保存 | [証明](../JonnyLean/NumberTheory/Divisibility.lean) | [契約](../contracts/JL008.lean) |
| [JL-009](../specs/JL-009.md) | 整除の自然数線形結合 | [証明](../JonnyLean/NumberTheory/DivisibilitySums.lean) | [契約](../contracts/JL009.lean) |
| [JL-010](../specs/JL-010.md) | 相互整除の反対称性 | [証明](../JonnyLean/NumberTheory/DivisibilityOrder.lean) | [契約](../contracts/JL010.lean) |
| [JL-011](../specs/JL-011.md) | 合同類の標準剰余の一意性 | [証明](../JonnyLean/NumberTheory/Congruence.lean) | [契約](../contracts/JL011.lean) |
| [JL-012](../specs/JL-012.md) | 二次多項式による合同の保存 | [証明](../JonnyLean/NumberTheory/CongruenceOperations.lean) | [契約](../contracts/JL012.lean) |
| [JL-013](../specs/JL-013.md) | 累乗列の整除と順序 | [証明](../JonnyLean/NumberTheory/Powers.lean) | [契約](../contracts/JL013.lean) |
| [JL-014](../specs/JL-014.md) | 自然数の平方展開 | [証明](../JonnyLean/Algebra/Quadratic.lean) | [契約](../contracts/JL014.lean) |
| [JL-015](../specs/JL-015.md) | 有限和がゼロとなる条件 | [証明](../JonnyLean/Algebra/FiniteSum.lean) | [契約](../contracts/JL015.lean) |
| [JL-016](../specs/JL-016.md) | 有限和の線形性 | [証明](../JonnyLean/Algebra/SumLinearity.lean) | [契約](../contracts/JL016.lean) |
| [JL-017](../specs/JL-017.md) | 有限和の区間分割 | [証明](../JonnyLean/Algebra/SumIntervals.lean) | [契約](../contracts/JL017.lean) |
| [JL-018](../specs/JL-018.md) | 連続する奇数の区間和 | [証明](../JonnyLean/Algebra/OddSum.lean) | [契約](../contracts/JL018.lean) |
| [JL-019](../specs/JL-019.md) | 等比和の除算を使わない公式 | [証明](../JonnyLean/Algebra/GeometricSum.lean) | [契約](../contracts/JL019.lean) |
| [JL-020](../specs/JL-020.md) | 階乗の単調性 | [証明](../JonnyLean/NumberTheory/Factorial.lean) | [契約](../contracts/JL020.lean) |
| [JL-021](../specs/JL-021.md) | 階乗による小さい正整数の整除 | [証明](../JonnyLean/NumberTheory/FactorialDivisibility.lean) | [契約](../contracts/JL021.lean) |
| [JL-022](../specs/JL-022.md) | Fibonacci 数列の前方和 | [証明](../JonnyLean/NumberTheory/Fibonacci.lean) | [契約](../contracts/JL022.lean) |
| [JL-023](../specs/JL-023.md) | Fibonacci の加法公式と倍角公式 | [証明](../JonnyLean/NumberTheory/FibonacciAddition.lean) | [契約](../contracts/JL023.lean) |
| [JL-024](../specs/JL-024.md) | 単調列の差分和 | [証明](../JonnyLean/Algebra/Telescoping.lean) | [契約](../contracts/JL024.lean) |
| [JL-025](../specs/JL-025.md) | アフィン写像の反復の閉形式 | [証明](../JonnyLean/Algebra/Affine.lean) | [契約](../contracts/JL025.lean) |
| [JL-026](../specs/JL-026.md) | 述語の束と分配法則 | [証明](../JonnyLean/Logic/Predicates.lean) | [契約](../contracts/JL026.lean) |
| [JL-027](../specs/JL-027.md) | 像と逆像の随伴関係 | [証明](../JonnyLean/Logic/Images.lean) | [契約](../contracts/JL027.lean) |
| [JL-028](../specs/JL-028.md) | 単射写像の像と共通部分 | [証明](../JonnyLean/Logic/InjectiveImages.lean) | [契約](../contracts/JL028.lean) |
| [JL-029](../specs/JL-029.md) | 写像の合成と全単射 | [証明](../JonnyLean/Functions/Composition.lean) | [契約](../contracts/JL029.lean) |
| [JL-030](../specs/JL-030.md) | 左右の逆写像の一意性 | [証明](../JonnyLean/Functions/Inverses.lean) | [契約](../contracts/JL030.lean) |
| [JL-031](../specs/JL-031.md) | レトラクションと冪等写像 | [証明](../JonnyLean/Functions/Retractions.lean) | [契約](../contracts/JL031.lean) |
| [JL-032](../specs/JL-032.md) | 反射推移閉包の最小性 | [証明](../JonnyLean/Relations/Closure.lean) | [契約](../contracts/JL032.lean) |
| [JL-033](../specs/JL-033.md) | 二項関係の合成代数 | [証明](../JonnyLean/Relations/Composition.lean) | [契約](../contracts/JL033.lean) |
| [JL-034](../specs/JL-034.md) | 核関係と明示的切断による因子分解 | [証明](../JonnyLean/Relations/Kernels.lean) | [契約](../contracts/JL034.lean) |
| [JL-035](../specs/JL-035.md) | 到達関係による不変条件の保存 | [証明](../JonnyLean/Relations/Invariants.lean) | [契約](../contracts/JL035.lean) |
| [JL-036](../specs/JL-036.md) | 安定分割の保存性と分離 | [証明](../JonnyLean/Collections/Partition.lean) | [契約](../contracts/JL036.lean) |
| [JL-037](../specs/JL-037.md) | 末尾再帰の反転と蓄積変数 | [証明](../JonnyLean/Collections/ReverseAccumulator.lean) | [契約](../contracts/JL037.lean) |
| [JL-038](../specs/JL-038.md) | 有限集合の共通部分と分配則 | [証明](../JonnyLean/Collections/Intersection.lean) | [契約](../contracts/JL038.lean) |
| [JL-039](../specs/JL-039.md) | 有限集合の差による濃度分解 | [証明](../JonnyLean/Collections/Difference.lean) | [契約](../contracts/JL039.lean) |
| [JL-040](../specs/JL-040.md) | 有限集合の単射像と包含反映 | [証明](../JonnyLean/Collections/InjectiveImage.lean) | [契約](../contracts/JL040.lean) |
| [JL-041](../specs/JL-041.md) | 挿入ソートの順列保存 | [証明](../JonnyLean/Algorithms/InsertionSort.lean) | [契約](../contracts/JL041.lean) |
| [JL-042](../specs/JL-042.md) | 挿入ソートの整列性と冪等性 | [証明](../JonnyLean/Algorithms/SortCorrectness.lean) | [契約](../contracts/JL042.lean) |
| [JL-043](../specs/JL-043.md) | 状態付き走査の不変条件 | [証明](../JonnyLean/Algorithms/StateTraversal.lean) | [契約](../contracts/JL043.lean) |
| [JL-044](../specs/JL-044.md) | 重複除去と有限集合の構成 | [証明](../JonnyLean/Algorithms/Deduplicate.lean) | [契約](../contracts/JL044.lean) |
| [JL-045](../specs/JL-045.md) | 最初の一致の探索証明書 | [証明](../JonnyLean/Algorithms/FirstMatch.lean) | [契約](../contracts/JL045.lean) |
| [JL-046](../specs/JL-046.md) | 有向グラフの構成と包含の反対称性 | [証明](../JonnyLean/GraphTheory/Basic.lean) | [契約](../contracts/JL046.lean) |
| [JL-047](../specs/JL-047.md) | 端点付き歩道と頂点列の長さ | [証明](../JonnyLean/GraphTheory/Walk.lean) | [契約](../contracts/JL047.lean) |
| [JL-048](../specs/JL-048.md) | 歩道の連結と結合則 | [証明](../JonnyLean/GraphTheory/Append.lean) | [契約](../contracts/JL048.lean) |
| [JL-049](../specs/JL-049.md) | 到達可能性と反射推移閉包の最小性 | [証明](../JonnyLean/GraphTheory/Reachability.lean) | [契約](../contracts/JL049.lean) |
| [JL-050](../specs/JL-050.md) | グラフ準同型による歩道の輸送 | [証明](../JonnyLean/GraphTheory/Morphism.lean) | [契約](../contracts/JL050.lean) |
| [JL-051](../specs/JL-051.md) | 無向グラフの歩道反転 | [証明](../JonnyLean/GraphTheory/Reverse.lean) | [契約](../contracts/JL051.lean) |
| [JL-052](../specs/JL-052.md) | 相互到達可能性による強連結成分 | [証明](../JonnyLean/GraphTheory/Components.lean) | [契約](../contracts/JL052.lean) |
| [JL-053](../specs/JL-053.md) | 閉歩道の反復と始点の移動 | [証明](../JonnyLean/GraphTheory/ClosedWalk.lean) | [契約](../contracts/JL053.lean) |
| [JL-054](../specs/JL-054.md) | 部分グラフでの到達可能性と空グラフ | [証明](../JonnyLean/GraphTheory/Subgraph.lean) | [契約](../contracts/JL054.lean) |
| [JL-055](../specs/JL-055.md) | 有限アルファベット上の語の列挙 | [証明](../JonnyLean/Combinatorics/Words.lean) | [契約](../contracts/JL055.lean) |
| [JL-056](../specs/JL-056.md) | 有限語の計数と積の法則 | [証明](../JonnyLean/Combinatorics/WordCount.lean) | [契約](../contracts/JL056.lean) |
| [JL-057](../specs/JL-057.md) | 順序を保つ位置の選択列挙 | [証明](../JonnyLean/Combinatorics/Selections.lean) | [契約](../contracts/JL057.lean) |
| [JL-058](../specs/JL-058.md) | 二項係数と位置選択の個数 | [証明](../JonnyLean/Combinatorics/Binomial.lean) | [契約](../contracts/JL058.lean) |
| [JL-059](../specs/JL-059.md) | 自然数重み付き有限質量と事象の加法性 | [証明](../JonnyLean/DiscreteProbability/Mass.lean) | [契約](../contracts/JL059.lean) |
| [JL-060](../specs/JL-060.md) | 有限計数分布の正規化と補事象 | [証明](../JonnyLean/DiscreteProbability/Distribution.lean) | [契約](../contracts/JL060.lean) |

全課題はLean 4.29.1同梱ライブラリのみを利用する。許可する公理依存は propext と Quot.sound。
グラフは型一般の有向グラフで、閉歩道と単純サイクルを区別する。有限確率は自然数重みの有限分布である。

今後の追加候補: 素数と最大公約数、二項定理、多重集合、有限グラフの木・彩色、期待値の有限和。これらは未実装であり、上記60課題の完成状態と区別する。
