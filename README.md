# JonnyLean

人間が数学の目標を決め、AIが証明を作成し、Leanと別のAIで検証する数学ライブラリです。
初等整数論・組合せ論を起点とする **300課題・178数学モジュール・1121個の明示的な名前付き定理** と、継続作業のためのローカルワーカーを備えています。
数論、代数、論理、写像、関係、集合、アルゴリズム、グラフ、数え上げ、有限確率を扱います。
多項式の形式微分、二分木と永続データ構造、式の最適化とスタック機械コンパイラ、形式言語・オートマトン・有限測度を扱います。
v4では自然数上の有限線形代数、正規表現・パーサー・符号化、命令型言語の操作的意味論とHoare論理、検証記録付き配布アーカイブを追加しました。
以前の別プロジェクトやTau Cetiのコード・監査ツールは流用していません。

## すぐに検証する

必要なものは **Python 3.11以上**、**elan / Lake** です。
Leanは `leanprover/lean4:v4.29.1` に固定し、Lean同梱ライブラリのみを使います。
MathlibやPython追加パッケージは不要です。AIを呼び出さず、保存された成果を再検証できます。

```sh
cd /Users/naoki/dev/JonnyLean
python3 tools/jonnylean.py run all --jobs 4
python3 -m unittest discover -s tests -v
```

別の場所にcloneした場合は、そのディレクトリを使います。
初回はelanが固定版のツールチェーンをダウンロードする場合があります。
[elan公式](https://github.com/leanprover/elan)を参照してください。

結果は `artifacts/index.html`、課題ごとの `artifacts/JL-00N/report.json` と `report.md` に保存します。
HTMLはブラウザでそのまま開ける、外部通信のないレポートです。分野・状態・語句で絞り込めます。

## 数学ライブラリ

| 課題 | 分野・内容 |
| --- | --- |
| JL-001〜005 | 偶数、連続積、三角数、有限集合、冪集合 |
| JL-006〜025 | 整除、合同、冪、二次式、有限和、階乗、Fibonacci、アフィン写像 |
| JL-026〜035 | 述語、像・逆像、写像合成・逆写像、関係合成・閉包、不変条件 |
| JL-036〜045 | 分割、反転、有限集合演算、挿入ソート、状態走査、重複除去、探索 |
| JL-046〜054 | 有向グラフ、歩道、到達可能性、準同型、反転、連結成分、閉歩道、部分グラフ |
| JL-055〜060 | 語の列挙と濃度、部分列選択と二項係数、有限質量・離散分布 |
| JL-061〜080 | gcd・lcm、Euclid法の停止と正当性、既約対、剰余計算、有限積 |
| JL-081〜100 | 係数列多項式、畳み込み積、合成、差分商、形式微分・積則・連鎖律、Horner同時計算 |
| JL-101〜120 | 二分木の走査・鏡映・fold、永続stack・queue・連想map |
| JL-121〜140 | 式の評価・置換・最適化、スタック機械、コンパイル意味保存、静的深さ検査、逆コンパイル |
| JL-141〜160 | 構成的な言語代数、Kleene閉包、機械の走行・積・状態写像・不変量・有限carrier |
| JL-161〜180 | 積・部分列・順列・shuffleの計数、有限測度の押し出し・期待値分子・核の合成 |
| JL-181〜220 | 有限和・ベクトル・行列、積の結合則、転置、対角・ブロック行列、trace、行列冪・外積 |
| JL-221〜260 | 正規表現の微分と照合の正しさ、パーサー合成、接頭辞解析、符号化と復号の往復 |
| JL-261〜300 | 状態・式・命令、big-step意味論、燃料付き実行器、Hoare論理、不変条件、検証済みプログラム |

```sh
python3 tools/jonnylean.py catalog list
python3 tools/jonnylean.py catalog search fibonacci
python3 tools/jonnylean.py catalog show JL-042
python3 tools/jonnylean.py catalog graph --format mermaid
python3 tools/jonnylean.py catalog stats
python3 tools/jonnylean.py plan JL-100 --include-dependencies
python3 tools/jonnylean.py library search "derivative evaluate" --kind theorem
python3 tools/jonnylean.py library export --format json > artifacts/declarations.json
python3 tools/jonnylean.py run all --domain graph-theory
python3 tools/jonnylean.py verify all --tag cardinality
python3 tools/jonnylean.py run all --changed HEAD
```

[全課題一覧](roadmaps/elementary.md)から仕様・Lean証明・契約に移動できます。
新分野の型・定理・実行例は [v4の数学を使う](docs/mathematics.md) を参照してください。
`catalog/fragments/` を原本として、`catalog sync` がレジストリと集約importを再生成します。
`catalog check` は登録との不一致を検出します。並列検証・CI分割・実際の定理型の検索は [大規模運用ガイド](docs/platform.md) を参照してください。課題の追加は [CONTRIBUTING](CONTRIBUTING.md) を参照。
`--changed` はGit参照からの変更と未追跡ファイルを含み、影響する課題を選びます。
選択にかかわらず、機械監査はライブラリ全体を対象にします。

有限集合は重複なしリストで表現します。順序による表現の違いで濃度が変わらないこと、
和集合のmembership、冪集合の部分集合性・網羅性・代表の一意性も証明しています。
JL-001〜003の主定理は公理依存なし。JL-004〜005はLean標準公理の `propext` と
`Quot.sound` に依存します。プロジェクトの許可リストはこの2つだけです。
`sorryAx`、独自公理、`Classical.choice` は許可しません。

閉歩道は頂点が重複しない単純サイクルとは区別します。有限確率は自然数の重みと正の総質量による
未約分の分数表現です。v3の有限測度も自然数重みの有限リストを使い、期待値は分子を扱います。
多項式の導関数は形式微分です。オートマトンは一般状態機械の法則と有限carrierに制限する定理を区別します。
実数の解析や一般の測度論は実装範囲に含めません。

`contracts/` は仕様を独立した型で述べ、実際の定理をその型に代入して確認します。
全数学モジュールを列挙して検査漏れを拒否し、私有・未使用の宣言も公理監査します。
契約も原文をstrict検査し、Leanの監査コードを加えた一時コピーで私有・未使用を含むローカル宣言の公理を調べます。
匿名の例は環境に保存されない場合があるため、全数学ソースと契約を警告がエラーになる
設定でも再検査します。採用する成果は名前付き定理です。

## AIワーカーを使う

Codex CLIをインストールし、`codex login` を済ませます。既存のChatGPTログインを使えます。
Codex実行の仕様は[公式ドキュメント](https://learn.chatgpt.com/docs/developer-commands#codex-exec)に基づきます。

```sh
# 認証・ツール・設定を確認
python3 tools/jonnylean.py doctor

# 1課題を作成担当 → Lean検査 → 独立レビューまで処理
python3 tools/jonnylean.py work --task JL-001

# 状態、履歴、使用量を確認
python3 tools/jonnylean.py status
python3 tools/jonnylean.py report JOB_ID

# 検証とAIレビューを通った提案をローカルに取り込む
python3 tools/jonnylean.py adopt JOB_ID

# 最大60課題を順に処理し、合格したものを自動でローカルに取り込む
python3 tools/jonnylean.py work --loop 60 --adopt

# 独立した課題を最大2件同時に処理する（取り込みは別途）
python3 tools/jonnylean.py work --loop 5 --jobs 2

# 分野・タグを指定して処理（依存課題は先にadoptが必要）
python3 tools/jonnylean.py work --domain number-theory --loop 10 --adopt

# 中断・失敗したジョブを同じ履歴と予算で再開
python3 tools/jonnylean.py resume JOB_ID
```

各ジョブは `.jonnylean/jobs/JOB_ID/workspace/` にソースだけを複製します。
ビルド生成物や状態フォルダを再帰的にコピーしません。SQLiteの原子的なclaimと
定期更新するleaseにより、同じ課題の二重処理を防ぎます。

AI作成担当は読取専用の新しいCodexセッションで、許可されたLeanファイルの置換案をJSONで返します。
仕様、契約、設定、検査ツール、レビュー記録の変更は提案できません。
ホスト側が変更を適用してLeanで検証し、別の新しいCodexセッションで7項目のレビューを行います。
入力ハッシュと実際の呼出履歴はホスト側が記録します。モデル名は実行側から報告された場合だけ記録します。

失敗時は理由を次の試行へ渡し、最大3回まで修正します。認証やプロバイダーのエラーも履歴に残します。
`resume`は試行回数・経過時間・使用量をリセットしません。期限を使い切ったジョブは新規ジョブが必要です。
キューは過去に処理した課題を黙って繰り返さず、依存課題の取り込みを待ちます。
明示的な `--task` は新しいジョブの作成要求ですが、依存条件は満たす必要があります。

取り込み時には元ソースが変わっていないことを確認します。並列作業の後で元ソースが変わった場合は
古い提案の取り込みを拒否し、検証済み候補を保存します。新しい元ソースで再実行してください。
共有定義の変更で他課題のレビューが古くなった場合、`run all` が再レビューの必要を表示します。

## 時間・使用量・予算

`worker.toml` に、呼出時間、ジョブ時間、試行回数、呼出回数、トークン予算、日次予算を設定します。
開始前にSQLiteで予算を予約するため、並列ジョブが同じ残予算を重複使用しません。
取得できたトークン数はCodexのイベントから記録し、不明な呼出は予約分を保持します。

USD表示は設定した単価による**ローカルの見積り**です。設定中の単価は予算計算用の仮定値で、
OpenAIの現在の価格やChatGPT契約の請求額を表しません。
Codex CLIの1呼出にサーバー側のトークン上限を設定する機能は使っていないため、実測で予約量を
超えたときは記録して後続呼出を止めます。1呼出中の超過を絶対に防ぐ費用上限ではありません。
時間上限ではプロセスと子プロセスを終了させます。

## 検証・レビュー・レポート

```sh
python3 tools/jonnylean.py verify all --jobs 4 # 機械検査のみ
python3 tools/jonnylean.py run all --jobs 4    # 機械検査＋保存されたAIレビュー
python3 tools/jonnylean.py review JL-003    # 1課題の再検証
python3 tools/jonnylean.py fingerprint all # レビュー対象の入力ハッシュ
python3 tools/jonnylean.py dashboard       # 保存結果からHTMLを更新
python3 tools/jonnylean.py release status  # 全課題の配布準備状態
python3 tools/jonnylean.py release build artifacts/JonnyLean-v4.zip
python3 tools/jonnylean.py release check artifacts/JonnyLean-v4.zip
```

`run`や`review`はAIを新規に呼び出しません。新たな独立AIレビューには `work` を使います。
レビューは [7項目の基準](reviews/rubric.md) に沿って定義・量化・仮定・結論・証明・対象範囲・監査を確認します。
課題自身と依存先の仕様・数学コード、課題の契約、関連メタデータが変わると、その範囲のレビューが失効します。
検査ツール・ワーカー・テスト・公理方針などの共通基盤の変更は全レビューを失効させます。
機械検証は別の全体ハッシュに結び付け、どこかの検証入力が変われば保存結果を古いものとして表示します。
CIが入力ハッシュを更新するだけで自動承認する処理はありません。

レビューはAIによる自己申告です。本人認証・電子署名・自然言語との同値性の機械証明ではありません。
人間の承認は別情報として未記録と表示します。Leanのツールチェーンとローカル実行環境を信頼する方式で、
独立カーネルによる再検証や敵対的LeanコードのOS隔離を提供するものではありません。
作業領域の分離、パス制限、メタコマンドの制限は作業範囲を制御する機能です。

終了コード: **0 合格、1 検査・レビュー不合格、2 設定や実行のエラー**。
Leanコンパイル失敗・契約不一致も2になります。いずれもCIでは不合格です。
各呼出の出力、プロンプト、構造化応答、使用量は `.jonnylean/` に保存します。
これはGit管理対象外です。

## GitHubとの連携

```sh
# 全課題を再検証し、PRのタイトルと本文をローカルに作成
python3 tools/jonnylean.py pr

# 公開先を明示し、コミット済みcodex/ブランチをpushしてdraft PRを作成
python3 tools/jonnylean.py pr --publish --repo OWNER/REPOSITORY --base main
```

通常の `pr` は公開しません。`--publish` は `origin` と指定先の一致、作業ツリーがcleanであること、
ベースとの差分を確認します。既存の同ブランチのPRがあればそのURLを返します。
GitHub CLIの認証と、利用者が設定したリモートリポジトリが必要です。
自動マージは行いません。GitHub Actionsは全課題の検査と統合テストを実行します。

## 開発

```sh
python3 -m unittest discover -s tests -v
```

並列契約検査、入力の同時変更、依存の展開、CI分割、監査済みの型検索、Leanの正常系、意図的な証明の破損、公理・仮定・定義の変更、検査漏れ、古いレビュー、
ワーカーの再試行・並列claim・予算・再開・取り込み競合・タイムアウトを検査します。
テスト用の合成AI応答は一時コピーの中だけで使い、実際のレビュー記録とは明確に区別します。

実行済みの検査・実AIワーカーの結果は [検証記録](docs/validation.md) にまとめています。

詳細は [設計](docs/architecture.md)、[課題追加手順](CONTRIBUTING.md)、
[数学ロードマップ](roadmaps/elementary.md) を参照してください。
