# JonnyLean

人間が数学の目標を決め、AIが証明を作成し、Leanと別のAIで検証する数学ライブラリです。
初等整数論・組合せ論の5課題と、継続作業のためのローカルワーカーを備えています。
以前の別プロジェクトやTau Cetiのコード・監査ツールは流用していません。

## すぐに検証する

必要なものは **Python 3.11以上**、**elan / Lake** です。
Leanは `leanprover/lean4:v4.29.1` に固定し、Lean同梱ライブラリのみを使います。
MathlibやPython追加パッケージは不要です。AIを呼び出さず、保存された成果を再検証できます。

```sh
cd /Users/naoki/dev/JonnyLean
python3 tools/jonnylean.py run all
python3 -m unittest discover -s tests -v
```

別の場所にcloneした場合は、そのディレクトリを使います。
初回はelanが固定版のツールチェーンをダウンロードする場合があります。
[elan公式](https://github.com/leanprover/elan)を参照してください。

結果は `artifacts/index.html`、課題ごとの `artifacts/JL-00N/report.json` と `report.md` に保存します。
HTMLはブラウザでそのまま開ける、外部通信のないレポートです。

## 数学ライブラリ

| 課題 | 公開定理 | 仕様 |
| --- | --- | --- |
| JL-001 偶数どうしの和 | `JonnyLean.even_add` | [仕様](specs/JL-001.md) |
| JL-002 連続する自然数の積 | `JonnyLean.even_consecutive_product` | [仕様](specs/JL-002.md) |
| JL-003 三角数の公式 | `JonnyLean.triangular_formula` | [仕様](specs/JL-003.md) |
| JL-004 交わらない有限集合の和集合の濃度 | `JonnyLean.FiniteSet.card_union_of_disjoint` | [仕様](specs/JL-004.md) |
| JL-005 冪集合の濃度 | `JonnyLean.FiniteSet.card_powerset` | [仕様](specs/JL-005.md) |

有限集合は重複なしリストで表現します。順序による表現の違いで濃度が変わらないこと、
和集合のmembership、冪集合の部分集合性・網羅性・代表の一意性も証明しています。
JL-001〜003の主定理は公理依存なし。JL-004〜005はLean標準公理の `propext` と
`Quot.sound` に依存します。プロジェクトの許可リストはこの2つだけです。
`sorryAx`、独自公理、`Classical.choice` は許可しません。

`contracts/` は仕様を独立した型で述べ、実際の定理をその型に代入して確認します。
全数学モジュールを列挙して検査漏れを拒否し、私有・未使用の宣言も公理監査します。
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

# 最大5課題を順に処理し、合格したものを自動でローカルに取り込む
python3 tools/jonnylean.py work --loop 5 --adopt

# 独立した課題を最大2件同時に処理する（取り込みは別途）
python3 tools/jonnylean.py work --loop 5 --jobs 2

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
python3 tools/jonnylean.py verify all       # 機械検査のみ
python3 tools/jonnylean.py run all          # 機械検査＋保存されたAIレビュー
python3 tools/jonnylean.py review JL-003    # 1課題の再検証
python3 tools/jonnylean.py fingerprint all # レビュー対象の入力ハッシュ
python3 tools/jonnylean.py dashboard       # 保存結果からHTMLを更新
```

`run`や`review`はAIを新規に呼び出しません。新たな独立AIレビューには `work` を使います。
レビューは [7項目の基準](reviews/rubric.md) に沿って定義・量化・仮定・結論・証明・対象範囲・監査を確認します。
仕様、数学コード、契約、ツール、ワーカー、テスト、設定が変わると記録は失効します。
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

Leanの正常系、意図的な証明の破損、公理・仮定・定義の変更、検査漏れ、古いレビュー、
ワーカーの再試行・並列claim・予算・再開・取り込み競合・タイムアウトを検査します。
テスト用の合成AI応答は一時コピーの中だけで使い、実際のレビュー記録とは明確に区別します。

詳細は [設計](docs/architecture.md)、[課題追加手順](CONTRIBUTING.md)、
[数学ロードマップ](roadmaps/elementary.md) を参照してください。
