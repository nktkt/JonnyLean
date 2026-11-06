# JonnyLeanの構成

## 信頼と担当

- `specs/`, `contracts/`, `jonnylean.toml`: 課題の対象・命題・契約・依存関係。数学実装ワーカーは編集不可。
- `JonnyLean/`: 許可された数学ファイルだけを作成担当AIが提案。
- `tools/Audit.lean`: Leanの環境からモジュール、宣言、型、推移的公理依存を取得。
- `tools/jonnylean.py`: ビルド、契約、全ファイル網羅、公理、名前付き対象、レビューの現在性を検査。
- `worker/provider.py`: 読取専用Codex CLIの構造化出力。作成とレビューは別の呼出。
- `worker/engine.py`: スナップショット、許可パス、検証、レビュー記録、楽観的な取り込み。
- `worker/state.py`: SQLiteのclaim、lease、履歴、使用量予約と精算。
- `tools/reporting.py`: 現在性を確認した保存結果を外部通信なしのHTMLに出力。
- `tools/publish.py`: ローカルPR文面と、明示的な公開操作。

## 1件の状態遷移

`claimed → ready → generating → verifying → reviewing → verified → adopted`

作成・検証・レビューに失敗すると `retrying` を経て次の試行へ移る。
上限到達は `failed` または `budget_exhausted`、実行中断・lease失効は `interrupted`。
元データとの競合がある提案は取り込まず保持する。再開で過去の予算は消去しない。

## 永続データ

`.jonnylean/state.sqlite3` の `jobs`, `history`, `calls`, `daily` が状態と会計を保持する。
ジョブごとの `base.json` は作成時のソースのハッシュ、`workspace/` は候補ソース、
`verification.json` と `review.json` は検査と独立AIレビュー、`calls/` は実行証跡。
SQLiteトランザクションはclaimと予算予約を原子的に行い、リースをバックグラウンドで更新する。

検査のロックと取り込みのロックは `.jonnylean.lock` を共有する。
強制終了でロックが残る場合は、記録されたPIDの処理が終了したことを確認してから削除する。

## 変更とレビュー

レビューはファイルのSHA-256に結び付く。証明だけの変更やコメントも再レビューになる。
これは初期規模で単純に変更を見逃さないための選択であり、論理的同値性の比較ではない。
レビュー記録は自分自身をハッシュに含めず、表示・取り込み時に現在のレコードを別途確認する。
レビューの権限認証や保護ブランチ設定は外部GitHub運用の責務である。

## 運用上の境界

ワーカーは利用者が管理するローカルプロジェクトを処理する。Leanはビルド時にコードを実行できる。
パス制限と読取専用のAIセッションは、OSの隔離や独立証明検査器の代わりではない。
予算は予約と実測記録による次回呼出の制御。Codex CLIの単一呼出にはトークン数の絶対上限がなく、
時間上限はプロセス終了で実施する。日付境界はworker設定に従う。
