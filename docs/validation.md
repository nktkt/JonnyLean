# v1.0 検証記録

検証日: 2026-11-06（Asia/Tokyo）。ローカルのmacOS、Python 3.14.4、Lean 4.29.1、Codex CLI 0.166.0で確認。

## 数学と統合テスト

- `python3 tools/jonnylean.py verify all`: 全5課題合格。
- 対象: 6数学モジュール、67宣言。各課題の独立した契約と全ソースのstrict検査に成功。
- JL-001〜003の主定理の公理依存は空。JL-004〜005は`propext`、`Quot.sound`。
- `python3 -W error::ResourceWarning -m unittest discover -s tests -v`: **51件合格、130.979秒**。
- 内訳: 検証・レビュー27件、ワーカー17件、PR公開境界7件。
- 全テスト出力はローカル生成物`artifacts/test-output.txt`に保存。

## 実サービスを使ったワーカー実行

コマンド: `python3 tools/jonnylean.py work --task JL-001 --adopt`

成功ジョブ: `job-05475951025e4433`。状態`adopted`、CLI終了コード0。
作成担当と独立レビュー担当の2回のCodex呼出を行い、Lean検査を経てローカルに取り込んだ。
作成担当は既存のJL-001の証明を有効と判断し、ファイル変更案は0件だった。
独立レビュアーは7項目について根拠を記録し、未解決の指摘なしで承認した。
プロバイダーの報告使用量は合計382,859トークン。これは請求金額ではない。

初回の`job-aaa5e75279064052`では初期トークン予約量を超え、後続処理が停止した。
履歴は消去せず保持し、既定の予約量を実測に合わせて調整したうえで上記ジョブを実行した。

実行証跡は`.jonnylean/jobs/`に保存される（Git管理対象外）。
`report.json`、`verification.json`、`review.json`、呼出ごとの`events.jsonl`と構造化応答を確認できる。

## 確認範囲

GitHub公開境界のテストはネットワークを使わず、外部操作の呼出条件を検査した。
実際のリモート作成・push・PR公開は実施していない。
Linux上のGitHub Actionsの設定は同梱しているが、このローカル実行記録はmacOSでの結果である。
人間の数学的承認は記録していない。
