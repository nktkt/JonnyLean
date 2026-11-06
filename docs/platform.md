# 多数の課題を扱う

数学の仕様と証明は課題ごとに管理し、機械監査は選択範囲にかかわらずライブラリ全体に行います。
以下のコマンドはJonnyLeanのルートで実行します。AIを呼び出すのは `work` と `resume` です。

## 検証する範囲を先に見る

```sh
python3 tools/jonnylean.py plan all
python3 tools/jonnylean.py plan JL-100 --include-dependencies
python3 tools/jonnylean.py plan all --domain polynomials --format json
python3 tools/jonnylean.py plan all --changed HEAD --include-dependencies
```

`plan` は依存関係の層、選択外の前提課題、分野別件数を表示します。
ビルド、AI呼出、使用量の予約、取り込みは行いません。
`--include-dependencies` は推移的な依存課題を追加します。
同じモジュールの複数定理を別課題として扱う場合もあり、課題数とモジュール数は一致するとは限りません。

通常の機械検証はLeanのimport先をビルドするので、前提課題のワーカージョブがなくても実行できます。
AIワーカーのキューは前提課題のジョブが `adopted` であることを別途要求します。
依存関係の層は数学上の順序であり、ワーカーが既に採用した課題の一覧ではありません。

## 並列検証

```sh
python3 tools/jonnylean.py verify all --jobs 4
python3 tools/jonnylean.py run all --jobs 4
python3 tools/jonnylean.py run JL-100 --include-dependencies --jobs 4
```

`--jobs` は1〜16です。最初に新しい全体ビルド・公理監査・ソース検査を成功させ、その呼出中の結果を共有して
課題ごとの契約を並列に検査します。ソースのstrict検査も並列化します。1課題の契約が不合格でも他の契約は検査します。
ライブラリ自体のビルドや監査が不合格なら、その同じ失敗を選択課題に伝え、課題数分の無意味な再ビルドを避けます。
過去の保存レポートを新たなコンパイルの代わりにはしません。

バッチ開始時の全体fingerprintを固定し、課題間や並列実行中に入力が変われば不合格にします。
結果は各課題の `report.json` と `artifacts/batch.json` に記録します。
後者には選択課題、並列数、終了コード、実時間、入力が安定していたかを保存します。
CLIのプロジェクトロックはバッチ終了まで維持します。

## CIでの分割

```sh
python3 tools/jonnylean.py plan all --shard 1/4 --format json
python3 tools/jonnylean.py run all --shard 1/4 --jobs 2
```

`I/N` は1始まりです。選択課題をID順に並べ、順番にN個の分割へ振り分けるので、同じ選択集合なら分割は重ならず、
全分割の和が元の集合になります。依存追加は分割より先に行います。
各分割は全ライブラリを監査し、自分の分割に入る課題の契約とレビューを検査します。
並列のCIジョブには独立したチェックアウトを使ってください。同じディレクトリで複数CLIを同時実行する用途ではありません。
空の選択は「検証未実行」と明示して終了し、全課題合格という意味にはしません。

## コンパイルされた宣言を検索する

```sh
python3 tools/jonnylean.py library search "derivative evaluate" --kind theorem
python3 tools/jonnylean.py library show JonnyLean.Polynomials.evaluate_derivative_cons
python3 tools/jonnylean.py library stats --module JonnyLean.VerifiedPrograms
python3 tools/jonnylean.py library export --format json > artifacts/declarations.json
python3 tools/jonnylean.py library export --module JonnyLean.Polynomials --format markdown > artifacts/polynomials-api.md
```

`catalog` は登録課題を検索します。`library` は名前付き補題、定義、帰納型、Leanが生成した宣言も含む監査結果から、
名前・実際の型・モジュール・公理依存を表示します。語句検索は名前と型へのAND検索、モジュール指定は接頭辞による絞り込みです。
現在の全体入力に一致する機械検証済みレポートが必要です。未実行・古い結果しかない場合は検索を拒否します。
検索や書き出し自体は再検証やAIレビューを行いません。保存レポートの信頼境界は他のローカル成果物と同じです。

## 変更時のレビュー

証明や定義を変えると、そのモジュールに依存する課題のレビューが古くなります。
共通の検査基盤を変えた場合は全課題のレビューが古くなります。
ハッシュを書き換えて承認を維持するのではなく、担当以外のレビュアーが変更の意味を確認して新しい根拠を残します。
仕様モデルを別のLeanモジュールに置く場合も、契約からimportし、ワーカーの `editable` に含めないことで保護します。

## 検証記録付きの配布アーカイブ

```sh
python3 tools/jonnylean.py release status
python3 tools/jonnylean.py run all --jobs 4
python3 tools/jonnylean.py release build artifacts/JonnyLean-v4.zip
python3 tools/jonnylean.py release check artifacts/JonnyLean-v4.zip
# 別途受け取ったアーカイブ全体のSHA-256とも照合する場合
python3 tools/jonnylean.py release check artifacts/JonnyLean-v4.zip --sha256 SHA256_HEX
```

`release status` は全課題の現在の機械検証・AIレビューとカタログ生成結果を読み、準備不足の課題と理由をJSONで返します。
準備済みは終了コード0、準備不足は1、設定・実行エラーは2です。LeanやAIを新規に実行せず、ファイルを書き換えません。

`release build` は全課題が現在の入力で合格している場合だけ、ソース・仕様・契約・レビュー・運用文書・CI設定をZIPにまとめます。
`source/` は展開して `python3 tools/jonnylean.py run all --jobs 4` を実行できるプロジェクトです。
固定版Leanのインストールは別途必要です。`.lake`、`.git`、`.jonnylean` とAI呼出履歴は含めません。

`evidence/` には全ライブラリの宣言監査を1コピー、課題ごとの実際の型と契約監査、入力ハッシュを保存します。
同じ依存範囲は内容のSHA-256で共有し、全体監査を課題数分複製しません。実行ログや経過時間は配布証跡に含めず、元の `artifacts/` に保持します。
ファイル順・ZIP時刻・権限を固定するので、同じソースと証跡から同じPython/zlib環境で同じバイト列を作れます。
プロジェクトロック、収集中の変更検査、既存出力を上書きしない原子的な保存を行います。
プロジェクト内の出力先は `artifacts/` に限定し、シンボリックリンク経由のソースは拒否します。

`release check` はファイル一覧・サイズ・SHA-256を照合します。展開・コード実行・Leanの再検証は行いません。
全体digestとZIPの内容は同じファイル記述子で読み、検査後もdigestを照合します。
検査中にパスの参照先が差し替わっても、最初に開いたファイルが検査対象です。
重複名・相対パス逸脱・暗号化・リンク・対応上限を超えるZIPは拒否します。
上限はファイル20,000個（manifestを除く）、1ファイル64 MiB、展開サイズ合計512 MiBです。
内部manifestもアーカイブの一部なので、この検査だけでは作成者や数学的正しさを認証できません。
`--sha256` は別経路で取得した全体digestとの一致を追加確認します。人間の承認や電子署名とは区別します。

GitHub Actionsは全課題とテストが合格した後に同じアーカイブを作り、既存の検証成果物とともに保存します。
