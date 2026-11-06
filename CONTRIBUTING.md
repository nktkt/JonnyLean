# JonnyLeanへの課題追加

1. `specs/JL-NNN.md` に対象、定義、量化、仮定、結論、証明方針を明記する。
2. `contracts/` に独立した命題の型と必要な定義の性質を記述する。単なる定理名の型表示で済ませない。
3. `JonnyLean/` にモジュールを用意し、必要な依存importを記す。
4. `catalog/fragments/` のJSONに一意なID・定理名・分野・説明・タグ・仕様・契約・review・editable・depends_onを登録する。
   `python3 tools/jonnylean.py catalog sync` で `jonnylean.toml` と `JonnyLean.lean` を再生成する。
   editableは数学Leanファイルのみ。仕様と契約はワーカーの編集対象にしない。
5. 仕様と契約の内容を確認してから `work --task JL-NNN` を実行する。依存課題は先に取り込む。
6. 合格した候補を `adopt JOB_ID` で取り込み、`run all` で他課題への影響も確認する。

関連する複数課題が同じモジュールを共有してもよい。公開対象の定理名は一意にし、
課題ごとの独立した意味・仕様・契約を持たせる。定理数やモジュール数を増やすためだけのラッパーは追加しない。
共通の仕様モデルを作る場合は数学実装とは別ファイルに置き、契約からimportし、editableから除外する。
登録後は `plan JL-NNN --include-dependencies` で依存範囲を確認する。

ワーカーは既存のeditableファイルだけを置換する。新規モジュールとそのimportの追加は準備段階で行う。
編集中の `sorry` は不合格となり、成果や承認済み証明として扱わない。

共有定義の変更は依存する課題の意味を変え得る。仕様や契約を勝手に弱めず、その変更を独立した
設計変更として確認する。公理ポリシー、CI、検査ツール、レビュー基準も数学実装とは分けて確認する。

検査基盤を変更するときは、実際のLeanで正常な証明が通ることと、不正変更を拒否することをテストする。
合成レビューの試験データに人間の確認者名や実レビューを装った記録を入れない。

```sh
python3 tools/jonnylean.py catalog check
python3 tools/jonnylean.py verify all --jobs 4
python3 -m unittest discover -s tests -v
```

監査ツール変更後は独立レビュアーが内容を読み直し、現在のfingerprintと具体的根拠を記録する。
自動CIでハッシュを書き換えるだけの再承認はしない。
