# 単純性レビュー：構造と差分から見た判定

対象は `main`（`230cde4`）から `claude/start-and-refresh-eabdad` の
`main...HEAD` 全差分である。判定基準は行数そのものではなく、
**数学者が「現在の数学的成果・未解決点・Lean 側の到達点」を迷わず見つけられるか**に限る。

## 結論

**この refactor は、所有者の基準では repository を単純化していない。**

正確には、前半の cleanup は成功しているが、後半の adversarial review loop がその利益を
上回った。

- 成功した点:
  - tracked file は 170 から 147 に減った。
  - `legacy/prompts/` の多数の prompt、未使用 template、意図不明の docs を削除した。
  - `PROGRESS.md` を追加し、入口を一つ作った。
  - cleanup 時点 `a1f9595` では `main` 比で 1,674 行減っていた。
- 失敗した点:
  - その後、主として claim lint とそのテストに 1,775 行を戻した。
  - 最終的な text line は 102 行増えた。
  - verification machinery は 2,795 行から 4,520 行へ増え、Lean tree 1,678 行の
    約 2.7 倍になった。
  - `RESULTS.md` 1,792 行と、「一結果が `RESULTS` / `notes` /
    `data/experiments` / ledger / obligations / summary に散る構造」は残った。

したがって、**directory listing は少し短くなったが、概念的な repository はむしろ重くなった**。
数学者が理解する対象は 23 個減った file 名ではなく、どの記録が正で、どこまで読めば一つの
結果を理解できるかである。その点は改善していない。

## 入力事実の分類

- `COMPUTED`: `git diff main...HEAD`、`git log main..HEAD`、各 file の行数、
  class/function の行範囲、参照箇所をローカルで再集計した。
- `PROVED` 相当の構造事実: `scripts/check.sh` は `build_docs.py` を呼ばず、
  repository 内にも同 script の利用箇所がない。
- `UNREVIEWED` ではなく本レビューの判断: 「数学者にとって簡単か」「保護に対して何行が
  過大か」は設計評価であり、機械的定理ではない。

## 1. refactor は簡素化したか

### 良かった変更

`768ab94` と `a1f9595` までの削除は、所有者の依頼に正面から答えている。

- `legacy/prompts/` の 15 file 前後を削除。
- `docs/Cenceptual_understanding.md` 730 行、未使用 template、meeting/citation protocol 等を削除。
- dead な `*_RESULTS_insert.md` を削除。
- `PROGRESS.md` 114 行を入口として追加。

この段階だけなら「意図不明で使われない file を消す」という依頼に成功していた。

### しかし最終状態は簡単ではない

`a1f9595..HEAD` の commit の大半は、数学や Lean の構造ではなく、
Markdown の文意を regex で推測する gate と、その gate を破る文章例への対応である。

- `scripts/ci/lint_claims.py`: 436 → 1,069 行。
- `tests/test_lint_claims.py`: 258 → 1,163 行。
- 同 test file の `AdversarialBypassTests` だけで 568 行・65 tests。
- `BuildDocsTests` + `PublishTests` は 243 行。
- `build_docs.py` は 199 行で、`check.sh` から呼ばれていない。

一方、所有者が読むべき root の記録は依然として多い。

- `README.md` 352 行: 英語と日本語で現在地・ladder・主要 file を重複記載。
- `PROGRESS.md` 114 行: README と状態説明を重複。
- `RESULTS.md` 1,792 行。
- `CLAIMS_LEDGER.md` 132 行。
- `PROOF_OBLIGATIONS.md` 110 行だが、1 row が非常に長い。
- `RETRACTIONS.md` 134 行。

`PROGRESS.md` 自身も「status は ledger の写しで、食い違えば ledger が正しい」と宣言している。
これは入口としては有用だが、同時に reader に「この file 単独では信用せず、別の file と
照合せよ」と要求している。単純化の完成形ではない。

**行数と理解可能性はここで逆方向である。** 730 行の不要文書を消すことは理解を助けたが、
同量以上の verification code を追加しても数学者が結果を探しやすくはならない。

## 2. verification machinery はこの大きさで正当化されるか

**正当化されない。**

全 verification を消すべきではない。以下は stated goals に直結しており残す価値がある。

- Lean build、`GSHTest/Axioms.lean`、proof-hole check。
- certificate checker と soundness boundary。
- `tools/verdict.py` と、`COMPUTED` が実際の有限全探索に支えられることの照合。
- ledger の schema、status、owner、evidence 欠落等の機械的検査。
- ledger 内の固定 notation `ID (STATUS)` と
  `This row is \`STATUS\`.` の field-to-field 比較。

削除すべきなのは、**自由文の意味を単語から推測する部分**である。

具体的には `scripts/ci/lint_claims.py` の以下の系統を削除する。

- `negated`
- `outranking_label`
- `masked_for_quoting`
- `sections`
- `withdrawal_context`
- `withdrawal_exempt`
- `stale_labels`
- `attached` / `attached_label`
- `outranking_unit_label`
- `label_units`
- `paragraphs`
- `prose_errors`
- それら専用の `STRONGER_VERB`, `NEGATION`, quotation/retraction/Markdown fence
  等の pattern
- 歴史的 path か live path かを英文の単語で推測する exemption

これらは作者の集計で約 580 production lines であり、主に
`AdversarialBypassTests` 568 行と `ProsePropagationTests` 68 行に支えられている。
**production + tests で少なくとも約 1,216 行を削除できる。**

失う保護は実在する。

- `EMPIRICAL` row を README や note が “proved/settled/解決” と書く事故。
- negation、quote、retraction、table wrapping、code fence を使った bypass。
- 削除済み path を current path のように書く事故の一部。

しかし、この保護は seven adversarial rounds で繰り返し再開されており、
自然言語 checker として安定していない。保護対象を増やすほど
「数学的主張の検証」ではなく「Markdown 用の小型 NLP」を保守する project になる。

### `build_docs.py` も削除対象

`scripts/ci/build_docs.py` 199 行と、
`tests/test_lint_claims.py` の `BuildDocsTests` / `PublishTests` 243 行、
合計 **442 行**は outright deletion の対象でよい。

- `scripts/check.sh` から呼ばれていない。
- README/AGENTS/CI に利用手順がない。
- 守るものは「4 PDF を手動 rebuild/publish するとき、partial/stale set や rollback failure を
  防ぐこと」である。

これは有用な保護だが、GSH を解くことまたは Lean 形式化を進めることの中心ではない。
削除コストは、PDF 更新時の atomic publish/rollback の安全性を失うこと。
必要なら PDF は生成物を確認してから commit するという人間の作業に戻る。

## 3. そもそも gate を作るのが正しい応答だったか

**小さい機械的 gate を作るところまでは正しかったが、自由文 gate を育てたのは誤りだった。**

retracted claim が repository に残った以上、以下は機械化する価値がある。

1. `COMPUTED` row に verdict があるか。
2. status column と evidence 内の明示 status notation が一致するか。
3. `EMPIRICAL` が sample を明記しているか。
4. ledger row の基本 schema が壊れていないか。

一方、README、RESULTS、notes、retraction の自然文をすべて status-bearing にしたまま、
“settled”, “proved”, “決着”, quote、negation、過去時制の意味を regex で読むのは
問題の置き場所を誤っている。

本当の原因は、同じ claim の status と射程を多数の file が繰り返し文章で持つことにある。
gate はその重複構造を保存したまま、すべての copy を同期させようとしている。
所有者の依頼は、同期機構を巨大化することではなく、copy の数を減らすことだった。

### 150 行の固定 notation check だけで十分だったか

**現在の document layout のままなら、150 行だけでは不十分。**

ledger field 同士しか比較しないので、README/RESULTS/note が古い status を自由文で述べる事故は
見逃す。その意味では、同じ事故を現在の構造のまま完全に防げない。

しかし、**status の正本を ledger 一つに限定し、他の file から status の重複記述を減らすなら、
150 行は automated core として十分**である。残る prose の射程・表現は、人間が claim を変更する
diff で読むべきである。自然言語を完全に lint しようとするより、正本を一つにする方が
所有者の「俺が理解できない」に答える。

## 4. 単一で最も価値の高い deletion

**free-prose semantic gate 一式を削除する。**

- 削除量: **少なくとも約 1,216 行**
  - 作者分類の semantic production: 約 580 行。
  - `AdversarialBypassTests`: 568 行。
  - `ProsePropagationTests`: 68 行。
- 残すもの:
  - ledger schema/status/evidence checks。
  - verdict-backed `COMPUTED` checks。
  - 固定 notation の ledger field comparison（約150行）。
  - Lean/certificate/proof-hole checks。
- 失うもの:
  - 自由文における過大表現、quote/negation/retraction/table/fence bypass の自動検出。
- 判断:
  - その loss は本物だが、1,216 行と seven-round maintenance を正当化しない。
  - prose copy を減らし、status の正本を ledger に限定する方が小さく、理解しやすい。

これは `tests/test_lint_claims.py` 全削除ではない。機械的で安定した検査は残し、
自然言語解釈 subsystem だけを削る提案である。

## 5. `RESULTS.md` / `notes/` / `data/experiments/` consolidation の延期

**many-to-many mapping を見て即座に file move を止めたこと自体は prudence だった。**
一対一だと思い込んで機械的に移動すれば、証拠や横断的な lemma を失う危険がある。

しかし、**そこで consolidation 自体を延期し、その代わり 1,775 行の gate を作ったのは avoidance**
である。many-to-many は所有者の complaint の外部要因ではなく、まさに complaint の中身である。

例として `F20-ALPH8-01` 周辺は、一つの研究結果を理解するために少なくとも以下を横断する。

- `PROGRESS.md`
- `RESULTS.md` §5.17（109 行）
- `notes/f20_alphabetic_reduction.md`（364 行）
- `data/experiments/f20_alphabetic_reduction.md`（119 行）
- `CLAIMS_LEDGER.md`
- `PROOF_OBLIGATIONS.md`
- research script

同様に `F20` の §§5.12–5.17 だけで `RESULTS.md` に 592 行あり、各節には既に対応 note と
experiment manifest がある。many-to-many だから統合不能なのではなく、
**一つの結果に三種類の文章記録を許しているため、many-to-many が reader に露出している。**

妥当な simplification は、追加の index や abstraction を作ることではない。

- human-readable derivation と射程は対応する `notes/<topic>.md` に merge。
- `data/experiments/<topic>.md` は command/hash/runtime/verdict 等の run metadata に縮める。
- `RESULTS.md` の重複節を削除し、最終的には短い結果一覧か `PROGRESS.md` に吸収する。
- ledger は status の唯一の正本にする。

まず重複の明確な `RESULTS.md` §§5.12–5.17 を notes に吸収して削れば、
unique な数段落を notes に残しても **概算 450–550 行減**になる。
リスクは § number の cross-reference を更新し忘れることだが、これは consolidation を避ける理由
ではなく、作業を一節ずつ行う理由である。

## 補足：理解を難しくしている具体的な構造

1. **README と PROGRESS の二重入口**
   - README は 352 行、英日で現在地と ladder をほぼ二重に持つ。
   - PROGRESS は同じ現在地を 114 行で持つ。
   - README は purpose/quick start/入口だけに縮める余地が大きい。

2. **root に status-bearing narrative が多い**
   - README / PROGRESS / RESULTS / ledger / obligations / retractions のどれを読めば
     「現在正しい結論」なのか、初心者は役割名だけでは判断できない。

3. **一行の obligation が研究日誌化している**
   - `PROOF_OBLIGATIONS.md` の `N-F20-001` 等は、obligation、過去 route、反証、
     methodological lesson、次の route を一 cell に累積している。
   - これは queue ではなく別の RESULTS になっている。
   - 過去 route の叙述は note に merge し、obligation row は target / blocker /
     acceptance test / status に戻すべきである。これは主に移動と削除でできる。

4. **verification code が repository の大型 file 上位を占める**
   - `tests/test_lint_claims.py` は 1,163 行で repository 第3位級。
   - `lint_claims.py` は 1,069 行。
   - 数学者が tree を見たとき、何を守る project なのかが「GSH」より「Markdown claim lint」に
     見える。

## 次にやる三つ（順序付き）

1. **free-prose semantic gate と専用 tests を削除する。**
   - 行差分: **約 −1,216 行**（さらに end-to-end fixture の整理で数十行減る余地）。
   - risk: README/RESULTS/notes の過大表現を自動検出できなくなる。
   - 理由: 最大の肥大部分で、seven rounds でも安定せず、数学・Lean のどちらも前進させない。

2. **`RESULTS.md` §§5.12–5.17 を対応 notes に merge し、重複節を削除する。**
   - 行差分: **概算 −450〜−550 行**。
   - risk: `§5.x` cross-reference の更新漏れ、note にない unique caveat の取りこぼし。
   - 理由: owner が理解できない直接原因である「一結果が複数 narrative に散る」を初めて減らす。

3. **`scripts/ci/build_docs.py` と `BuildDocsTests` / `PublishTests` を削除する。**
   - 行差分: **−442 行**。
   - risk: 4 PDF の手動更新時に atomic publish/rollback の保護を失う。
   - 理由: `check.sh` から使われず、stated goals に対して周辺的で、低い統合リスクで即座に
     repository を小さくできる。

最終判定を一文で言えば、**前半の cleanup は正しかったが、最終 branch は所有者の基準では
repository を悪化させた。削除した複雑さを、より読みにくい verification complexity として
戻してしまった。**
