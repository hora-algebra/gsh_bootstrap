# PROGRESS — どのアイデアがどこまで行き、何が死んだか

このリポジトリの目的は2つ。**(1) generalized star-height 問題を肯定的または否定的に解く。
(2) それを Lean で形式化し形式的証明を完了する。** この文書は、その2つに対して
「どのアイデアを試し、どこまで行き、何が死んだか」を1枚で見るためのものです。

**読む順序はここが最初。** 詳細は各行のリンク先にあります。ここに書いてある status は
`CLAIMS_LEDGER.md` の写しであり、食い違ったら**台帳が正しい**。

- ID の `P3` `D1` `S1` などは [docs/SCENARIOS.md](docs/SCENARIOS.md) の route 記号です。
- 撤回した主張は [RETRACTIONS.md](RETRACTIONS.md) に全文があります。
- この文書は [docs/SUGGESTIONS.md](docs/SUGGESTIONS.md) §7 が要求していた approach registry です。

---

## 30秒で現在地

- **下界の道具が1つも無い。** 高さ ≥ 2 を証明する手段は、本リポジトリにも監査済みの文献にも**知られていない**（`N-LOWER-001` OPEN）。「存在しない」ではない — それ自体が未解決である。
  以下で「反例候補」と呼ぶものはすべて「**既知手法が構造的に不適用**」という意味であって、
  高さ ≥ 2 の証明ではない。この区別を崩したら研究が死ぬ。
- **有限群の障壁は位数 20（`F_20`）**。Bourne 2017 が置いた位数 12 の壁は 2026-07-27 に
  `A4-ALLLANG-01`（`PROVED`）で越えた。位数 ≤ 31 の非可換群 45 個のうち PST クラス外はちょうど 6 群、
  うち `A_4` は解決済み、`C_2×A_4` は `SUBDIRECT-RED-01` で `A_4` に合流するので
  **独立な未解決は 4 群**: `F_20`(20), `C_7⋊C_3`(21), `SL(2,3)`(24), `S_4`(24)。
  ⚠️ ここでの「未解決」は**本リポジトリが監査した被覆定理の外**という意味であって、文献全体で未解決という
  意味ではない。`FRONTIER-ORD20-01` は文献側を `UNREVIEWED` と明記している（1992–2026 の網羅調査は未実施）。
- **位数60以下の正判定178群は構造 witness まで独立監査済み。** `COVER-LE60-POS-01`
  (`COMPUTED`) が280個の正判定表（可換102、非可換178）について群公理とC1--C5/R1を全数再検査し、
  位数32--60の非可換137群を新たに閉じた。残る32群はGAP探索の残余
  `COVER-LE60-RESIDUAL-01` (`UNREVIEWED`) であり、witness非存在や高さ2以上を意味しない。
- **最大の成果**: PST 1992 が提案し Weis 2011 が未解決として残した**フル版 `L2` の gsh = 1**
  を決定（`WEIS-L2-GSH-01`, COMPUTED）。さらに rsh = 2 なので、`L2` は **gsh = 1 < rsh = 2 の明示例**。
- **Lean 側**: 可換有限群すべてと位数 ≤ 5 で `HeightOneForGroup` を証明済み、axiom 監査つき。
  さらに 2026-07-27 に full-alphabet 還元・reversal・有限 Boolean 結合・syntactic monoid が入った。
  `A_4` は数学としては解決したが **Lean への移送は未了**（`L-A4-001` OPEN）。

---

## アイデア別の進捗

### 生きている / 成果になったもの

| アイデア | route | どこまで行ったか | 状態 |
|---|---|---|---|
| フル版 `L2` を対角 anchor 法で落とす | P3 | 6頂点作用では anchor 基準が破れるが、中心対合による**対角線4点への商作用**では成立。gsh = 1 を決定。rsh = 2 も決定 | ✅ `WEIS-L2-GSH-01` / `WEIS-L2-RSH-01` COMPUTED |
| `A_4` 2生成元 word problem | P3 | 高さ1の式を構成し、384状態の積オートマトン到達可能性で言語として等しいことを完全証明 | ✅ `A4-STD-01` / `-02` COMPUTED |
| `F_20` 2生成元 word problem | P3 | 同じ機構が通る。phase mod 4・count mod 5 の W 原子を使用 | ✅ `F20-STD-01` COMPUTED |
| `A_5` の生成系依存の高さ1 | P3 | 生成系 `(123),(145)` の word problem が高さ1。**台帳が持つのはこの一組だけ**。「単一サイクル生成元が anchor 点を共有する生成系はすべて」という一般化は `RESULTS.md` §5.7 にあり、対応する台帳行は無い（未登録） | ✅ `A5-GEN145-01` COMPUTED |
| `Dic_3` を PST クラスに埋め込む | S1 | 明示的埋め込み `Dic_3 ↪ (C_3×C_4)⋊C_2`。副産物として**全 dicyclic 群**（したがって全 generalized quaternion 群）が PST クラス内 | ✅ `DIC3-RED-01` / `DICM-EMB-01` PROVED |
| subdirect 還元（定理C） | P2 | height-one 群の class は**有限直積で閉じる**。系として直接攻撃が必要なのは **monolithic な群だけ**。これで `C_2×A_4` → `A_4`、`C_2×S_4` → `S_4` に合流 | ✅ `SUBDIRECT-RED-01` PROVED |
| 逆 alphabetic morphism の閉包を自前化 | P2 | `h^{-1}` が gsh ≤ 1 を保つことを4段で自証。`F_20` の20文字は8文字、identity erasure後は7文字に落ちる。ただし旧cut機構は7文字でも衝突する。さらにphase-rigidityにより、このschemeを`F_20`座標だけで組む限り少なくとも1座標は4文字以上で、2/3文字還元は不可能 | ✅ `ALPH-RED-01` / `F20-ALPH8-01` / `F20-PHASE-RIGID-01` PROVED；`F20-ALPH7-OBS-01` COMPUTED |
| `C_7⋊C_3` 全21元アルファベット | P3 | `F_20` の障害診断（下記）から「phase 群が素数位数なら機構が動く」と予測し、非周期性 288/288・GF(7) 階数 6/6 が通った。ただし式・言語同値まではなく、`N-C7C3-001` は OPEN。**「解けた」ではない** | ⚠️ `C7C3-FULL-01` EMPIRICAL（`C7C3-IDENT-01` の再構成部分は PROVED） |
| star-free ラベル付きオートマトン | P2 | `gsh(L) ≤ r_SF(L)`（loop complexity）。肯定的結果がすべて同じ形をしていたのを1つの言葉に整理。`L2` の最小 DFA の loop complexity は 2 なので **`r_SF(L2) ≤ 2`**（等号は非主張） | ✅ `SFA-EGGAN-01` PROVED。測定は `SFA-L2-MEASURE-01` COMPUTED。**ただし新規ではない**（Sakarovitch §3.6、`M-SFA-PRIOR-001` で確認済み） |
| `A_4` 全12元アルファベット | P3 | **Bourne 2017 Question 5.9 の半分**。pattern 条件つき cut で作った高さ1の特徴に、反転語の同じ特徴と文字数を足して GF(2) 7本の系を立て、`N[g,p]` を復元する。有限部分（279 個の token automaton の非周期性、特徴恒等式、GF(2) 復元、群公式）は全 reachable state を走査して決定済み、17/17 controls 発火。合成は人間証明 + Schützenberger 1965 | ✅ `A4-FULL-01` / `A4-ALLLANG-01` PROVED（2026-07-27）。有限 core は `A4-FULL-FINITE-CORE-01` COMPUTED |
| 証明書チェッカー | S4 | Python 側は健全性を証明済み。**Lean 側は未着手** | ⚠️ `CERT-01` PROVED / `L-CERT-001` OPEN |

### 詰まっているもの（証拠が足りない）

| アイデア | どこで止まったか | 状態 |
|---|---|---|
| 位数 ≤ 12 の総合主張 | 個々のケースは全て CITED か PROVED になり EMPIRICAL な入力は消えたが、**五群分類と被覆の合成に独立監査が入っていない**。Lean 合成も未了（`L-ORD12-GRP-001` / `L-ORD12-001`） | ⚠️ `ORD12-ALL-01` UNREVIEWED |
| `A_5` 全60元アルファベット | §5.7–5.8 の2つの不可能性定理が適用され、現手法の全ルートが破れる | 🔵 未解決。反例候補の次点 |
| 段階付き `ba*b` 対カウント mod 3 | phase mod 2 は全 Boolean 結合で高さ1。mod 3 以上は障害が特定された形で停止 | 🔵 `N-L2-M3-001` OPEN |
| transducer route | `F_20` の word problem は `Z/4` を状態モノイドに持つ length-preserving sequential function の逆像に落ちる。**状態モノイドが有限 abelian なら gsh ≤ 1 が保たれるか**が焦点。真なら `N-F20-001` が落ちる | 🔵 `TRANSD-ABEL-01` CONJECTURAL。**先に文献調査**（`N-FIB-PRIOR-001` PARTIAL） |
| SF-automaton の rank 削減 | loop complexity 2 の SF-automaton が rank 1 の Boolean 結合になるか | 🔵 `N-SFA-RANK2-001` OPEN |
| `exploring-math` からの輸入 | CORE2 族・binary finite-code KR obstruction など5行。**未監査のまま** | ⚠️ 全て UNREVIEWED（`M-EXP-PR2-001`） |
| topos / isotropy 定式化 | Place–Zeitoun の local monoid の aperiodicity を Karoubi envelope の isotropy の消滅として読み替える提案（`TOPOS-ORB-01`）と、その上の中心予想（`TOPOS-ISO-01`）。**止まっているのは isotropy subtopos の正準な定義**で、Kobin の構成を取り出すまで予想として precise にならない。仮に真でも gsh を解くわけではなく base quotient を与えるだけ。**着手されていない**（コードも Lean も無い）。構成の全文は 2026-07-27 に削除した `docs/Cenceptual_understanding.md`（`git show 230cde4:docs/Cenceptual_understanding.md` で復元） | ⚠️ 読み替えは1つの主張ではなく3つ（`TOPOS-BASE-01` / `TOPOS-ORB-01` / `TOPOS-KAR-01`）で、出典が別々。全て UNREVIEWED／`TOPOS-ISO-01` SPECULATIVE。`N-TOPOS-001` は **BLOCKED**（定義が無いので検査を書く対象が無い） |

### 最有力の反例候補

| 対象 | なぜ候補か | 注意 |
|---|---|---|
| **(2,3,5)型生成系の `A_5` word problem**（例 {(12)(34),(135)}） | `RESULTS.md` §5.8 の**2つの不可能性定理**により、既知の全構成法（anchor 法・可換カウント法の Boolean 結合）の外にある。⚠️ **対応する台帳行が無く**、status も evidence も規範台帳で追えない（`scripts/research/a5_235.py` も台帳に現れない） | これは「既知手法が効かない」であって高さ ≥ 2 ではない |
| Weis の `L3`（syntactic monoid `S_5`、Weis 2011 で未解決） | フル版 `L2` が落ちたので、可解軸の候補は「構文群のどの推移作用でも anchor 対条件が破れる」ものに絞られた。`L3` は非可解軸にも属する | `N-L3-ANCHOR-001` OPEN |

### 死んだルート

| アイデア | route | どう死んだか |
|---|---|---|
| **cohomology を不変量にする** | P4 / D5 | ❌ **三重に死亡**。(a) 確立した不変量ではない（`COH-01` REFUTED）。(b) `C_5⋊_r C_4` を `r ∈ {1,4,2}` = `C_20`, `Dic_5`, `F_20` で走らせると `H^n(C_4, Z/5)` は `n ≥ 1` で**三つとも全次数 0** — 前2つは settled、`F_20` は open なのに分類データが完全に同一。**この extension の分類データではこの問題を見分けられない**（`F20-COH-SEP-01` COMPUTED）。台帳は他の cohomological construction まで排除するとは述べていない。(c) `N-COH-001` BLOCKED |
| `F_20` 全20元アルファベットに `A_4` の機構を移す | P3 | ❌ 291 候補パターンが**全滅**。原因を特定: phase 群 `Z/4` が**合成数**なので `ε = 2` の文字が奇 phase を `1 ↔ 3` と往復し、遷移モノイドに period 2 の元を作る。`A_4` の機構は phase 群が素数位数であることを暗黙に要求していた（`F20-FULL-OBS-01`） |
| `F_20` 部分アルファベット | P3 | ❌ certified family の**表現力**で破れる（`F20-SUB10-OBS-01` PROVED） |
| `F_20` 有限符号ブロック分解 | P3 | ❌ **遅延定理**により、このルートは自分自身への還元になる（`F20-BLOCK-OBS-01` PROVED） |
| 商への関係づけによる剛性 | P2 | ❌ 全アルファベット上では relabeling の交叉で `T` を作れない（`F20-QUOT-OBS-01` PROVED） |
| `A ⋊ C_3` への直接拡張 | P3 | ❌ 一意分解のステップで破れる（`SMALL-C3-FAIL` CITED）。最小の明示的反例はまだ作られていない（`M-C3-FAIL-001` OPEN） |
| 総当たり探索 `search.py` | P6 | 🗄️ `tools/height_search.py` に置換（証明書つきサイズ順列挙） |
| ランダム長語一致による検証 `verify.py` | — | ❌ **手法ごと死亡**。2026-07-25 の完全性監査が、有界長とランダム語の一致を証拠として認めなくなった。この種の出力は定義により `EMPIRICAL` — 反証はできるが立証はできない |

詳細は [legacy/README.md](legacy/README.md)（捨てたプログラムと「replaced by」）と、`notes/` の各導出 — [f20_full_alphabet_obstruction.md](notes/f20_full_alphabet_obstruction.md)、[f20_subalphabet_obstruction.md](notes/f20_subalphabet_obstruction.md)、[f20_block_decomposition.md](notes/f20_block_decomposition.md)、[f20_fibration_geometry.md](notes/f20_fibration_geometry.md)。（2026-07-26 に `RESULTS.md` §5.12–5.15 をこれらへ統合した。）

---

## Lean 形式化の現在地

| 済 | `HeightOneForGroup` が可換有限群すべてで成立（`L-ABEL-001`）／位数 ≤ 5 すべて（`L-ORD5-001`）／単射・全射群射に沿って降下、したがって divisor へ（`L-TRANS-001`）／counting 言語（`L-CNT-001`）／full-alphabet 還元（`L-RED-001`）／reversal（`L-REV-001`）／有限 Boolean 結合（`L-FIN-BOOL-001`）／syntactic congruence と quotient monoid（`L-SYN-001` / `L-SYN-002`） |
|---|---|
| **保証** | `GSHTest/Axioms.lean` が `GSH` namespace の**全定理**を掃引し、`sorryAx` / `native_decide` / 任意の axiom の混入で落ちる |
| 未 | 登録済み `sorry` は**1件**（`GSH/Conjecture.lean:30`、`L-GSH-CHALLENGE-001` = 予想そのもの）。Schützenberger インターフェース（`L-SF-001`）と証明書健全性の Lean 版（`L-CERT-001`）は未着手 |
| OPEN | `L-A4-001`（`HeightOneForGroup A4`）。**数学は 2026-07-27 に閉じた** — 残るのは有限 core と人間証明を Lean kernel へ移送する作業で、Python の `COMPUTED` verdict を Lean theorem と読み替えてはならない |

---

## 撤回した主張（4件）

全文と再発防止ゲートは [RETRACTIONS.md](RETRACTIONS.md)。要点だけ：

1. **「位数 ≤ 12 は決着」「障壁は位数 20 に移動」** → 撤回。`A_4` の全アルファベット版が標本検証にすぎなかった。
   `COMPUTED` に「有限対象の網羅」と「標本」を区別する定義が無かったのが原因。今は分離され、`lint_claims.py` が機械的に拒否する。
2. **「標本行を決定済みに格上げした」** → 4行のうち `THOMAS-D2-02` は撤回。
   証拠欄の記述は全部正しく、**検査が空だった**（正しい有限対象ではないものを網羅していた）。今は `tools/verdict.py` が「何が走ったか」からラベルを計算する。
3. **「ladder の import 閉包に未証明宣言は無い」** → 記述として偽だった（後に真にした）。今は手書きの名前リストではなく namespace 全掃引。
4. **上の再発防止ゲート自体が、書かれた当日の敵対的レビューで6通り突破された** → 全て修正＋回帰テスト。
   教訓は「**ゲートはそれが制約するはずのプロセス自身が書いたので、同じ盲点を継承した**」。

---

## 次の一手（優先順）

1. `L-A4-001` — `A4-FULL-01` の有限 core と人間証明を Lean へ移送する。数学は 2026-07-27 に
   閉じた（`N-A4FULL-002` は closed）ので、残っているのは形式化と `L-ORD12-GRP-001` / `L-ORD12-001`。
2. `N-FIB-PRIOR-001` の文献調査を先に閉じる。真なら transducer route が `F_20` を落とす。調査前に工数を注ぐのは禁止。
3. `M-EXP-PR2-001` — UNREVIEWED 5行の監査。未監査の輸入が台帳に居座っている状態は良くない。
4. `N-L2-AUDIT-001` — 最大の成果（`WEIS-L2-GSH-01`）の独立人間査読。まだ誰もやっていない。
