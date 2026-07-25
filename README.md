# Generalized Star-Height Workshop Bootstrap

**[English](#english) | [日本語](#日本語版)**

<a id="english"></a>

This repository is a working base for a mixed team of formal-language theorists, group/number theorists, and Lean contributors attacking the **generalized star-height problem**. The primary record of mathematical results is [RESULTS.md](RESULTS.md); the single source of truth for the status of every claim is [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md).

## The target, stated precisely

For a finite alphabet `A`, generalized regular expressions are built from `∅`, `ε`, and letters using union, concatenation, complement (relative to `A*`), and Kleene star. The generalized star-height of an expression is the maximum nesting depth of Kleene star; the generalized star-height of a language is the minimum height of any generalized expression defining it.

The project separates two questions that are often conflated:

1. **Height-one collapse conjecture:** every regular language has generalized star-height at most one.
2. **Decision problem:** compute the generalized star-height of an input regular language.

No language of generalized star-height greater than one is currently known (open since the 1960s). A proof of height-one collapse would reduce exact computation to the decidable star-free-versus-height-one distinction. A counterexample would leave the decision problem open but settle the central structural conjecture.

On the Lean side, the conjecture is registered as an **explicitly open challenge** in `GSH/Challenges/GeneralizedStarHeight.lean` (`PROOF_OBLIGATIONS.md`, L-GSH-CHALLENGE-001).

## Where the project stands (as of 2026-07-25)

The initial plan was to climb Bourne's ladder from the first unresolved order-12 cases (`A_4` / `Dic_3`) toward `A_5`. The computational results of 2026-07-22/25 (details and verification levels in `RESULTS.md`; statuses in the ledger) moved the frontier substantially:

- **The finite-group barrier moved from order 12 to order 20.** Exactly six non-abelian groups of order at most 31 fall outside the class covered by the published theorems — `A_4` (12), `F_20 = C_5⋊C_4` (20), `C_7⋊C_3` (21), `SL(2,3)`, `S_4`, `C_2×A_4` (24) — and `A_4` is settled here, so `F_20` is the smallest unsettled case. See the ladder below.
- **The full language `L2` of Pin–Straubing–Thérien 1992, left open in Weis 2011, has generalized star-height exactly 1** (`WEIS-L2-GSH-01`, COMPUTED, 2026-07-25). The anchor criterion fails on the 6-state automaton but succeeds on the induced action on the four cube diagonals. Its restricted star-height is 2, so `L2` is an explicit standard example of gsh = 1 < rsh = 2 (`WEIS-L2-RSH-01`). This settles one `C_2×S_4`-recognized language, **not** `HeightOneForGroup (C_2×S_4)`.
- **`A_4` is completely off the candidate list**: height 1 for the standard generators and for the full 12-element alphabet (§5–5.5, COMPUTED), hence for every generating morphism.
- **Every group of order ≤ 12 is settled (2026-07-23, with stated verification levels)**: order < 12 and `C_12`, `C_6×C_2`, `Dih_6` are CITED (PST 1992); `Dic_3` reduces to the PST class via the explicit embedding `Dic_3 ↪ (C_3×C_4)⋊C_2` (machine-verified, `scripts/dic3_embedding.py`), closing the `Dic_3` half of Bourne's order-12 barrier; `A_4` follows from the full-alphabet result plus the now self-contained full-alphabet reduction (`FULL-ALPH-RED-01` PROVED, `A4-ALLLANG-01` COMPUTED). Independent human review pending (ledger row `ORD12-ALL-01`).
- **Even `A_5` collapses for many generating sets**: starting from the point-stabilizer filtration for (123),(145) (§5.6), the machine-checkable **anchor criterion** (§5.7) sends every generating set of single-cycle generators sharing an anchor point to height 1.
- **The leading counterexample candidate is the `A_5` word problem with (2,3,5)-type generators** (e.g. {(12)(34),(135)}): two impossibility theorems (§5.8) machine-verify that it lies outside every known construction (the anchor method and Boolean combinations of commutative counting). The runner-up is the full 60-element-alphabet version.
- **L(aab,0,4)** — the parameter case (|u| = 3, modulus 4) left open by Pin–Straubing–Thérien in 1992 — **is height 1** (§3, §5).
- **The staged ba*b pair-counting ("Weis L2") family is height 1 for phase mod 2** (§5.9); mod 3 and above remain open with the obstruction identified.
- **No lower-bound tool exists.** Every "candidate" above means "structurally out of reach of all known methods", never "proved of height ≥ 2" (research rule 1).
- A mathematical proof note of a **single-observer reduction** for word problems of non-abelian simple groups is in `notes/simple_group_height1_reduction.md` (external theorems: PST quotient closure, Place–Zeitoun star-free closure; novelty audit, independent review, and Lean formalization pending).

## Lean formalization status (2026-07-25)

The ladder below records the **literature/computational** status. The Lean tree is far behind it, deliberately: nothing is transcribed from a `CITED` or `COMPUTED` row (research rules 1 and 4). What is actually proved in Lean, with no `sorry`:

| Statement | Lean | Ledger |
|---|---|---|
| `{w \| count a w % m = r}` has height ≤ 1 | `GSH.Counting.hasHeightAtMost_count` | `LEAN-CNT-01` |
| `HeightOneForGroup` descends to divisors | `GSH.HeightOneForGroup.of_injective` / `.of_surjective` | `LEAN-TRANSFER-01` |
| every finite **commutative** group | `GSH.heightOne_of_commGroup` | `LEAN-ABELIAN-01` |
| **every group of order ≤ 5** | `GSH.heightOneUpTo_five : HeightOneUpTo 5` | `LEAN-ORD5-01` |

The whole repository contains **exactly one** `sorry`: `generalized_star_height_conjecture`, the open problem itself. `GSHTest/Axioms.lean` proves mechanically, via `#guard_msgs in #print axioms`, that none of the four theorems above depends on it (or on `native_decide`); `scripts/check.sh` runs that audit, and `scripts/check_proof_holes.py` now rejects any `sorry` other than the flagship one.

**Why the Lean ladder stops at 5 and not at 19.** Every group of order ≤ 19 *except `A_4`* has a commutative subgroup of index ≤ 2 (odd orders are commutative; 2-groups by the Burnside basis theorem; `2p` by Sylow; order 16 as a group of order `p⁴`; `D_6` and `Dic_3` contain `C_6`; order 18 by its Sylow 3-subgroup). Such a `G` need **not** be a semidirect product `H ⋊ C_2` — the extension frequently does not split (`C_4` over `C_2`, `Q_8` over `C_4`, `Dic_3` over `C_6`) — which is exactly why the chain goes through the Krasner–Kaloujnine universal embedding, valid for split and non-split extensions alike: `G ↪ H ≀ C_2 = (H × H) ⋊ C_2`, a *split* product of a commutative group by `C_2`. So with that embedding plus the divisor transfer above, the entire non-commutative part of `n ≤ 19` reduces to the **single** theorem "`A ⋊ C_2` has the height-one property" — the general PST class `A ⋊ E` is not needed. That theorem (`L-ABC2-001` / `M-PST-003`) is not yet formalized. `A_4` is worse than unformalized: it has no proof in this repository at all, only a `COMPUTED` search result (`L-A4-001`, `BLOCKED`).

## The non-abelian finite groups in increasing order, and who first settled each

For a finite group `G`, the **full solution** is the statement

> for every finite alphabet, every monoid morphism `φ : Σ* → G` and every accepting set `P ⊆ G`, the language `φ⁻¹(P)` has generalized star-height at most one

(the property `HeightOneForGroup G`). It is strictly stronger than "the word problem of `G` for one fixed generating morphism has height one". Abelian groups are covered wholesale by Pin–Straubing–Thérien 1992, so the ladder below lists the **non-abelian** groups, ordered by size, together with the first solution known to this repository. All 45 non-abelian groups of order at most 31 appear; rows are merged when the covering mechanism is identical. Audited exhaustively by `scripts/small_group_pst_coverage.py` (exact, ~3 s; ledger rows `PST-DIV-CRIT-01`, `DICM-EMB-01`, `SMALL-NONAB-31-01`, `FRONTIER-ORD20-01`; derivation in `notes/small_group_pst_frontier.md`).

Mechanisms: **nil₂** = nilpotent of class at most two (`PST-GRP-02`); **A⋊E** = split semidirect product of an abelian group by an elementary abelian 2-group (`PST-GRP-03`); **div** = the same theorem reached through an explicit embedding, because the extension does not split.

| Order | Non-abelian groups | Mechanism | First settled |
|---|---|---|---|
| 6 | `S_3` | A⋊E | Pin–Straubing–Thérien 1992 |
| 8 | `D_4`, `Q_8` | nil₂ | Pin–Straubing–Thérien 1992 |
| 10 | `D_5` | A⋊E | Pin–Straubing–Thérien 1992 |
| 12 | `D_6` | A⋊E | Pin–Straubing–Thérien 1992 |
| 12 | `Dic_3` | div | PST 1992 + explicit embedding, this repository 2026-07-23 (`DIC3-RED-01`); listed as open in Bourne 2017 |
| 12 | `A_4` | — outside the PST class | this repository, 2026-07-22/23 (`A4-ALLLANG-01`, `COMPUTED`, independent human review pending); listed as open in Bourne 2017 |
| 14 | `D_7` | A⋊E | Pin–Straubing–Thérien 1992 |
| 16 | `D_8`, `SD_16` | A⋊E | Pin–Straubing–Thérien 1992 |
| 16 | `M_4(2)`, `D_4×C_2`, `Q_8×C_2`, `C_4⋊C_4`, `(C_2×C_2)⋊C_4`, `C_4∘D_4` | nil₂ | Pin–Straubing–Thérien 1992 |
| 16 | `Q_16` | div | PST 1992; embedding made explicit here 2026-07-25 (`DICM-EMB-01`) |
| 18 | `D_9`, `C_3×S_3`, `(C_3×C_3)⋊C_2` | A⋊E | Pin–Straubing–Thérien 1992 |
| 20 | `D_10` | A⋊E | Pin–Straubing–Thérien 1992 |
| 20 | `Dic_5` | div | PST 1992; embedding made explicit here 2026-07-25 (`DICM-EMB-01`) |
| **20** | **`F_20 = C_5⋊C_4` (faithful action)** | outside the PST class | **OPEN — the smallest unsettled non-abelian group** (`N-F20-001`); the two-generator word problem is height 1 as of 2026-07-25 (`F20-STD-01`), the full 20-letter alphabet is not |
| **21** | **`C_7⋊C_3`** | outside the PST class | **OPEN** — smallest odd-order case; exactly Bourne's failed `A⋊C_3` step (`N-C7C3-001`) |
| 22 | `D_11` | A⋊E | Pin–Straubing–Thérien 1992 |
| 24 | `C_4×S_3`, `D_12`, `(C_6×C_2)⋊C_2`, `C_2×C_2×S_3` | A⋊E | Pin–Straubing–Thérien 1992 |
| 24 | `C_3×D_4`, `C_3×Q_8` | nil₂ | Pin–Straubing–Thérien 1992 |
| 24 | `C_3⋊C_8`, `Dic_6`, `C_2×Dic_3` | div | PST 1992; embeddings made explicit here 2026-07-25 |
| **24** | **`SL(2,3)`, `S_4`, `C_2×A_4`** | outside the PST class | **OPEN** (`N-S4-001`) |
| 26 | `D_13` | A⋊E | Pin–Straubing–Thérien 1992 |
| 27 | Heisenberg over `F_3`, `C_9⋊C_3` | nil₂ | Pin–Straubing–Thérien 1992 |
| 28 | `D_14`, `Dic_7` | A⋊E / div | Pin–Straubing–Thérien 1992 (`Dic_7` embedding explicit here) |
| 30 | `D_15`, `C_5×S_3`, `C_3×D_5` | A⋊E | Pin–Straubing–Thérien 1992 |
| 32+ | not audited | — | 44 non-abelian groups at order 32 alone |
| 60 | `A_5` | outside the PST class | OPEN; height one is known for *some* generating morphisms only (§5.6–5.7) |

Two infinite families are settled outright: every dihedral group `D_n = C_n⋊C_2` is a PST semidirect product by definition, and every dicyclic group `Dic_n` — hence every generalized quaternion group `Q_{2^k}` — embeds into `(C_2 × C_{2n})⋊C_2` by the uniform formula `x ↦ v`, `y ↦ ut` (`DICM-EMB-01`, `PROVED`).

**How to read the "first settled" column.** These are the earliest sources *audited in this repository*, not the outcome of a literature survey covering 1992–2026. The audit is against `PST-GRP-01/02/03`, plus `PST-WREATH-COMM-01` (2026-07-25), which **proves** that PST 1992's remaining wreath-product result covers no non-abelian group at all — its wreath products carry a single commutative group layer between aperiodic ones, so every group in the generated pseudovariety is commutative. What is still unchecked is other 1992–2026 literature: no search specific to `F_20`, `C_7⋊C_3`, `SL(2,3)`, `S_4`, `C_2×A_4` has been made. Independent evidence that the criterion tracks the real state of the art: it reproduces Bourne 2017's own statement that everything below order 12 is covered and that `A_4` and `Dic_3` are the order-12 residue. Finally, **"outside the PST class" is never a lower bound** — it means a new mechanism is needed, not that the height exceeds one (research rule 1).

The machine-readable candidate list is [CANDIDATES.md](CANDIDATES.md). Each candidate has a minimal-DFA builder in `tools/targets.py`, and

```bash
python3 -m tools.height_search --list
python3 -m tools.height_search --target a5_235 --max-size 12
```

runs a complete size-ordered synthesis search for a height-≤1 expression (search failure is never a lower bound).

## Quick start

```bash
./scripts/bootstrap.sh
./scripts/check.sh
```

The pinned toolchain is Lean `v4.32.0` with mathlib `v4.32.0` (locked by `lake-manifest.json`). `check.sh` builds the Lean library, runs the smoke file, the Python unit tests, the certificate checks, the claims-ledger lint, and the scan for unregistered proof holes. The API repairs of the first build are recorded in the First-build repair log of `PROOF_OBLIGATIONS.md`, and GitHub Actions CI (`.github/workflows/lean.yml`, with the mathlib cache) runs the same checks on every push.

## Main files

| File | Purpose |
|---|---|
| [RESULTS.md](RESULTS.md) | Primary record of analysis, machine search, constructions, and their verification (§5–§6 hold the current conclusions). |
| [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) | Status ledger for every mathematical claim (PROVED / CITED / COMPUTED / CONJECTURAL / SPECULATIVE / REFUTED / UNREVIEWED). |
| [CANDIDATES.md](CANDIDATES.md) | Tiered counterexample-candidate list with machine-readable targets. |
| [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) | Lean holes, mathematical dependencies, first-build repair log. |
| `notes/` | Full proof notes for individual results (A5 §5.6, Weis L2 §5.9–5.10, the small-group frontier, the simple-group reduction). |
| `scripts/a4_*.py`, `a5_*.py`, `weis_l2_*.py` | Verification scripts for each result (Python standard library only). |
| `scripts/small_group_pst_coverage.py` | Exact audit of which non-abelian groups of order ≤ 31 are covered by the published height-one theorems (the ladder above). |
| `tools/` | Certificate checker for generalized expressions (`regex_cert.py`), candidate DFA builders (`targets.py`), height-≤1 synthesis search (`height_search.py`). |
| [docs/SURVEY.md](docs/SURVEY.md) | Preceding work, verified claims, and a reading order. |
| [docs/SCENARIOS.md](docs/SCENARIOS.md) | Proof, disproof, partial-success, and failure scenarios. |
| [docs/ROADMAP.md](docs/ROADMAP.md) / [docs/SUGGESTIONS.md](docs/SUGGESTIONS.md) | Workshop plan and how to run the project. |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | Durable instructions for coding/research agents. |
| `docs/blueprint.{tex,pdf}` | Formalization blueprint. |
| `docs/textbook_*.{tex,pdf}` | Three role-specific primers. |
| `site/index.html` | Bilingual (ja/en) presentation slides for the workshop report — a self-contained HTML file; open it directly in a browser. |
| `site/a5_word_problem.html` | Interactive automaton for the word problem of `A_5 = <a,b \| a^2=b^3=(ab)^5=1>`: the 60-state Cayley graph drawn as a truncated dodecahedron, driven by a/b buttons (data built in `site/a5_cayley.js`, tested by `tests/test_a5_cayley.mjs`). |
| `GSH/` | Lean skeleton: executable definitions, theorem interfaces, and the challenge statement under `Challenges/`. |

## Non-negotiable research rules

1. **Do not call a computationally resistant candidate a lower bound.** Failure to synthesize a height-one expression up to a size bound is only a search result. Likewise, never promote bounded-exhaustive-plus-random verification (COMPUTED) to a theorem (PROVED).
2. **Do not identify "recognized by `M`" with "having syntactic monoid `M`."** The former is existential and stable under division; the latter is a minimality statement.
3. **Do not import restricted-star-height arguments without checking complementation.** "Star-height" here means generalized star-height unless explicitly marked `restricted`.
4. **No proof is announced from an AI transcript.** A result must survive domain-specific adversarial review, independent reconstruction, reference audit, and — where in scope — a clean Lean build. Statuses are upgraded only by adding a verification artifact to the ledger.
5. **Partial progress is preserved.** Failed mechanisms, counterexamples to sublemmas, and reusable formal infrastructure are never deleted; they are recorded in `RESULTS.md` and the ledger with the exact obstruction (the failure records in §5 are this policy in action).

## Recommended first assignments

- Formal-language theorist: audit `RESULTS.md` §5.6–5.9 and the proofs in `notes/`, especially the novelty check against the literature (Thomas 1981, the PST 1992 transfer lemma, Robson, Weis 2011).
- Group/number theorists: attack the (2,3,5)-type candidate, or verify and extend the reduction in `notes/simple_group_height1_reduction.md`.
- Lean team: get expert approval of the `L-GSH-CHALLENGE-001` statement, discharge the registered sorries in `GSH/Recognition.lean` (L-SYN-002 and the Schützenberger interface L-SF-001), and formalize the COMPUTED results via certificates.
- One independent referee: read only `docs/SCENARIOS.md`, the ledger, and candidate outputs; do not join the favored route during the first search wave.

## Provenance and verification status

Most artifacts in this repository — documents, proof notes, and code — were drafted by AI agents (Claude, and others as recorded per artifact) under human direction. No claim here asserts more than its ledger status: every mathematical statement carries an explicit status in [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md), and research rule 4 forbids announcing a proof from an AI transcript alone. Disclosure conventions for prompts and model versions are in [docs/CONTRIBUTIONS.md](docs/CONTRIBUTIONS.md).

## License

Code is released under MIT. Documentation is released under CC BY 4.0 unless a cited source imposes different terms. The included Ryuya template and bibliography remain source materials and are copied for workshop use.

---

<a id="日本語版"></a>

# 一般化スター高さ問題 ワークショップ・ブートストラップ（日本語版）

このリポジトリは、**一般化スター高さ問題（generalized star-height problem）** に取り組む形式言語理論・群論/数論・Lean の混成チームのための作業基盤です。数学的成果の記録は [RESULTS.md](RESULTS.md)、主張のステータス管理は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) が唯一の正です。

## 問題の正確な定式化

有限アルファベット `A` 上の一般化正規表現は、`∅`・`ε`・各文字から、和集合・連接・補集合（`A*` に対する）・Kleene スターで構成される。式の一般化スター高さはスターの最大入れ子深さ、言語の一般化スター高さはその言語を定義する式の高さの最小値である。

本プロジェクトは、しばしば混同される 2 つの問いを区別する:

1. **高さ 1 崩壊予想**: すべての正規言語は一般化スター高さ 1 以下である。
2. **決定問題**: 入力された正規言語の一般化スター高さを計算する。

一般化スター高さが 1 を超える言語は現在も知られていない（1960年代からの未解決問題）。高さ 1 崩壊が証明されれば、正確な計算は決定可能な「星無し vs 高さ 1」の判別に帰着する。反例が見つかれば決定問題自体は残るが、中心的な構造予想は解決する。

Lean 側では、この予想文が `GSH/Challenges/GeneralizedStarHeight.lean` に**明示的な open challenge** として登録されている（`PROOF_OBLIGATIONS.md` の L-GSH-CHALLENGE-001）。

## 現在地（2026-07-25 時点）

初期計画は「Bourne の梯子で最初の未解決だった位数 12 の `A_4` / `Dic_3` から始めて `A_5` を目指す」だったが、2026-07-22〜25 の計算的成果（詳細と検証水準はすべて `RESULTS.md`、ステータスは台帳）により最前線は大きく動いた:

- **有限群の障壁が位数 12 から位数 20 に移動した。** 位数 31 以下の非可換群のうち既知定理の被覆クラスの外にあるのはちょうど 6 群 — `A_4`(12), `F_20 = C_5⋊C_4`(20), `C_7⋊C_3`(21), `SL(2,3)`, `S_4`, `C_2×A_4`(24) — で、`A_4` は本リポジトリで解決済みなので**最小の未解決は `F_20`**。詳細は下の一覧表。
- **PST 1992 が提案し Weis 2011 が未解決として残したフル版 `L2` の一般化スター高さは 1**（`WEIS-L2-GSH-01`、COMPUTED、2026-07-25）。6 状態オートマトンではアンカー基準が破れるが、**立方体の 4 本の対角線への誘導作用**では成立する。制限スター高さは 2 なので、`L2` は gsh = 1 < rsh = 2 の明示的な標準例になる（`WEIS-L2-RSH-01`）。これは `C_2×S_4` が認識する**1 つの言語**の決着であり、`HeightOneForGroup (C_2×S_4)` は未解決のまま。
- **`A_4` は候補から完全に脱落**: 標準生成元でも全 12 元アルファベットでも高さ 1（§5〜5.5、COMPUTED）。したがって任意の生成射で高さ 1。
- **位数 ≤ 12 の全群が決着（2026-07-23、検証水準明記つき）**: 位数 < 12 と `C_12`・`C_6×C_2`・`Dih_6` は CITED（PST 1992）。`Dic_3` は明示的埋め込み `Dic_3 ↪ (C_3×C_4)⋊C_2` で PST のクラスに帰着（機械検証 `scripts/dic3_embedding.py`）— Bourne の位数 12 障壁の `Dic_3` 側を解消。`A_4` は全元アルファベット版＋自己完結化した全元還元（`FULL-ALPH-RED-01` PROVED、`A4-ALLLANG-01` COMPUTED）による。独立な人間査読は未了（台帳 `ORD12-ALL-01`）。
- **`A_5` ですら生成系によっては高さ 1**: (123),(145) の点安定化群フィルトレーション（§5.6）から始まり、機械判定可能な **anchor criterion**（§5.7）により「単一サイクル生成元がアンカー点を共有する生成系」はすべて高さ 1 に落ちる。
- **最有力の反例候補は (2,3,5) 型生成系の `A_5` word problem**（例: {(12)(34),(135)}）: 2 つの不可能性定理（§5.8）により、既知の全構成法（アンカー法・可換カウント法の Boolean 結合）の外にあることが機械検証つきで確定した最初の明示的インスタンス。次点は全 60 元アルファベット版。
- **PST が 1992 年に未解決としていた L(aab,0,4)**（|u|=3, 法 4）**も高さ 1**（§3, §5）。
- **「Weis L2」型の段階付き ba*b 対カウントは位相 mod 2 の範囲で高さ 1**（§5.9）。mod 3 以上は障害が特定された形で未解決。
- **下界の道具は依然として存在しない**。上の「候補」はすべて「既知手法が構造的に不適用」という意味であり、高さ ≥ 2 の証明ではない（研究ルール 1）。
- 非可換単純群の word problem に対する**単一観測器還元**の数学的証明ノートが `notes/simple_group_height1_reduction.md` にある（外部定理: PST の商閉性、Place–Zeitoun の star-free closure。新規性監査・独立査読・Lean 化は未了）。

## 非可換有限群の位数順一覧と、それぞれを最初に解決した人

有限群 `G` の **full solution** とは

> 任意の有限アルファベット、任意のモノイド射 `φ : Σ* → G`、任意の受理集合 `P ⊆ G` に対し、`φ⁻¹(P)` の一般化スター高さが 1 以下である

という主張（性質 `HeightOneForGroup G`）。「特定の生成射での word problem が高さ 1」より真に強い。可換群は Pin–Straubing–Thérien 1992 で一括して解決済みなので、以下は**非可換**群を位数順に並べ、本リポジトリが把握している最初の解決を記す。位数 31 以下の非可換群 45 個すべてを含み、被覆機構が同一の群は 1 行にまとめた。判定は `scripts/small_group_pst_coverage.py` による全数・厳密（約 3 秒。台帳 `PST-DIV-CRIT-01`, `DICM-EMB-01`, `SMALL-NONAB-31-01`, `FRONTIER-ORD20-01`、導出は `notes/small_group_pst_frontier.md`）。

機構の略号: **nil₂** = 冪零・class ≤ 2（`PST-GRP-02`）／**A⋊E** = 可換群 by 基本可換 2 群の分裂半直積（`PST-GRP-03`）／**div** = 同じ定理だが拡大が非分裂なので明示的埋め込み経由。

| 位数 | 非可換群 | 機構 | 最初の解決 |
|---|---|---|---|
| 6 | `S_3` | A⋊E | Pin–Straubing–Thérien 1992 |
| 8 | `D_4`, `Q_8` | nil₂ | Pin–Straubing–Thérien 1992 |
| 10 | `D_5` | A⋊E | Pin–Straubing–Thérien 1992 |
| 12 | `D_6` | A⋊E | Pin–Straubing–Thérien 1992 |
| 12 | `Dic_3` | div | PST 1992 ＋ 明示的埋め込み（本リポジトリ 2026-07-23、`DIC3-RED-01`）。Bourne 2017 では未解決扱い |
| 12 | `A_4` | PST クラス外 | 本リポジトリ 2026-07-22/23（`A4-ALLLANG-01`、`COMPUTED`、独立な人間査読は未了）。Bourne 2017 では未解決扱い |
| 14 | `D_7` | A⋊E | Pin–Straubing–Thérien 1992 |
| 16 | `D_8`, `SD_16` | A⋊E | Pin–Straubing–Thérien 1992 |
| 16 | `M_4(2)`, `D_4×C_2`, `Q_8×C_2`, `C_4⋊C_4`, `(C_2×C_2)⋊C_4`, `C_4∘D_4` | nil₂ | Pin–Straubing–Thérien 1992 |
| 16 | `Q_16` | div | PST 1992（埋め込みの明示は本リポジトリ 2026-07-25、`DICM-EMB-01`） |
| 18 | `D_9`, `C_3×S_3`, `(C_3×C_3)⋊C_2` | A⋊E | Pin–Straubing–Thérien 1992 |
| 20 | `D_10` | A⋊E | Pin–Straubing–Thérien 1992 |
| 20 | `Dic_5` | div | PST 1992（埋め込みの明示は本リポジトリ 2026-07-25、`DICM-EMB-01`） |
| **20** | **`F_20 = C_5⋊C_4`（忠実作用）** | PST クラス外 | **未解決 — 最小の未解決非可換群**（`N-F20-001`）。2 生成元の word problem は 2026-07-25 に高さ 1（`F20-STD-01`）、全 20 元アルファベットは未解決 |
| **21** | **`C_7⋊C_3`** | PST クラス外 | **未解決** — 最小の奇数位数例。Bourne が破綻した `A⋊C_3` そのもの（`N-C7C3-001`） |
| 22 | `D_11` | A⋊E | Pin–Straubing–Thérien 1992 |
| 24 | `C_4×S_3`, `D_12`, `(C_6×C_2)⋊C_2`, `C_2×C_2×S_3` | A⋊E | Pin–Straubing–Thérien 1992 |
| 24 | `C_3×D_4`, `C_3×Q_8` | nil₂ | Pin–Straubing–Thérien 1992 |
| 24 | `C_3⋊C_8`, `Dic_6`, `C_2×Dic_3` | div | PST 1992（埋め込みの明示は本リポジトリ 2026-07-25） |
| **24** | **`SL(2,3)`, `S_4`, `C_2×A_4`** | PST クラス外 | **未解決**（`N-S4-001`） |
| 26 | `D_13` | A⋊E | Pin–Straubing–Thérien 1992 |
| 27 | `F_3` 上の Heisenberg 群, `C_9⋊C_3` | nil₂ | Pin–Straubing–Thérien 1992 |
| 28 | `D_14`, `Dic_7` | A⋊E / div | Pin–Straubing–Thérien 1992（`Dic_7` の埋め込みは本リポジトリで明示） |
| 30 | `D_15`, `C_5×S_3`, `C_3×D_5` | A⋊E | Pin–Straubing–Thérien 1992 |
| 32 以上 | 未判定 | — | 位数 32 だけで非可換群が 44 個 |
| 60 | `A_5` | PST クラス外 | 未解決。**一部の**生成射については高さ 1 が判明（§5.6〜5.7） |

無限族として決着しているものが 2 つある: 二面体群 `D_n = C_n⋊C_2` は定義から PST の半直積であり、双環群 `Dic_n`（したがってすべての一般化四元数群 `Q_{2^k}`）は一律の式 `x ↦ v`, `y ↦ ut` で `(C_2 × C_{2n})⋊C_2` に埋め込まれる（`DICM-EMB-01`、`PROVED`）。

**「最初の解決」欄の読み方**: これは**本リポジトリが監査した範囲での**最古の出典であり、1992〜2026 年の文献を網羅調査した結果ではない。判定は `PST-GRP-01/02/03` ＋ `PST-WREATH-COMM-01`（2026-07-25）に対して行っている。後者は「PST 1992 の残るラッパー積定理は非可換群を 1 つも覆わない」ことを**証明**したもの — そのラッパー積は aperiodic の間に可換群の層が 1 枚だけなので、生成される pseudovariety の群はすべて可換になる。未確認なのは 1992〜2026 年の他文献で、`F_20`・`C_7⋊C_3`・`SL(2,3)`・`S_4`・`C_2×A_4` に特化した調査は行っていない。この基準が実際の技術水準を捉えている独立な証拠として、判定は Bourne 2017 自身の「位数 12 未満はすべて被覆、`A_4` と `Dic_3` が位数 12 の残り」という記述を再現している。なお **「PST クラス外」は決して下界ではない** — 新しい機構が必要という意味であって、高さが 1 を超えるという意味ではない（研究ルール 1）。

反例候補の機械可読リストは [CANDIDATES.md](CANDIDATES.md)。各候補には `tools/targets.py` の最小 DFA ビルダーがあり、

```bash
python3 -m tools.height_search --list
python3 -m tools.height_search --target a5_235 --max-size 12
```

で高さ ≤ 1 の式をサイズ順に完全列挙探索できる（探索失敗は下界ではない）。

## クイックスタート

```bash
./scripts/bootstrap.sh
./scripts/check.sh
```

固定ツールチェーンは Lean `v4.32.0` + mathlib `v4.32.0`（`lake-manifest.json` で固定）。`check.sh` は Lean ライブラリのビルド、スモークファイル、Python 単体テスト、証明書チェック、台帳 lint、未登録の証明穴の走査を一括で行う。初回ビルドの API 修理記録は `PROOF_OBLIGATIONS.md` の First-build repair log にあり、GitHub Actions の CI（`.github/workflows/lean.yml`、mathlib キャッシュ使用）が全 push で同じチェックを実行する。

## 主要ファイル

| ファイル | 役割 |
|---|---|
| [RESULTS.md](RESULTS.md) | 分析・計算機探索・構成と機械検証の一次記録（§5〜§6 が現在の結論）。 |
| [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) | 全数学的主張のステータス台帳（PROVED / CITED / COMPUTED / CONJECTURAL / SPECULATIVE / REFUTED / UNREVIEWED）。 |
| [CANDIDATES.md](CANDIDATES.md) | 階層化された反例候補リスト（機械可読ターゲット付き）。 |
| [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) | Lean の穴・数学的依存関係・初回ビルド修理ログ。 |
| `notes/` | 個別結果の完全な証明ノート（A5 §5.6、Weis L2 §5.9〜5.10、小さい群の frontier、単純群還元）。 |
| `scripts/a4_*.py`, `a5_*.py`, `weis_l2_*.py` | 各結果の検証スクリプト（Python 標準ライブラリのみ）。 |
| `scripts/small_group_pst_coverage.py` | 位数 ≤ 31 の非可換群のうちどれが既知の高さ 1 定理で被覆されるかの厳密判定（上の一覧表の根拠）。 |
| `tools/` | 一般化正規表現の証明書チェッカー（`regex_cert.py`）、候補 DFA ビルダー（`targets.py`）、高さ ≤ 1 式の合成探索（`height_search.py`）。 |
| [docs/SURVEY.md](docs/SURVEY.md) | 先行研究、検証済みの主張、読む順番。 |
| [docs/SCENARIOS.md](docs/SCENARIOS.md) | 証明・反証・部分成功・失敗の各シナリオ。 |
| [docs/ROADMAP.md](docs/ROADMAP.md) / [docs/SUGGESTIONS.md](docs/SUGGESTIONS.md) | ワークショップ計画と運営方法。 |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | コーディング/研究エージェント向けの恒久的指示。 |
| `docs/blueprint.{tex,pdf}` | 形式化ブループリント。 |
| `docs/textbook_*.{tex,pdf}` | 役割別の入門書 3 冊。 |
| `site/index.html` | ワークショップ報告用の二言語（日/英）発表スライド。自己完結の単一 HTML で、ブラウザで直接開ける。 |
| `site/a5_word_problem.html` | `A_5 = <a,b \| a^2=b^3=(ab)^5=1>` の word problem を触れるオートマトンにしたページ。60 状態の Cayley グラフを切頂十二面体として描き、a/b ボタンで遷移できる（データ構成は `site/a5_cayley.js`、テストは `tests/test_a5_cayley.mjs`）。 |
| `GSH/` | Lean スケルトン（実行可能定義と定理インターフェース、`Challenges/` に予想文）。 |

## 交渉不可能な研究ルール

1. **計算的に手強い候補を下界と呼ばない。** サイズ上限までの合成探索の失敗は探索結果にすぎない。同様に、有限長全数＋ランダム検証（COMPUTED）を定理（PROVED）に昇格させない。
2. **「`M` が認識する」と「構文モノイドが `M` である」を同一視しない。** 前者は存在的で division に安定、後者は最小性の主張である。
3. **restricted star-height の議論を補集合の扱いを確認せずに輸入しない。** 本リポジトリで「スター高さ」は明示がない限り generalized の意味。
4. **AI の出力から証明を宣言しない。** 結果は分野別の敵対的レビュー、独立な再構成、参照監査、範囲内なら clean な Lean ビルドを経て初めて成立する。ステータスの昇格は台帳への検証アーティファクト追加によってのみ行う。
5. **部分的進捗は保存する。** 失敗した機構・補題への反例・再利用可能な形式的基盤は削除せず、`RESULTS.md` と台帳に障害の内容つきで記録する（§5 の失敗記録はこの運用の実例）。

## 推奨される最初の作業

- 形式言語理論家: `RESULTS.md` §5.6〜5.9 と `notes/` の証明の監査、特に新規性の文献照合（Thomas 1981、PST 1992 の transfer lemma、Robson、Weis 2011 原文）。
- 群論/数論側: (2,3,5) 型候補への攻撃、または `notes/simple_group_height1_reduction.md` の還元の検証と拡張。
- Lean チーム: `L-GSH-CHALLENGE-001` の文の専門家承認、`GSH/Recognition.lean` の登録済み `sorry`（L-SYN-002 と Schützenberger インターフェース L-SF-001）の解消、COMPUTED 結果の証明書ベースの形式化。
- 独立レフェリー 1 名: `docs/SCENARIOS.md`・台帳・候補出力のみを読み、最初の探索段階では本命ルートに加わらない。

## 出自と検証状態

本リポジトリの成果物（文書・証明ノート・コード）の大部分は、人間の指示のもと AI エージェント（Claude ほか、各成果物に記録）が作成した草稿である。いかなる主張も台帳ステータス以上のことを意味しない：すべての数学的主張は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) に明示的なステータスを持ち、研究ルール 4 により AI の出力のみから証明を宣言することは禁じられている。プロンプトやモデルバージョンの開示方針は [docs/CONTRIBUTIONS.md](docs/CONTRIBUTIONS.md) にある。

## ライセンス

コードは MIT、ドキュメントは引用元が別条件を課さない限り CC BY 4.0。同梱の Ryuya テンプレートと文献リストは原資料であり、ワークショップ用に複製されている。
