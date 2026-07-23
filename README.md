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

## Where the project stands (as of 2026-07-23)

The initial plan was to climb Bourne's ladder from the first unresolved order-12 cases (`A_4` / `Dic_3`) toward `A_5`. The computational results of 2026-07-22/23 (details and verification levels in `RESULTS.md`; statuses in the ledger) moved the frontier substantially:

- **`A_4` is completely off the candidate list**: height 1 for the standard generators and for the full 12-element alphabet (§5–5.5, COMPUTED), hence for every generating morphism.
- **Even `A_5` collapses for many generating sets**: starting from the point-stabilizer filtration for (123),(145) (§5.6), the machine-checkable **anchor criterion** (§5.7) sends every generating set of single-cycle generators sharing an anchor point to height 1.
- **The leading counterexample candidate is the `A_5` word problem with (2,3,5)-type generators** (e.g. {(12)(34),(135)}): two impossibility theorems (§5.8) machine-verify that it lies outside every known construction (the anchor method and Boolean combinations of commutative counting). The runner-up is the full 60-element-alphabet version.
- **L(aab,0,4)** — the parameter case (|u| = 3, modulus 4) left open by Pin–Straubing–Thérien in 1992 — **is height 1** (§3, §5).
- **The staged ba*b pair-counting ("Weis L2") family is height 1 for phase mod 2** (§5.9); mod 3 and above remain open with the obstruction identified.
- **No lower-bound tool exists.** Every "candidate" above means "structurally out of reach of all known methods", never "proved of height ≥ 2" (research rule 1).
- A mathematical proof note of a **single-observer reduction** for word problems of non-abelian simple groups is in `notes/simple_group_height1_reduction.md` (external theorems: PST quotient closure, Place–Zeitoun star-free closure; novelty audit, independent review, and Lean formalization pending).

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
| `notes/` | Full proof notes for individual results (A5 §5.6, Weis L2 §5.9, the simple-group reduction). |
| `scripts/a4_*.py`, `a5_*.py`, `weis_l2_family.py` | Verification scripts for each result (Python standard library only). |
| `tools/` | Certificate checker for generalized expressions (`regex_cert.py`), candidate DFA builders (`targets.py`), height-≤1 synthesis search (`height_search.py`). |
| [SURVEY.md](SURVEY.md) | Preceding work, verified claims, and a reading order. |
| [SCENARIOS.md](SCENARIOS.md) | Proof, disproof, partial-success, and failure scenarios. |
| [ROADMAP.md](ROADMAP.md) / [SUGGESTIONS.md](SUGGESTIONS.md) | Workshop plan and how to run the project. |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | Durable instructions for coding/research agents. |
| `docs/blueprint.{tex,pdf}` | Formalization blueprint. |
| `docs/textbook_*.{tex,pdf}` | Three role-specific primers. |
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
- Lean team: get expert approval of the `L-GSH-CHALLENGE-001` statement, discharge the registered sorries in `Monoid.Syntactic` and `StarFree.Aperiodic`, and formalize the COMPUTED results via certificates.
- One independent referee: read only `SCENARIOS.md`, the ledger, and candidate outputs; do not join the favored route during the first search wave.

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

## 現在地（2026-07-23 時点）

初期計画は「Bourne の梯子で最初の未解決だった位数 12 の `A_4` / `Dic_3` から始めて `A_5` を目指す」だったが、2026-07-22〜23 の計算的成果（詳細と検証水準はすべて `RESULTS.md`、ステータスは台帳）により最前線は大きく動いた:

- **`A_4` は候補から完全に脱落**: 標準生成元でも全 12 元アルファベットでも高さ 1（§5〜5.5、COMPUTED）。したがって任意の生成射で高さ 1。
- **`A_5` ですら生成系によっては高さ 1**: (123),(145) の点安定化群フィルトレーション（§5.6）から始まり、機械判定可能な **anchor criterion**（§5.7）により「単一サイクル生成元がアンカー点を共有する生成系」はすべて高さ 1 に落ちる。
- **最有力の反例候補は (2,3,5) 型生成系の `A_5` word problem**（例: {(12)(34),(135)}）: 2 つの不可能性定理（§5.8）により、既知の全構成法（アンカー法・可換カウント法の Boolean 結合）の外にあることが機械検証つきで確定した最初の明示的インスタンス。次点は全 60 元アルファベット版。
- **PST が 1992 年に未解決としていた L(aab,0,4)**（|u|=3, 法 4）**も高さ 1**（§3, §5）。
- **「Weis L2」型の段階付き ba*b 対カウントは位相 mod 2 の範囲で高さ 1**（§5.9）。mod 3 以上は障害が特定された形で未解決。
- **下界の道具は依然として存在しない**。上の「候補」はすべて「既知手法が構造的に不適用」という意味であり、高さ ≥ 2 の証明ではない（研究ルール 1）。
- 非可換単純群の word problem に対する**単一観測器還元**の数学的証明ノートが `notes/simple_group_height1_reduction.md` にある（外部定理: PST の商閉性、Place–Zeitoun の star-free closure。新規性監査・独立査読・Lean 化は未了）。

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
| `notes/` | 個別結果の完全な証明ノート（A5 §5.6、Weis L2 §5.9、単純群還元）。 |
| `scripts/a4_*.py`, `a5_*.py`, `weis_l2_family.py` | 各結果の検証スクリプト（Python 標準ライブラリのみ）。 |
| `tools/` | 一般化正規表現の証明書チェッカー（`regex_cert.py`）、候補 DFA ビルダー（`targets.py`）、高さ ≤ 1 式の合成探索（`height_search.py`）。 |
| [SURVEY.md](SURVEY.md) | 先行研究、検証済みの主張、読む順番。 |
| [SCENARIOS.md](SCENARIOS.md) | 証明・反証・部分成功・失敗の各シナリオ。 |
| [ROADMAP.md](ROADMAP.md) / [SUGGESTIONS.md](SUGGESTIONS.md) | ワークショップ計画と運営方法。 |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | コーディング/研究エージェント向けの恒久的指示。 |
| `docs/blueprint.{tex,pdf}` | 形式化ブループリント。 |
| `docs/textbook_*.{tex,pdf}` | 役割別の入門書 3 冊。 |
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
- Lean チーム: `L-GSH-CHALLENGE-001` の文の専門家承認、`Monoid.Syntactic` と `StarFree.Aperiodic` の登録済み `sorry` の解消、COMPUTED 結果の証明書ベースの形式化。
- 独立レフェリー 1 名: `SCENARIOS.md`・台帳・候補出力のみを読み、最初の探索段階では本命ルートに加わらない。

## ライセンス

コードは MIT、ドキュメントは引用元が別条件を課さない限り CC BY 4.0。同梱の Ryuya テンプレートと文献リストは原資料であり、ワークショップ用に複製されている。
