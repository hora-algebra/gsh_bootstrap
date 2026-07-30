# generalized star-height problem ワークショップ・ブートストラップ

このリポジトリは、**generalized star-height problem** に取り組む形式言語理論・群論/数論・Lean の混成チームのための作業基盤です。数学的成果の記録は [RESULTS.md](RESULTS.md)、主張のステータス管理は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) が唯一の正です。

## このリポジトリが確立したこと

各ラベルの定義は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) 冒頭にある。最も重いのは
`COMPUTED`（有限対象への還元と全数走査で主張全体を決定した）と `EMPIRICAL`
（有限標本を検査した。反証はできるが確立はできない）の区別である。

1. **Lean で `sorry` なしに証明済み:** counting language の height ≤ 1、divisor
   による height-one property の移送、有限 commutative group、したがって位数 ≤ 5
   の全群。
2. **全数計算で決定済み（`COMPUTED`）:** Pin–Straubing–Thérien 1992 が提示し
   Weis 2011 が未解決とした full `L2` の generalized star-height = 1 かつ
   restricted star-height = 2；`L(aab,0,4)` の height 1（**新規ではない** —
   PST 1992 Theorem 7.4 が `L(a^i b a^j, k, n)` を全パラメータで覆っている。
   本 repo の寄与は独立な機械検証のみ）；`A_4` と `F_20` の2生成元 word
   problem；位数 ≤ 31 の非可換群 45 個すべての PST 被覆判定。
3. **最初の非可換群の全言語定理:** `HeightOneForGroup A_4` は数学的に証明済み
   （`A4-ALLLANG-01`, 2026-07-27）。有限部分の全数計算と Schützenberger の定理を
   合成する。Lean 形式化は未完。監査済み梯子で最小の未解決非可換群は位数 20 の
   `F_20` である。
4. **lower bound を出す道具は存在しない**（本 repo にも文献にも）。「候補」とは常に
   「既知のあらゆる手法の射程外」であって、「height ≥ 2 が証明された」ではない。

本 repo が行って撤回した主張は [RETRACTIONS.md](RETRACTIONS.md) に、それぞれを
今後捕捉するゲートとともに記録してある。

## 問題の正確な定式化

有限アルファベット `A` 上の一般化正規表現は、`∅`・`ε`・各文字から、和集合・連接・補集合（`A*` に対する）・Kleene スターで構成される。式の generalized star-height はスターの最大入れ子深さ、言語の generalized star-height はその言語を定義する式の高さの最小値である。

本プロジェクトは、しばしば混同される 2 つの問いを区別する:

1. **高さ 1 崩壊予想**: すべての正規言語は generalized star-height 1 以下である。
2. **決定問題**: 入力された正規言語の generalized star-height を計算する。

generalized star-height が 1 を超える言語は現在も知られていない（1960年代からの未解決問題）。高さ 1 崩壊が証明されれば、正確な計算は決定可能な「star-free vs 高さ 1」の判別に帰着する。反例が見つかれば決定問題自体は残るが、中心的な構造予想は解決する。

Lean 側では、この予想文が `GSH/Challenges/GeneralizedStarHeight.lean` に**明示的な open challenge** として登録されている（`PROOF_OBLIGATIONS.md` の L-GSH-CHALLENGE-001）。

## 現在地（2026-07-27 時点）

初期計画は「Bourne の梯子で最初の未解決だった位数 12 の `A_4` / `Dic_3` から始めて `A_5` を目指す」だったが、2026-07-22〜25 の計算的成果（詳細と検証水準はすべて `RESULTS.md`、ステータスは台帳）により最前線は大きく動いた:

- **監査済み有限群の障壁は位数 20**（`FRONTIER-ORD20-01`）。2026-07-25 の完全性監査は `A_4` の旧サンプル証拠を正しく撤回したが、2026-07-27 に全語を覆う有限 core と査読済み人間証明が完成した。`C_2×A_4` も subdirect-product 還元で従う。これは本リポジトリが監査した範囲の最前線であり、1992〜2026 年の全論文を網羅した主張ではない。
- **PST 1992 が提案し Weis 2011 が未解決として残したフル版 `L2` のgeneralized star-heightは 1**（`WEIS-L2-GSH-01`、COMPUTED、2026-07-25）。6 状態オートマトンではアンカー基準が破れるが、**立方体の 4 本の対角線への誘導作用**では成立する。restricted star-heightは 2 なので、`L2` は gsh = 1 < rsh = 2 の明示的な標準例になる（`WEIS-L2-RSH-01`）。これは `C_2×S_4` が認識する**1 つの言語**の決着であり、`HeightOneForGroup (C_2×S_4)` は未解決のまま。
- **`A_4`・全 12 元アルファベット版は証明済み**（`A4-FULL-01`, PROVED）。有限部分 `A4-FULL-FINITE-CORE-01` は 238,742 状態と 17/17 controls を全探索し、`notes/a4_full_alphabet_exact.md` が Schützenberger の定理と合成する。sorry-free Lean 定理 `heightOneForGroup_of_fullIdentityFiber` により任意の有限 alphabet・morphism・accepting set へ拡張できる（`A4-ALLLANG-01`, PROVED）。`A_4` 前提そのものの Lean 化は `L-A4-001` に残る。
- **位数 ≤ 12: 旧 `A_4` 数学ギャップは閉じたが、総合主張は `UNREVIEWED`。** 各群のケースは CITED または PROVED まで進み、EMPIRICAL な入力は残っていない。残るのは五群分類と被覆の独立監査、および Lean 定理 `heightOneUpTo_twelve`（`L-ORD12-GRP-001`, `L-ORD12-001`）。
- **`A_5` ですら生成系によっては高さ 1**: (123),(145) の点安定化群フィルトレーション（§5.6）から始まり、機械判定可能な **anchor criterion**（§5.7）により「単一サイクル生成元がアンカー点を共有する生成系」はすべて高さ 1 に落ちる。
- **最有力の反例候補は (2,3,5) 型生成系の `A_5` word problem**（例: {(12)(34),(135)}）: 2 つの不可能性定理（§5.8）により、既知の全構成法（アンカー法・可換カウント法の Boolean 結合）の外にあることが機械検証つきで確定した最初の明示的インスタンス。次点は全 60 元アルファベット版。
- **L(aab,0,4) も高さ 1**（§3, §5）。ただしこれは**先行研究であって新規結果ではない**。PST 1992 の **Theorem 7.4** が `h(L(a^i b a^j, k, n)) ≤ 1` を、`n` の squarefree 条件なし・語長の制限なしで述べており、`aab = a^2 b a^0` はその instance である。PST が `|u| = 3` で未解決として残したのは**3 文字が相異なる**場合の非 squarefree な `n`（Theorem 7.5 は `n` が squarefree であることを要求する）。本 repo の寄与は独立な機械検証（繰り上がり分解＋negative control）であり、priority ではない。
- **「Weis L2」型の段階付き ba*b 対カウントは phase mod 2 の範囲で高さ 1**（§5.9）。mod 3 以上は障害が特定された形で未解決。
- **下界の道具は依然として存在しない**。上の「候補」はすべて「既知手法が構造的に不適用」という意味であり、高さ ≥ 2 の証明ではない（研究ルール 1）。
- 非可換単純群の word problem に対する**単一観測器還元**の数学的証明ノートが `notes/simple_group_height1_reduction.md` にある（外部定理: PST の商閉性、Place–Zeitoun の star-free closure。新規性監査・独立査読・Lean 化は未了）。

## 位数31以下の非可換有限群：監査済みの解決状況

有限群 `G` の **full solution** とは

> 任意の有限アルファベット、任意のモノイド射 `φ : Σ* → G`、任意の受理集合 `P ⊆ G` に対し、`φ⁻¹(P)` の generalized star-height が 1 以下である

という主張（性質 `HeightOneForGroup G`）。「特定の生成射での word problem が高さ 1」より真に強い。

以下は「誰が最初に解決したか」ではなく、**現在の監査済みの数学的状況**を記す。1992〜2026年の全文献を網羅調査していないため、優先権は主張しない。位数31以下の非可換群45個をすべて含み、状態と機構が同じ場合だけ1行にまとめた。群の列挙とPST被覆は `scripts/research/small_group_pst_coverage.py` が全数検査する（約3秒、`SMALL-NONAB-31-01`, `FRONTIER-ORD20-01`）。

表示は次の3種類に限定する。

- **✅ Lean形式化完了**: 群ごとの定理がLean kernelで検査済み。
- **⭕️ 証明完了**: 数学的なfull solutionはあるが、群ごとのLean形式化は未完。
- **× 未知**: full solutionは未証明。部分成果がある場合は根拠欄に明記する。

内訳は、**✅ Lean形式化完了 0群、⭕️ 証明完了 41群、× 未知 4群**。未知4群のうち `F_20`, `C_7⋊C_3` には有意な部分成果があり、`SL(2,3)`, `S_4` には全元alphabetへの正の成果物が台帳上まだない。PST被覆の39群は、高さ定理が `CITED`、各群が定理の仮定を満たすことが `COMPUTED` である。残る証明完了2群は `A_4` と `C_2×A_4`。`A_4` もLean移送 `L-A4-001` は `OPEN` である。

機構の略号: **nil₂** = 冪零・class ≤ 2（`PST-GRP-02`）／**A⋊E** = 可換群 by 基本可換 2 群の分裂 semidirect product（`PST-GRP-03`）／**div** = 同じ定理だが拡大が非分裂なので明示的埋め込み経由。

| 位数 | 非可換群 | 機構 | 監査済みの状態と根拠 |
|---|---|---|---|
| 6 | `S_3` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 8 | `D_4`, `Q_8` | nil₂ | **⭕️ 証明完了** — `PST-GRP-02` `CITED`、被覆判定 `COMPUTED` |
| 10 | `D_5` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 12 | `D_6` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 12 | `Dic_3` | div | **⭕️ 証明完了** — `PST-GRP-03` `CITED` ＋ 明示的埋め込み `DIC3-RED-01` `PROVED` |
| 12 | **`A_4`** | PST クラス外 | **⭕️ 証明完了** — `A4-FULL-01` / `A4-ALLLANG-01` `PROVED`。Lean移送 `L-A4-001` は `OPEN` |
| 14 | `D_7` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 16 | `D_8`, `SD_16` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 16 | `M_4(2)`, `D_4×C_2`, `Q_8×C_2`, `C_4⋊C_4`, `(C_2×C_2)⋊C_4`, `C_4∘D_4` | nil₂ | **⭕️ 証明完了** — `PST-GRP-02` `CITED`、被覆判定 `COMPUTED` |
| 16 | `Q_16` | div | **⭕️ 証明完了** — `PST-GRP-03` `CITED` ＋ `DICM-EMB-01` `PROVED` |
| 18 | `D_9`, `C_3×S_3`, `(C_3×C_3)⋊C_2` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 20 | `D_10` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 20 | `Dic_5` | div | **⭕️ 証明完了** — `PST-GRP-03` `CITED` ＋ `DICM-EMB-01` `PROVED` |
| **20** | **`F_20 = C_5⋊C_4`（忠実作用）** | PST クラス外 | **× 未知**（部分成果あり） — 1つの2生成元語問題は `F20-STD-01` `COMPUTED`。全20元版は `N-F20-001` `OPEN` |
| **21** | **`C_7⋊C_3`** | PST クラス外 | **× 未知**（部分成果あり） — 全語に対する算術的再構成 `C7C3-IDENT-01` は `PROVED`。`C7C3-FULL-01` は `EMPIRICAL` で、高さ1の式は未構成（`N-C7C3-001`） |
| 22 | `D_11` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 24 | `C_4×S_3`, `D_12`, `(C_6×C_2)⋊C_2`, `C_2×C_2×S_3` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 24 | `C_3×D_4`, `C_3×Q_8` | nil₂ | **⭕️ 証明完了** — `PST-GRP-02` `CITED`、被覆判定 `COMPUTED` |
| 24 | `C_3⋊C_8`, `Dic_6`, `C_2×Dic_3` | div | **⭕️ 証明完了** — `PST-GRP-03` `CITED` ＋ 明示的埋め込み `PROVED` |
| **24** | **`SL(2,3)`**、**`S_4`** | PST クラス外 | **× 未知** — 全元alphabetへの正の成果物は未登録（`N-SL23-001`, `N-S4-001`）。`C_2×S_4` 認識言語 `L2` の解決は `S_4` 全体を解かない |
| 24 | `C_2×A_4` | subdirect還元 | **⭕️ 証明完了** — `A4-ALLLANG-01` ＋ `SUBDIRECT-RED-01`、ともに `PROVED` |
| 26 | `D_13` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 27 | `F_3` 上の Heisenberg 群, `C_9⋊C_3` | nil₂ | **⭕️ 証明完了** — `PST-GRP-02` `CITED`、被覆判定 `COMPUTED` |
| 28 | `D_14`, `Dic_7` | A⋊E / div | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、`Dic_7` の埋め込み `PROVED` |
| 30 | `D_15`, `C_5×S_3`, `C_3×D_5` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |

無限族として決着しているものが 2 つある: 二面体群 `D_n = C_n⋊C_2` は定義から PST の semidirect product であり、双環群 `Dic_n`（したがってすべての一般化四元数群 `Q_{2^k}`）は一律の式 `x ↦ v`, `y ↦ ut` で `(C_2 × C_{2n})⋊C_2` に埋め込まれる（`DICM-EMB-01`、`PROVED`）。

**範囲と出典の読み方**: `CITED`, `COMPUTED`, `PROVED`, `EMPIRICAL` は `CLAIMS_LEDGER.md` 冒頭の規範的な意味で用いる。とくに、群がPST定理の仮定に入るという計算は、それが参照する高さ定理そのものの証明ではない。監査対象は明記したPST定理と本リポジトリ内の還元であり、1992〜2026年の他文献は網羅調査していない。したがって `OPEN` はこの監査記録に相対的な状態であって、全出版物に関する断言ではない。**「PSTクラス外」は決して下界ではない**。位数32以上はこの表の監査範囲外。位数60の `A_5` は未解決だが、一部の生成射は `COMPUTED` である（§5.6〜5.7）。

反例候補の機械可読リストは [docs/CANDIDATES.md](docs/CANDIDATES.md)。各候補には `tools/targets.py` の最小 DFA ビルダーがあり、

```bash
python3 -m tools.height_search --list
python3 -m tools.height_search --target a5_235 --max-size 12
```

で高さ ≤ 1 の式をサイズ順に完全列挙探索できる（探索失敗は下界ではない）。

## クイックスタート

```bash
./scripts/ci/bootstrap.sh
./scripts/check.sh
```

固定ツールチェーンは Lean `v4.32.0` + mathlib `v4.32.0`（`lake-manifest.json` で固定）。`check.sh` は Lean ライブラリのビルド、スモークファイル、Python 単体テスト、証明書チェック、台帳 lint、未登録の証明穴の走査を一括で行う。初回ビルドの API 修理記録は `PROOF_OBLIGATIONS.md` の First-build repair log にあり、GitHub Actions の CI（`.github/workflows/lean.yml`、mathlib キャッシュ使用）が全 push で同じチェックを実行する。

## 主要ファイル

| ファイル | 役割 |
|---|---|
| [PROGRESS.md](PROGRESS.md) | **最初に読む。** 1画面で「どのアイデアがどこまで行き、何が詰まり、何が死んだか」と次の一手4つ。 |
| [RESULTS.md](RESULTS.md) | 分析・計算機探索・構成と機械検証の一次記録（§5〜§6 が現在の結論）。 |
| [RETRACTIONS.md](RETRACTIONS.md) | 本 repo が行って撤回した主張。各々がなぜ当時の検査を通過したかと、今それを捕捉するゲート。 |
| [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) | 全数学的主張のステータス台帳（PROVED / CITED / COMPUTED / EMPIRICAL / CONJECTURAL / SPECULATIVE / REFUTED / UNREVIEWED）。定義は同ファイル冒頭。最も重いのは COMPUTED と EMPIRICAL の区別で、プログラムが決定した主張と標本を取っただけの主張を分ける。 |
| [docs/CANDIDATES.md](docs/CANDIDATES.md) | 階層化された反例候補リスト（機械可読ターゲット付き）。 |
| [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) | Lean の穴と数学的依存関係。義務ごとに status がつく。 |
| `notes/` | 個別結果の完全な証明ノート（A5 §5.6、Weis L2 §5.9〜5.10、小さい群の frontier、単純群還元）。 |
| `scripts/research/` | 各結果の検証スクリプト、1結果1ファイル（Python 標準ライブラリのみ）。`scripts/ci/run_research.py` が再実行する。 |
| `scripts/research/small_group_pst_coverage.py` | 位数 ≤ 31 の非可換群のうちどれが既知の高さ 1 定理で被覆されるかの厳密判定（上の一覧表の根拠）。 |
| `tools/` | 一般化正規表現の証明書チェッカー（`regex_cert.py`）、候補 DFA ビルダー（`targets.py`）、高さ ≤ 1 式の合成探索（`height_search.py`）。 |
| [docs/SURVEY.md](docs/SURVEY.md) | 先行研究、検証済みの主張、読む順番。 |
| [docs/SCENARIOS.md](docs/SCENARIOS.md) | 証明・反証・部分成功・失敗の各シナリオ。 |
| [docs/ROADMAP.md](docs/ROADMAP.md) / [docs/SUGGESTIONS.md](docs/SUGGESTIONS.md) | ワークショップ計画と運営方法。 |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | コーディング/研究エージェント向けの恒久的指示。 |
| `docs/blueprint.{tex,pdf}` | 形式化ブループリント。追跡PDFの再生成は `cd docs && d=$(mktemp -d) && latexmk -pdf -outdir=$d blueprint.tex textbook_*.tex && [ $(ls $d/*.pdf | wc -l) -eq 4 ] && mv $d/*.pdf pdf/`。一時領域に出して4件揃ったときだけ公開するので、途中で失敗しても新旧の混在は起きない。 |
| `docs/textbook_*.{tex,pdf}` | 役割別の入門書 3 冊。 |
| `site/index.html` | **2026-07-25 に撤回し、版管理から外した。** 公開時点の位数12/frontier主張は `A_4` の有限標本に依存していたため、撤回は歴史的に正しい。2026-07-27 の新証明は削除済みスライドを遡及的に正当化しない。新しい公開物には owner preview が必要で、未完の Lean/分類境界を明記する。 |
| `site/a5_word_problem.html` | `A_5 = <a,b \| a^2=b^3=(ab)^5=1>` の word problem を触れるオートマトンにしたページ。60 状態の Cayley グラフを切頂十二面体として描き、a/b ボタンで遷移できる（データ構成は `site/a5_cayley.js`、テストは `tests/test_a5_cayley.mjs`）。 |
| `GSH/` | Lean スケルトン（実行可能定義と定理インターフェース、`Challenges/` に予想文）。 |

## 交渉不可能な研究ルール

1. **計算的に手強い候補を下界と呼ばない。** サイズ上限までの合成探索の失敗は探索結果にすぎない。同様に、有限長全数＋ランダム検証は `EMPIRICAL` であって `COMPUTED` ではなく、まして定理（`PROVED`）でもない。標本は反証はできても立証にならない。
2. **「`M` が認識する」と「syntactic monoid が `M` である」を同一視しない。** 前者は存在的で division に安定、後者は最小性の主張である。
3. **restricted star-height の議論を補集合の扱いを確認せずに輸入しない。** 本リポジトリで「star-height」は明示がない限り generalized の意味。
4. **AI の出力から証明を宣言しない。** 結果は分野別の敵対的レビュー、独立な再構成、参照監査、範囲内なら clean な Lean ビルドを経て初めて成立する。ステータスの昇格は台帳への検証アーティファクト追加によってのみ行う。
5. **部分的進捗は保存する。** 失敗した機構・補題への反例・再利用可能な形式的基盤は削除せず、`RESULTS.md` と台帳に障害の内容つきで記録する（§5 の失敗記録はこの運用の実例）。

## 推奨される最初の作業

- 形式言語理論家: `RESULTS.md` §5.6〜5.9 と `notes/` の証明の監査、特に新規性の文献照合（Thomas 1981、PST 1992 の transfer lemma、Robson、Weis 2011 原文）。
- 群論/数論側: (2,3,5) 型候補への攻撃、または `notes/simple_group_height1_reduction.md` の還元の検証と拡張。
- Lean チーム: `L-GSH-CHALLENGE-001` の文の専門家承認、Schützenberger インターフェース `L-SF-001` の形式化、COMPUTED 結果を検証済み証明書で信頼境界の内側へ移すこと。syntactic quotient monoid の前提 `L-SYN-002` は閉鎖済み。
- 独立レフェリー 1 名: `docs/SCENARIOS.md`・台帳・候補出力のみを読み、最初の探索段階では本命ルートに加わらない。

## 出自と検証状態

本リポジトリの成果物（文書・証明ノート・コード）の大部分は、人間の指示のもと AI エージェント（Claude ほか、各成果物に記録）が作成した草稿である。いかなる主張も台帳ステータス以上のことを意味しない：すべての数学的主張は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) に明示的なステータスを持ち、研究ルール 4 により AI の出力のみから証明を宣言することは禁じられている。プロンプトやモデルバージョンの開示方針は [docs/CONTRIBUTIONS.md](docs/CONTRIBUTIONS.md) にある。

## ライセンス

コードは MIT、ドキュメントは引用元が別条件を課さない限り CC BY 4.0。同梱の Ryuya テンプレートと文献リストは原資料であり、ワークショップ用に複製されている。
