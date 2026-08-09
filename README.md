# generalized star-height problem ワークショップ・ブートストラップ

このリポジトリは、**generalized star-height problem** に取り組む形式言語理論・群論/数論・Lean の混成チームのための作業基盤です。数学的成果の記録は [RESULTS.md](RESULTS.md)、主張のステータス管理は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) が唯一の正です。

## このリポジトリが確立したこと

各ラベルの定義は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) 冒頭にある。最も重いのは
`COMPUTED`（有限対象への還元と全数走査で主張全体を決定した）と `EMPIRICAL`
（有限標本を検査した。反証はできるが確立はできない）の区別である。

1. **Lean で `sorry` なしに証明済み:** counting language の height ≤ 1、divisor
   による height-one property の移送、有限 commutative group、可換な指数2部分群を
   持つ全群、そして **位数 ≤ 12 の全群**（`GSH.heightOneUpTo_twelve`）。
   **2026-07-28 完成、2026-08-04 main 統合:** Schützenberger の定理の難しい方向（local divisor
   による証明、`GSH/StarFree/`）、`A_4` の全 12 元アルファベット word problem、
   そして `HeightOneForGroup A_4` そのもの—すなわち **`A_4` が認識する
   全言語の height ≤ 1**。この完全形式化は Kazumi Kasaura
   （GitHub: [`Hziwara`](https://github.com/Hziwara)）により
   [PR #53](https://github.com/hora-algebra/gsh_bootstrap/pull/53) で提出・統合された。
   これを既存の可換群定理と新しい二項直積補題に接続し、任意の有限可換群 `C` に対する
   `HeightOneForGroup (C × A₄)`、特に `C₂ × A₄` も Lean で検査済みとなった
   （`LEAN-PROD-01` / `LEAN-A4PROD-01`）。この系は PR #53 の `A₄` 定理を前提として使い、
   その証明自体には変更を加えない。位数 ≤ 12 の証明も同じ方針で、`A₄` 分岐は
   Hziwara 氏の定理をそのまま呼び、それ以外だけを Sylow 理論と指数2埋め込みで補う。
2. **全数計算で決定済み（`COMPUTED`）:** Pin–Straubing–Thérien 1992 が提示し
   Weis 2011 が未解決とした full `L2` の generalized star-height = 1 かつ
   restricted star-height = 2；`L(aab,0,4)` の height 1（**新規ではない** —
   PST 1992 Theorem 7.4 が `L(a^i b a^j, k, n)` を全パラメータで覆っている。
   本 repo の寄与は独立な機械検証のみ）；`A_4` と `F_20` の2生成元 word
   problem；位数 ≤ 31 の非可換群 45 個すべての PST 被覆判定。
3. **最初の非可換群の全言語定理:** `HeightOneForGroup A_4`（`A4-ALLLANG-01`）。
   2026-07-27 に数学的に、2026-07-28 に **Lean で端から端まで**証明された
   （`GSH.A4FullAlphabet.heightOneForGroup_A4`）。二つの証明は独立である—前者は
   有限部分の全数計算と Schützenberger の定理の引用を合成し、後者はその
   定理自体を Lean 化する。監査済み梯子で最小の未解決非可換群は位数 20 の
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

## 現在地（2026-08-04 時点）

初期計画は「Bourne の梯子で最初の未解決だった位数 12 の `A_4` / `Dic_3` から始めて `A_5` を目指す」だったが、2026-07-22〜25 の計算的成果（詳細と検証水準はすべて `RESULTS.md`、ステータスは台帳）により最前線は大きく動いた:

- **監査済み有限群の障壁は位数 20**（`FRONTIER-ORD20-01`）。2026-07-25 の完全性監査は `A_4` の旧サンプル証拠を正しく撤回したが、2026-07-27 に全語を覆う有限 core と査読済み人間証明が完成した。`C_2×A_4` も subdirect-product 還元で従う。これは本リポジトリが監査した範囲の最前線であり、1992〜2026 年の全論文を網羅した主張ではない。
- **PST 1992 が提案し Weis 2011 が未解決として残したフル版 `L2` のgeneralized star-heightは 1**（`WEIS-L2-GSH-01`、COMPUTED、2026-07-25）。6 状態オートマトンではアンカー基準が破れるが、**立方体の 4 本の対角線への誘導作用**では成立する。restricted star-heightは 2 なので、`L2` は gsh = 1 < rsh = 2 の明示的な標準例になる（`WEIS-L2-RSH-01`）。これは `C_2×S_4` が認識する**1 つの言語**の決着であり、`HeightOneForGroup (C_2×S_4)` は未解決のまま。
- **`A_4`・全 12 元アルファベット版は証明済み**（`A4-FULL-01`, PROVED）。**独立な 2 つの証明がある。**(1) 人間の証明 `notes/a4_full_alphabet_exact.md`—有限部分 `A4-FULL-FINITE-CORE-01` は 238,742 状態と 17/17 controls を全探索し、Schützenberger の定理を引用して合成する。(2) **Kazumi Kasaura（GitHub: `Hziwara`）による Lean の完全な証明**（[PR #53](https://github.com/hora-algebra/gsh_bootstrap/pull/53)、`GSH/Results/A4FullAlphabet.lean` の `wordProblem_hasHeightAtMost_one`。`sorry` なし、公理は `[propext, Classical.choice, Quot.sound]` のみ）—こちらは Schützenberger の定理を引用せず、その難しい方向を local divisor 証明で Lean 化して使う（`GSH/StarFree/`、台帳 `LEAN-SCHUTZ-01` / `LEAN-CFREE-01`）。sorry-free 定理 `heightOneForGroup_of_fullIdentityFiber` と合成して `heightOneForGroup_A4` が得られるので、**`A4-ALLLANG-01` は端から端まで機械検証済み**となった（`L-A4-001` 閉鎖）。
- **位数 ≤ 12 の総合主張は Lean で証明済み**（`ORD12-ALL-01` / `LEAN-ORD12-01`, PROVED）。外部分類表を仮定せず、位数12の群を Sylow `3`-部分群数 `1 ∨ 4` で分け、前者から可換な指数2部分群、後者から `G ≃ A₄` を得る。主定理 `GSH.heightOneUpTo_twelve` は任意の有限アルファベット・任意の認識射・任意の受理集合を保つ。
- **`A_5` ですら生成系によっては高さ 1**: (123),(145) の点安定化群フィルトレーション（§5.6）から始まり、機械判定可能な **anchor criterion**（§5.7）により「単一サイクル生成元がアンカー点を共有する生成系」はすべて高さ 1 に落ちる。
- **最有力の反例候補は (2,3,5) 型生成系の `A_5` word problem**（例: {(12)(34),(135)}）: 2 つの不可能性定理（§5.8）により、既知の全構成法（アンカー法・可換カウント法の Boolean 結合）の外にあることが機械検証つきで確定した最初の明示的インスタンス。次点は全 60 元アルファベット版。
- **L(aab,0,4) も高さ 1**（§3, §5）。ただしこれは**先行研究であって新規結果ではない**。PST 1992 の **Theorem 7.4** が `h(L(a^i b a^j, k, n)) ≤ 1` を、`n` の squarefree 条件なし・語長の制限なしで述べており、`aab = a^2 b a^0` はその instance である。PST が `|u| = 3` で未解決として残したのは**3 文字が相異なる**場合の非 squarefree な `n`（Theorem 7.5 は `n` が squarefree であることを要求する）。本 repo の寄与は独立な機械検証（繰り上がり分解＋negative control）であり、priority ではない。
- **「Weis L2」型の段階付き ba*b 対カウントは phase mod 2 の範囲で高さ 1**（§5.9）。mod 3 以上は障害が特定された形で未解決。
- **下界の道具は依然として存在しない**。上の「候補」はすべて「既知手法が構造的に不適用」という意味であり、高さ ≥ 2 の証明ではない（研究ルール 1）。
- 非可換単純群の word problem に対する**単一観測器還元**の数学的証明ノートが `notes/simple_group_height1_reduction.md` にある（外部定理: PST の商閉性、Place–Zeitoun の star-free closure。新規性監査・独立査読・Lean 化は未了）。

## 位数60以下の非可換有限群：監査済みの解決状況

有限群 `G` の **full solution** とは

> 任意の有限アルファベット、任意のモノイド射 `φ : Σ* → G`、任意の受理集合 `P ⊆ G` に対し、`φ⁻¹(P)` の generalized star-height が 1 以下である

という主張（性質 `HeightOneForGroup G`）。「特定の生成射での word problem が高さ 1」より真に強い。

以下は「誰が最初に解決したか」ではなく、**現在の監査済みの数学的状況**を記す。1992〜2026年の全文献を網羅調査していないため、優先権は主張しない。位数60以下の非可換群210個をすべて含み、状態と機構が同じ場合だけ1行にまとめた。位数31以下は独立な純Python実装が全数検査する（`SMALL-NONAB-31-01`, `FRONTIER-ORD20-01`）。位数32〜60は GAP SmallGroups の `(order,id)` を併記する。同じ `StructureDescription` を持つ非同型群があるため、完全性は名前ではなくこのIDで検査する。

表示は次の3種類に限定する。

- **✅ Lean形式化完了**: 群ごとの定理がLean kernelで検査済み。
- **⭕️ 証明完了**: 数学的なfull solutionはあるが、群ごとのLean形式化は未完。
- **× 未知**: full solutionは未証明。部分成果がある場合は根拠欄に明記する。

内訳は、**✅ Lean形式化完了 8群、⭕️ 証明完了 170群、× 未知 32群**。Lean形式化済みには位数 ≤ 12 の非可換7群と `C₂×A₄` を数える。前者は群名ごとの列挙ではなく、全ての `G` に対する定理 `GSH.heightOneUpTo_twelve` で一括して覆う。一般定理は任意の有限可換 `C` に対する `C×A₄` も覆うが、SmallGroup ID との同型を Lean 化していない追加例はこの集計に入れない。位数32〜60で新たに加わった非可換正判定137群を含め、正判定178群はすべて `COVER-LE60-POS-01` の独立 checker が乗法表と構造 witness を全数再検査した。A4独自証明を入れる前の系列では40群が残るが、`A_4` とそのsubdirect帰結7群を `A4-ALLLANG-01` / `SUBDIRECT-RED-01` が回収し、現在の未知候補は32群（うちmonolithicで直接攻撃が必要なのは24群）。32群は witness の非存在を証明したものではなく、現行探索の残余にすぎない（`COVER-LE60-RESIDUAL-01` `UNREVIEWED`）。したがって高さ2以上の下界ではない。

機構の略号: **nil₂** = 冪零・class ≤ 2（`PST-GRP-02`）／**A⋊E** = 可換群 by 基本可換 2 群の分裂 semidirect product（`PST-GRP-03`）／**div** = 同じ定理だが拡大が非分裂なので明示的埋め込み経由／**subdirect還元** = 2つの真の商からの復元（`SUBDIRECT-RED-01`）。

| 位数 | 非可換群 | 機構 | 監査済みの状態と根拠 |
|---|---|---|---|
| 6 | `S_3` | 指数2 | **✅ Lean形式化完了** — `GSH.heightOneUpTo_twelve` / `LEAN-INDEX2-01` |
| 8 | `D_4`, `Q_8` | 指数2 | **✅ Lean形式化完了** — 非分裂の場合も含め `GSH.heightOneUpTo_twelve` / `LEAN-INDEX2-01` |
| 10 | `D_5` | 指数2 | **✅ Lean形式化完了** — `GSH.heightOneUpTo_twelve` / `LEAN-INDEX2-01` |
| 12 | `D_6` | 指数2 | **✅ Lean形式化完了** — `GSH.heightOneUpTo_twelve` / `LEAN-ORD12-01` |
| 12 | `Dic_3` | 指数2 | **✅ Lean形式化完了** — 非分裂拡大を専用 Krasner--Kaloujnine 埋め込みで処理する `GSH.heightOneUpTo_twelve` |
| 12 | **`A_4`** | Sylow `3` が4個 | **✅ Lean形式化完了** — `GSH.heightOneUpTo_twelve` の `G ≃ A₄` 分岐が、Kazumi Kasaura（GitHub: `Hziwara`）の PR #53 の定理を無変更で使用 |
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
| 24 | `C_2×A_4` | 二項直積 | **✅ Lean形式化完了** — `heightOne_C2_prod_A4`（`LEAN-A4PROD-01`）。入力となる `A₄` 定理は PR #53 |
| 26 | `D_13` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 27 | `F_3` 上の Heisenberg 群, `C_9⋊C_3` | nil₂ | **⭕️ 証明完了** — `PST-GRP-02` `CITED`、被覆判定 `COMPUTED` |
| 28 | `D_14`, `Dic_7` | A⋊E / div | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、`Dic_7` の埋め込み `PROVED` |
| 30 | `D_15`, `C_5×S_3`, `C_3×D_5` | A⋊E | **⭕️ 証明完了** — `PST-GRP-03` `CITED`、被覆判定 `COMPUTED` |
| 32 | `SmallGroup(32, 2) ≅ (C4 x C2) : C4`, `SmallGroup(32, 4) ≅ C8 : C4`, `SmallGroup(32, 5) ≅ (C8 x C2) : C2`, `SmallGroup(32, 12) ≅ C4 : C8`, `SmallGroup(32, 17) ≅ C16 : C2`, `SmallGroup(32, 22) ≅ C2 x ((C4 x C2) : C2)`, `SmallGroup(32, 23) ≅ C2 x (C4 : C4)`, `SmallGroup(32, 24) ≅ (C4 x C4) : C2`, `SmallGroup(32, 25) ≅ C4 x D8`, `SmallGroup(32, 26) ≅ C4 x Q8`, `SmallGroup(32, 27) ≅ (C2 x C2 x C2 x C2) : C2`, `SmallGroup(32, 28) ≅ (C4 x C2 x C2) : C2`, `SmallGroup(32, 29) ≅ (C2 x Q8) : C2`, `SmallGroup(32, 30) ≅ (C4 x C2 x C2) : C2`, `SmallGroup(32, 31) ≅ (C4 x C4) : C2`, `SmallGroup(32, 32) ≅ (C2 x C2) . (C2 x C2 x C2)`, `SmallGroup(32, 33) ≅ (C4 x C4) : C2`, `SmallGroup(32, 34) ≅ (C4 x C4) : C2`, `SmallGroup(32, 35) ≅ C4 : Q8`, `SmallGroup(32, 37) ≅ C2 x (C8 : C2)`, `SmallGroup(32, 38) ≅ (C8 x C2) : C2`, `SmallGroup(32, 46) ≅ C2 x C2 x D8`, `SmallGroup(32, 47) ≅ C2 x C2 x Q8`, `SmallGroup(32, 48) ≅ C2 x ((C4 x C2) : C2)`, `SmallGroup(32, 49) ≅ (C2 x C2 x C2) : (C2 x C2)`, `SmallGroup(32, 50) ≅ (C2 x Q8) : C2` | nil₂ | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 32 | `SmallGroup(32, 9) ≅ (C8 x C2) : C2`, `SmallGroup(32, 11) ≅ (C4 x C4) : C2`, `SmallGroup(32, 18) ≅ D32`, `SmallGroup(32, 19) ≅ QD32`, `SmallGroup(32, 39) ≅ C2 x D16`, `SmallGroup(32, 40) ≅ C2 x QD16`, `SmallGroup(32, 42) ≅ (C8 x C2) : C2`, `SmallGroup(32, 43) ≅ C8 : (C2 x C2)` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 32 | `SmallGroup(32, 20) ≅ Q32` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 32 | `SmallGroup(32, 10) ≅ Q8 : C4`, `SmallGroup(32, 13) ≅ C8 : C4`, `SmallGroup(32, 14) ≅ C8 : C4`, `SmallGroup(32, 41) ≅ C2 x Q16` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 32 | `SmallGroup(32, 6) ≅ (C2 x C2 x C2) : C4`, `SmallGroup(32, 7) ≅ (C8 : C2) : C2`, `SmallGroup(32, 8) ≅ C2 . ((C4 x C2) : C2) = (C2 x C2) . (C4 x C2)`, `SmallGroup(32, 15) ≅ C4 . D8 = C4 . (C4 x C2)`, `SmallGroup(32, 44) ≅ (C2 x Q8) : C2` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 34 | `SmallGroup(34, 1) ≅ D34` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 36 | `SmallGroup(36, 4) ≅ D36`, `SmallGroup(36, 10) ≅ S3 x S3`, `SmallGroup(36, 12) ≅ C6 x S3`, `SmallGroup(36, 13) ≅ C2 x ((C3 x C3) : C2)` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 36 | `SmallGroup(36, 1) ≅ C9 : C4` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 36 | `SmallGroup(36, 3) ≅ (C2 x C2) : C9`, `SmallGroup(36, 6) ≅ C3 x (C3 : C4)`, `SmallGroup(36, 7) ≅ (C3 x C3) : C4`, `SmallGroup(36, 11) ≅ C3 x A4` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 36 | `SmallGroup(36, 9) ≅ (C3 x C3) : C4` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 38 | `SmallGroup(38, 1) ≅ D38` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 39 | `SmallGroup(39, 1) ≅ C13 : C3` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 40 | `SmallGroup(40, 10) ≅ C5 x D8`, `SmallGroup(40, 11) ≅ C5 x Q8` | nil₂ | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 40 | `SmallGroup(40, 5) ≅ C4 x D10`, `SmallGroup(40, 6) ≅ D40`, `SmallGroup(40, 8) ≅ (C10 x C2) : C2`, `SmallGroup(40, 13) ≅ C2 x C2 x D10` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 40 | `SmallGroup(40, 4) ≅ C5 : Q8` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 40 | `SmallGroup(40, 1) ≅ C5 : C8`, `SmallGroup(40, 7) ≅ C2 x (C5 : C4)` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 40 | `SmallGroup(40, 3) ≅ C5 : C8`, `SmallGroup(40, 12) ≅ C2 x (C5 : C4)` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 42 | `SmallGroup(42, 3) ≅ C7 x S3`, `SmallGroup(42, 4) ≅ C3 x D14`, `SmallGroup(42, 5) ≅ D42` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 42 | `SmallGroup(42, 1) ≅ C7 : C6`, `SmallGroup(42, 2) ≅ C2 x (C7 : C3)` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 44 | `SmallGroup(44, 3) ≅ D44` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 44 | `SmallGroup(44, 1) ≅ C11 : C4` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 46 | `SmallGroup(46, 1) ≅ D46` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 48 | `SmallGroup(48, 21) ≅ C3 x ((C4 x C2) : C2)`, `SmallGroup(48, 22) ≅ C3 x (C4 : C4)`, `SmallGroup(48, 24) ≅ C3 x (C8 : C2)`, `SmallGroup(48, 45) ≅ C6 x D8`, `SmallGroup(48, 46) ≅ C6 x Q8`, `SmallGroup(48, 47) ≅ C3 x ((C4 x C2) : C2)` | nil₂ | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 48 | `SmallGroup(48, 4) ≅ C8 x S3`, `SmallGroup(48, 5) ≅ C24 : C2`, `SmallGroup(48, 6) ≅ C24 : C2`, `SmallGroup(48, 7) ≅ D48`, `SmallGroup(48, 14) ≅ (C12 x C2) : C2`, `SmallGroup(48, 25) ≅ C3 x D16`, `SmallGroup(48, 26) ≅ C3 x QD16`, `SmallGroup(48, 35) ≅ C2 x C4 x S3`, `SmallGroup(48, 36) ≅ C2 x D24`, `SmallGroup(48, 37) ≅ (C12 x C2) : C2`, `SmallGroup(48, 38) ≅ D8 x S3`, `SmallGroup(48, 43) ≅ C2 x ((C6 x C2) : C2)`, `SmallGroup(48, 51) ≅ C2 x C2 x C2 x S3` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 48 | `SmallGroup(48, 8) ≅ C3 : Q16` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 48 | `SmallGroup(48, 1) ≅ C3 : C16`, `SmallGroup(48, 9) ≅ C2 x (C3 : C8)`, `SmallGroup(48, 10) ≅ (C3 : C8) : C2`, `SmallGroup(48, 11) ≅ C4 x (C3 : C4)`, `SmallGroup(48, 12) ≅ (C3 : C4) : C4`, `SmallGroup(48, 13) ≅ C12 : C4`, `SmallGroup(48, 15) ≅ (C3 x D8) : C2`, `SmallGroup(48, 16) ≅ (C3 : Q8) : C2`, `SmallGroup(48, 17) ≅ (C3 x Q8) : C2`, `SmallGroup(48, 18) ≅ C3 : Q16`, `SmallGroup(48, 19) ≅ (C6 x C2) : C4`, `SmallGroup(48, 27) ≅ C3 x Q16`, `SmallGroup(48, 31) ≅ C4 x A4`, `SmallGroup(48, 34) ≅ C2 x (C3 : Q8)`, `SmallGroup(48, 39) ≅ (C4 x S3) : C2`, `SmallGroup(48, 40) ≅ Q8 x S3`, `SmallGroup(48, 41) ≅ (C4 x S3) : C2`, `SmallGroup(48, 42) ≅ C2 x C2 x (C3 : C4)`, `SmallGroup(48, 49) ≅ C2 x C2 x A4`, `SmallGroup(48, 50) ≅ (C2 x C2 x C2 x C2) : C3` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 48 | `SmallGroup(48, 3) ≅ (C4 x C4) : C3`, `SmallGroup(48, 28) ≅ C2 . S4 = SL(2,3) . C2`, `SmallGroup(48, 29) ≅ GL(2,3)`, `SmallGroup(48, 30) ≅ A4 : C4`, `SmallGroup(48, 32) ≅ C2 x SL(2,3)`, `SmallGroup(48, 33) ≅ ((C4 x C2) : C2) : C3`, `SmallGroup(48, 48) ≅ C2 x S4` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 50 | `SmallGroup(50, 1) ≅ D50`, `SmallGroup(50, 3) ≅ C5 x D10`, `SmallGroup(50, 4) ≅ (C5 x C5) : C2` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 52 | `SmallGroup(52, 4) ≅ D52` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 52 | `SmallGroup(52, 1) ≅ C13 : C4` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 52 | `SmallGroup(52, 3) ≅ C13 : C4` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 54 | `SmallGroup(54, 10) ≅ C2 x ((C3 x C3) : C3)`, `SmallGroup(54, 11) ≅ C2 x (C9 : C3)` | nil₂ | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 54 | `SmallGroup(54, 1) ≅ D54`, `SmallGroup(54, 3) ≅ C3 x D18`, `SmallGroup(54, 4) ≅ C9 x S3`, `SmallGroup(54, 7) ≅ (C9 x C3) : C2`, `SmallGroup(54, 12) ≅ C3 x C3 x S3`, `SmallGroup(54, 13) ≅ C3 x ((C3 x C3) : C2)`, `SmallGroup(54, 14) ≅ (C3 x C3 x C3) : C2` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 54 | `SmallGroup(54, 5) ≅ (C3 x C3) : C6`, `SmallGroup(54, 6) ≅ C9 : C6`, `SmallGroup(54, 8) ≅ ((C3 x C3) : C3) : C2` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 55 | `SmallGroup(55, 1) ≅ C11 : C5` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 56 | `SmallGroup(56, 9) ≅ C7 x D8`, `SmallGroup(56, 10) ≅ C7 x Q8` | nil₂ | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 56 | `SmallGroup(56, 4) ≅ C4 x D14`, `SmallGroup(56, 5) ≅ D56`, `SmallGroup(56, 7) ≅ (C14 x C2) : C2`, `SmallGroup(56, 12) ≅ C2 x C2 x D14` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 56 | `SmallGroup(56, 3) ≅ C7 : Q8` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 56 | `SmallGroup(56, 1) ≅ C7 : C8`, `SmallGroup(56, 6) ≅ C2 x (C7 : C4)` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 56 | `SmallGroup(56, 11) ≅ (C2 x C2 x C2) : C7` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 57 | `SmallGroup(57, 1) ≅ C19 : C3` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |
| 58 | `SmallGroup(58, 1) ≅ D58` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 60 | `SmallGroup(60, 8) ≅ S3 x D10`, `SmallGroup(60, 10) ≅ C6 x D10`, `SmallGroup(60, 11) ≅ C10 x S3`, `SmallGroup(60, 12) ≅ D60` | A⋊E | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 60 | `SmallGroup(60, 3) ≅ C15 : C4` | div | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 60 | `SmallGroup(60, 1) ≅ C5 x (C3 : C4)`, `SmallGroup(60, 2) ≅ C3 x (C5 : C4)`, `SmallGroup(60, 9) ≅ C5 x A4` | subdirect還元 | **⭕️ 証明完了** — 構造 witness を `COVER-LE60-POS-01` `COMPUTED` で独立再検査 |
| 60 | `SmallGroup(60, 5) ≅ A5`, `SmallGroup(60, 6) ≅ C3 x (C5 : C4)`, `SmallGroup(60, 7) ≅ C15 : C4` | 現行被覆外 | **× 未知** — 現行の被覆機構では未到達 |

無限族として決着しているものが 2 つある: 二面体群 `D_n = C_n⋊C_2` は定義から PST の semidirect product であり、双環群 `Dic_n`（したがってすべての一般化四元数群 `Q_{2^k}`）は一律の式 `x ↦ v`, `y ↦ ut` で `(C_2 × C_{2n})⋊C_2` に埋め込まれる（`DICM-EMB-01`、`PROVED`）。

**範囲と出典の読み方**: `CITED`, `COMPUTED`, `PROVED`, `EMPIRICAL`, `UNREVIEWED` は `CLAIMS_LEDGER.md` 冒頭の規範的な意味で用いる。とくに、群がPST定理の仮定に入るという計算は、それが参照する高さ定理そのものの証明ではない。監査対象は明記したPST定理と本リポジトリ内の還元であり、1992〜2026年の他文献は網羅調査していない。したがって `OPEN` はこの監査記録に相対的な状態であって、全出版物に関する断言ではない。**「現行被覆外」は決して下界ではない**。位数60の `A_5` は未解決だが、一部の生成射は `COMPUTED` である（§5.6〜5.7）。生成表・完全なID一覧・検査境界は `data/experiments/coverage_le60.tsv`、正判定 witness は `data/experiments/coverage_le60_witnesses.jsonl`、独立 checker は `scripts/ci/verify_small_group_witnesses.py`、導出は `notes/small_group_coverage_le60.md` にある。SmallGroups catalogue の完全性とID対応は外部入力 `CITED` のままである。

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
| `scripts/research/small_group_pst_coverage.py` / `scripts/gap/coverage_le60.g` / `scripts/ci/verify_small_group_witnesses.py` | 位数 ≤ 31 の独立監査、位数 ≤ 60 のGAP証明書生成、全280正判定の独立再検査（上の一覧表の根拠）。 |
| `tools/` | 一般化正規表現の証明書チェッカー（`regex_cert.py`）、候補 DFA ビルダー（`targets.py`）、高さ ≤ 1 式の合成探索（`height_search.py`）。 |
| [docs/SURVEY.md](docs/SURVEY.md) | 先行研究、検証済みの主張、読む順番。 |
| [docs/SCENARIOS.md](docs/SCENARIOS.md) | 証明・反証・部分成功・失敗の各シナリオ。 |
| [docs/ROADMAP.md](docs/ROADMAP.md) / [docs/SUGGESTIONS.md](docs/SUGGESTIONS.md) | ワークショップ計画と運営方法。 |
| [AGENTS.md](AGENTS.md) / [CLAUDE.md](CLAUDE.md) | コーディング/研究エージェント向けの恒久的指示。 |
| `docs/blueprint.{tex,pdf}` | 形式化ブループリント。追跡PDFの再生成は `cd docs && d=$(mktemp -d) && latexmk -pdf -outdir=$d blueprint.tex textbook_*.tex && [ $(ls $d/*.pdf | wc -l) -eq 4 ] && mv $d/*.pdf pdf/`。一時領域に出して4件揃ったときだけ公開するので、途中で失敗しても新旧の混在は起きない。 |
| `docs/textbook_*.{tex,pdf}` | 役割別の入門書 3 冊。 |
| `site/index.html` | **2026-07-25 に撤回し、版管理から外した。** 公開時点の位数12/frontier主張は `A_4` の有限標本に依存していたため、撤回は歴史的に正しい。後日の証明は削除済みスライドを遡及的に正当化しない。新しい公開物には owner preview が必要で、位数 ≤ 12 の総合 Lean 定理が 2026-08-04 に新たに完成したことを根拠とともに記す。 |
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
- Lean チーム: `L-GSH-CHALLENGE-001` の文の専門家承認と、残りの COMPUTED 結果を検証済み証明書で信頼境界の内側へ移すこと。`L-ORD12-GRP-001` / `L-ORD12-001` / `L-SYN-002` / `L-A4-001` は閉鎖済み。Schützenberger の定理は、実用上必要な方向（有限非周期モノイドが認識 ⇒ star-free）が `L-SF-004` として証明済み。`L-SF-001`（構文モノイド版の同値性）は逆方向と Myhill–Nerode を要するが、**何もブロックしていない**。
- 独立レフェリー 1 名: `docs/SCENARIOS.md`・台帳・候補出力のみを読み、最初の探索段階では本命ルートに加わらない。

## 出自と検証状態

本リポジトリの成果物（文書・証明ノート・コード）の大部分は、人間の指示のもと AI エージェント（Claude ほか、各成果物に記録）が作成した草稿である。いかなる主張も台帳ステータス以上のことを意味しない：すべての数学的主張は [CLAIMS_LEDGER.md](CLAIMS_LEDGER.md) に明示的なステータスを持ち、研究ルール 4 により AI の出力のみから証明を宣言することは禁じられている。プロンプトやモデルバージョンの開示方針は [docs/CONTRIBUTIONS.md](docs/CONTRIBUTIONS.md) にある。

## ライセンス

コードは MIT、ドキュメントは引用元が別条件を課さない限り CC BY 4.0。同梱の Ryuya テンプレートと文献リストは原資料であり、ワークショップ用に複製されている。
