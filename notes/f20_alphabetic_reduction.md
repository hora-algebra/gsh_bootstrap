# 経路(iv): inverse alphabetic morphism — 20文字から四つの固定4文字義務へ

**台帳行**: `ALPH-RED-01`、`SUBDIRECT-RED-01`、`F20-QUOT-OBS-01`、`F20-ALPH8-01`、`F20-ALPH7-OBS-01`、`F20-PHASE-RIGID-01`、`F20-ALPH4-RIGID-01`、`F20-ALPH5-01`、`F20-GENPAIR-AUDIT-01`、`DIC3-ALL-01`（`FRONTIER-ORD20-01` の現状もここで更新された）。導出はこの note にある（2026-07-26 に `RESULTS.md` の要約節をここへ統合したので、id で引くとここに来る）。

対象: `N-F20-001` の経路(iv)。「reversal 以外の closure property を使う。inverse **alphabetic**
morphism は height を保つので、full alphabet の identity fibre を reduced alphabet の instance
から再構成する」。

結論を先に書く。**経路(iv)は閉塞していない。** これまでの経路(i)–(iii)と違って、ここで得られる
のは obstruction ではなく還元である。

- 経路(iv)の**素直な形**（reduced alphabet の identity fibre の交叉）は、`F_20` が monolithic
  であるために閉塞する（§5）。だがそれは経路(iv)の一部にすぎない。
- **一般 accepting set**を許すと真に強くなり、simple group ですら還元できる（§6）。
- `F_20` への最初の適用では、20文字の obligation が単一の8文字alphabet、identity erasure後の
  7文字へ落ちた（§7）。その後、5文字下界が鋭い16座標構成を得て、最終的に**四つの固定4文字
  identity fibre**まで縮めた（§13）。
- 副産物として `C_2 × A_4` が `A_4` と同一の問題に合流し（2026-07-27 に `A4-ALLLANG-01` が
  `PROVED` になったので、合流の結果 `C_2 × A_4` も従う）、
  `Dic_3` の既知結果に独立な二つ目の証明がつく（§4）。
- 2026-08-01 の phase-rigidity とその強化により、この scheme を `F_20` 座標群だけで組む限り
  少なくとも1座標は5文字以上で、**2・3・4文字還元は不可能**（§§10–12）。この下界は鋭い:
  16座標の明示構成で全座標を5文字にでき、identity erasure 後の残余は4種類の特定4文字
  identity fibre に落ちる（§13）。ただしその4つの height-one 証明は未解決である。

旧8文字構成の機械検証は `scripts/research/f20_alphabetic_reduction.py`、鋭い5文字構成の有限入力検査は
`scripts/ci/f20_alph5_reduction.py`。run manifest はそれぞれ
`data/experiments/f20_alphabetic_reduction.md` と `data/experiments/f20_alph5_reduction.md`。

---

## 1. 記号

`G` を有限群、`Σ = G` を full alphabet（文字が群の元そのもの）、`mu : Σ* → G` を評価射、
`T = mu^{-1}(e)` を identity fibre とする。`FULL-ALPH-RED-01`（PROVED）により

> `HeightOneForGroup G` ⟺ `gsh(T) ≤ 1`

なので、以下すべて `T` の話をする。

morphism `h : Σ* → Δ*` が **alphabetic**（letter-to-letter, non-erasing）とは、各文字 `a` に対して
`h(a) ∈ Δ`（1文字）であること。とくに `h` は長さを保つ。erasing を許す場合（`h(a) = ε` があり
うる）は `FULL-ALPH-RED-02` の状況で、そこは別扱い。

---

## 2. 補題A（alphabetic closure）: `h^{-1}` は `gsh ≤ 1` を保つ

**補題A.** `h : Σ* → Δ*` が alphabetic なら、`gsh(L) ≤ 1 ⟹ gsh(h^{-1}(L)) ≤ 1`。

*証明.* 四段。

1. **Boolean.** 逆像なので `h^{-1}` は `∪`, `∩`, 補（`Σ*` 上の補）と可換。

2. **concatenation.** `h^{-1}(L_1 L_2) = h^{-1}(L_1) h^{-1}(L_2)`。
   `⊇` は明らか。`⊆`: `h(w) = u_1 u_2`（`u_i ∈ L_i`）とする。`h` は長さを保つので
   `|h(w)| = |w|`、よって `w = w_1 w_2` を `|w_i| = |u_i|` で切れる。`h` は letterwise なので
   `h(w_i) = u_i`。∎

3. **star.** `h^{-1}(L^*) = (h^{-1}(L))^*`。同じ議論で、`h(w) = v_1 ⋯ v_n`（`v_i ∈ L`）の
   切れ目をそのまま `w` に移す（`v_i = ε` は捨てる、`w = ε` は両辺に属す）。∎

4. **star-free は star-free に写る.** star-free expression の構成に関する帰納法。
   `h^{-1}(∅) = ∅`；1文字 `d ∈ Δ` に対して `h^{-1}({d}) = {a ∈ Σ : h(a) = d}` は**有限の文字集合**
   なので star-free；`h^{-1}(Δ*) = Σ*`；`∪`・補は 1、concatenation は 2。∎

`gsh ≤ 1` の expression は「star-free な部分式に star を1回だけかけ、あとは Boolean と
concatenation」で書ける。1・2・3・4 がその各構成子を保つので、`h^{-1}` は class を保つ。∎

これは `PST-CL-01`（CITED、「exact hypotheses must be checked」）のうち inverse alphabetic
morphism の部分を、non-erasing の場合について repo 内で自前に証明したものである。以降 CITED に
依存しない。

---

## 3. 補題B（剛性）: 素直な形は homomorphism を強制する

経路(iv)の素直な読み方は「reduced alphabet 上の**同じ問題**（identity fibre）の交叉として `T` を
書く」である。これは実は身動きが取れない。

**補題B.** `Σ = G` を full alphabet とする。関数 `f_j : G → G'_j`（`j = 1..k`）から誘導される
morphism を `mu_j : Σ* → G'_j`（文字 `g` を `f_j(g)` に送る）とする。もし

  `⋂_j mu_j^{-1}(e) = mu^{-1}(e) = T`

なら、**各 `f_j` は群準同型**であり、かつ `⋂_j mu_j^{-1}(e) = mu^{-1}(⋂_j ker f_j)`。

*証明.* `f = f_j` と書く。仮定の `⊇` 側、すなわち「`mu(w) = e ⟹ mu_f(w) = e`」を三つの語に当てる。

- `w = (e)`（identity 文字1つ）: `mu(w) = e` なので `f(e) = e`。
- `w = (g)(g^{-1})`: `mu(w) = e` なので `f(g) f(g^{-1}) = e`、すなわち `f(g^{-1}) = f(g)^{-1}`。
- `w = (g)(h)((gh)^{-1})`: `mu(w) = e` なので `f(g) f(h) f((gh)^{-1}) = e`。前項を `gh` に使えば
  `f((gh)^{-1}) = f(gh)^{-1}`、よって `f(g) f(h) = f(gh)`。∎

`f` が準同型なら `mu_f = f ∘ mu` なので `mu_f^{-1}(e) = mu^{-1}(ker f)`、交叉は
`mu^{-1}(⋂ ker f_j)`。`mu` は全射なので、これが `mu^{-1}(e)` に等しいのは `⋂ ker f_j = 1` のとき
に限る。∎

`|Δ_j| < |Σ|`（真に小さいアルファベット）は `f_j` が単射でないこと、すなわち
`ker f_j ≠ 1` と同値である。**この補題が効くのは full alphabet だからである**: 文字が群の元
すべてなので、上の三つの語がすべて `Σ*` の中に実在する。

機械検証（§3 of the script）: `C_4`, `C_6`, `S_3` について、`G → G` の**全ての**写像
（それぞれ 256, 46656, 46656 通り）を列挙し、長さ ≤ 3 の fibre 語をすべて保つ写像の集合が
endomorphism の集合と**完全に一致**することを確認した。長さ3で足りるのは証明が使う語が
長さ 1, 2, 3 だからで、これは補題の sharp な形である。

---

## 4. 定理C（subdirect reduction, 正の結果）

**定理C.** `G` を有限群、`N_1, …, N_k ⊴ G` を**非自明**な正規部分群で `⋂_j N_j = 1` とする。
各 `G/N_j` が height-one group（`HeightOneForGroup (G/N_j)`）なら、`G` も height-one group。

*証明.* `q_j : G → Q_j := G/N_j` を商写像とし、`h_j : Σ = G → Q_j = Σ_{Q_j}` を「文字 `g` を文字
`q_j(g)` に送る」写像から誘導される morphism とする。これは alphabetic である（`Q_j` の full
alphabet に落ちる）。すると

  `h_j^{-1}(T_{Q_j}) = { w : ∏ q_j(w_i) = e } = { w : q_j(mu(w)) = e } = mu^{-1}(N_j)`。

`HeightOneForGroup (Q_j)` と `FULL-ALPH-RED-01` から `gsh(T_{Q_j}) ≤ 1`、補題Aから
`gsh(mu^{-1}(N_j)) ≤ 1`。`⋂ N_j = 1` なので `T = ⋂_j mu^{-1}(N_j)`、Boolean closure から
`gsh(T) ≤ 1`。再び `FULL-ALPH-RED-01` で `HeightOneForGroup G`。∎

**系C1（direct product closure）.** height-one group の class は有限 direct product で閉じる。
（`G = Q_1 × Q_2` に `N_1 = 1 × Q_2`, `N_2 = Q_1 × 1` を取る。）

**系C2（frontier は monolithic に限る）.** 「非自明な正規部分群が交叉して 1 になる」は
「`G` が **monolithic でない**」と同値である。実際、極小正規部分群が2つ以上あればその交叉は
両方に真に含まれる正規部分群なので 1；逆に極小正規部分群 `M` が一意なら任意の非自明正規部分群は
`M` を含むので交叉も `M` を含む。したがって **monolithic でない群は真の商に還元される**。
直接攻撃が必要なのは monolithic な群だけである。

> 注意（citation obligation）: 系C1「height-one は direct product で閉じる」は folklore の
> 可能性がある。ここには完全な証明があるので status は PROVED だが、先行文献の確認は
> `N-ALPH-CITE-001` として未了である。PST 1992 item 7 は **non-**alphabetic な inverse morphism
> が height を保た**ない**と述べており、そこと矛盾しない（補題Aは alphabetic に限る）。

### 4.1 既知データでの照合と、frontier の剪定

`SMALL-NONAB-31-01` によれば、位数 31 以下の非可換群 45 個のうち PST クラス外は6個:
`A_4`(12), `F_20`(20), `C_7⋊C_3`(21), `SL(2,3)`(24), `S_4`(24), `C_2×A_4`(24)。
monolith を機械計算した（script §2）:

| 群 | 位数 | 正規部分群 | monolith | 判定 |
|---|---|---|---|---|
| `F_20 = C_5⋊C_4` | 20 | 4 | `C_5`（位数5） | MONOLITHIC |
| `C_7⋊C_3` | 21 | 3 | 位数7 | MONOLITHIC |
| `SL(2,3)` | 24 | 4 | 位数2（中心） | MONOLITHIC |
| `S_4` | 24 | 4 | `V_4`（位数4） | MONOLITHIC |
| `A_4` | 12 | 3 | `V_4`（位数4） | MONOLITHIC |
| **`C_2 × A_4`** | 24 | 6 | **自明** | **定理Cで還元** |
| `Dic_3` | 12 | 5 | **自明** | **定理Cで還元** |
| `C_2 × S_4` | 48 | 9 | **自明** | **定理Cで還元** |

読み取れることが三つある。

1. **`C_2 × A_4` は独立な問題ではなくなり、`A_4` に合流する。** `C_2` は abelian なので、
   系C1により **`C_2 × A_4` が height-one ⟺ `A_4` が height-one**。この同値は
   `SUBDIRECT-RED-01`（`PROVED`）であって `A_4` の解決には依存しない。証明は両方向を要する:
   (⇐) は系C1（直積閉性）、(⇒) は `A_4` が `C_2 × A_4` の商かつ部分群であることと
   `LEAN-TRANSFER-01`（height-one は単射・全射群射に沿って降下する）による。系C1 だけでは
   一方向しか出ない。
   **2026-07-27 更新**: `A4-ALLLANG-01` が `PROVED` になったので、この同値により
   `C_2 × A_4` も `PROVED` となり、両者とも frontier から外れる。独立な未解決は
   `F_20`(20), `C_7⋊C_3`(21), `SL(2,3)`(24), `S_4`(24) の**4個**である。
   （経緯: 当初は「未解決リストは4個」と書き、2026-07-25 の完全性監査が `A4-ALLLANG-01` を
   `EMPIRICAL` に降格したため「`A_4` を含む5個」に撤回し、2026-07-27 の新しい証明で
   再び4個になった。撤回は当時のサンプル証拠に対して正しく、遡って無効になるわけではない。）

2. **`Dic_3` に独立な二つ目の証明がつく。** `Dic_3` は中心 `C_2` と `C_3` を持ち交叉は自明、
   商は `Dic_3/C_2 ≅ S_3`（位数6の非可換群）と `Dic_3/C_3 ≅ C_4`。どちらも位数 12 未満なので
   PST 1992 Cor. 7.7 で covered。したがって `DIC3-ALL-01` は `DIC3-RED-01` の埋め込みを経由せず
   にも従う。既知の結論を別ルートで再現できたので、これは定理Cの positive control である
   （機械検証済み: 商の位数・可換性・元の位数分布を照合）。

3. **`C_2 × S_4` は `S_4` に完全に帰着する。** `N-S4-001` の後半（`HeightOneForGroup (C_2×S_4)`）
   は、系C1により前半 `HeightOneForGroup S_4` から自動的に従う。独立な obligation ではない。

**再利用可能な手順**: PST クラス外の群を新しく見つけたら、**まず monolith を計算する**。
自明なら定理Cで真の商に落ちるので、直接攻撃してはいけない。

---

## 5. 障害D: `F_20` は monolithic なので素直な形は閉塞

`F_20` の正規部分群は `1`, `C_5`（translation part）, `D_5`（位数10）, `F_20` の4つだけで、
非自明なものはすべて `C_5` を含む（機械検証済み）。よって補題Bと合わせて:

**障害D.** full alphabet 上で reduced-alphabet の identity fibre をいくら交叉させても、
得られるのは `mu^{-1}(N)`（`N ⊇ C_5`）であり、決して `T = mu^{-1}(e)` には届かない。

得られる最良は `N = C_5` の場合、すなわち

  **`gsh(mu^{-1}(C_5)) ≤ 1`**（`F_20/C_5 ≅ C_4` は abelian なので height-one）

である。これは positive な部分結果ではあるが、内容は「phase（`ε` の総和 mod 4）が 0 という条件
だけなら height 1」で、`F20-FULL-OBS-01` が「`β` は formally 決まっており GF(5) の線形代数は
bottleneck ではない」と言っていたことの裏返しでもある。**残る困難は phase 0 の上での `C_5` 座標
の分離に完全に局在している。**

---

## 6. 定理E: 一般 accepting set では真に強い（simple group でも還元できる）

補題Bが強制するのは「accepting set を `{e}` に固定した交叉形」の場合だけである。reduced-alphabet
instance の accepting set を自由に取り、Boolean 結合を許すと状況が変わる。

一般形はこうなる。`f_j : G → G'_j` を任意の写像、`Φ = (mu_1, …, mu_k) : Σ* → ∏_j G'_j`、
`H = ⟨Φ(Σ*)⟩` とする。`mu_j^{-1}(A_j)` の Boolean 結合全体は cylinder の生成する Boolean 代数
なので `Φ^{-1}(S)`（`S ⊆ ∏G'_j` 任意）を尽くす。よって

> `T` が reduced-alphabet instance の Boolean 結合になる
> ⟺ **`mu` が `Φ` を経由して分解する**、すなわち準同型 `rho : H → G` が存在して `mu = rho ∘ Φ`
> ⟺ `K = ⟨(Φ(g), g) : g ∈ Σ⟩ ≤ (∏G'_j) × G` が `K ∩ (1 × G) = 1` を満たす。

（`⟸` は `T = Φ^{-1}(ker rho)`。`⟹` は、`Φ(w) = Φ(w')` のとき `mu(w) = mu(w')` が必要で、これが
ちょうど `K ∩ (1×G) = 1`。）これは**有限で決定可能な条件**である。

**定理E.** この一般形は補題Bの形より真に強い。実際 `G = C_5`（simple、したがって monolithic）で
成立する。`β ↦ (a_β, b_β)` を

| `β` | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| `a_β` | 0 | 1 | 0 | 0 | 1 |
| `b_β` | 0 | 0 | 2 | 3 | 3 |

と取ると `a_β + b_β = β`、`β ↦ (a_β,b_β)` は単射、像は `A = {0,1}`（2文字）と `B = {0,2,3}`
（3文字）でどちらも真に小さい。`rho(u,v) = u+v` は `C_5 × C_5 → C_5` の準同型なので分解が成立し、

  `T = ⋃_{c ∈ Z/5} ( mu_1^{-1}(c) ∩ mu_2^{-1}(-c) )`

は5個の rectangle の union になる。`a` も `b` も準同型ではない（補題Bをすり抜けている）。
長さ ≤ 7 の全 97,656 語で機械検証済み。

要点は「群の元を、**小さい像しか持たない部品の積に分解する**」であって、部品が準同型である
必要はない。

---

## 7. 定理F: `F_20` の 20文字 → 8文字 → 7文字

**定理F.** `Δ = Z/4 × {0,1} ⊆ F_20`（8文字）とする。`F_20` が認識する `Δ*` 上のすべての言語が
`gsh ≤ 1` なら、`gsh(T_Σ) ≤ 1`、したがって `HeightOneForGroup F_20`。

*構成.* 元を `(ε, β)`（`ε ∈ Z/4`, `β ∈ Z/5`）で書き、積は
`(ε,β)(ε',β') = (ε+ε', 2^{ε'}β + β')`（repo の `f20_full_alphabet.compose` と一致、
`α = 2^ε` の読み替えで400積すべて照合済み）。

- `k = 4` 座標を取り、`H = { (x_1,…,x_4) ∈ F_20^4 : 4つの phase が等しい } ≅ (C_5^4) ⋊ C_4`
  （位数 2500）。これは部分群である。
- `rho(ε, u_1,…,u_4) = (ε, Σ_i u_i)`。これは**準同型**である:
  積の第 `i` 座標は `2^{ε'}u_i + u'_i` なので、総和は `2^{ε'}(Σu_i) + (Σu'_i)` となり、
  ちょうど `F_20` の積の形になる。（全 `2500² = 6{,}250{,}000` 対で網羅検証。）
- `β` を4つの `{0,1}` 値に分割する:

  | `β` | 0 | 1 | 2 | 3 | 4 |
  |---|---|---|---|---|---|
  | `(a_1,a_2,a_3,a_4)` | 0000 | 1000 | 1100 | 1110 | 1111 |

  `Σ a_i = β (mod 5)` で、5つの tuple は互いに異なる。
- `λ(ε,β) = ((ε,a_1), (ε,a_2), (ε,a_3), (ε,a_4)) ∈ H`。すると `rho(λ(g)) = g`（全20文字で検証）。

`λ` は文字ごとの写像なので、各座標 `f_j(ε,β) = (ε, a_j(β))` は alphabetic morphism
`h_j : Σ* → Δ*` を誘導し、その像は4座標すべてで**同じ8文字**
`Δ = {(ε,a) : ε ∈ Z/4, a ∈ {0,1}}`。`Φ(w) = ∏_i λ(w_i) ∈ H` なので `mu = rho ∘ Φ`
（長さ ≤ 4 の全 168,421 語で網羅検証、長さ 5..40 の乱択 60,000 語でも検証）。したがって

  `T_Σ = Φ^{-1}(ker rho) = ⋃_{(g_1,…,g_4) ∈ ker rho} ⋂_{j=1}^{4} h_j^{-1}( mu_Δ^{-1}(g_j) )`

（`|ker rho| = 125` 項）。`mu_Δ^{-1}(g)` は `Δ*` 上の `F_20`-recognized language、`h_j^{-1}` は
補題Aで `gsh ≤ 1` を保ち、有限 union/intersection も保つ。∎

**7文字への追加削減.** `Δ` は identity `(0,0)` を含むので、`FULL-ALPH-RED-02` と同じ erasure の
議論がそのまま使える（`mu(v) = mu(pi(v))` を長さ ≤ 5 の全 37,449 個の `Δ` 語で検証）。
よって obligation は `Δ ∖ {e}` の**7文字**になる。

**accepting set の始末.** 「すべての accepting set」は identity fibre 一つに落とせる。`Δ` は
`F_20` を生成するので各 `g` に対し `mu(u_g) = g^{-1}` なる `u_g ∈ Δ*` があり、
`mu_Δ^{-1}(g) = T_Δ u_g^{-1}`（語による right quotient）。`gsh ≤ 1` は単文字 quotient で閉じる
（`FULL-ALPH-RED-01` の自前補題 §3.5、Brzozowski derivative）ので反復してよい。よって定理Fの
仮定は **`gsh(T_Δ) ≤ 1`** 一つでよい。

---

## 8. 補題G: 残る座標は `F_20` instance でなければならない

**補題G.** `𝒞` を subgroup, quotient, direct product で閉じた群の class とし `F_20 ∉ 𝒞` とする。
このとき、`F_20` の route-(iv) 還元で**すべての**座標群 `K_j = ⟨Δ_j⟩` が `𝒞` に属するものは
存在しない。

*証明.* 分解 `mu = rho ∘ Φ` があれば `G = F_20` は `H ≤ ∏_j K_j` の商である。`𝒞` は
direct product・subgroup・quotient で閉じるので `F_20 ∈ 𝒞`、矛盾。∎

`𝒞 =`「abelian by elementary abelian 2」（PST クラスの一部、`DIC3-RED-01` の語法）を取ると:
この class は三演算で閉じており（`A_1×A_2`、`H ∩ A`、`AN/N` を取ればよい）、機械検証で
`C_4`, `C_5`, `C_20`, `C_2×C_2`, `D_5`, `S_3` は属し、**`F_20` は属さない**。さらに `F_20` の
14個の部分群のうち `𝒞` を外れるのは `F_20` 自身だけである（位数の内訳
1,2,2,2,2,2,4,4,4,4,4,5,10,20 をすべて判定）。

**帰結.** `Δ_j ⊆ F_20` の範囲では、少なくとも一つの座標は `⟨Δ_j⟩ = F_20`、すなわち
**`F_20` を生成する真の sub-alphabet 上の instance** でなければならない。定理Fの8文字は
まさにそれである（`Δ` は `F_20` を生成する）。

これは経路(iv)の性格を決める。**経路(iv)は既知の height-one 群だけを使って frontier を越える
ことはできない。** 使えるのは `F20-STD-01` のような**アルファベット限定の結果**だけである。

（未検討の変種: 座標群として `F_20` の部分群でない群、たとえば `A_4`（`A4-ALLLANG-01` で
height-one だが `𝒞` の外）を使う道は補題Gでは排除されていない。§10 に登録する。）

---

## 9. 主張していないこと

- **8文字還元は既知の障害を回避しない。** 機械検証した:
  `Δ` は `ε = 2` の文字 `(2,0)`, `(2,1)` を含むので `F20-FULL-OBS-01` の period-2 の原因は残る。
  `F20-SUB10-OBS-01` の minimal witness `k = (0,0)`, `u_0 = (1,0)`, `u_1 = (1,1)` は3文字すべて
  `Δ` の中にあり、`k u_0 u_1 k` と `k u_1 u_0 k` の像は `Δ` 上でも `(2,1)` と `(2,2)` で異なる。
  つまりあの obstruction は8文字 instance にそのまま transfer する。
  → **定理Fは obligation を小さくしたが、mechanism を与えていない。**
- **7文字 instance も旧cut機構では閉じない** (`F20-ALPH7-OBS-01`, `COMPUTED`)。
  上の witness 自体は `k` が identity なので erasure で消えるが、端点を非自明な非mover
  `k=(0,1)` に替えた
  `k(1,0)(1,1)k` と `k(1,1)(1,0)k` が、両方向の全36 feature fieldsで一致しながら
  像 `(2,1)` と `(2,2)` を分ける。さらに7文字上では base/single/pair の全17 signatureが
  非周期的でない。したがって実際には認証できないbase/single座標まで無償で与えても衝突する。
  長さ3以下の全400語には衝突がないので、これはこのfeature familyの最短衝突である。
- **これは lower bound ではない**（research rule 1）。どの言語の height も下から押さえていない。
- 定理C・系C1は folklore の可能性があり、先行文献の確認は未了（`N-ALPH-CITE-001`）。
- 定理Eの `C_5` 構成は「経路(iv)が simple group でも動く」ことの存在証明であって、`C_5` について
  新しい数学ではない（abelian なので既知）。

---

## 10. phase rigidity: 2文字・3文字への還元は不可能

§6 の一般形を `G=F_20`、全座標群も `F_20` として考える。すなわち任意の有限 `k`、
写像 `f_j:G→Δ_j⊆G`、`λ(g)=(f_1(g),…,f_k(g))` を取り、
`H=⟨λ(G)⟩≤G^k` とする。準同型 `rho:H→G` が `rho(λ(g))=g` を満たすと仮定する。

**定理H（`F20-PHASE-RIGID-01`）。** ある座標 `j` が、すべての `g∈G` について

`phase(f_j(g)) = phase(g)`

を満たす。従って `|Δ_j|≥4`、特に `max_j |Δ_j|≥4` である。この結論は `k` に依存せず、
equal-phase family を仮定しない。

*証明.* `N=C_5◁G`、`Q=G/N=C_4`、`V=N^k≅F_5^k` と置く。`U=H∩V`、
`P=phase(H)≤C_4^k` とすれば `1→U→H→P→1` である。

`U` は可換なので、`P` の元のliftを替えても `U` 上の共役作用は変わらず、`P`-作用が
well-definedになる。まず `rho(U)≠1`。もし `rho(U)=1` なら、全射 `rho` は2群 `P` を経由するが、
位数20の `G` へ2群から全射することはできない。`U` は5群で `N` は `G` の一意なSylow 5-subgroup
だから `rho(U)⊆N`。従って `L=rho|_U:U→N≅F_5` は非零、したがって全射である。
また `phase∘rho` は `U` 上自明なので、全射準同型 `chi:P→C_4` を誘導する。

repo の積

`(ε,β)(ε',β')=(ε+ε', 2^{ε'}β+β')`

では、phase `p_j` の元による `N` への共役作用は `u_j↦2^{-p_j}u_j` である。従って `V` は
座標character `theta_j(p)=2^{-p_j}` の直和で、`U` はその `P`-部分表現である。一方、準同型
`rho` が共役を保つことから

`L(p·u)=2^{-chi(p)}L(u)`

であり、`L` は `U` から1次元character `2^{-chi}` への非零 `P`-写像である。
ここは外部定理を使わず、character projector を直接書ける。`psi(p)=2^{-chi(p)}` とし、`D_p` を
`V` 上の作用とすると

`E_psi = |P|^{-1} Σ_{p∈P} psi(p)^{-1} D_p`

が定義できる（`5∤|P|`）。`L(u)≠0` なる `u∈U` に対して equivariance から
`L(E_psi u)=L(u)≠0`、従って `E_psi u≠0`。一方 `V` の第 `j` 座標上で `E_psi` は
`theta_j=psi` のとき恒等、そうでなければ位数4以下の非自明characterの総和が0なので零である。
従ってある `j` で `theta_j=psi`。`2∈F_5^×` は位数4なので `p_j=chi(p)` がすべての `p∈P`
で成立する。
`p=phase(λ(g))` を代入すれば

`phase(f_j(g))=chi(p)=phase(rho(λ(g)))=phase(g)`

である。`g` は4つのphaseをすべて走るので `|Δ_j|≥4`。∎

**負のcontrol.** phase quotient `C_4` だけならこの障害はない。
`ε↦(ε mod 2, floor(ε/2))` と `q(x,y)=x+2y mod 4` により、二つの2値像からphaseを復元できる。
従って定理Hの荷重部分は `C_5` 上のcharacterであり、単なる位数・情報量の議論ではない。
`scripts/ci/f20_phase_rigidity.py` は共役公式を全100対、controlの準同型性を全256和で照合するが、
全称定理を担うのは上の証明である。

**`F20-STD-01` の量化監査（`F20-GENPAIR-AUDIT-01`, `COMPUTED`）。** 旧記述には独立な
ギャップもあった。`F20-STD-01` が証明するのは標準生成対 `{a=(0,1),b=(1,0)}` だけで、任意の
2元生成集合ではない。全190個の2元部分集合のうち生成するものは120個で、位数profile
`(4,5)`, `(4,4)`, `(2,4)` が各40個。全automorphism 20個による標準対のorbitは20組だけで、
残る100組はautomorphismだけでは既存証明へ移らない。従って、定理Hがなくても
「任意の2文字へ到達すれば `F20-STD-01` で閉じる」という推論は正当化されていなかった。

これにより `N-F20-ALPH2-001` は負に閉じる。定理Fの8文字構成との間に残る最小候補は4文字。
ただし、4文字分解を見つけるだけでは足りず、その**特定の4文字 sub-alphabet**の identity fibre
に height-one 証明が別途必要である。

**副問い.** 座標群に `F_20` の部分群でない群（`A_4` など既知 height-one で `𝒞` 外）を許す変種。
補題Gでは排除されない。ただし `F_20` は位数5の元を要求し、`A_4` は持たないので、
`C_5` 部分は abelian 座標から来るしかなく、abelian 直積因子は共役で動かないため
その `rho` 像は `F_20` の中心 `= 1` になる — という筋で潰れる見込みが強い。要検証。

---

## 11. 4文字境界の分類

定理Hが強制する座標が4文字ちょうどなら、その像は各phaseを1点ずつ含む。そこで

`S = {(0,b_0),(1,b_1),(2,b_2),(3,b_3)}` (`b_i∈F_5`)

という全 `5^4=625` 個を分類する。

**定理I（`F20-ALPH4-CLASS-01`）。** `S` が `F_20` を生成しないことと、ある `a∈F_5` に対して

`(b_0,b_1,b_2,b_3) = (0,a,3a,2a)`

となることは同値である。従って625個中620個が `F_20` を生成し、残る5個は `C_5` の補群
`C_4` である。さらに `Aut(F_20)` の作用について、5個の補群は1 orbit、620個の生成sectionは
各20元の31 orbitに分かれる。

*生成判定の証明.* `q:F_20→C_4` をphase商、`H=⟨S⟩` とする。`q(S)=C_4` なので
`q(H)=C_4`。核 `H∩C_5` は位数5の群 `C_5` の部分群だから、`1` または `C_5` である。後者なら
`H` は核と全商を含むので `H=F_20`。前者なら `|H|=4=|S|` であり、`S⊆H` だから `S=H`、
すなわち `S` 自身が補群である。

phase 1 の元 `c_a=(1,a)` は

`c_a^2=(2,3a)`, `c_a^3=(3,2a)`, `c_a^4=(0,0)`

を満たすので、`K_a=⟨c_a⟩` は上記の形の補群である。逆に補群上では `q` が同型だから、
phase 1 の一意な元が補群を生成する。従って補群は `a∈F_5` に対応するこの5個で尽くされる。∎

*orbit数の証明.* `a=(0,1)`, `b=(1,0)` とすれば
`F_20=⟨a,b | a^5=b^4=1, bab^{-1}=a^3⟩`。`C_5=⟨a⟩` はcharacteristicである。
automorphismが商 `C_4` 上で `bC_5` を `b^sC_5` (`s=1` または3) に送るとする。関係式を
移すと `C_5` 上の共役指数はなお3でなければならないが、phase `s` の共役指数は `2^{-s}`。
よって `s=1` であり、すべてのautomorphismは各phaseを保つ。`a` の像は4通り、`b` の像は
phase 1 の5通りで、逆にこれら20通りはすべて上の表示を保って全体を生成するため
`|Aut(F_20)|=20`。生成sectionを集合として固定するautomorphismは、各phaseの一意な元を
点ごとに固定し、そのsectionが全体を生成するので恒等写像である。従って生成sectionのorbitは
すべて20元で、`620/20=31` 個。補群は `b` の5通りの像により互いに移るので1 orbitである。∎

探索に使える完全orbit不変量も書ける。sectionを `b=(b_0,b_1,b_2,b_3)∈F_5^4`、
`q=(0,1,3,2)` と同一視すると、automorphismの作用は

`b ↦ r b + c q` (`r∈F_5^×`, `c∈F_5`)

である。従って補群直線 `W=F_5q` の外のorbitは射影平面
`P(F_5^4/W)≅P^2(F_5)` の点と一致する。具体的には

`u(b)=(b_0, b_2-3b_1, b_3-2b_1)`

の最初の非零成分を1に正規化したものが完全不変量である。正規形は
`(1,s,t)` が25個、`(0,1,t)` が5個、`(0,0,1)` が1個、計31個。これにより次の有限探索では
620 sectionを直接走らず31代表から始められる。

`scripts/ci/f20_alph4_classification.py` は625 section、5補群、20 automorphismと全orbitを厳密に
列挙し、この射影不変量を全orbit像で照合して4個の負のcontrolを退ける。これは有限長の語実験
ではないが、全称的な星高主張でもなく、上の有限群論証明の監査である。

**この時点での限界.** この分類だけでは4文字分解を構成も排除もしない。とくに定理Hが選ぶ
phase-preserving座標が補群で、補題Gが要求する生成座標が別にある可能性を排除しない。
この残差は次節の定理Jで排除する。

---

## 12. 4文字分解も不可能

§10と同じ一般形を使う。`J={j : theta_j=psi}`、すなわちtargetの `C_5`-characterと一致する
座標の集合とする。

**定理J（`F20-ALPH4-RIGID-01`）。** route-(iv)の分解を `F_20` 座標群だけで作るなら、ある座標
`j` が

`phase(f_j(g))=phase(g)`（全 `g`）かつ `|Δ_j|≥5`

を満たす。従って `max_j |Δ_j|≥5` であり、全座標を4文字以下にする分解は、座標数 `k` を
いくら増やしても存在しない。

*証明.* §10のprojectorをもう一段使う。任意の `u∈U` に対して

`L(E_psi u)=L(u)`

であり、`E_psi` は `J` に属する座標だけを残し、それ以外を零にする。後半はcharacter直交性から
直接従う。実際 `theta_j psi^{-1}` が非自明なら、その像は `F_5^×` の位数2または4の部分群で、
像上の総和はそれぞれ `1+(-1)=0` または `1+2+4+3=0`。従って `u` の `J`-座標がすべて零なら
`E_psi u=0`、ゆえに `L(u)=0` である。§10で `L≠0` と `L(E_psi u)=L(u)` を示したので
`J` は空でない。

背理法で、すべての `j∈J` について `|Δ_j|≤4` と仮定する。`j∈J` なら §10 と同じ
characterの一致から

`phase(f_j(g))=phase(g)`

がすべての `g∈F_20` で成り立つ。この像は4つのphaseをすべて含む一方で高々4元だから、
各phaseにちょうど1元しかない。従って同じphaseの `g,h` には `f_j(g)=f_j(h)` である。

同じphaseの異なる `g,h` を取り、`x=lambda(g)lambda(h)^{-1}∈H` と置く。すると
`rho(x)=gh^{-1}` は `C_5` の非自明元である。`P≤C_4^k` の指数は4を割るので

`u=x^4 ∈ H∩C_5^k=U`。

すべての `j∈J` では `x_j=f_j(g)f_j(h)^{-1}=1` だから、`u` の `J`-座標もすべて零である。
projectorの結論から `L(u)=0`。しかし準同型性から、`N=C_5` を `F_5` と同一視すれば

`rho(u)=(gh^{-1})^4≠e`、従って `L(u)≠0`

である。最後の不等号は `gh^{-1}` が位数5だから従う。矛盾。∎

`scripts/ci/f20_alph4_impossibility.py` は、この証明の有限な入力だけを検査する。同じphaseの異なる
全80順序対で差が位数5かつ4乗後も非自明であること、全625 phase sectionが全80対を潰すこと、
非自明character像の2種類の根の和が零であることを確認する。これは任意の `k` に対する定理を
有限探索で代用しておらず、全称部分を担うのは上のproofである。

**負のcontrol.** 4乗を5乗に替えると `C_5` の差はすべて消えて矛盾が出ない。また像を5元まで
許せば、一つのphaseだけ2元に分けて同じphaseの対を区別できる。このため**この証明**は下界6へ
は延長しない。5文字分解の存在はまだ主張していない。

これで `N-F20-ALPH4-001` は負に閉じる。§11の31生成orbit＋1補群orbitは正しい分類だが、
**全座標を4文字以下にする**route-(iv)の分解探索候補としてはすべて一括して排除された。
より大きい別座標と併用される可能性までは排除しない。異なる群を座標に許す変種には
定理Jもそのまま適用できないので、§10の副問いとして残る。

---

## 13. 5文字分解は存在し、下界は鋭い

元を引き続き `(epsilon,beta)∈Z/4×Z/5` と書く。`beta` には標準代表
`0,1,2,3,4` を使い、`t=1,2,3,4` に対して

`a_t(beta)=1` if `beta≥t`, and `a_t(beta)=0` otherwise

と置く。各 `r∈Z/4` と `t` に対し、文字写像

`f_{r,t}(epsilon,beta) = (epsilon,a_t(beta))` if `epsilon=r`,
and `(epsilon,0)` otherwise

を定める。その像は `t` によらず

`Delta_r = {(epsilon,0):epsilon∈Z/4} ∪ {(r,1)}`

で、正確に5元である。16個の座標を `(r,t)` で添字づけ、
`lambda(g)=(f_{r,t}(g))_{r,t}` とする。

**定理K（`F20-ALPH5-01`）。** 上の `lambda` は route-(iv) factorization を与える。従って
`F_20` 座標群だけを用いるこのschemeでの `max_j |Delta_j|` の最小値は正確に5である。さらに

`Gamma_r = Delta_r minus {(0,0)}`

と置くと、4つの `Gamma_r` はすべて4元で `F_20` を生成し、4つの identity fibre
`T_{Gamma_r}` がすべて `gsh≤1` なら `HeightOneForGroup F_20` が従う。

*factorization の証明.* 16座標のphaseが等しいtuple全体を `E` とする。これは部分群で、

`rho(epsilon,(u_{r,t})_{r,t})=(epsilon,sum_{r,t}u_{r,t})`

は `E→F_20` の準同型である。実際、`x=(epsilon,u)`, `y=(epsilon',v)` なら各座標の積の
translation成分は `2^{epsilon'}u_{r,t}+v_{r,t}` なので

`rho(xy)=(epsilon+epsilon', 2^{epsilon'}sum u_{r,t}+sum v_{r,t})=rho(x)rho(y)`。

また `g=(epsilon,beta)` に対して非零の寄与は `r=epsilon` の4座標だけであり、`F_5` で

`sum_{t=1}^4 a_t(beta)=beta`。

従って `rho(lambda(g))=g` が全20文字で成り立つ。`H=<lambda(F_20)>≤E` に制限すれば、
`rho:H→F_20` は全射である。文字上の等式と準同型性から、任意の語 `w` について
`mu(w)=rho(Phi(w))`。従って §7 と同じ有限 union/intersection と逆alphabetic morphism の議論で、
各 `Delta_r` 上の全 accepting fibre が height one なら full-alphabet identity fibre も height one。

*4文字 obligation への消去.* 各 `Delta_r` はidentityを含むので `FULL-ALPH-RED-02` を適用できる。
`Gamma_r` が `F_20` を生成することも直接分かる。`r=0` では `(0,1)` と `(1,0)` が含まれる。
`r≠0` では `(1,0)` が全phase subgroupを生成し、従って `(r,0)` も生成され、
`(r,0)^{-1}(r,1)=(0,1)` を得る。よって `T_{Gamma_r}` から erasure により `T_{Delta_r}`、
固定語によるright quotientで各singleton fibre、有限unionで各accepting fibreを得る。前段と
`FULL-ALPH-RED-01` を合成すれば結論が従う。ここで現れる `Delta_r` は `r` ごとの4種類だけである。∎

この段は台帳上 `PROVED` の `FULL-ALPH-RED-02` を入力に使う。その独立再監査
`N-ERASE-AUDIT-001` はなお `OPEN` であり、定理Kはそれを閉じるものではない。

これは定理Jと矛盾しない。元の20文字からの各座標写像の像は5元であり、4文字になるのはその後に
identity letterを消す別の閉包操作だからである。定理Jと定理Kを合わせると、route-(iv)の
**最大座標alphabetの最適値5**が確定するが、generalized star-height の下界は何も与えない。

`scripts/ci/f20_alph5_reduction.py` は16写像の全20入力、準同型公式の400個のphase/総和、sectionの
全20文字、4つの消去後alphabetの生成部分群を全数検査する。有限長の語は検査しない。任意長の語
への延長を担うのは上の準同型証明である。負のcontrolは、level 4を落とすと `beta=4` を復元
できないこと、thresholdをphase局在化
しない旧写像では像が8元に戻ること、一つのsection値の変更で復元が破れることを確認する。

---

## 14. 次の一手

残る最小補題は、4つの具体的alphabet

`Gamma_r = {(1,0),(2,0),(3,0),(r,1)}`（phase表記、重複なし）

の identity fibre の `gsh≤1`。まず `r` の間に automorphism・reversal・左右quotientによる同値が
あるかを決定し、独立なinstance数を減らす。なければ各4文字alphabetに対し、既存の
base/single/pair cutとは異なるreset規則を一つずつ反証可能な形で試す。

旧 `A4-FULL-01` §5.5 mechanism の7文字版再測定は `F20-ALPH7-OBS-01` で完了し、
**BLOCKED**。次にcutを試すなら、同じbase/single/pair familyを増やすのではなく、
`C7C3-ALLLANG-01` のようにreset規則そのものが異なるpatternを提案し、まず2生成元版で
正のcalibrationを通す必要がある。

保留は `SL(2,3)` と `S_4`。どちらも monolithic なので定理Cでは落ちず、直接攻撃が必要。
ただし `C_2×S_4` が `S_4` に帰着したので `N-S4-001` の作業量は半分になった。
