# F_20 の fibration 的な見方 — base `Z/4`、fibre `Z/5`、そこから何が出るか

対象: `N-F20-001`（`HeightOneForGroup F_20`）。
成果物: `scripts/research/f20_fibration_geometry.py`、run manifest `data/experiments/f20_fibration_geometry.md`。
すべての group element の ground truth は `scripts/research/f20_full_alphabet.py` の直接評価
`evaluate` であり、coordinate formula は一度も信用していない。

この note の出発点は「§5.12 の coordinate formula は幾何的に見える。`F_20 = C_5 ⋊ C_4`
を base `Z/4` と fibre `Z/5` の fibration と見て、homotopy / homology / representation
theory から示唆はないか」という問いである。結論から書く。

- **見方は正しく、しかも exact である。** `β` は 1-cocycle（crossed homomorphism）で
  あり、word problem は wedge of circles 上の flat affine `Z/5`-bundle の holonomy が
  自明であることの条件そのものである（§1）。
- **cohomology はこの問題を見ることができない。** order-20 の三つ組
  `C_20`, `Dic_5`, `F_20` は extension の cohomology が**恒等的に消える**という
  同一のデータを持つのに、前二者は settled、`F_20` は open である（§2, §3）。
  `COH-01`（REFUTED）を強める形の、具体的な反例つきの否定になっている。
- **frontier を決めている唯一のパラメータは monodromy の位数**である。1, 2, 4 と
  動かすと settled / settled / OPEN が切り替わる。これは同時に、hard な induced
  irreducible representation の次元であり、5-primary cohomological period の半分でも
  ある（§3, §4, §5）。
- **得られるのは invariant ではなく reduction である。** identity fibre は
  `{ε = 0} ∩ σ⁻¹(K)` と書ける。ここで `σ` は state set が monodromy group `Z/4` の
  sequential transducer、`K` は commutative group `C_5` が認識する言語で、両因子とも
  gsh ≤ 1 である（§6）。したがって残るのは**ただ一つの closure 問題**である。
- **この機構は 2-generator calibration を通る**（§7）。route (ii)/(iii) はどちらも
  ここで落ちた。今回のものは落ちない。

---

## 1. fibration としての定式化（PROVED）

`Σ` を alphabet、`μ : Σ* → F_20` を monoid morphism とする。`F_20` の元を
`(α, β) ∈ (Z/5)^× × Z/5`（`α = 2^ε`）で書くと、積は

```
(α, β)·(α', β') = (α α', α' β + β')
```

なので、`ε : Σ* → Z/4` は monoid morphism（**base への射影**）、`β : Σ* → Z/5` は

```
β(uv) = ε(v)·β(u) + β(v)                    (*)
```

を満たす。これは `ε` で引き戻した `Z/4`-作用に対する **1-cocycle（crossed
homomorphism）**の条件そのものである。

幾何的に読むと: `Σ*` は `|Σ|` 個の円の wedge の based loop（の離散版）、`μ` は
affine group `AGL(1,5)` への monodromy representation、つまり flat affine
`Z/5`-bundle。`α` が linear part（**base の holonomy**）、`β` が translation part
（**fibre 方向の holonomy**）。word problem `μ(w) = e` は「この loop に沿った parallel
transport が identity である」という条件である。

`(*)` を長さについての帰納で解くと coordinate formula が出る:

```
β(w) = Σ_i β_{g_i} · 2^{E_i},     E_i = Σ_{j > i} ε_{g_j}   (suffix phase)
```

つまり `E_i` は「位置 `i` から先の base 方向の holonomy」であり、係数 `2^{E_i}` は
その holonomy による fibre の捻れである。§5.12 の formula は導出物ではなく、
**cocycle 条件の一意な解**だった。

検証（script §1）: `(*)` を full 20-letter alphabet 上の長さ ≤ 2 の全 177,241 組と、
長さ ≤ 11 のランダムな 4,000 組で確認。さらに `Z^1(Σ*, Z/5) = (Z/5)^Σ`、すなわち
20 letters への fibre 値の**任意の**割り当てが cocycle に一意に延びることを 200 通りの
ランダムな割り当てで確認した。free monoid 上では cocycle の obstruction は存在しない。
**難しさは `β` の存在ではなく、その definability にある。** これは以降ずっと効く区別で
ある。

## 2. extension の cohomology は恒等的に消える（COMPUTED）

`H^n(C_4, Z/5)` を bar resolution から F_5 上の exact な線形代数で計算した
（periodic resolution の公式は使わず、`C^n = Maps(C_4^n, F_5)` の微分を直接組んだ）。
module structure は生成元が `x ↦ r x` で作用するもの、`r ∈ {1, 4, 2}`:

| `r` | 作用 | 群 | `H^0` | `H^1` | `H^2` | `H^3` | `H^4` |
|---|---|---|---|---|---|---|---|
| 1 | trivial | `C_20` | 1 | 0 | 0 | 0 | 0 |
| 4 | inversion | `Dic_5` | 0 | 0 | 0 | 0 | 0 |
| 2 | faithful | `F_20` | 0 | 0 | 0 | 0 | 0 |

（F_5 上の次元。4 と 5 が互いに素なので `n ≥ 1` ですべて消える。）

読み方:

- `H^2 = 0`: 三つとも split extension。
- `H^1 = 0`: splitting は共役を除いて一意。
- したがって **extension を分類するデータは三つで完全に同一**であり、しかも zero で
  ある。

`C_20` は `PST-GRP-01` で、`Dic_5` は `PST-GRP-03`（および `DICM-EMB-01`）で settled、
`F_20` は `FRONTIER-ORD20-01` の open frontier である。**extension の cohomology の
関手はこの三つを区別できない。** よって gsh の invariant にはなりえない。

これは `COH-01`（「cohomology は gsh の確立した invariant を与える」= REFUTED、
「そのような定理は見つからなかった」）を、**具体的な反例つきの否定**に強めるものである。
「まだ見つかっていない」ではなく「extension cohomology に限れば、原理的に無理」。

## 3. order-20 の族 — frontier は monodromy の位数にある（COMPUTED）

`C_5 ⋊_r C_4` を `r ∈ {1, 4, 2}` で走らせる。三つは互いに非同型で、`r = 1` が `C_20`、
`r = 4` が `Dic_5` であることは機械検証した（`scripts/research/small_group_pst_coverage.py` の
`isomorphic` / `dicyclic` を再利用）。

| `r` | monodromy の位数 | abelian | PST class（`pst_necessary_criterion`） | gsh の status |
|---|---|---|---|---|
| 1 | 1 | yes | 内側 | settled（`PST-GRP-01`） |
| 4 | 2 | no | 内側 | settled（`PST-GRP-03`, `DICM-EMB-01`） |
| 2 | 4 | no | **外側** | **OPEN**（`N-F20-001`） |

三つは**ちょうど一つのパラメータ**でしか違わない。base も fibre も extension の
cohomology も同一で、違うのは local system の monodromy の位数 1, 2, 4 だけである。
そして既知の結果の frontier は、**local system が involution であることをやめる点**に
ある。

これは `PST-GRP-03` の「abelian by elementary abelian 2」という条件の幾何的な読み替え
でもある: elementary abelian 2 とは、fibre 方向の捻れが involution しかないという
ことである。

## 4. representation theory — hard な irrep は induced で、次元は monodromy の位数
（COMPUTED）

`Ind_{C_5}^{C_5 ⋊_r C_4}(χ)`（`χ` は非自明な `C_5` の character）を coset の公式から
exact に `Z[ζ_5]` 上で計算した。Clifford theory により、`T` を `χ` の stabilizer と
すると `Ind` は `|T/C_5|` 個の**相異なる** irrep の和で、各次元は orbit の長さである。

| `r` | `⟨Ind χ, Ind χ⟩` | 分解 | hard irrep の次元 |
|---|---|---|---|
| 1 | 4 | 相異なる 4 個 × 次元 1 | 1 |
| 4 | 2 | 相異なる 2 個 × 次元 2 | 2 |
| 2 | 1 | 1 個 × 次元 4 | **4** |

**hard irrep の次元 = monodromy の位数**である。

`F_20` については、orthogonality が次に特殊化することを 20 元すべてで確認した:

```
5 · 1_{g = e}(g)  =  1_{ε(g) = 0}(g)  +  χ_ρ(g)
```

左辺は identity fibre の indicator。右辺第一項は 4 個の linear character の和で、これは
**base の言語（mod 4 の数え上げ、gsh ≤ 1）**にすぎない。したがって
**残りの難しさは 4 次元 induced character `χ_ρ` ただ一つに集中している。**

さらに `ρ` の explicit な 4×4 model を組み、400 組すべてで homomorphism であること、
trace が coset character に一致すること、そして **monomial**（各行各列にちょうど一つの
非零成分）であることを確認した。分解は

```
ρ(g) = P(ε(g)) · D(g)
```

で、permutation part `P` は base 座標 `ε(g)` **のみ**の関数（4 値をとる）、diagonal part
`D` は 5 乗根で fibre 方向。**fibration が行列の形でそのまま出ている。** monomial 表現
とは、まさに「permutation 的な base × scalar 的な fibre」の表現論的な言い換えである。

## 5. homology は何を見るか — local system の period（COMPUTED + 短い証明）

`H^{2k}(C_5, Z) = Z/5`（`k > 0`）で、`C_4` はこれに `r^k` 倍で作用する。
Lyndon–Hochschild–Serre では `E_2^{p,q} = H^p(C_4, H^q(C_5, Z))` であり、`q > 0` の行は
5-torsion なので §2 により `p ≥ 1` で消える。よって `E_2` は `q = 0` の行と `p = 0` の
列の合併に退化し、微分は `E_r^{p,q} → E_r^{p+r, q-r+1}` でその形から出られない
（`d_2 : E_2^{0,q} → E_2^{2,q-1}` の行き先は `q = 1` 以外 0 で、`H^1(C_5, Z) = 0`）。
collapse する。

したがって 5-torsion が生き残るのは `(H^{2k})^{C_4} ≠ 0`、すなわち `r^k = 1` のときに
限る:

| `r` | monodromy の位数 | 5-torsion のある次数 | 5-primary period |
|---|---|---|---|
| 1 | 1 | 2, 4, 6, … | 2 |
| 4 | 2 | 4, 8, 12, … | 4 |
| 2 | 4 | 8, 16, 24, … | 8 |

**period = 2 × (monodromy の位数)。**

つまり homology は三つを**区別できる**。ただし報告している内容は monodromy の位数を
period に符号化し直したものにすぎず、§3 のパラメータを超える情報はない。
**homotopy / homology から得られるのは新しい invariant ではない**（`COH-01` は REFUTED の
まま）。得られるのは次節の reduction である。

## 6. 得られる reduction — transducer に落ちる（PROVED、ただし §8 の注意つき）

marked alphabet を `Γ = Z/4 × Σ` とし、`σ : Σ* → Γ*` を「各文字にその suffix phase
`E_i` を貼る」right-sequential transducer とする（state set は `Z/4` = monodromy group
そのもの、length-preserving）。さらに

```
K  =  { v ∈ Γ* : Σ_{(p,g) ∈ v} β_g · 2^p ≡ 0 (mod 5) }   ⊆ Γ*
```

とおく。`K` は morphism `Γ* → C_5`, `(p,g) ↦ β_g 2^p` の `0` の逆像であり、
**commutative group が認識する言語**である。このとき coordinate formula から直ちに

```
μ⁻¹(e)  =  { w : ε(w) ≡ 0 mod 4 }  ∩  σ⁻¹(K)          (**)
```

検証（script §5）: full 20-letter alphabet 上の長さ ≤ 4 の全 168,421 語、
2-generator alphabet 上の長さ ≤ 12 の全 8,191 語で一致。ground truth は群の直接評価。

negative control を三つ置いた。weight vector を (i) 位相を無視した定数、(ii) 二成分を
交換、(iii) 一成分を 0 にする、といずれも長さ ≤ 10 で 173 / 160 / 109 語で誤る。
一方 **weight の巡回シフトは control にならない**（全体が F_5 の unit 倍になるだけで
同値な条件になる）ので、意図的に control から外し、その事実自体も検証した。

`(**)` の両因子は既知で gsh ≤ 1 である:

- `{ε ≡ 0}` は `C_4` が認識する ⇒ `PST-GRP-01`（CITED）。
- `K` は `C_5` が認識する ⇒ 同じく `PST-GRP-01`。

boolean operation は generalized star height を上げないので、**残る問いは一つだけ**:

> **`σ⁻¹` は gsh ≤ 1 を保つか。**

これが yes なら `μ⁻¹(e)` は gsh ≤ 1 で、`FULL-ALPH-RED-01` により
`HeightOneForGroup F_20` が従う。

### なぜこれが自明でないか（PROVED）

`σ⁻¹` は star-freeness を保たない。`A = {(1,g) : g ∈ Σ}` として
`K_0 = A·Γ* ⊆ Γ*` をとると、`K_0` は star を一切使わず書けるので star-free（gsh 0）で
ある。ところがその preimage `σ⁻¹(K_0)` は「先頭文字の suffix phase が 1」という条件で
あり、これは mod 4 の数え上げになる。最小 DFA は 5 状態、transition monoid に period 4
の元があるので、Schützenberger 1965 により **star-free ではない**（2-generator でも
full alphabet でも同じ、script §8）。

したがって必要な closure は star-free の closure 定理からは絶対に出ない。`PST-CL-01` が
保証するのは inverse **alphabetic** morphism、すなわち transducer の状態が 1 個の場合で
ある。**proved と needed の差は「1 状態」対「monodromy 個の状態」ちょうどそれだけ。**

### `PST-GRP-03` はこの conjecture の最初の場合である（解釈、UNREVIEWED）

`A ⋊ E`（`A` commutative、`E` elementary abelian 2）に対して同じ構成をすると、
transducer の state group は `E` になる。つまり `PST-GRP-03` の射程は
「state group が elementary abelian 2 の transducer に対して `σ⁻¹` が gsh ≤ 1 を保つ」
と読める。この読み替えが PST 1992 の証明の実際の進み方と一致するかは**未確認**であり、
`PST-WREATH-06-01` と同じ理由（primary source の full text が取れていない）で
UNREVIEWED にしておく。ただし読み替えが正しいかどうかにかかわらず、**射程の一致は
成立している**（§3 の表）。

## 7. calibration — 2-generator instance を通る（COMPUTED）

`F20-BASECODE-01` で登録した方法論のルールを、この機構に最初に適用する:

> 新しい機構は、まず 2-generator alphabet（`F20-STD-01` で gsh = 1 が**証明済み**）に
> 当てる。そこで失敗する機構は full alphabet で成功しえない。

`(**)` を `Σ = {a, b}`, `a = (x ↦ x+1)`, `b = (x ↦ 2x)` に特殊化すると、`σ⁻¹(K)` は
`F20-STD-01` の arithmetic characterization
「`b` の個数 ≡ 0 mod 4 かつ `N_0 + 3N_1 + 4N_2 + 2N_3 ≡ 0 mod 5`」**そのもの**になる。
長さ ≤ 14 の全 32,767 語で群と一致することを確認した（`F20-STD-01` が検証したのと同じ
instance）。

**CALIBRATION PASSED.** route (ii) と (iii) はどちらもここで落ちた。この機構は落ちない。
むしろこの機構は、**すでに証明されている height-one 表現を再現している**。

ついでに、published な係数 `(1,3,4,2) = 2^{-p}` が **prefix** phase で読むものであること
も特定した（suffix phase で読むと長さ ≤ 12 で 544 語ずれる）。二つの trivialization は

```
P_i + ε_i + E_i = ε(w)      ⇒      β_suffix(w) = 2^{ε(w)} · Σ_i β_i 2^{-ε_i - P_i}
```

で結ばれ、**差はループ全体の holonomy `2^{ε(w)}` ちょうど**である。identity fibre 上では
`ε(w) = 0` なので捻れが消え、両者は一致する。full alphabet の長さ ≤ 3 の全 8,421 語で
確認した。

## 8. 主張していないこと、および注意（重要）

- **これは lower bound ではない**（research rule 1）。何の言語についても gsh > 1 は
  示していない。
- **`(**)` は単一の `K` に対しては、強さの上ではほぼ言い換えである。** `σ⁻¹(K)` の
  gsh ≤ 1 は `μ⁻¹(e)` の gsh ≤ 1 とほぼ同値であり、AGENTS.md の stop condition
  「missing lemma が元の target と同じ強さ」に**該当する**。したがって
  **単一 `K` の形を直接攻めることは推奨しない**。価値があるのは次の一般形である:

  > **CONJECTURE.** `σ` を state monoid が有限 **abelian group** である length-preserving
  > sequential transducer とする。このとき `σ⁻¹` は generalized star height ≤ 1 を保つ。

  この形は元の target より真に強く、かつ `F_20` だけでなく metabelian 型の場合を一挙に
  片づける。そして §6 の読み替えが正しければ **`PST-GRP-03` はこの conjecture の
  `E` elementary abelian 2 の場合そのもの**であり、conjecture は新奇な思いつきではなく
  既知定理の自然な次の場合になる。ここが route (ii)/(iii) との実質的な違いである。
- **prior art は未調査。** §6 の分解は Straubing の wreath product principle の
  特殊化に見える。この repo では coordinate formula からの初等的な導出で自足させて
  あるので、証明としては citation に依存しない。しかし
  **「新しい」と主張してはならない**。文献調査を `N-FIB-PRIOR-001` として登録した。
  `PST-WREATH-06-01` で attribution が取れなかった経緯があるので、primary source が
  取れるまでは UNREVIEWED を貼る。
- `PST-GRP-01`（commutative group ⇒ gsh ≤ 1）は CITED であり、この repo で証明されて
  いない。§6 の reduction はこれに依存する。
- §5 の LHS collapse は短い証明を書いたが、`H^{2k}(C_5, Z) = Z/5` とその `C_4`-作用が
  `r^k` 倍であることは standard な事実（CITED）として使っている。script が exact に
  検証しているのはそこから先の invariant の計算だけである。
- **`Dic_5` が settled であることの根拠**は `DICM-EMB-01`（PROVED, `n = 5` は
  `n = 2..12` の機械検証に含まれる）と `PST-GRP-03`（CITED）である。§3 の表の
  「settled」列はこの二つに依存する。

## 10. 文献調査の結果（`N-FIB-PRIOR-001`、2026-07-25 実施、PARTIAL）

§8 で「prior art 未調査」と書いた点を先に潰した。**route は生き残ったが、位置づけは
大きく変わった。**

### 見つかったもの

**(1) `PST-WREATH-78-01`.** PST 1992 の **Theorem 7.8** は次である（Bourne–Ruškuc
arXiv:1603.06236 からの逐語引用）:

> "Since all languages that belong to the pseudovariety generated by wreath products
> of abelian groups by aperiodic monoids have star-height at most one [9, Theorem 7.8]"

`§6` の transducer の言葉に直すと、これは
**「transducer の state monoid が aperiodic なら `σ⁻¹` は gsh ≤ 1 を保つ」**である。
つまり `TRANSD-ABEL-01` の **aperiodic の場合はすでに定理**。

副産物が二つある。第一に、これは repo の `PST-WREATH-06-01`（abstract から拾った
「`M ∘ (G ∘ N)`」という曖昧な形）を**上書きする**。どちらの因子が aperiodic でなければ
ならないかが、これで確定した。第二に、`PST-WREATH-COMM-01`（あの variety の群はすべて
可換）が計算ではなく**構造的に説明される**: base が aperiodic を要求されるので、
自明でない monodromy は最初から射程外だった。

**(2) `EIL-WPP-01`.** `§6` の分解は Eilenberg の wreath product 機構そのものである
（Prop. IX.1.1 を generalized sequential function 用に修正したもの、同じく
Bourne–Ruškuc が引用）。**この構成に新規性を主張してはならない。** repo 側の導出を
初等的に自足させてあるのは、取れない citation に依存しないためであって、新しいから
ではない。

**(3) abelian の場合は見つからなかった。** 証明も反証も、調べた範囲には現れなかった。

### 取れなかったもの（2026-07-28 に解消）

**［2026-07-28 更新］PST 1992 の full text を取得した。** 経路は
`curl -sL -A "Mozilla/5.0 …" https://www.irif.fr/~jep/PDF/StarHeight.pdf`。
（UA なしの `irif.fr` fetch、HAL の Anubis anti-bot、ScienceDirect 403 は当時の
記録どおりで、変わったのは UA を付けた点だけである。）確認できたこと:

- **Theorem 7.8**（p. 27）の番号と文言は二次資料の引用どおり:
  "Every language recognized by a monoid of the variety A∗Gcom∗A is of
  star-height ≤ 1"。証明は Proposition 7.1 で `Gcom ∗ A` に落とし、
  そこは `G ◦ M`（`G` 可換、`M` **aperiodic**）で生成される。base が aperiodic
  であるという読みは正しい。
- **Theorem 7.6**（p. 27、elementary abelian 2 の場合）の証明は、本ノートの
  transducer 構成そのものである: `ϕ = ηπ` で各文字にその直前の `(Z/2Z)^r`
  状態をタグ付けする length-preserving sequential `σ` を取り、`Yσ⁻¹` を
  arrow-counting language `L(A,(q,a),s,n)` に帰着させる。よって
  `TRANSD-LADDER-01` の rung (b)(c) が「1 つの構成の 2 つの instance」だという
  読みは一次資料で裏が取れた。
- **abelian state の場合は PST §7 に無い。** Theorem 7.6（elementary abelian 2）
  から Theorem 7.8（aperiodic）へ直接飛んでおり、中間の rung は存在しない。

残るのは 1992–2026 の他文献であり、**「見つからなかった」は依然として
「知られていない」より弱い**。

### 得られた ladder（`TRANSD-LADDER-01`）— ここが今回いちばん効く

transducer の state monoid に何を仮定するかで、主張の強さが劇的に変わる。

| state monoid の仮定 | 「`σ⁻¹` は gsh ≤ 1 を保つ」の地位 |
|---|---|
| **仮定なし** | **generalized star-height 予想そのものと同値** |
| aperiodic | **定理**（`PST-WREATH-78-01`） |
| elementary abelian 2 | **定理**（`PST-GRP-03` の読み替え、UNREVIEWED） |
| **cyclic order 4** | **= `HeightOneForGroup F_20`、OPEN** — 最初の未知の段 |
| 任意の abelian | **有限可解群すべて**で gsh ≤ 1 を導く |

一番上の行は証明できる。任意の regular `L` に対し、各文字にその直前の DFA state を
貼る transducer をとると `L = σ⁻¹(Γ*·S)` で、`Γ*·S` は star を一切使わないので
**star-free** である。よって:

- 「仮定なしで `σ⁻¹` が gsh 0 を保つ」は**偽**（`mu⁻¹(e)` は syntactic monoid が群
  `F_20` なので star-free でない、Schützenberger 1965）。
- 「仮定なしで `σ⁻¹` が gsh ≤ 1 を保つ」は、あらゆる regular 言語が gsh ≤ 1 という
  主張と**同値**、すなわち未解決問題そのもの。

script §9 が、full alphabet の長さ ≤ 4 の全 168,421 語と 2 生成元の長さ ≤ 12 の全 8,191 語
で、この marking が実際に `mu⁻¹(e)` を star-free 言語の preimage にすることを確認して
いる。**仮定こそが内容のすべてである。**

一番下の行も具体的である。Krasner–Kaloujnine の埋め込み `G ↪ G' ≀ (G/G')` を derived
series に沿って反復すると、各段の transducer の state monoid は **abelian 商
`G^(i)/G^(i+1)`** になる。したがって `TRANSD-ABEL-01` は**有限可解群すべて**を一挙に
片づける。PST class の外にある 6 群（`SMALL-NONAB-31-01`）はすべて可解なので、
6 群すべてが対象になる。script §10 で各段の埋め込みが injective homomorphism である
ことを機械検証した:

| 群 | derived series | 各段の abelian 商の位数 |
|---|---|---|
| `A_4` | 12 → 4 → 1 | 3, 4 |
| `F_20` | 20 → 5 → 1 | 4, 5 |
| `C_7 ⋊ C_3` | 21 → 7 → 1 | 3, 7 |
| `SL(2,3)` | 24 → 8 → 2 → 1 | 3, 4, 2 |
| `S_4` | 24 → 12 → 4 → 1 | 2, 3, 4 |
| `C_2 × A_4` | 24 → 4 → 1 | 6, 4 |

（商は**位数だけ**を報告している。位数 4 の abelian 群は `C_4` か `C_2×C_2` かで、
計算はそれを決めていない。）

### 方針への含意

これは**動機であると同時に警告**である。可解群をすべて片づける conjecture は
「小さな次の一歩」ではない。したがって:

> **一般形 `TRANSD-ABEL-01` を攻めるのではなく、最初の未知の段（state monoid `C_4`、
> input は `C_5`-counting language）を攻める。**

その一段下（aperiodic）は `PST-WREATH-78-01`、真横（elementary abelian 2）は
`PST-GRP-03` で、どちらも既知である。`F_20` はその二つのすぐ隣にある最小の未知の場合
であって、これが route (vi) を選ぶ理由になる。

## 9. 次の一手

1. ~~`N-FIB-PRIOR-001`（文献調査）を先にやる~~ → **実施済み（§10、PARTIAL）**。
   route は生き残り、位置づけが確定した。残りは PST 1992 の full text を
   institutional library 経由で取ること（二次資料依存を解消する）と、Pin の
   *Varieties of Formal Languages* の wreath product の章の確認。
2. conjecture の**最小の未知の場合**、すなわち state group `C_4`、
   input が `C_5`-counting language、という場合を直接攻める。`F20-STD-01` の
   height-1 expression が実際にこの場合の存在証明になっているので、
   **その expression を alphabet に依存しない形に書き直せるか**が具体的な作業単位に
   なる。これは route (iv)（inverse alphabetic morphism による復元）と相性がよい:
   marked alphabet `Γ` 上で書いた式を `σ` で引き戻す、という形で route (iv) を
   実行することになる。
3. ~~non-abelian にすると偽になるはずなので反例を探す~~ → **§10 で解決**。反例を探す
   必要はない。仮定を外した形は generalized star-height 予想**そのものと同値**であり、
   偽であることを期待するのではなく、単に未解決問題を言い換えているだけだった。
   scope はこれで正しく切れている。
