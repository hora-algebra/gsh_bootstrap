# `W_{A_5}` と first-return substitution の二つの構造的障害

作業日: 2026-07-23

## 1. 設定

有限群 `G`、部分群 `H < G` を取り、全要素アルファベットを

$$
\Gamma=\{\underline g\mid g\in G\}
$$

とする。評価準同型を

$$
\mu:\Gamma^*\to G,\qquad
\mu(\underline{g_1}\cdots\underline{g_n})=g_1\cdots g_n
$$

と書く。

各 `h in H` について、`H` への first-return block を

$$
\mathcal B_h=
\left\{
w\in\Gamma^+
\mid
\mu(w)=h,\ 
\mu(v)\notin H\text{ for every nonempty proper prefix }v<w
\right\}
$$

とする。置換

$$
\sigma:H^*\to\mathcal P(\Gamma^*),\qquad h\sigma=\mathcal B_h
$$

を first-return substitution と呼ぶ。

以下では

$$
G=A_5,
\qquad
H=\operatorname{Stab}_{A_5}(1)\cong A_4
$$

を主対象とする。

---

## 2. pending-coset obstruction

### 定理 2.1

`L subset H*` が非空語を一つでも含むとする。`x notin H` を取り、

$$
K=H\cap x^{-1}Hx
$$

と置く。`K` の `H` における core が自明なら、`L sigma` の構文モノイドは `H` の非自明な群作用を divisor として持つ。特に `L sigma` は star-free でない。

### 証明

`v=a_1\cdots a_m in L` を非空語とする。各 `h in H` に対し、接頭語

$$
p_h=\underline x\,\underline h
$$

を読む。`xh notin H` なので、これは未完了の first-return block の途中にいる状態である。

`h_0 in H` を固定し、接尾語

$$
s_{h_0}
=
\underline{(xh_0)^{-1}a_1}\,
\underline{a_2}\cdots\underline{a_m}
$$

を考える。`p_{h_0}s_{h_0}` では最初の追加文字を読んだ時点で積が `a_1 in H` となり、その後は singleton block `a_2,...,a_m` を読む。したがって

$$
p_{h_0}s_{h_0}\in L\sigma.
$$

一方、`p_hs_{h_0}` が最初の追加文字で `H` に戻るための必要十分条件は

$$
xhh_0^{-1}x^{-1}\in H,
$$

すなわち

$$
hh_0^{-1}\in H\cap x^{-1}Hx=K
$$

である。これが成り立たなければ、その後 `H` の文字を掛け続けても `H` の外の同じ右剰余類に留まるので、語は受理されない。

よって異なる左剰余類 `Kh` に属する `p_h` は異なる residual を与える。また `k in H` の文字を読むと

$$
p_h\longmapsto p_{hk}
$$

となる。従って residual 上に `H` の右作用が生じ、その kernel は `core_H(K)` に含まれる。core が自明なら、この作用は忠実である。したがって構文モノイドは非自明な有限群を divisor として持ち、aperiodic ではない。Schuetzenberger の定理により `L sigma` は star-free でない。$\square$

### `A_5/A_4` への適用

`H=Stab(1)`、`x` が `1` を `2` へ移す元なら

$$
K=H\cap x^{-1}Hx=\operatorname{Stab}_{A_5}(1,2)\cong C_3.
$$

これは自然な4点作用における点安定化群であり、`H cong A_4` における core は自明である。従って、

$$
\boxed{
L\subseteq H^*,\ L\cap H^+\ne\varnothing
\quad\Longrightarrow\quad
L\sigma\text{ is not star-free}
}
$$

である。特に各一文字像 `B_h={h}sigma` 自体が star-free でない。

具体的には、`K=< (345) >` と取れる。pending residual の4剰余類上で `(345)` は1点を固定し、残り3点を巡回する。

---

## 3. bounded synchronization delay も必ず失敗する

### 定理 3.1

`X subset H+` を非空な prefix code とし、

$$
C=X\sigma
$$

と置く。このとき `C` は prefix code だが、bounded synchronization delay を持たない。

### `C` が prefix code であること

first-return block の境界は、積が初めて `H` に戻る位置なので一意である。従って `C` の語が別の `C` の語の接頭語なら、外側の `X`-語も接頭語関係にある。`X` が prefix code なので両者は等しい。

### synchronization delay が非有界であること

`u=h_1\cdots h_m in X` を固定する。各 `h_i` は singleton first-return block `underline{h_i} in B_{h_i}` を持つので

$$
z=\underline{h_1}\cdots\underline{h_m}\in C.
$$

`z` の任意の接頭辞の積は `H` に属する。

任意の `d>=1` と `x notin H` に対して

$$
a=\mu(z)^d\in H,
\qquad
 y=(xa)^{-1}h_1\in G
$$

と置き、

$$
w=
\underline x\,z^d\,\underline y\,
\underline{h_2}\cdots\underline{h_m}
$$

を考える。`underline x` の後、`z^d` の途中では積は常に右剰余類 `xH` にあり `H` へ戻らない。`underline y` を読んだ瞬間に積は `h_1` となる。従って

$$
\underline x\,z^d\,\underline y\in\mathcal B_{h_1},
$$

その後の singleton blocks と合わせて `w in C` である。

ところが

$$
z^d\in C^d
$$

である一方、接頭辞 `underline x z^d` の積は `xa notin H` なので `C+` に属さない。よって synchronization delay `d` の条件に反する。`d` は任意なので bounded delay は存在しない。$\square$

従って

$$
\boxed{
X\ne\varnothing\text{ prefix code}
\quad\Longrightarrow\quad
X\sigma\text{ is neither star-free nor of bounded synchronization delay}
}
$$

である。

---

## 4. `A_4` の93 token languages への帰結

`gsh_bootstrap/scripts/a4_full12.py` の full-alphabet `A_4` 構成は、93個の star-free token languages を用いている。各 token language は prefix code として star の直下に現れる。

これらを `A_5` の first-return substitution に通した `X sigma` は、上の二定理により一律に

1. star-free ではない。
2. bounded synchronization delay を持たない。

従って、次の二つの標準的な平坦化はどちらも使えない。

- `X sigma` が star-free だから `(X sigma)*` を一段 star とみなす。
- bounded-delay prefix code の star を Boolean 演算と連接だけで消去する。

Place--Zeitoun の bounded-delay 消去公式自体は、`K` が高さ `n` に属し bounded synchronization delay を持てば `K*` も同じ高さ `n` に留まることを与える。しかし今回の substituted code は、その仮説をすべて破る。

---

## 5. 何が未否定か

この結果は

$$
gh(W_{A_5})\ge2
$$

を示すものではない。また

$$
(X\sigma)^*
$$

が別の全く異なる高さ1表現を持つ可能性も否定していない。

否定したのは、次の「componentwise flattening」である。

> `A_4` の高さ1式の各 starred base `X` を別々に置換し、
> `X sigma` 自身を star-free または bounded-delay code として処理する方法。

もし first-return substitution をなお使うなら、複数の substituted atoms の間の共通の pending-coset `A_4` 作用を、Boolean 結合の段階で同時に相殺する新しい恒等式が必要になる。

---

## 6. 次の具体的対象: evaluation-aligned `A_5` code

十分条件として、全要素アルファベット `Gamma=A_5` 上に star-free code `D` と有限個の左右文脈 `p_i,q_i` があり、

$$
W_{A_5}
=
\bigcap_i p_i^{-1}D^*q_i^{-1}
$$

またはその有限 Boolean 結合として書ければよい。`D*` は高さ1であり、左右商と Boolean 演算は高さを増やさないからである。

有限 bifix code は自動的に star-free で、その syntactic monoid に `A_5` を permutation group として持たせる既知の構成がある。ただし必要なのは単に `A_5` が局所群として現れることではなく、その作用が元の評価準同型

$$
\mu:\Gamma^*\to A_5
$$

と文脈を通して整合することである。この **evaluation alignment** が次の有限探索・構成問題になる。

---

## 参考

- hora-algebra/gsh_bootstrap, `RESULTS.md`, `CLAIMS_LEDGER.md`, `scripts/a4_full12.py`, `scripts/a5_frontier.py`.
- T. Place and M. Zeitoun, *Closing Star-Free Closure*, ACM TOCL, 2025; arXiv:2307.09376.
- V. Diekert and T. Walter, *Characterizing Classes of Regular Languages Using Prefix Codes of Bounded Synchronization Delay*, ICALP 2016; arXiv:1602.08981.
- J. Berstel, C. de Felice, D. Perrin, C. Reutenauer, G. Rindone, *Recent Results on Syntactic Groups of Prefix Codes*, European J. Combin. 33 (2012), 1386--1401.

## 7. 有限群部分の検算

付属スクリプト `a5_first_return_obstruction_check.py` は、次を有限計算で確認する。

- `|A5|=60`, `|H|=12`。
- `K=H∩x^{-1}Hx` は位数3。
- `core_H(K)=1`。
- `K\H` 上の `H` の作用は忠実で、像の位数は12。
- `(345)` は4剰余類のうち1つを固定し、残り3つを巡回する。
- singleton outer code `X={h}` について、delay `d=1,...,10` の明示的な反例語。

一般の `d` に対する結論は §3 の記号的証明による。スクリプトは証明の有限群計算部分と具体例を独立に検算するためのものである。
