# \(A_4\) 全元アルファベットの高さ 1 構成 — 完全性修復

## 1. 主張と量化

\(\underline{A_4}\) を \(A_4\) の十二元を一文字ずつ持つアルファベットとし、

\[
\mu:\underline{A_4}^{*}\to A_4
\]

を各文字を対応する群元へ送る評価準同型とする。このノートが扱う主張は

\[
W_{A_4}:=\{w\in\underline{A_4}^{*}\mid \mu(w)=1\}
\quad\text{について}\quad
h_{\mathrm g}(W_{A_4})\leq 1
\tag{A4-FULL-01}
\]

である。「ある生成系」ではなく全十二元を文字に持つが、任意の alphabet・
任意の morphism・任意の accepting set まで量化した
`HeightOneForGroup A4` ではない。後者には
`FULL-ALPH-RED-01` を別途合成する。

## 2. 入力事実の水準

| 入力 | 水準 | 根拠 |
|---|---|---|
| generalized star height は Boolean 演算・有限和で閉じる | `PROVED` | `GSH/Height/Closure.lean` |
| 文字数の合同条件は高さ \(\leq1\) | `PROVED` | `GSH/Height/Counting.lean` |
| aperiodic な有限 transition monoid を持つ DFA の言語は star-free | `CITED` | M.-P. Schützenberger, “On Finite Monoids Having Only Trivial Subgroups”, *Information and Control* 8(2) (1965), 190–194, Main Property, DOI 10.1016/S0019-9958(65)90108-7（非 minimal DFA でも、この向きは transition monoid から syntactic monoid への quotient で従う） |
| \(A_4=V_4\rtimes C_3\) の具体的十二文字と \(v t^e\) 分解 | `COMPUTED` | `check_a4_full_alphabet` |
| cut block の star-freeness と偶奇分解 | `COMPUTED` | `check_a4_full_token_aperiodicity`, `check_a4_full_token_factorization` |
| cut 特徴量と adjacent-event 数の恒等式 | `COMPUTED` | `check_a4_full_feature_equations` |
| \(N[g,p]\) の GF(2) 復元 | `COMPUTED` | `check_a4_full_reconstruction` |
| \((P,N[g,p])\) から群積を得る公式 | `COMPUTED` | `check_a4_full_step4` |

`COMPUTED` は `tools/verdict.py` の意味である。すなわち、対象を有限状態へ
帰着し、その全 reachable states を走査し、主張の定数を壊した negative
controls がすべて発火したことを指す。これら有限部分の親 verdict は
`A4-FULL-FINITE-CORE-01` である。`A4-FULL-01` 自体は、この有限 verdict
だけでなく、上記の `CITED` 定理と以下の人間による合成証明を使うので、
`tools/verdict.py` の `COMPUTED` 判定を付けない。

## 3. 具体的な \(A_4\) 座標

\[
t=(012),\qquad
V_4=\{1,(01)(23),(02)(31),(03)(12)\}.
\]

各 \(g\in A_4\) は一意に

\[
g=v(g)t^{\varepsilon(g)},\qquad
v(g)\in V_4,\quad \varepsilon(g)\in\mathbb Z/3
\]

と書ける。`check_a4_full_alphabet` は、スクリプトの十二文字が相異なる
十二個の偶置換すべてと一致すること、および全文字でこの分解を直接再構成
できることを決定する。文字を一つ除く control と指数を一つずらす control
はいずれも拒否される。

語 \(w=g_1\cdots g_n\) に対し、\(g_i\) を読む直前の phase を
\(p_i\in\mathbb Z/3\)、最終 phase を \(P\) と書く。また

\[
N[g,p]=\#\{i\mid g_i=g,\ p_i=p\}\pmod 2
\]

とする。

## 4. cut 特徴言語は高さ 1

phase が \(q\) へ到着するたびに cut する。ただし pattern
\(\pi\in\{\varnothing,h,hg\}\) が現在の token の末尾に一致するときだけ
cut を延期する。`CutPat(q,π)` はこの deterministic process そのものである。

reset state \((q,\mathrm{None})\) を固定し、次の四言語を取る。

- \(X\): reset から始まり、最初の cut を末尾に持つ block。
- \(O\): global start \((0,\mathrm{None})\) から最初の cut まで。
- \(V\): reset から始まり、その後一度も cut しない tail。
- \(V_0\): global start から一度も cut しない語。

cut の直後には必ず同じ reset state へ戻るため、分解は一意である。cut が
零回なら \(V_0\)、一回以上なら、cut 数を \(k\) として

\[
w\in O\,X^{k-1}V.
\]

従って cut 数が奇数・偶数の言語はそれぞれ

\[
L_{\mathrm{odd}}=O(XX)^*V,
\qquad
L_{\mathrm{even}}=V_0\cup OX(XX)^*V.
\tag{4.1}
\]

`check_a4_full_token_factorization` は、使用する
\(3\times93=279\) 個の \((q,\pi)\) 全てについて次を行う。

1. \(O,X\) の transition monoid を全生成し、aperiodic と判定する。
   \(V\) は \(X\)、\(V_0\) は \(O\) と transition structure が同じで、
   accepting set だけが異なる。
2. (4.1) を epsilon-NFA 結合から DFA へ決定化する。
3. `CutPat` の直接 parity DFA と product reachability で完全同値を判定する。

訪問対象は合計 137,494。`(XX)*` を `X*` に変える control と、
even 側から \(V_0\) を除く control は拒否される。Schützenberger の定理により
\(O,X,V,V_0\) は star-free であり、(4.1) に現れる star は一段だけなので
各 cut parity language は generalized star height \(\leq1\) である。

## 5. cut 特徴量から event 数へ

全 cut の parity を \(Z_q\)、pattern \(hg\) の cut parity を
\(F(q,hg)\)、arrival phase \(q\) で隣接対 \(hg\) が現れる回数を
\(N'[hg,q]\) とする。

非 mover \(h\) について

\[
F(q,h)=Z_q+N[h,q].
\tag{5.1}
\]

mover \(g\) について、同一文字 pattern \(gg\) は periodic なので使わず、

\[
\sum_{h\ne g}F(q,hg)
=
Z_q+\sum_{h\ne g}N'[hg,q].
\tag{5.2}
\]

和は GF(2) 上で取る。`check_a4_full_feature_equations` は各 CutPat 固有の
buffer と直接 event counter の product を全探索する。したがって
「pattern が以前の cut boundary をまたがない」ことを仮定せず、状態として
検査している。全 5,792 reachable states で (5.1), (5.2) が成り立つ。

## 6. 反転特徴と \(N[g,p]\) の復元

generalized expression \(E\) の反転を、atom・Boolean 演算・star を保ち、
concatenation の順序だけ逆にすることで再帰的に定める。構造帰納法により

\[
L(E^{\mathrm{rev}})
=\{w\mid w^{\mathrm{rev}}\in L(E)\},
\qquad
h(E^{\mathrm{rev}})=h(E).
\tag{6.1}
\]

補集合では word reversal が \(\Sigma^*\) の全単射であること、star では
\((u_1\cdots u_k)^{\mathrm{rev}}
=u_k^{\mathrm{rev}}\cdots u_1^{\mathrm{rev}}\) を使う。
従って §4–5 の特徴を反転語に適用しても高さは増えない。

固定した mover \(g\)、\(e=\varepsilon(g)\ne0\) に対し、

\[
x_p=N[g,p],\qquad n_q=N'[gg,q].
\]

さらに、すべて GF(2) 上で

\[
A_p=\sum_{h\ne g}N'[hg,p+e],
\qquad
s=[\text{\(w\) の先頭文字が \(g\)}]
\]

と置く。反転語について同じ規約で定めた量を
\(\widetilde A_r,\widetilde s\) と書く。すなわち
\(\widetilde A_r=\sum_{h\ne g}\widetilde N'[hg,r+e]\) であり、
\(\widetilde s\) は反転語の先頭、つまり元の語の末尾が \(g\) であることの
指示関数である。

前向き特徴から三本

\[
x_p+n_{p+e}=A_p+s[p=0],
\]

反転特徴から三本

\[
x_m+n_{m+2e}
=\widetilde A_{r(m)}+\widetilde s[r(m)=0],
\qquad r(m)=P-e-m,
\]

文字数から一本

\[
x_0+x_1+x_2=|w|_g\pmod2
\]

を得る。この 7 本を 6 未知数 \((x_0,x_1,x_2,n_0,n_1,n_2)\) について
解く。

`check_a4_full_reconstruction` は表示式を先に解いて defect だけを検査する
のではない。各 observable の意味

- \(x,n,A\) の直接 increment、
- original word の successor pair \((g,h)\)、
- total phase、最初・最後の文字、文字数

を独立に状態へ持ち、各 reachable state で GF(2) 消去を実行して得た解を
直接 \(x\) と比較する。反転語の predecessor sum は、original word の
successor sum \(S\) から

\[
\widetilde A_q=S_{P-q}
\tag{6.2}
\]

として導出する。(6.2) は adjacent pair を反転したときの順序と phase を
直接追えば得られる。全八 mover、合計 36,872 reachable states で一致した。

forward/backward の \(n\)-index、両端補正、文字数 parity、successor pair の
向きと phase を壊す controls はすべて拒否される。従って各 \(N[g,p]\) は
高さ \(\leq1\) の有限個の Boolean observables の関数である。有限 truth table
の各 cell を intersection で、目的 fibre をその有限 union で書けば、
\(\{w\mid N[g,p]=b\}\) も高さ \(\leq1\) になる。

最初・最後の文字条件は \(\Sigma^*g\), \(g\Sigma^*\) の形で star-free
（\(\Sigma^*\) は空言語の補集合）である。文字数 mod 2 と total phase mod 3
は有限個の文字数合同言語の Boolean 結合であり、高さ \(\leq1\) である。

## 7. 群積と単位元 fibre

\(\tau(v)=tvt^{-1}\) とすると

\[
\mu(w)
=
\left(
\prod_{(g,p):\,N[g,p]=1}\tau^p(v(g))
\right)t^P.
\tag{7.1}
\]

左因子は elementary abelian group \(V_4\) 内なので、順序によらず、同じ
項の偶数回出現は消える。`check_a4_full_step4` は (7.1) を前提にして
標本比較するのではなく、closed-form automaton と Cayley automaton の積を
全探索し、全 12 reachable states で一致を判定する。作用指数と phase advance
を変えた controls は拒否される。

\(P\) と有限個の bits \(N[g,p]\) が決まれば右辺は決まる。従って
\(\mu(w)=1\) の fibre は、それら高さ \(\leq1\) observable cells の有限 union
であり、高さ \(\leq1\) である。

## 8. 検証コマンドと射程

```bash
python3 -m unittest tests.test_a4_full_exact -v
python3 scripts/ci/completeness_upgrade.py
```

このノートの §§3–7 は、`A4-FULL-FINITE-CORE-01` の有限全探索、
Schützenberger の Main Property、および表示した閉性・合成証明を組み合わせて
`A4-FULL-01` を導く。ここで `A4-FULL-01` は人間の証明を含む主張であり、
有限全探索だけを根拠に `COMPUTED` と分類してはならない。次の二段階は別の
主張である。

1. `FULL-ALPH-RED-01` を合成し、任意の alphabet・morphism・accepting set
   へ拡張して `HeightOneForGroup A4` を得る。
2. 同じ内容を Lean kernel が検査できる expression/certificate として
   形式化する。

Python の `COMPUTED` verdict を Lean theorem と読み替えてはならない。
