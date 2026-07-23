# Conway の群恒等式・全元アルファベット・一般化 star height

作業日: 2026-07-23。

## 状態

- **目的**: §5.5 の全元アルファベット版 $A_4$ と、§5.6--5.8 の少数生成元版 $A_5$ の差を、Conway--Krob--Ésik の有限群オートマトン恒等式との対応から整理する。
- **証明状態**: §3 の還元命題は、当初 Pin--Straubing--Thérien の閉性を外部入力としていたが、2026-07-23 の追記 §3.5 により、使用する二つの閉性（一文字左商・letter-to-letter 逆準同型）に自己完結の帰納法証明を与えた。命題 3.1 はもはや PST の仮説監査に依存しない（機械コンパニオン: `scripts/closure_lemmas_check.py`）。独立な人間による査読は未了。
- **新規性状態**: Conway 理論との対応は概念整理であり、新規定理とは主張しない。§6 の bounded-depth input-extension は研究問題である。
- **証拠状態の注意**: 本ノートは `A4-FULL-01` の `COMPUTED` を `PROVED` に昇格させない。そこから導く $A_4$-言語全体の主張も、元の計算証拠と閉性定理の監査状態を継承する。

主要文献:

- J. H. Conway, *Regular Algebra and Finite Machines*, Chapman and Hall, 1971.
- D. Krob, [Complete systems of B-rational identities](https://doi.org/10.1016/0304-3975(91)90300-I), *Theoretical Computer Science* 89 (1991), 207--343.
- Z. Ésik, [Group axioms for iteration](https://doi.org/10.1006/inco.1998.2746), *Information and Computation* 148 (1999), 131--180.
- Z. Ésik, [Equational axioms associated with finite automata for fixed point operations in cartesian categories](https://arxiv.org/abs/1501.02190), 2015/2017.
- 良磨 新屋, [正規表現研究の過去・現在・未来（2024年版）](https://doi.org/10.51094/jxiv.1017), 2025.
- J.-E. Pin, H. Straubing, D. Thérien, [Some results on the generalized star-height problem](https://doi.org/10.1016/0890-5401(92)90063-L), 1992.

## 1. 全元アルファベットと Cayley オートマトン

有限群 $G$ に対し、各群元を一文字とするアルファベットを

\[
\underline G=\{\underline g\mid g\in G\}
\]

とする。標準評価準同型を

\[
\mu_G:\underline G^*\longrightarrow G,
\qquad
\mu_G(\underline g)=g
\]

とし、その単位元ファイバーを

\[
W_G=\mu_G^{-1}(1)
\]

と書く。

状態集合を $G$ とし、文字 $\underline g$ が右乗法

\[
h\xrightarrow{\underline g}hg
\]

として作用する決定性オートマトンを考える。これは $G$ の右正則 Cayley オートマトンである。

群元で添字づけた変数 $x_g$ を取り、行・列を $G$ で添字づけた行列

\[
M_G=(x_{p^{-1}q})_{p,q\in G}
\]

を考える。言語解釈 $x_g=\{\underline g\}$ の下では、行列 star の各成分は

\[
\llbracket(M_G^*)_{p,q}\rrbracket
=
\{w\in\underline G^*\mid p\mu_G(w)=q\}
=
\mu_G^{-1}(p^{-1}q)
\]

である。特に

\[
W_G=\llbracket(M_G^*)_{1,1}\rrbracket.
\]

したがって、全元アルファベット上の word problem は Conway の群行列 star の対角成分そのものである。

## 2. Conway の群恒等式との対応

Conway の有限群 $G$ に付随する group identity $P(G)$ は、一つの標準的な行列表示では

\[
\sum_{q\in G}(M_G^*)_{1,q}
=
\left(\sum_{g\in G}x_g\right)^*
\tag{$P(G)$}
\]

と書かれる。左辺は Cayley オートマトンの初期状態から各状態へ至る経路言語の総和である。これは変数 $x_g$ に任意の正規表現を代入できる普遍的な等式スキーマであり、単なる特定アルファベット上の集合等式より強い。

同じ行列 $M_G^*$ に対して、二つの理論は異なる問いを立てる。

| Conway--Krob--Ésik | 一般化 star height |
|---|---|
| 通常の正規表現の等式理論 | 補集合を許す一般化正規表現の複雑度 |
| $P(G)$ を公理として等式を導出する | $(M_G^*)_{p,q}$ を star 深さ $1$ で書けるか |
| 第一行の総和・行列 star 全体 | 各ファイバー、特に $(1,1)$ 成分 |
| star の存在・不動点等式 | star の**入れ子深さ**の上界 |

従って Krob の完全性定理から一般化 star height 予想は直接には従わない。しかし、両者が同じ有限群オートマトンを基礎データとしていることは、全元アルファベットが標準的な対象である理由を説明する。

## 3. 全元 word problem は全 $G$-認識言語を支配する

### 命題 3.1 (full-alphabet reduction)

有限群 $G$ と整数 $n\geq0$ について、次は同値である。

1. $h_{\mathrm g}(W_G)\leq n$。
2. 任意の $g\in G$ について $h_{\mathrm g}(\mu_G^{-1}(g))\leq n$。
3. 任意の有限アルファベット $A$、任意のモノイド準同型 $\varphi:A^*\to G$、任意の $P\subseteq G$ について
   \[
   h_{\mathrm g}(\varphi^{-1}(P))\leq n.
   \]

### 証明

$1\Rightarrow2$。各 $g\in G$ について

\[
\mu_G^{-1}(g)
=
\underline{g^{-1}}^{-1}W_G
\]

である。generalized star height $\leq n$ の言語は左商で閉じるので従う。

$2\Rightarrow3$。まず

\[
\mu_G^{-1}(P)=\bigcup_{g\in P}\mu_G^{-1}(g)
\]

は有限和であり、高さ $\leq n$ である。次に letter-to-letter morphism

\[
\widehat\varphi:A^*\longrightarrow\underline G^*,
\qquad
\widehat\varphi(a)=\underline{\varphi(a)}
\]

を取ると $\varphi=\mu_G\widehat\varphi$ なので

\[
\varphi^{-1}(P)
=
\widehat\varphi^{-1}(\mu_G^{-1}(P)).
\]

$\widehat\varphi$ は alphabetic morphism であり、既知の inverse-alphabetic closure から従う。

$3\Rightarrow1$ は $A=\underline G$、$\varphi=\mu_G$、$P=\{1\}$ とすればよい。∎

### 3.5 使用した二つの閉性の自己完結証明（2026-07-23 追記）

上の証明が外部入力として使った閉性は、次の二補題に限られる。いずれも
PST の閉包定理を引用せずに、構造帰納法で直接証明できる。以下で
$h_{\mathrm g}(E)$ は一般化正規表現 $E$ の構文的 star 高さ
（star の最大入れ子深さ）とする。

**補題 Q（一文字左商）.** アルファベット $B$、文字 $x\in B$、一般化正規表現
$E$ に対し、Brzozowski 微分 $\partial_x E$ を

- $\partial_x\emptyset=\partial_x\varepsilon=\emptyset$、
  $\partial_x y=\varepsilon$（$y=x$）、$\emptyset$（$y\neq x$）
- $\partial_x(E_1\cup E_2)=\partial_x E_1\cup\partial_x E_2$
- $\partial_x(E_1E_2)=(\partial_x E_1)E_2\ \cup\ \partial_x E_2$
  （後項は $\varepsilon\in L(E_1)$ のときのみ）
- $\partial_x(\lnot E_1)=\lnot(\partial_x E_1)$
- $\partial_x(E_1^*)=(\partial_x E_1)E_1^*$

で定める。このとき $L(\partial_x E)=x^{-1}L(E)$ かつ
$h_{\mathrm g}(\partial_x E)\leq h_{\mathrm g}(E)$。

*証明.* 言語等式は各節で標準的（補集合節は
$x^{-1}(B^*\setminus L)=B^*\setminus x^{-1}L$、star 節は
$x^{-1}(L^*)=(x^{-1}L)L^*$ による）。高さは、各節が
部分式の微分と**元の部分式のコピー**を和・連接・補集合で組むだけで
新しい star を導入しないことから、帰納法で
$h_{\mathrm g}(\partial_x E_1^*)=\max(h_{\mathrm g}(\partial_x E_1),
h_{\mathrm g}(E_1^*))=h_{\mathrm g}(E_1^*)$ を含めて従う。∎

**補題 M（letter-to-letter 逆準同型）.** 写像 $h:A\to B$ を文字ごとに
延長した準同型 $h:A^*\to B^*$ と、$B$ 上の一般化正規表現 $E$ に対し、
$E$ の各文字 $b$ を $\bigcup_{a\in h^{-1}(b)}a$（空なら $\emptyset$）で
置換した式を $\sigma_h(E)$ とする。このとき
$L(\sigma_h(E))=h^{-1}(L(E))$ かつ
$h_{\mathrm g}(\sigma_h(E))=h_{\mathrm g}(E)$ 以下。

*証明.* 置換は葉のみを書き換えるので高さは増えない。言語等式は構造帰納法。
文字・和は明らか。連接と star は、$h$ が長さ保存（一文字を一文字へ送る）
であることから、$h(w)$ の任意の因数分解が $w$ の同じ長さ配分の因数分解へ
一意に持ち上がることによる。補集合は $h$ が $A$ の全文字で定義されている
ことから $h^{-1}(B^*\setminus L)=A^*\setminus h^{-1}(L)$。∎

命題 3.1 の証明で必要なのは、$1\Rightarrow2$ で補題 Q（商をとる文字
$\underline{g^{-1}}$ はアルファベット $\underline G$ に属する）、
$2\Rightarrow3$ で有限和の閉性（自明）と補題 M（$\widehat\varphi$ は
letter-to-letter）だけである。従って**命題 3.1 は PST の閉包定理の
仮説監査に依存しない**。

機械検証: `scripts/closure_lemmas_check.py` が、疑似乱数生成した 400 個の
一般化正規表現について、微分と文字置換の両方を**厳密な DFA 同値**
（`tools/regex_cert.py` の product 同値判定）で検査し、あわせて構文高さの
不増加を全例で assert する。全例 PASS（決定的 seed 20260723）。

### 系 3.2

$G$ が非自明で $h_{\mathrm g}(W_G)\leq1$ なら

\[
h_{\mathrm g}(W_G)=1.
\]

実際、$W_G$ の構文モノイドは $G$ 自身である。異なる $g,h\in G$ は左文脈 $\underline{g^{-1}}$ で区別できる。非自明有限群は非周期的でないため、Schützenberger の定理により $W_G$ は star-free でない。

## 4. $A_4$ に対する帰結

`RESULTS.md` §5.5 の対象は、まさに

\[
W_{A_4}\subseteq\underline{A_4}^*
\]

である。従って、その高さ $\leq1$ 証明が確立すれば、命題 3.1 により次の強い結論が従う。

> 任意の有限アルファベット $A$、任意の準同型 $\varphi:A^*\to A_4$、任意の受理集合 $P\subseteq A_4$ について、$\varphi^{-1}(P)$ の一般化 star height は高々 $1$ である。

これは「任意の生成系での単位元ファイバー」より強く、**$A_4$ が認識する任意の言語**を含む。

ただし、リポジトリ上の証拠状態は次のように分ける。

- `A4-FULL-01`: 現在 `COMPUTED`。
- 命題 3.1: PST の閉性仮説を精査したうえでの数学的還元。
- 「全 $A_4$-認識言語」の結論: 上二つを合成するため、現時点では `UNREVIEWED` とする。

## 5. 少数生成元版から全元版が自動ではない理由

有限生成集合 $S$ と全射

\[
\eta:S^*\twoheadrightarrow G
\]

を取る。各 $g\in G$ を表す語 $u_g\in S^*$ を選び、

\[
\sigma:\underline G^*\longrightarrow S^*,
\qquad
\sigma(\underline g)=u_g
\]

とすれば

\[
\mu_G=\eta\sigma,
\qquad
W_G=\sigma^{-1}(\eta^{-1}(1)).
\]

しかし $\sigma$ は一般には letter-to-letter ではなく、一文字を長い語へ送る。PST の inverse alphabetic morphism に関する閉性だけでは、この逆像が高さ $1$ を保存するとは言えない。

従って、§5.6 の二生成元 $A_5$ の結果

\[
h_{\mathrm g}(\eta^{-1}(1))=1
\]

から、全60元アルファベット版 $W_{A_5}$ や任意の $A_5$-認識言語の高さ $\leq1$ は自動ではない。

## 6. Conway 型の bounded-depth input-extension 問題

有限オートマトンに新しい入力文字を追加し、その文字の作用を既存の語が誘導する変換と同じにする操作を input extension と呼ぶ。Ésik は Conway identities の下で、ある有限オートマトンの identity から任意の input extension の identity が従うことを証明している。

一般化 star height に対して対応する問いは次である。

### 問題 6.1 (height-one input extension)

有限群 $G$、全射 $\eta:A^*\twoheadrightarrow G$、語 $u\in A^*$ を取る。新しい文字 $c$ を加え、

\[
\eta':(A\sqcup\{c\})^*\longrightarrow G,
\qquad
\eta'|_A=\eta,
\qquad
\eta'(c)=\eta(u)
\]

とする。このとき

\[
h_{\mathrm g}(\eta^{-1}(1))\leq1
\quad\Longrightarrow\quad
h_{\mathrm g}((\eta')^{-1}(1))\leq1
\]

は成立するか。

これが肯定的なら、新しい文字を有限回追加することにより

\[
\boxed{
\text{二生成元版 }A_5\text{ の高さ }1
+
\text{height-one input extension}
\Longrightarrow
W_{A_5}\text{ の高さ }1
}
\]

となる。さらに命題 3.1 から、$A_5$ が認識する任意の言語の高さが高々 $1$ と従う。

この問題は、Conway の最終予想に現れる

\[
\text{全群元を使う巨大な群恒等式}
\quad\rightsquigarrow\quad
\text{少数生成元による圧縮された恒等式}
\]

という方向と平行である。新屋の2025年概説は、Conway の symmetric identities $R(n)$ による最終予想を未解決問題として紹介している。本ノート作成時の公開文献監査でも、それ以後の解決報告は確認できなかった。

## 7. 有限単純群と $A_5$

Ésik の iteration-theory の完全性定理では、有限オートマトン恒等式の族が十分であるための条件が、遷移モノイド内の群がすべての有限単純群を divisor として捉えることにより特徴づけられる。この意味で、最初の非可換有限単純群 $A_5$ は Conway--Krob 型の等式理論でも原子的な位置を占める。

ただし、一般化 star height において

\[
\text{有限単純群だけを解けば全有限群が従う}
\]

という reduction theorem は知られていない。Conway--Ésik の結果を star の**存在**から star の**深さ**へそのまま移すことはできない。

## 8. 圏論的な見方

アルファベット $A$ に対する自由モノイド $A^*$ は、始点を持つ $A$-作用の圏における初期対象とみなせる。$A=\underline G$ とし、Cayley 作用 $(G,1)$ を取ると、初期性から得られる一意な射が

\[
\mu_G:\underline G^*\to G
\]

である。

従って、

- Conway の群恒等式は、この普遍射に付随する全経路の行列 star を等式公理として見る。
- 一般化 star height は、この普遍射の各ファイバーを bounded-depth expression で記述できるかを問う。

という同一データの二つの読み方になる。

## 9. 次の具体的タスク

1. **PST 監査**: inverse alphabetic morphism の定義と仮説を原文で確認し、命題 3.1 を `PROVED` または `CITED+PROVED` に昇格させる。
2. **ledger**: `A4-ALLLANG-01` を追加し、`A4-FULL-01` と命題 3.1 の証拠状態を継承させる。
3. **一文字 input extension 実験**: §5.6 の $A_5$ 生成系へ一つの群元文字を追加し、既存の初回帰還符号または synthesis search で高さ $1$ が保たれるか調べる。
4. **Lean**: $M_G^*$ の状態間言語と $\mu_G$ の各ファイバーの同一視、命題 3.1 の closure reduction を形式化する。
5. **新屋良磨への確認事項**: permutation/group automata に限定した bounded-star-depth input-extension theorem が既知か、Conway の symmetric identities とのより直接的な関係があるかを確認する。
