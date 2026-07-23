# 非可換単純群の word problem に対する height 1 の単一観測器還元

作業日: 2026-07-23。

## 状態

- **証明状態**: 以下の還元は、Pin--Straubing--Thérien の商閉性と Place--Zeitoun の
  star-free closure の代数的特徴づけを外部定理として用いる数学的証明である。
- **未完了事項**: 文献上の新規性監査、独立査読、Lean 形式化。
- **主張しないこと**: $(2,3,5)$ 型 $A_5$ word problem の高さ $\geq 2$ はまだ証明していない。

主要な外部入力は次の 2 点である。

1. generalized star height $\leq n$ の言語は左右商で閉じる
   (Pin--Straubing--Thérien 1992)。
2. prevariety $\mathcal C$ に対し、$L\in\operatorname{SF}(\mathcal C)$ であることと、
   $L$ の構文射の全 $\mathcal C$-orbit が非周期的であることは同値
   (Place--Zeitoun 2023, Theorem 5.11)。

参照:

- J.-E. Pin, H. Straubing, D. Thérien,
  [Some results on the generalized star-height problem](https://doi.org/10.1016/0890-5401(92)90063-L),
  *Information and Computation* 101 (1992), 219--250.
- T. Place, M. Zeitoun,
  [Closing star-free closure](https://arxiv.org/abs/2307.09376),
  Theorem 5.11 and Lemmas 5.4--5.5.

## 1. flat-star prevariety

有限アルファベット $A$ を固定する。$\mathsf{SF}_0(A)$ を $A$ 上の star-free languages
の全体とする。次を定める。

\[
\mathcal B_A
=
\operatorname{BoolQuot}
\{K^*\mid K\in\mathsf{SF}_0(A)\}.
\]

ここで $\operatorname{BoolQuot}$ は、指定された言語を含む最小の、Boolean 演算と
左右商で閉じた言語族を表す。各 $K^*$ は正規言語なので、$\mathcal B_A$ は
Place--Zeitoun の意味で prevariety である。

$\operatorname{SF}(\mathcal C)$ は、$\mathcal C$ と全有限言語を含み、Boolean 演算と
連接で閉じた最小の言語族、すなわち star-free closure とする。

## 2. height-one flattening

### 命題 2.1

\[
\mathsf{GSH}_{\leq 1}(A)=\operatorname{SF}(\mathcal B_A).
\]

### 証明

$E$ を generalized star height $\leq 1$ の式とする。$E$ に現れる各 starred
subexpression $F^*$ の内部 $F$ は star を含まないので、$K=L(F)$ は star-free である。
したがって $L(F^*)=K^*\in\mathcal B_A$ である。各 starred subexpression を
$\mathcal B_A$ の原子と見れば、外側には Boolean 演算と連接しか残らない。よって
$L(E)\in\operatorname{SF}(\mathcal B_A)$ である。

逆に各 $K^*$ は generalized star height $\leq 1$ である。height $\leq 1$ の言語は
Boolean 演算、連接、および Pin--Straubing--Thérien の定理により左右商で閉じる。
また有限言語は height $0$ である。従って $\mathcal B_A$ とその star-free closure は
すべて height $\leq 1$ に含まれる。∎

## 3. 有限群 word problem では外側の連接を消去できる

全射モノイド射 $\pi:A^*\twoheadrightarrow G$ を有限群 $G$ へ取り、

\[
L_\pi=\pi^{-1}(1)
\]

とする。このとき $\pi$ は $L_\pi$ の構文射である。実際、$\pi(u)\neq\pi(v)$ なら、
全射性により $\pi(x)=\pi(u)^{-1}$ なる語 $x$ が存在し、$xu\in L_\pi$ だが
$xv\notin L_\pi$ である。

### 命題 3.1 (group collapse)

\[
h_{\mathrm g}(L_\pi)\leq 1
\quad\Longleftrightarrow\quad
L_\pi\in\mathcal B_A.
\]

### 証明

右から左は定義から明らかである。左から右を示す。命題 2.1 より
$L_\pi\in\operatorname{SF}(\mathcal B_A)$ である。

Place--Zeitoun の Theorem 5.11 を $\mathcal C=\mathcal B_A$ に適用する。群 $G$ の
冪等元は $1$ だけなので、調べる orbit は

\[
N=
\{g\in G\mid (1,g)\text{ が }\mathcal B_A\text{-pair}\}
\]

だけである。Place--Zeitoun の Lemmas 5.4--5.5 により $N$ は $G$ の部分モノイド、
従って有限群の部分群である。さらに $g\in N$ と $h\in G$ に対し、反射的 pair
$(h,h)$ と $(h^{-1},h^{-1})$ を左右から掛ければ $(1,hgh^{-1})$ も pair なので、
$N\triangleleft G$ である。

Theorem 5.11 より $N$ は非周期的である。しかし有限群が非周期的であるための
必要十分条件は自明群であることなので $N=\{1\}$ である。従って各 $g\neq 1$ について
$(1,g)$ は $\mathcal B_A$-pair ではない。すなわち、ある $H_g\in\mathcal B_A$ が存在して

\[
\pi^{-1}(1)\subseteq H_g,
\qquad
H_g\cap\pi^{-1}(g)=\varnothing
\]

となる。$G$ は有限なので

\[
\pi^{-1}(1)=\bigcap_{g\neq 1}H_g\in\mathcal B_A.
\]

これで示された。∎

### 含意

有限群の word problem については、height $1$ 式の「一段スターの外側」にある連接は、
最終的に $K^*$ の左右商と Boolean 結合へ吸収できる。従って lower bound の本体は
$\mathcal B_A$-separation、同値に $\mathcal B_A$-pair の非自明性である。

## 4. 非可換単純群では有限個の $K_i^*$ を一個へ潰せる

### 補題 4.1 (直積部分群から単純群への商)

$S$ を有限非可換単純群、$H\leq G_1\times\cdots\times G_r$ を部分群とする。全射
$\psi:H\twoheadrightarrow S$ が存在すれば、ある $i$ について $\psi$ は座標射影
$p_i:H\to p_i(H)$ を経由する。

### 証明

$r=2$ とする。$K_i=\ker p_i$ と置くと $K_1$ と $K_2$ は互いに可換する。
$\psi(K_i)\triangleleft S$ なので、単純性より各像は $1$ または $S$ である。両方が $S$
なら $S$ の任意の 2 元が可換し、$S$ が非可換であることに反する。従ってどちらか一方、
例えば $\psi(K_1)$ は自明であり、$\psi$ は $p_1$ を経由する。一般の $r$ は
$G_1\times(G_2\times\cdots\times G_r)$ とまとめた帰納法で従う。∎

### 補題 4.2 (有限モノイド版)

有限モノイド $M_i$ への射 $\eta_i:A^*\to M_i$ を有限個取り、
$\eta=(\eta_1,\ldots,\eta_r)$ とする。有限非可換単純群 $S$ への全射
$\pi:A^*\twoheadrightarrow S$ が $\eta$ を経由するなら、$\pi$ はある一つの $\eta_i$ を
経由する。

### 証明

$N=\operatorname{im}\eta\leq\prod_iM_i$ とし、$\theta:N\twoheadrightarrow S$ で
$\pi=\theta\eta$ とする。$N$ の最小イデアル $I$ は $S$ へ全射される。実際
$\theta(I)$ は群 $S$ の非空イデアルなので $S$ 全体である。

$I$ の冪等元 $e$ を取る。$\theta(e)=1$ であり、有限半群の標準事実より
$H=eNe$ は群である。また $x\in I$ で $\theta(x)=g$ とすれば $exe\in H$ かつ
$\theta(exe)=g$ なので、$\theta|_H:H\twoheadrightarrow S$ は全射である。

$H$ は各座標像 $p_i(H)$ の直積の部分群であるから、補題 4.1 より
$\theta|_H$ はある座標 $i$ を経由する。いま $\eta_i(u)=\eta_i(v)$ とすると、
$e\eta(u)e$ と $e\eta(v)e$ の第 $i$ 座標は等しい。従って

\[
\pi(u)=\theta(e\eta(u)e)=\theta(e\eta(v)e)=\pi(v).
\]

よって $\ker\eta_i\subseteq\ker\pi$ であり、$\pi$ は $\eta_i$ を経由する。∎

## 5. 単一観測器還元

$K^*$ の構文射を

\[
\eta_{K^*}:A^*\twoheadrightarrow\operatorname{Synt}(K^*)
\]

と書く。

### 定理 5.1 (simple-group single-observer reduction)

$S$ を有限非可換単純群、$\pi:A^*\twoheadrightarrow S$ を全射とする。次は同値である。

1. $h_{\mathrm g}(\pi^{-1}(1))\leq 1$。
2. ある star-free language $K\subseteq A^*$ が存在し、$\pi$ は $\eta_{K^*}$ を経由する。
3. ある star-free language $K\subseteq A^*$ が存在し、
   $\ker\eta_{K^*}\subseteq\ker\pi$。

### 証明

$1\Rightarrow2$: 命題 3.1 より $\pi^{-1}(1)\in\mathcal B_A$。$\mathcal B_A$ の各言語は、
有限個の star-free languages $K_1,\ldots,K_r$ に対する $K_i^*$ の左右商の Boolean
結合として書ける。従って

\[
(\eta_{K_1^*},\ldots,\eta_{K_r^*})
\]

が $\pi^{-1}(1)$ を認識する。$\pi$ はこの言語の構文射なので、この積射を経由する。
補題 4.2 より、ある一つの $\eta_{K_i^*}$ を経由する。

$2\Leftrightarrow3$ は商の普遍性から明らか。

$2\Rightarrow1$: $\pi^{-1}(1)$ は $\eta_{K^*}$ で認識される。構文射
$\eta_{K^*}$ が認識する全言語は $K^*$ の左右商の Boolean 結合で書ける。実際、異なる
構文モノイド元はある二側文脈で区別されるため、各構文モノイドのファイバーは有限個の
二側商とその補集合の交叉で書ける。従って
$\pi^{-1}(1)\in\operatorname{BoolQuot}(K^*)\subseteq\mathcal B_A$。命題 3.1 より
height $\leq1$ である。∎

## 6. hard $A_5$ に対する厳密な残存証明義務

\[
s=(12)(34),\qquad t=(135),
\]

\[
\pi:\{s,t\}^*\twoheadrightarrow A_5
\]

とする。定理 5.1 より、この word problem が height $\geq2$ であることは、次の一文と
同値である。

> 任意の star-free language $K\subseteq\{s,t\}^*$ に対して、ある語 $u,v$ が存在し、
> $\eta_{K^*}(u)=\eta_{K^*}(v)$ だが $\pi(u)\neq\pi(v)$ となる。

すなわち

\[
\forall K\in\mathsf{SF}_0(\{s,t\}),\quad
\exists u,v\in\{s,t\}^*:
\eta_{K^*}(u)=\eta_{K^*}(v),\quad \pi(u)\neq\pi(v).
\]

これは「任意の有限個の height-1 観測器」を量化する必要を、「任意の一個の $K^*$ 観測器」
へ縮約する。今後の pointlike、flow、profinite、論理ゲームによる lower-bound 探索はこの
命題を直接狙えばよい。

## 7. 抽象モノイド不変量では足りない理由

Pin は、任意の有限モノイド $M$ に対し、ある有限言語 $F$、しかも有限完全接頭符号 $F$ を
選んで、$M$ が $\operatorname{Synt}(F^*)$ を割ることを示している。

- J.-E. Pin,
  [Sur le monoïde syntactique de $L^*$ lorsque $L$ est un langage fini](https://doi.org/10.1016/0304-3975(78)90050-6),
  *Theoretical Computer Science* 7 (1978), 211--215.

従って、$A_5$ が抽象モノイドとして $\operatorname{Synt}(K^*)$ を割らない、という形の
障害は存在し得ない。必要なのは固定アルファベットと生成射を記憶する

\[
(A,\pi:A^*\twoheadrightarrow A_5)
\]

の **marked factorization** の非存在である。

同じ理由と、生成系 $(123),(145)$ では $A_5$ word problem が height $1$ であるという
本リポジトリの結果から、抽象群 $A_5$ の通常の群コホモロジーだけでは hard/easy 生成系を
区別できない。コホモロジーを使うなら、free monoid からの marked morphism、Cayley/Schreier
作用、または flat-star prevariety に対応する profinite quotient を係数系に含める必要がある。

## 8. profinite/cohomology 方向の正確な位置づけ

$\mathcal B_A$ に対応する pro-$\mathcal B_A$ quotient を $P_{\mathcal B}(A)$、標準写像を
$\eta:A^*\to P_{\mathcal B}(A)$ と書くことができれば、height $1$ は $\pi$ がこの quotient を
通じて連続に因子化することと対応する。候補となる相対対象は graph closure

\[
R_\pi=
\overline{\{(\eta(w),\pi(w))\mid w\in A^*\}}
\subseteq P_{\mathcal B}(A)\times A_5
\]

と第一射影 $R_\pi\to P_{\mathcal B}(A)$ である。同じ profinite point 上に複数の $A_5$-label
が残れば marked factorization は失敗する。

ただし、これを検出する標準的な cohomology class、係数系、height $1$ の場合の vanishing
定理はまだ構成されていない。この段落は研究方向であり、下界結果ではない。

## 9. 監査・形式化のチェックリスト

1. Place--Zeitoun Theorem 5.11 の使用条件として $\mathcal B_A$ が prevariety であることを確認。
2. Pin--Straubing--Thérien の「各 height level の左右商閉性」の正確な定理番号を確定。
3. 有限モノイドの最小イデアルにある冪等元 $e$ について $eNe$ が群である標準補題を引用。
4. 定理 5.1 の既存文献での先行性を調査。
5. Lean では、まず補題 4.1、有限モノイドの最小イデアル補題、構文射のファイバーが
   二側商の Boolean 結合で書けることを独立に形式化する。
