## 5.10 height 1 下界の理論的縮約: 非可換単純群では単一 $K^*$ 観測器で十分

詳細な証明は `notes/simple_group_height1_reduction.md` に記録した。状態は
**数学的証明あり（外部定理を使用）、文献上の新規性未監査、Lean 未形式化**である。
この節は $(2,3,5)$ 型 $A_5$ の高さ $\geq2$ を主張しない。

固定アルファベット $A$ 上で

\[
\mathcal B_A
=
\operatorname{BoolQuot}
\{K^*\mid K\text{ は star-free}\}
\]

と置く。Pin--Straubing--Thérien の各 height level の商閉性と、Place--Zeitoun
Theorem 5.11 の $\mathcal C$-orbit 特徴づけを組み合わせると、次が得られる。

1. **height-one flattening**:
   \[
   \mathsf{GSH}_{\leq1}(A)=\operatorname{SF}(\mathcal B_A).
   \]
2. **group collapse**: 全射 $\pi:A^*\twoheadrightarrow G$ が有限群への射なら、
   \[
   h_{\mathrm g}(\pi^{-1}(1))\leq1
   \iff
   \pi^{-1}(1)\in\mathcal B_A.
   \]
   群では唯一の orbit が正規部分群になり、aperiodic なら自明になるため、外側の
   star-free concatenation は $K^*$ の商と Boolean 結合へ吸収される。
3. **simple-group single-observer reduction**: $S$ が有限非可換単純群なら、
   \[
   h_{\mathrm g}(\pi^{-1}(1))\leq1
   \iff
   \exists K\text{ star-free such that }
   \pi\text{ factors through }\eta_{K^*}.
   \]
   ここで $\eta_{K^*}$ は $K^*$ の構文射。有限個の $K_i^*$ の積を通じた因子化は、
   最小イデアルの maximal subgroup と「直積部分群から非可換単純群への全射は一座標を
   経由する」という補題により、一個の $K_i^*$ へ潰れる。

従って hard generating set

\[
s=(12)(34),\qquad t=(135),\qquad
\pi:\{s,t\}^*\twoheadrightarrow A_5
\]

について高さ $\geq2$ を示すための残存証明義務は、正確に

\[
\forall K\text{ star-free},\quad
\exists u,v:\
\eta_{K^*}(u)=\eta_{K^*}(v),\quad
\pi(u)\neq\pi(v)
\]

である。「任意の有限個の height-1 観測器」を排除する代わりに、任意の**単一**
$K^*$ 観測器を排除すればよい。pointlike/separation、flow、profinite、論理ゲームの各方向は
この命題を直接狙うべきである。

### marked invariant が必要

Pin (1978) により、任意の有限モノイドは、ある有限完全接頭符号 $F$ に対する
$\operatorname{Synt}(F^*)$ を割る。従って「$A_5$ が抽象モノイドとして
$\operatorname{Synt}(K^*)$ を割れない」という障害は存在しない。必要なのは固定アルファベットと
生成射を記憶する marked factorization の非存在である。

同様に、§5.6 の easy generating set では構文モノイドが $A_5$ そのものである height-1
言語が存在するので、抽象群 $A_5$ の通常の cohomology だけでは下界にならない。cohomology
を使うなら、marked morphism または flat-star prevariety に対応する profinite quotient を
含む相対不変量が必要である。graph closure
$R_\pi\to P_{\mathcal B}(A)$ は候補だが、係数系と vanishing theorem は未構成である。
