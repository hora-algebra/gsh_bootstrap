## 5.5.1 全元アルファベット・全群言語・Conway 群恒等式

有限群 $G$ の全元アルファベットを

\[
\underline G=\{\underline g\mid g\in G\}
\]

とし、標準評価射 $\mu_G:\underline G^*\to G$ と単位元ファイバー
$W_G=\mu_G^{-1}(1)$ を取る。Pin--Straubing--Thérien の左右商と
inverse alphabetic morphism に関する閉性から、任意の $n\geq0$ について

\[
h_{\mathrm g}(W_G)\leq n
\quad\Longleftrightarrow\quad
G\text{ が認識する任意の言語の generalized star height が高々 }n
\]

が従う。実際、各ファイバーは

\[
\mu_G^{-1}(g)=\underline{g^{-1}}^{-1}W_G
\]

という左商であり、任意の $\varphi:A^*\to G$ は letter-to-letter morphism
$\widehat\varphi(a)=\underline{\varphi(a)}$ と $\mu_G$ の合成に分解する。

従って §5.5 の全12元アルファベット版 $A_4$ の結果は、証拠状態を保ったまま、
**$A_4$ が認識する任意の言語**へ拡張される。これは「任意の生成系の単位元
ファイバー」より強い。ただし `A4-FULL-01` は現在 `COMPUTED` であり、この帰結も
独立査読までは `UNREVIEWED` とする。

この全元アルファベットは Conway の有限群 group identity と同じ Cayley
オートマトンを使う。群元で添字づけた行列

\[
M_G=(x_{p^{-1}q})_{p,q\in G}
\]

の star の成分は、文字解釈 $x_g=\{\underline g\}$ の下で

\[
\llbracket(M_G^*)_{p,q}\rrbracket=\mu_G^{-1}(p^{-1}q)
\]

であり、$W_G$ は $(1,1)$ 成分である。Conway--Krob--Ésik はこの行列 star を
正規表現の等式公理として扱うのに対し、一般化 star height 問題は各成分を
star 深さ $1$ で書けるかを問う。

一方、少数生成元 $S$ 上の $\eta:S^*\twoheadrightarrow G$ から全元版へ移るには、
各 $g$ を表す語 $u_g\in S^*$ を選び、文字 $\underline g$ を語 $u_g$ へ送る必要がある。
これは alphabetic morphism でないため、§5.6 の二生成元 $A_5$ の高さ $1$ から
全60元版は自動ではない。

そこで次の **Conway 型 bounded-depth input-extension 問題**が生じる。
既存の語 $u$ と同じ変換をする新しい文字 $c$ を追加したとき、群 word problem の
高さ $\leq1$ は保存されるか。肯定的なら

\[
\text{二生成元版 }A_5
+\text{ input extension}
\Longrightarrow
\text{全元版 }A_5
\Longrightarrow
\text{全 }A_5\text{-認識言語}
\]

となる。Ésik は iteration categories の automaton identities に対して input
extension theorem を証明しているが、bounded star depth を保存する対応物は本調査では
見つかっていない。

詳細は `notes/conway_group_identities_and_full_alphabet.md` を参照。
