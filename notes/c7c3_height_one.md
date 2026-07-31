# \(C_7\rtimes C_3\) の全言語高さ 1 証明

## 1. 主張と量化

\(G=C_7\rtimes C_3\) を

\[
G=\langle x,y\mid x^7=y^3=1,\ yxy^{-1}=x^2\rangle
\]

で与える。このノートの最終主張は

\[
\forall\text{有限 alphabet }A,\quad
\forall\phi:A^*\to G,\quad
\forall P\subseteq G,\quad
h_{\mathrm g}(\phi^{-1}(P))\leq1.
\tag{C7C3-ALLLANG-01}
\]

まず、\(G\) の21元を一文字ずつ持つ全元 alphabet \(\underline G\) 上の
評価準同型 \(\mu:\underline G^*\to G\) の恒等 fibre を扱う。ここから上の
全量化への移送は `FULL-ALPH-RED-01` である。

## 2. 入力事実と水準

| 入力 | 水準 | 根拠 |
|---|---|---|
| 右から左への積 \(\nu(w)\) は total phase と57個の cut count の固定 GF(7) 線形条件で全語について特徴づく | `PROVED` | `C7C3-IDENT-01`; `RESULTS.md` §5.16.1 |
| 証明で使う first/post-cut token はすべて非周期的で、cut-count の mod 7 分解は直接 counter DFA と同値 | `COMPUTED` | `C7C3-H1-FINITE-CORE-01`; `scripts/ci/c7c3_height_one.py` |
| 非周期的な有限 transition monoid を持つ DFA の言語は star-free | `CITED` | M.-P. Schützenberger, “On Finite Monoids Having Only Trivial Subgroups”, *Information and Control* 8(2) (1965), 190–194, Main Property, DOI 10.1016/S0019-9958(65)90108-7 |
| 高さ \(\leq1\) は有限 Boolean 演算・連接で閉じ、文字数合同言語は高さ \(\leq1\) | `PROVED` | `GSH/Height/Closure.lean`, `GSH/Height/Counting.lean`, `LEAN-FIN-BOOL-01` |
| reversal は generalized star height を保つ | `PROVED` | `GSH.HasHeightAtMost.reverse` (`L-REV-001`) |
| 全元 alphabet の恒等 fibre から任意の alphabet・morphism・accepting set へ移せる | `PROVED` | `FULL-ALPH-RED-01`; `GSH.heightOneForGroup_of_fullIdentityFiber` |

旧 `C7C3-FULL-01` (`EMPIRICAL`) は使わない。そこでの741特徴の有限長一致を、
全語に対する同値と読み替えてはならない。本証明が使う算術入力は別の57原子を使う
`C7C3-IDENT-01` である。

## 3. 一つの cut count の高さ

cut phase \(q\in\mathbb Z/3\) と pattern \(\pi\) を固定する。各文字を読むと
phase を更新し、到着 phase が \(q\) で pattern が skip を許さないときに cut
する。cut の直後には private previous-letter state を `None` に戻す。

次の四言語を取る。

- \(O\): global start \((0,\mathrm{None})\) から最初の cut ちょうどまで。
- \(X\): post-cut state \((q,\mathrm{None})\) から次の cut ちょうどまで。
- \(V_0\): global start から一度も cut しない語。
- \(V\): post-cut state から一度も cut しない語。

`check_token_aperiodicity` は `anti` 14 pattern と `set` 3 pattern、全3 cut
phases、global/post-cut の両初期状態、計102 DFAを走査する。最小 DFA の
transition monoid 4,638元を生成元から閉包し、各元の冪が停止することを全数判定する。従って
Schützenberger の Main Property により \(O,X\) は star-free である。また

\[
V_0=\neg(O\,\underline G^*),\qquad
V=\neg(X\,\underline G^*)
\tag{3.1}
\]

なので \(V_0,V\) も star-free である。

cut 後の状態が毎回同じであるため、cut が \(k\geq1\) 回起きる語の分解

\[
w\in OX^{k-1}V
\tag{3.2}
\]

は一意である。従って cut 数が \(h\pmod7\) である言語は

\[
R_h=
\begin{cases}
V_0\ \cup\ OX^6(X^7)^*V,&h=0,\\
OX^{h-1}(X^7)^*V,&1\leq h\leq6.
\end{cases}
\tag{3.3}
\]

\(X^7\) は star-free であり、式 (3.3) の Kleene star は
\((X^7)^*\) の一段だけである。ゆえに \(h_{\mathrm g}(R_h)\leq1\)。

`check_residue_factorization` は (3.3) を仮定して有限長の語を比べるのではない。
全357組の pattern・\(q\)・\(h\) について式側 DFA と直接 mod-7 cut-counter DFA の
積9,555状態を完全探索し、識別語が存在しないことを決定する。ループを \(X^6\) に変える
control と、\(h=0\) から \(V_0\) を除く control はいずれも拒否される。

## 4. 57原子の有限 Boolean 合成

`C7C3-IDENT-01` が使う実際の57原子は

- forward `set`: 9個、
- forward `anti`: 24個、
- backward `anti`: 24個

である。`check_atom_coverage` は57個を列挙し、各 forward 原子が §3 の
pattern/phase に含まれること、各 backward 原子が反転語上の同じ forward cut
であることを検査する。

各原子 \(j\) の cut count を \(c_j(w)\in\mathbb Z/7\)、固定係数を
\(a_j\in\mathbb Z/7\) と書く。§3 により各 cell
\(\{w:c_j(w)=r\}\) は高さ \(\leq1\) である。backward cell は対応する
forward cell の reversal なので、やはり高さ \(\leq1\) である。従って

\[
D=\left\{w:\sum_{j=1}^{57}a_jc_j(w)=0\pmod7\right\}
\tag{4.1}
\]

は高さ \(\leq1\) の有限 Boolean 結合になる。明示的には

\[
S_{0,0}=\underline G^*,\qquad S_{0,t}=\varnothing\quad(t\ne0),
\]

\[
S_{k+1,t}=\bigcup_{r\in\mathbb Z/7}
\left(S_{k,t-a_{k+1}r}\cap\{w:c_{k+1}(w)=r\}\right)
\tag{4.2}
\]

と順に定めれば、\(D=S_{57,0}\) である。この running-sum 表示には有限 union と
intersection しか現れない。

total phase が0という条件も高さ \(\leq1\) である。実際、各文字 \(g\in G\)
の出現数 mod 3 を固定する言語は文字数合同言語の有限 intersection であり、
\(\sum_g\varepsilon(g)|w|_g=0\pmod3\) を満たす residue vector について有限
union を取ればよい。

`C7C3-IDENT-01` により、全語 \(w\) について

\[
\nu(w)=1\quad\Longleftrightarrow\quad
\operatorname{phase}(w)=0\ \text{かつ}\ w\in D.
\tag{4.3}
\]

右辺は高さ \(\leq1\) なので、\(\nu^{-1}(1)\) も高さ \(\leq1\) である。

## 5. 左から右の積と全言語への移送

\(\nu(w)=\mu(\operatorname{rev}w)\) であり、reversal は generalized star
height を保つ。従って全21元 alphabet 上の通常の恒等 fibre
\(\mu^{-1}(1)\) は高さ \(\leq1\) である (`C7C3-FULL-H1-01`)。

最後に `FULL-ALPH-RED-01` を適用する。これは任意の有限 alphabet、任意の
monoid morphism \(\phi:A^*\to G\)、任意の accepting subset \(P\subseteq G\)
を保ったまま移送する。従って (C7C3-ALLLANG-01)、すなわち

\[
\operatorname{HeightOneForGroup}(C_7\rtimes C_3)
\]

が従う。

## 6. 検証と射程

```bash
python3 -m unittest tests.test_c7c3_height_one -v
python3 scripts/ci/c7c3_height_one.py
python3 scripts/research/c7c3_identity_proof.py
./scripts/check.sh
```

有限 verdict `C7C3-H1-FINITE-CORE-01` は Schützenberger の定理や §§4–5 の
人間による合成を含まない。したがって有限 core は `COMPUTED`、全元恒等 fibre と
`HeightOneForGroup` はそれぞれ人間証明を含む `PROVED` と分類する。Lean kernel
内の定理は別 obligation とし、このノートを Lean 証明済みとは呼ばない。
