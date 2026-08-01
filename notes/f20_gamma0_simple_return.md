# `Gamma_0` の simple first-return token

## 1. 対象と証拠境界

`F_20=C_5 semidirect C_4` の元を `(epsilon,beta)` と書き、

```text
Gamma_0 = {a=(0,1), b=(1,0), c=(2,0), d=(3,0)}
```

とする。標準評価を `mu_0:Gamma_0^* -> F_20`、identity fibre を `T_0` と書く。
最終目標は `gsh(T_0)<=1` だが、このノートはそれを証明しない。ここで証明するのは、
既知の二文字 W-atom に一致する新しい star-free token 一個と、その token だけでは全語を
分解できないという正確な障害である。

入力の分類は次の通り。

- `F20-ALPH5-01`, `F20-GAMMA4-EQUIV-01`: `PROVED`。
- `F20-STD-01`: `COMPUTED`。ただしここで使うのは同じ二文字 token の式だけで、
  `T_0` の高さについて量化を広げない。
- 以下の simple-return の式と反例: このノート内で `PROVED`。
- DFA、transition monoid、旧14 cutとの比較: 完全有限探索による機械支援。

## 2. simple first-return token

文字の phase weight を

```text
omega(a)=0, omega(b)=1, omega(c)=2, omega(d)=3  (mod 4)
```

とする。mover skeleton `x_1...x_n` (`x_i in {b,c,d}`) を **simple first-return** と呼ぶのは、
部分和 `s_i=sum_{j<=i} omega(x_j)` が `i<n` では相異なる非零元であり、`s_n=0` となるときである。
非零 phase は三つしかないので `n<=4` であり、skeleton は正確に次の15個である。

```text
bbbb  bbc  bcb  bcdc  bd
cbb   cbcd cc   cdcb  cdd
db    dcbc dcd  ddc   dddd
```

`TOP=not empty`（ambient alphabet 全体）とし、

```text
A_0 = not (TOP (b union c union d) TOP)
```

を `a` だけからなる語全体とする。

```text
R_simp = {a} union
         union_{x_1...x_n simple} x_1 A_0 x_2 A_0 ... A_0 x_n
```

と置く。

**補題 1 (`F20-GAMMA0-SIMPLE-RETURN-01`).** `R_simp` は star-free である。各非自明 token は
phase 0から出て、途中でphase 0にも同じ非零phaseにも戻らず、最後に初めてphase 0へ戻る。
従って token の内部にある `a` はphase 0では読まれず、singleton token `a` だけがphase 0での
`a` の出現を一つ数える。

*証明.* `TOP` と `A_0` の表示はKleene starを使わないのでstar-freeである。
上の表示は15個の有限 union と concatenation しか使わないため
`R_simp` も star-free。残りは simple first-return の定義から従う。これは任意長の語に対する
式の証明であり、有限長標本ではない。∎

`{a,b}` へ制限すると唯一の非自明 skeleton は `bbbb` なので、

```text
R_simp intersect {a,b}^* = a union b a* b a* b a* b.
```

右辺は `F20-STD-01` の W-atom 構成が使う `TOKEN` と正確に同じである。

## 3. 自然な first-return 全体へは広がらない

simple 条件を外し、途中ではphase 0に戻らない全 first-return codeを `R_all` とする。
`R_simp` は `R_all` の真部分言語である。最小の鋭い witness は

```text
bbdd : 0 -> 1 -> 2 -> 1 -> 0.
```

これは途中でphase 0へ戻らないが、非零phase 1を再訪するので `R_simp` には入らない。
しかも最初のreturnが語末なので、複数の `R_simp` tokenへ分割することもできない。従って
`R_simp^*` はphase 0へ戻る全語を覆わず、singleton token数だけで全語の `N_0` を数える段階には
まだ達していない。

この欠落は単に15個の一覧を増やせば済むものではない。star-free な言語 `b c* d` との交わりは

```text
R_all intersect b c* d = { b c^(2m) d : m>=0 }.
```

実際、`b` の後のphaseは1で、`c` ごとに `1 <-> 3` と往復し、偶数個の `c` の後に `d` で
初めて0へ戻る。もし `R_all` が star-free なら、star-free言語とのintersectionと左右quotientに
より `{c^(2m):m>=0}` もstar-freeになる。しかしその最小DFAでは `c` が二状態を交換するため、
syntactic monoidはperiod 2を持つ。従って `R_all` は star-free ではない。

一方、phase-zero言語

```text
P = {w : omega(w)=0 mod 4}
```

はreturn位置で `R_all` の語へ一意に分解されるので `P=R_all^*` である。また

```text
R_all = P_plus minus (P_plus Gamma_0_plus).
```

`P` は可換群 `C_4` が認識するので `gsh(P)<=1` は `PST-GRP-01`（`CITED`）から従い、
Boolean演算とconcatenationにより `gsh(R_all)<=1`。上のperiod-2証明からstar-freeではないため、
`gsh(R_all)=1` である。従って `R_all` を既知二文字式のstarの内側へそのまま代入すると、構文上は
starが二重になる。これは**その直接代入法**の障害であり、`T_0` の高さが2だという下界ではない。

これは `R_simp` の visited-set 条件が本質的であることを示す。自然な次案は訪問回数の上限を
一段ずつ増やすことだが、次節でこの有限階層route自体が完結不能であることを示す。

## 4. bounded-visit finite hierarchy は完結しない

語から `a` を消して得る mover skeleton を `x_1...x_n` とし、

```text
s_i = omega(x_1)+...+omega(x_i) mod 4
```

と置く。ここで訪問として数えるのは mover を読んだ直後の `s_i` だけであり、間に挿入された
`a` の前後を別訪問とは数えない。また終端 `s_n=0` も非零phaseの訪問数には含めない。
`k>=1` に対し、`R^(k)` を singleton `a` と、各非零phase `p=1,2,3` が
`s_1,...,s_{n-1}` に高々 `k` 回しか現れない非自明 `R_all` tokenとの和とする。

**補題 2 (`F20-GAMMA0-VISIT-HIER-01`).** 任意の `k>=1` について次が成り立つ。

1. `R^(k)` はstar-freeであり、`R^(1)=R_simp`。
2. `R^(k)` は真に増大し、`w_k=b c^(2k) d` は
   `R^(k+1) minus R^(k)` に属する。さらに `w_k` はphase-zero言語
   `P={w:omega(w)=0}` に属するが、`(R^(k))*` には属さない。
3. `union_{k>=1} R^(k)=R_all` だが、star-free部分言語
   `L_1,...,L_N subseteq R_all` を有限個とって `R_all=union_i L_i` とすることはできない。

*証明.* `R^(k)` の非自明 tokenでは、終端直前までに現れる非零phaseは三つで、各々の訪問は
高々 `k` 回である。従って mover skeleton の長さは高々 `3k+1`。許される skeleton は有限個で、
各 `x_1...x_n` が定める語の集合は

```text
x_1 a* x_2 a* ... a* x_n
```

である。§2の通り ambient alphabet上の `a*` はstar-freeなので、有限和 `R^(k)` もstar-free。
`k=1` は非零部分和がすべて相異なるというsimple条件そのものであり、§2の15 skeletonを与える。

`w_k=b c^(2k) d` のphaseは、最初の `b` の後で1、`j` 個目の `c` の後で
`1+2j mod 4` である。従ってphase 1を `k+1` 回、phase 3を `k` 回訪れ、途中で0を訪れず、
最後の `d` で初めて0へ戻る。よって `w_k in R^(k+1) minus R^(k)`。しかもproper prefixは
phase 0に無いので、phase-zero位置で複数tokenに分けることもできない。従って
`w_k in P minus (R^(k))*`。

任意の `R_all` tokenは有限語なので、各非零phaseの訪問回数には有限の最大値があり、ある
`R^(k)` に属する。これで増大和が `R_all` に等しい。一方§3で、`R_all` はunary parityを
quotientに持つためstar-freeでないことを証明した。star-free言語は有限和で閉じるので、
有限個のstar-free部分言語 `L_i subseteq R_all` の和が正確に `R_all` になることはない。∎

従って、`R^(k)` の上限を有限回増やしてphase-zero語をすべてfactorizeするrouteは **BLOCKED**。
これは無限訪問を別の一様なheight-one式で処理する可能性を排除せず、`T_0` の下界でもない。

## 5. 二文字式の素朴な pullback も失敗する

monoid morphism

```text
h(a)=a, h(b)=b, h(c)=bb, h(d)=bbb
```

は `mu_0` を `F20-STD-01` の二文字評価へ移すので、`T_0=h^{-1}(T_std)` は正しい。しかし
starはtoken境界を保存しない。二文字の `TOKEN=a union b a* b a* b a* b` に対し、

```text
cdd maps to b^8 in TOKEN^* = b^4 b^4,
```

一方 `cdd` の非空連続部分語のphase長は `2,3,3,5,6,8` で、`b^4` のpullbackになる部分語が無い。
従って

```text
h^{-1}(TOKEN^*) != (h^{-1}(TOKEN))^*.
```

一般のnon-alphabetic inverse morphismがgeneralized star heightを保つと仮定してはならず、
この具体例でも既存 W-token式への素朴な代入は成立しない。

以上により、この自然な符号化 `h(c)=bb,h(d)=bbb` で既存の literal `TOKEN*` 式を直接pullbackする
routeはここで停止する。別の代表語を使う符号化や、同じ二文字言語の別のheight-one ASTは未検査であり、
この反例では排除されない。続行するなら、`R_all` 自体をstar-freeと誤認せず、補題2が排除した
有限bounded-visit layerとも異なる、一様でflatなheight-one構成が必要。

## 6. 機械検査と次の acceptance test

`scripts/ci/f20_gamma0_simple_return.py` は次を有限対象上で完全に検査する。

1. `R_simp` の最小DFAは15状態、transition monoidは50元で全変換がperiod 1。
2. 旧base/single/pairの14 DFAすべてと完全積到達可能性で非同値。
3. `{a,b}` 制限は既知 `TOKEN` の6状態DFAと完全に同値。
4. visited-setを外した `R_all` では `c` がperiod 2となる負control。

bounded-visit layerを増やすrouteは補題2で停止した。次の合格条件はtoken候補を増やしたという
だけでは満たさない。実際のheight-one ASTを構成し、
20状態の `T_0` DFAと完全積到達可能性で同値を証明すること、かつstarの入れ子が1以下であることが
必要である。それまでは `N-F20-GAMMA4-001` と `HeightOneForGroup F_20` はOPENのままである。
