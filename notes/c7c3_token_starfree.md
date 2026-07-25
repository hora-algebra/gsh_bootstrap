# 位数 21：token language の star-free 表現はどこまで書けるか（2026-07-25）

`C7C3-IDENT-01`（`RESULTS.md` §5.16.1）で算術部分は全語に対する定理になった。残る唯一の
作業は「認証済み各 cut pattern の token language を star-free **表現**として書き下す」ことである。
本メモはその作業の現状を記録する。結論だけ先に書くと、**57 atoms のうち 12 個は書ける／
残り 45 個は書けていない**。書けていない理由は「star-free でない」ではなく（monoid は非周期的
なので star-free であることは確定している）、局所可検性という書きやすい十分条件が成り立たない
ためである。

## 0. なぜ V ひとつで済むか

`V` を「一度も cut しない語」、`Σ⁺ = Σ·Σ*` とすると、token language（post-cut 状態から
次の cut ちょうどまで）は

```
T = ¬V ∩ ¬(¬V · Σ⁺)
```

である（cut するが真の接頭辞はどれも cut しない語）。剰余言語は entry phase を q、開始 phase
を 0 として

```
{u : cut 数 ≡ h mod 7} = (h=0 なら V₀) ∪ cat(T₀, T^{(h−1) mod 7}, star(T⁷), V)
```

（`T₀`, `V₀` は開始状態が post-cut 状態と異なる q ≠ 0 の場合の先頭ぶん。q = 0 なら
`T₀ = T`, `V₀ = V`）。したがって star が現れるのは `star(T⁷)` ただ 1 箇所で、
**`V` さえ star-free に書ければ atom の高さは 1** になる。他はすべて Boolean 演算と連接である。

## 1. 21 文字は 3〜4 記号に潰れる

各 pattern について、cut 機械が区別できない文字を同一視する最粗の分割を計算すると、
21 文字はきれいに潰れる（機械確認済み、`congruence=True`）。

| pattern | 記号 |
|---|---|
| base | ε = 0, 1, 2 の 3 個 |
| `("set", S)` | S 内の nonmover, S 外の nonmover, class 1 mover, class 2 mover の 4 個 |
| `("anti", g)` | nonmover, g, g 以外の class ε_g mover, もう一方の class の mover の 4 個 |

これは length-preserving morphism `h: Σ* → Δ*` による `V = h⁻¹(V_Δ)` を意味するので、
`V_Δ` の star-free 表現は各記号をその逆像の literal の union に置き換えるだけで 21 文字に持ち上がる。

## 2. 書ける 12 個：base と set は狭義局所可検

「nonmover の極大 run を 1 記号 `N` に縮約した接尾辞」＋左端アンカーで状態が決まるか、を
最小化した collapsed DFA 上で調べた（`V` の最小 DFA は 4〜5 状態）。

| pattern | 局所幅 |
|---|---|
| base | **3** |
| `("set", S_k)`（3 個の bit set） | **4** |
| `("anti", g)`（14 個の mover） | 幅 8 まで**不成立** |

base と set が通る理由は明快である。これらでは mover が phase q に到達すると必ず cut する
ので、走行は最初の mover 以降 **phase q を二度と踏まない**。phase q 以外の phase r からは
`r + ε ≠ q` を満たす mover class が一意に決まるので、class 列は最初の 1 個を除いて強制され、
phase は直前の mover の class だけで決まる。唯一の曖昧さ「その mover が最初かどうか」は
左端アンカーで解消される。したがって `V` は禁止 factor の有限集合＋許容接頭辞で定義でき、
`neg(cat(TOP, x, NSTAR, y, TOP))` 型の star-free 表現になる。

これで **base cut 3 個と nonmover set cut 9 個、計 12 atoms** は書ける。

## 3. 書けない 45 個：`anti` の障害

`("anti", g)` では g が phase q へ「跳べる」（arrival が q で letter が g、直前が g でない
ときだけ cut を飛ばす）。phase q からは両方の mover class が許されるので、jump のたびに
「class 列が自由に選び直される」区間の切れ目が生じる。

障害を正確に書くと次のようになる。区間内の j 番目の mover の後の phase は

- j = 1（jump 直後）なら class そのもの、
- j ≥ 2 なら class の反転

で決まる。よって「ある g が jump か」を判定するには直前の mover が区間の先頭かどうかを知る
必要があり、それは**2 つ前の mover が jump か**に帰着する。この連鎖は 2 movers ずつ遡る。
連鎖が切れるのは間に nonmover が入ったときだけなので、**mover だけからなる語では語頭まで
遡る**。ゆえに幅をいくら広げても状態は接尾辞から決まらない。

実際に見つかった曖昧な signature（q=0, s=0, 幅 4）：

```
[g, N, g, M2]  ->  状態 2 と 3 の両方が到達可能
```

念のため：これは `V` が star-free でないことを意味しない。§5.16.1 section 1 で token monoid の
完全列挙により非周期性は確認済みで、Schützenberger により star-free 表現は**存在する**。
狭義局所可検性という「書きやすい十分条件」が成り立たないだけである。

## 4. 潰した袋小路（再訪しないための記録）

- **phase を素朴に数える**：`{u : Σε ≡ r}` は star-free でない（syntactic monoid が `Z/3`）。
  `V = ¬((P_r ∩ NoSkipEnd)·Σ*)` と書くと `P_r` の高さ 1 が入り、atom の高さが 2 になる。
- **区間分解**：`V(anti,q,q) = Vbase ∪ (E·g·V(anti,q,q))` すなわち `(E g)* Vbase` は star を含む。
  star-free 言語は star で閉じないので、この形のままでは使えない。
- **mover 集合への bit 分解**：`("antiset", S)` は非周期的ですらない（period 3、反例は同じ ε の
  2 つの mover の交替、`RESULTS.md` §5.16.1）。
- **mover を数える phase-blind な cut**：`("set", movers)` 型なら局所的だが、
  `Σ_g x_g[q−ε_g]` しか得られず文字ごとに分離できない。
- **mover を phase 込みで数えるのに phase q に入らない pattern**：原理的に不可能。
  ある mover を数えるにはその mover の arrival で skip する必要があり、skip は phase q に留まる
  ことを意味する。

## 5. 次の一手

1. §2 の 12 atoms について実際に表現を構成し、`compile_dfa` と
   `equivalence_counterexample`（`scripts/weis_l2_full_gsh1.py`）で token DFA と厳密に
   一致することを確認する。21 文字アルファベットでの pipeline（`T = ¬V ∩ ¬(¬V·Σ⁺)`、
   atom 公式、高さ計算）をここで検証しておく。
2. `anti` については狭義局所可検性を諦め、次のどれかを取る。
   - (a) 非周期 DFA から star-free 表現を作る一般アルゴリズム（Schützenberger）を、
     5 状態・4 記号という小ささを前提に実装する。生成物は厳密な DFA 同値判定で検証できるので、
     正しさのリスクは「作れないこと」だけになる。
   - (b) §6 の亀裂（同 class pair は局所的）を使う再構成を探す。
3. `N-C7C3-001` は OPEN のまま。

## 6. 亀裂：pair pattern の一部は局所的（2026-07-25 追加）

§5 では「元の scheme の `("pair", h, g)` にも同じ障害が出るはず」と予想したが、実測すると
**一部は通る**。`ε_g = 1` の `g` を固定して 20 個の `h` すべてを調べた結果：

| `h` の種類 | 個数 | 局所幅 |
|---|---|---|
| `ε_h = ε_g` の mover（`h ≠ g`） | 6 | **6** |
| nonmover（`ε_h = 0`） | 7 | 不成立 |
| `ε_h ≠ ε_g` の mover | 7 | 不成立 |

理屈は合う。jump（arrival が q で letter が `g`）の直前を**同じ class の mover** に限ると、
2 手前の phase が一意に定まるので §3 の再帰がそこで切れる。直前が nonmover や反対 class だと
phase が絞れず再帰が続く。

ただしこれだけでは足りない。必要なのは

```
x_p = n_{gg} + Σ_{h ∈ M_ε∖{g}} + Σ_{h ∈ M_other} + Σ_{h nonmover} + [先頭]
```

の全項であり、局所的に書けるのは 2 項目だけである（`n_{gg}` すなわち pure power pattern は
そもそも非周期的ですらない）。

### 6.1 亀裂は塞がっている（BLOCKED、2026-07-25）

「局所的に書ける observable だけで `β` が決まるか」を直接調べた。使った observable は
**局所可検性が確認できたものすべて**である：base cut・nonmover set cut・同 class pair cut を
前後両方向で計 528 個、＋各文字の出現数 mod 7 を 21 個。長さ ≤ 4 の phase 0 の語 68069 個を
網羅したところ、**衝突が存在する**。

```
w₁ = g(e=1,b=0) g(e=2,b=0) g(e=2,b=0) g(e=1,b=1)   β = 4
w₂ = g(e=1,b=1) g(e=2,b=0) g(e=2,b=0) g(e=1,b=0)   β = 1
```

この 2 語は 549 個の observable すべてで一致し、`β` だけが異なる。互いに逆語であって
`β` を担う 2 文字が入れ替わっているだけ、という形をしている。

したがって **局所ルート (b) は反証された**。「局所可検な cut だけを使う再構成」は
存在しない。`Σ_p 2^p x_p` を決めるには、`anti` か非局所 pair か、いずれにせよ
狭義局所可検でない token language を通る必要がある。

残る道は (a) のみ：非周期 DFA から star-free 表現を作る一般的な構成を実装する。対象は
5 状態・4 記号と小さく、生成物は厳密な DFA 同値判定で検証できるので、正しさのリスクではなく
**作れるかどうか**だけが問題になる。
