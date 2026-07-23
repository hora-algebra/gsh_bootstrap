# Weis 2011 一次資料監査（M-WEIS-001）

作業日: 2026-07-23。従来 `BLOCKED`（一次資料到達不能）だった監査を、本日
の環境から実施した。監査者は AI エージェント（取得 URL・引用箇所を全て
記録）。独立な人間による突き合わせは未了。

## 1. 取得経路と書誌

- 直接アクセス: scholarworks.umass.edu は 403。
- 取得成功: Internet Archive Wayback Machine 経由で**学位論文全文 PDF
  （143 ページ）**を取得。
  - landing: `web.archive.org/web/20240414014021/https://scholarworks.umass.edu/open_access_dissertations/407/`
  - PDF: `web.archive.org/web/20240413154848/https://scholarworks.umass.edu/cgi/viewcontent.cgi?article=1419&context=open_access_dissertations`
- 2009 年セミナー要旨: `people.cs.umass.edu/~barrington/thysemS12/3nov09.html`
  を直接取得（verbatim 確保）。
- 書誌: Philipp P. Weis, *Expressiveness and Succinctness of First-Order
  Logic on Finite Words*, PhD thesis, UMass Amherst, 2011.
  Open Access Dissertations 407, DOI `10.7275/2177022`。指導 Neil Immerman、
  委員に D. M. Barrington、**Howard Straubing**。generalized star-height は
  第 4 章（p.83–125）。

## 2. 主要な発見

### 2.1 候補言語の定義（§4.4, p.114–116）

論文の候補は L1, L2, L3 の 3 つ＋§4.6 の S3 語問題言語。すべて {a,b} 上
（§4.6 のみ {a,b,c}）。

- L1 := L((ab\*a ∪ b(ab\*a)\*b)\*)（p.114）— 高さ 1 の式を明示構成済み。
- **L2 := L((ab\*a ∪ ba\*b(ab\*a)\*ba\*b)\*)**（p.115）— L1 のパターン b を
  ba\*b に置換したもの。
- L3 := L((ab\*a ∪ b(ab\*ab\*a)\*b)\*)（p.116）— 法 2 と 3 が交替。

### 2.2 帰属の修正: L2 の提案者は PST

p.115: "has been proposed in [30]"（[30] = Pin–Straubing–Thérien 1992）。
**L2 は Weis の発案ではなく PST 1992 の提案**。台帳 `WEIS-L2-AUDIT-01` の
旧文面はこの帰属を欠いていた。

### 2.3 Weis はフル版 L2 の高さ 1 を証明していない

p.115: "we do not know whether it has generalized star-height 2"。
示されたのは**制限版**（b と b の間の a が 4 以上の部分集合）の高さ 1 のみ。
L3 もフル版は未解決。アブストラクト（p.vi–vii）も "While some of them
still stand as promising candidates" と明言。

### 2.4 2009 年講演要旨との不整合

要旨（verbatim）: "present a series of four candidate languages, and show
that all of these languages have generalized star height one"。
**2011 年の論文本体はフル版 L2・L3 を未解決のまま残しており、この要旨を
「Weis がフル版 L2 の高さ 1 を証明した」と読むのは誤り**。講演の 4 候補は
L1・制限版 L2・制限版 L3・S3 語問題だった可能性が高い（**推測**。講演
スライドは未入手）。台帳 `WEIS-TALK-01` の証拠水準を「要旨の記述としては
正確、論文と不整合」に更新する。

### 2.5 位数 48 の群は正しい（旧「再現不能」記録の訂正）

p.115: "The syntactic monoid of this language is a group with 48 elements
that is not nilpotent"。印字どおりの正規表現から最小 DFA（6 状態、論文
Fig 4.3 と一致）を構成すると、構文モノイドは**ちょうど位数 48 の非冪零群
≅ C₂×S₄**（下降中心列 48→12 で停留、可解、中心位数 2、位数分布
{1:1, 2:19, 3:8, 4:12, 6:8}）。M(L1) は位数 8・冪零類 2（D₄）、M(L3) は
位数 120（S₅ 型）で論文の記述と一致。**従来の「位数 48 は走査で再現され
なかった」（旧 `WEIS-L2-AUDIT-01`、notes/weis_l2_stage2_height1.md §6）は、
二次情報から再構成した族が実物の L2 と異なっていたことによる**。
再現スクリプト: `scripts/weis_l2_actual.py`（本監査に伴い追加）。

### 2.6 論文内部の不整合（監査上の注意）

p.118 の "M(L1) and M(L2) are isomorphic" は位数 8 ≠ 48 と矛盾。p.119 の
"a5 acts as the identity in M(L2)" も計算（a² = id、p.115 と整合）と矛盾。
**p.118–119 の同型構成の記述は別の自動機に対する残骸か誤りとみられ、
引用に使わない。**

### 2.7 その他

- "cumulative" という語は論文に不出現。ただし §4.2（Thomas の segment
  counting）と §4.5（語全体での部分語出現数 = 累積、Proposition 4.5.3 で
  高さ 1）の実質的区別はある。
- A4・A5・位数 12 への言及は皆無。群語問題は S3 のみ（§4.6）。
  **本リポジトリの位数 ≤ 12 の結果（RESULTS §3）とは対象が重ならない。**

## 3. 帰結（台帳・候補リストへの反映）

1. `M-WEIS-001`: BLOCKED を解除（一次資料取得済み）。stage-2 族定理との
   比較も完了（2026-07-23）: **フル版 L2 は認証済み特徴族（拡張込み）の
   関数でない**（厳密判定、最短反例 `bababbb` ∉ L2 / `bbababb` ∈ L2、
   `scripts/weis_l2_actual.py`、台帳 `WEIS-L2-NOTFN-01`）。残作業は
   人間による監査ノートの突き合わせのみ（status REVIEW）。
2. `WEIS-L2-AUDIT-01`: 帰属（PST 提案）と位数 48 の確認を反映して更新。
3. `WEIS-TALK-01`: 論文との不整合を注記。
4. 新規 `WEIS-L2-OPEN-01`: 「フル版 L2 の一般化スター高さは Weis 2011 で
   未解決のまま」を CITED で登録。フル版 L2 は **PST が提案し Weis が
   未解決のまま残した、文献に裏付けのある候補言語**である。
