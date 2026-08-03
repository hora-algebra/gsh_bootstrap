# Contributions and Credit Log

Record contributions continuously rather than reconstructing them after a result appears.

| Contributor | Mathematical ideas | Counterexamples/refereeing | Lean/code | Sources/exposition | Dates |
|---|---|---|---|---|---|
| Kazumi Kasaura（GitHub: [`Hziwara`](https://github.com/Hziwara)） | `A_4` の full-alphabet identity fibre から `HeightOneForGroup A4` までの形式化構成。local divisor による Schützenberger 定理の hard direction と、counter-free automaton を介した mover cut core の star-freeness。 | 明示的 star-free expression が得られなかった探索を記録した上で、counter-free route に切り替え。namespace-wide axiom auditにより `sorryAx` / `native_decide` 非依存を確認。 | `GSH/StarFree/{LocalDivisor,MarkedCode,Schutzenberger,TransitionMonoid}.lean`、`GSH/Results/A4{CutFeature,FullAlphabet,LetterCut,MoverCut}.lean`、関連する regex 基盤・tests・search scripts。[PR #53](https://github.com/hora-algebra/gsh_bootstrap/pull/53)。 | Kufleitner および Diekert–Kufleitner の local-divisor proof を Lean 用に再構成し、台帳と proof obligations を更新。AI-assisted commits の一部は GitHub 上で Claude を co-author として開示。 | 2026-07-28 完成、2026-08-04 main 統合 |

## Credit principles

- Negative results and decisive counterexamples count as research contributions.
- Formalization architecture, certificate checking, and source auditing are not clerical work.
- AI systems are tools, not authors; prompts, model/version, and generated artifacts are disclosed in a reproducibility appendix.
- Authorship is discussed before public announcement and revisited when the contribution profile changes.
