# Run manifest: PST-class coverage of the small non-abelian groups

Claims: `PST-DIV-CRIT-01` (lemma, `PROVED`), `DICM-EMB-01` (lemma, `PROVED`),
`SMALL-NONAB-31-01` (`COMPUTED`), `FRONTIER-ORD20-01` (`COMPUTED` /
literature scope `UNREVIEWED`).

Derivation and proofs: `notes/small_group_pst_frontier.md`.
Base commit: `2ef6633` (merge of PR #26).

## Commands

```bash
python3 scripts/small_group_pst_coverage.py                    # orders <= 31
python3 scripts/small_group_pst_coverage.py --max-order 12     # Bourne's ladder only
```

No third-party packages; Python standard library only.

## Environment

- Python 3.14.6, macOS (darwin 25.5.0), single process, no network.
- Wall clock: about 3 seconds for the default run.
- Peak memory: a few tens of MB (largest constructed group has order 96).

## Hashes

| Artifact | sha256 |
|---|---|
| `scripts/small_group_pst_coverage.py` | `18677d9c0e23ec1d423292919944048db781006578cbd16116649363e1a59919` |
| stdout of the default run | `18b3bbddd0b4f314825ee8c00a2609d02f30a3bd0f30cdc9fc1466470f4a3411` |

Reproduce the output hash with

```bash
python3 scripts/small_group_pst_coverage.py | shasum -a 256
```

The output is deterministic: no randomness, no sampling, no dictionary-order
dependence (all iteration is over sorted or explicitly constructed lists).

## What the run checks

1. **Constructions.** All 45 listed groups are validated for closure,
   associativity, a unique identity, and inverses (exhaustive, `O(|G|^3)`), have
   the intended order, and are non-abelian.
2. **Completeness of the catalogue.** For each order the listed groups are
   pairwise non-isomorphic (invariants: order profile, centre, derived subgroup,
   conjugacy class sizes; on collision, an exhaustive search over generator
   images), and their number equals the classification count in
   `NONABELIAN_COUNTS` (`CITED`, standard classification of groups of small
   order). Hence the catalogue is complete for orders <= 31.
3. **Coverage.** For each group: nilpotency class via the upper central series
   (`PST-GRP-02`); then an exhaustive search over all subgroups for a split
   decomposition `G = A x| E` with `A` abelian normal and `E` elementary abelian
   2 (`PST-GRP-03`); then the exact necessary criterion of `PST-DIV-CRIT-01`;
   then, for groups that pass the criterion but do not split, a bounded search
   for an embedding into a host `A x| C_2^k` (`|H| <= 96`, rank `<= 2`, abelian
   `A` with at most 3 invariant factors).
4. **Dicyclic lemma.** The explicit map of `DICM-EMB-01`
   (`x |-> v`, `y |-> u t`) is checked to be an injective homomorphism
   `Dic_n -> (C_2 x C_2n) x| C_2` for `n = 2..12`.
5. **Literature consistency.** The audit reproduces `SMALL-12-01`
   (every non-abelian group of order < 12 covered; `A_4` outside the class;
   `Dic_3` inside via a divisor embedding). Asserted, not merely printed.

## Verdict

Exactly 6 non-abelian groups of order <= 31 lie outside the PST class:

| Order | Group | Solvable |
|---|---|---|
| 12 | `A_4` | yes (settled here: `A4-ALLLANG-01`, `COMPUTED`) |
| 20 | `F_20 = C_5 x| C_4` (faithful) | yes — **open** |
| 21 | `C_7 x| C_3` | yes — **open** |
| 24 | `SL(2,3)` | yes — **open** |
| 24 | `S_4` | yes — **open** |
| 24 | `C_2 x A_4` | yes — **open** |

## Known gaps

- "Outside the PST class" is not a star-height lower bound (research rule 1).
- The audit is against `PST-GRP-01/02/03` only. PST 1992's wreath-product /
  pseudovariety results (`docs/SURVEY.md` §3 item 6) are **not** audited at the
  level needed to decide these six groups, and no 1992-2026 literature search
  specific to `F_20`, `C_7 x| C_3`, `SL(2,3)`, `S_4`, `C_2 x A_4` was performed.
  The claim "order 20 is the smallest open case" is therefore scoped to this
  repository's audit.
- The classification counts are `CITED`, not proved here.
- Orders >= 32 are not audited (44 non-abelian groups at order 32 alone).
- Program audit and independent human re-derivation of the script are pending.
