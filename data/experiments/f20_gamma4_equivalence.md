# Run manifest: exact equivalence classes of the four `F_20` Gamma alphabets

Claim: `F20-GAMMA4-EQUIV-01` (`PROVED`).  The all-word structural proof is in
`notes/f20_alphabetic_reduction.md` §14.  The program below completely decides
the finite automorphism data and the relevant regular-language comparisons;
it uses no word-length cutoff.

## Acceptance test

```bash
python3 -m unittest -v tests.test_f20_gamma4_equivalence
python3 scripts/ci/f20_gamma4_equivalence.py
```

| Exact check | Universe | Result |
|---|---:|---|
| automorphism and anti-automorphism images | all `20+20` maps, all `Gamma_r` | automorphisms fix each index; anti-automorphisms relate exactly `r` and `-r` |
| direct letter maps | all `16*4^4 = 4096` maps | identity kernels agree only on the four diagonal pairs |
| letter maps followed by reversal | all `16*4^4 = 4096` maps | identity kernels agree exactly for `(r,s)=(0,0),(1,3),(2,2),(3,1)` |
| fixed left/right group contexts | all `20^2 = 400` pairs | 380 reject the empty word; the 20 inverse pairs preserve exactly the identity |

Every language comparison is decided by complete reachability in the product
of two 20-state group automata.  In each mode the run visits 1,152,000 states
and 4,608,000 transitions in total; the largest reachable product has all 400
states.  The four accepted maps are checked to be exactly the restrictions of
the relevant automorphisms or anti-automorphisms.

The shortest distinguishing-word distribution for the 4092 rejected maps is,
in both modes, lengths `2:4074, 3:2, 4:12, 5:3, 6:1`.  The unique length-six
case is pinned as a negative control on `Gamma_2`:

```text
(1,0) (2,1) (3,0) (2,1) (2,0) (2,1)
```

It rejects both using the `Gamma_2` anti-automorphism without reversal and
using the identity map with reversal.  Thus replacing full reachability by a
word-length-five test, or confusing the forward and reversal update orders,
breaks the acceptance suite.

## Evidence classification

- `PROVED`: `F20-ALPH5-01`, the `F_20` multiplication law, the direct kernel
  rigidity argument and its anti-homomorphic analogue in §14, and reversal
  preserving generalized star height.
- exact finite support, not a bounded sample: the four traversals in the table.
- no `CITED`, `COMPUTED`, `EMPIRICAL`, `CONJECTURAL`, `SPECULATIVE`,
  `REFUTED`, or `UNREVIEWED` input establishes the claim.

The result reduces four pending identity fibres to three independent ones:
`r=0,1,2`.  It does not prove height one for any of them and does not exclude
equivalences by operations outside letter relabeling, reversal, and fixed-word
left/right quotients.
