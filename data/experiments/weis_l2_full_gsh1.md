# Run manifest: full L2, generalized and restricted star height

Claims: `WEIS-L2-GSH-01` (gsh(L2) = 1), `WEIS-L2-RSH-01` (rsh(L2) = 2),
`UNIV-SUBGRP-01` (lemma, `PROVED` in `notes/weis_l2_full_height_one.md` §6),
`A4-STD-02` (independent complete proof for A4-STD-01).

- date: 2026-07-25
- base commit: f122ccc
- environment: Python 3 stdlib only (no third-party packages), macOS
  (darwin 25.5.0), CPython 3; Lean untouched by this work

## Commands

    python3 scripts/research/weis_l2_full_gsh1.py            # gsh(L2) = 1, seconds
    python3 scripts/research/weis_l2_restricted_height.py    # rsh(L2) = 2, seconds
    python3 scripts/research/a4_std_dfa_equivalence.py       # A4-STD-01 complete proof

    # regenerate the repository-standard certificate and check it with the
    # independent checker (also run by ./scripts/check.sh on every invocation)
    python3 scripts/research/weis_l2_full_gsh1.py \
        --certificate data/certificates/height1_weis_l2_full.json
    python3 scripts/ci/check_certificate.py \
        data/certificates/height1_weis_l2_full.json
    # => PASS: equivalent; height=1 <= 1; minimal states expression=6, target=6

Every script exits 0 iff all of its assertions and checks pass; each one
fails loudly (`[FAIL]`, exit 1) on the first mismatch.

## Hashes

script sha256:

- `scripts/research/weis_l2_full_gsh1.py`
  dd095ec32e018ff47f2de2c1486223fe50e1071edc9042e71982dbad5684f7e8
- `scripts/research/weis_l2_restricted_height.py`
  cf9f279993f024d26b055b03271d4b13d25f6f431372e4f6f8b73ec449c935a1
- `scripts/research/a4_std_dfa_equivalence.py`
  f7c7d1242802e22bd07a7dab66984593cc828fb446450eeca240bfe1c1937f88

generated artifact sha256:

- `data/certificates/height1_weis_l2_full.json`
  64e7312dd0803c42b0c73e2b54891e95d6775cfcd72afbd85aa1755f3c00886b

normalized run output sha256 (timings `([0-9]*s)` stripped; the
`--certificate` line is absent from the plain runs recorded here):

- gsh run:
  0c4d53bc1c4595e0cdb480e6af1568aadb72a6a81482d1a020d1193c226961b7
- rsh run:
  51085f543454ac7ff191a783e6e7fc76f94485e4667ef16e20bb731dae90b728
- A4 run:
  8138a12fda5d34a0960f81db62fb8b14df4a89259269ad8db80af7f4e55b6d08

Reproduce a hash with:

    python3 scripts/research/weis_l2_full_gsh1.py | sed 's/([0-9]*s)//g' | shasum -a 256

## Resource bound

All three runs finish in a few seconds on a single CPU. Largest exact
searches: 2¹² = 4096 labelled-edge subsets (rsh), product automata of size
≤ 36 (gsh) and ≤ 144 (A4), regex-vs-DFA comparisons over all 8191 words of
length ≤ 12. No sampling and no randomness anywhere in these three scripts,
so the outputs are deterministic.

## Verdict summary

- **gsh(L2) = 1.** Ground truth derived from the printed regex by exact
  compilation (6-state walk automaton of a = (01)(34), b = (0235)); the
  height-1 expression built from the four-diagonal action is proved
  language-equal to it by product reachability. Lower bound from
  Schützenberger (syntactic monoid is a nontrivial group, order 48 ≅ C₂×S₄).
- **rsh(L2) = 2.** Of the 4096 subautomata of the universal automaton
  (= minimal DFA, by `UNIV-SUBGRP-01`), exactly one recognises L2 — the
  full automaton — with loop complexity 2. Cited: Eggan Thm. 7.5 and
  Lombardy–Sakarovitch Thm. 7.10 (TUA 2008), verified verbatim.
- **A4-STD-01 evidence strengthened** from "length ≤ 16 plus 30k random
  words" to a complete finite proof for the two-generator case.
  A4-FULL-01 (all twelve letters) is untouched.

## Known gaps

- Program audit by a second party is not done (`N-L2-AUDIT-001`).
- The four evaluation paths (exact compiler, recursive matcher, Python
  `re` on the printed regex, and `tools/regex_cert.py` on the emitted
  certificate) share the AST but not the evaluation logic; a bug common
  to all four would have to be in the AST construction, which is what the
  ground-truth comparison in step 6 is designed to catch.
- No L2-specific prior-art search beyond Weis 2011, PST 1992, Pin's
  star-height pages and the arXiv neighbourhood; required before any
  external write-up.
