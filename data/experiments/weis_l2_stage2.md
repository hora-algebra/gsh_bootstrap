# Run manifest: Weis-L2 family, stage 2 (WEIS-L2-M2-01, THOMAS-D2-02, WEIS-L2-M3-01)

- date: 2026-07-22
- commit: f59abdd
- environment: Python 3 stdlib only, Linux (Claude Code remote session; Lean untouched)

## Commands

    python3 scripts/weis_l2_family.py          # stage-2 theorem, ~1 min
    python3 scripts/weis_l2_family.py --m3     # stage-3 frontier record

## Hashes

- scripts/weis_l2_family.py sha256: 3608481c2b6dee6ca98853b56a235da4517d12af241fece488f70fd66506952b
- stage-2 run normalized output sha256: 32d5b12b04104285f5c52f71e24308512b4aa4a0bb08b34bc6078a8a4f0e88ae
- stage-3 run normalized output sha256: cb8b412b7920cb9da46487c8c50aea0c7ff0549141bb003443a1d2cf2bb429a9

## Resource bound

Both runs complete in under 10 minutes on a single CPU; the largest exact
product search visits < 100k states (stage 2) and < 20M cap (stage 3,
never reached).  All verdicts are deterministic (fixed RNG seeds for the
sampling layers; the proofs themselves are exhaustive BFS, no sampling).

## Verdict summary

- stage 2: all 8 pair atoms (mod 2, mod 4) + odd-run count mod 4 PROVEN
  functions of certified height-1 features; identity exhaustive to len 16;
  270k cell-table comparisons and independent `re` evaluation agree.
- stage 3: T1 mod 2 PROVEN; all other stage-3 atoms exactly NOT functions
  of the current certified feature family (recorded obstruction).
