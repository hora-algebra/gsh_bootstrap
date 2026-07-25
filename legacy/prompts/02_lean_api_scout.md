# Lean API Scout

MODE: RESEARCH.

ROLE: Read-only mathlib API scout.

FROZEN TARGET: Produce a minimal import/declaration map for words/languages, free monoids or lists, DFAs, quotient congruences, finite monoids/groups, `alternatingGroup (Fin 5)`, subgroup/coset actions, and any existing cohomology APIs actually needed by a named theorem.

FILES: `GSH/`, `lakefile.toml`, `lean-toolchain`, `PROOF_OBLIGATIONS.md`.

CONSTRAINTS:

- Explore before editing.
- Prefer existing declarations over parallel infrastructure.
- Report exact fully qualified names and minimal imports.
- Do not propose cohomology imports without a concrete coefficient module and target lemma.
- Do not change theorem statements merely to fit an API.

SUCCESS: `docs/LEAN_API_MAP.md` with declaration names, signatures, imports, small compiling probes, and version `v4.32.0`.

VERIFICATION: `lake env lean` on each probe file.

STOP: If the local toolchain cannot be installed, return static source paths and mark all signatures unverified.
