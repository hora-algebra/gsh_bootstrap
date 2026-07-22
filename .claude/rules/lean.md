---
paths:
  - "**/*.lean"
---

- Run `lake env lean <changed-file>` before the full build when possible.
- Every `sorry` must be listed in `PROOF_OBLIGATIONS.md` with an ID.
- Do not introduce `axiom`, `unsafe`, or `noncomputable` merely to silence an error; explain why each is mathematically appropriate.
- Preserve theorem statements during API repair.
