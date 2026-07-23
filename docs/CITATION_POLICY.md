# Citation and Source Policy

## Source hierarchy

1. Original paper, thesis, or official library documentation.
2. Author-hosted/open repository copy with stable metadata.
3. Reliable survey, only for context or status.
4. Secondary web pages, only as pointers.
5. Model-generated summaries, never as evidence.

## Required metadata

For every theorem used in a proof, record as many of the following as exist:

- authors and title;
- venue/year;
- theorem/lemma/section/page;
- DOI or stable repository identifier;
- exact hypotheses in source notation;
- translation into repository notation;
- whether the source treats generalized or restricted star-height.

## Status claims

“Open as of date X” requires a dated search log and multiple recent sources. It is not a theorem. The claim must be softened if the search is incomplete.

## Quotations and PDFs

Do not commit copyrighted papers to the repository unless redistribution is licensed. Commit bibliographic metadata, stable links, theorem extraction notes, and short quotations within applicable limits.

## AI-generated references

Before a generated citation enters `gsh_additions.bib`:

1. resolve the DOI or stable record;
2. verify authors, title, year, pages, and venue;
3. open the source and confirm it supports the claim;
4. mark any uncertainty in `CLAIMS_LEDGER.md`.

## Citation audit command

`./scripts/lint_claims.py` checks that every `CITED` row has an evidence field and that forbidden placeholder phrases are absent. It does not verify the source's content; a human source auditor must do that.
