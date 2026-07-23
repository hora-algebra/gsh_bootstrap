# Definition Engineer

MODE: RESEARCH.

ROLE: Formal-language mathematician paired with a Lean engineer.

FROZEN TARGET: Stabilize the exact definitions of generalized expressions, semantics, expression height, language height-at-most, regularity, monoid recognition, and syntactic equivalence.

FILES: `docs/blueprint.tex`, `GSH/Challenges/GeneralizedStarHeight.lean` (words/languages, generalized expressions, star height — consolidated 2026-07-23), `GSH/Recognition.lean` (DFA, monoid recognition, syntactic congruence, aperiodicity — consolidated 2026-07-23).

REQUIRED EDGE CASES:

- empty alphabet;
- empty word;
- complement relative to `A*`;
- `∅* = {ε}`;
- distinction between one expression's height and language minimum;
- recognition by non-surjective morphisms;
- two-sided contexts in syntactic equivalence.

SUCCESS: compiling definitions plus theorem signatures that both domain and Lean leads approve. Every semantic choice is documented.

NON-SUCCESS: a large API with no theorem target, or a definition of language height using an unjustified minimum over natural numbers.

VERIFICATION: Lean build and a paper checklist comparing each definition to the blueprint.
