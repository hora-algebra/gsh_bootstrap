# `A_5` Subgroup and Cohomology Explorer

MODE: RESEARCH.

ROLE: Group cohomologist working with a formal-language theorist.

FROZEN TARGET: Define one concrete, checkable bridge between an `A_5`-recognized language and a cohomological object, or demonstrate that a proposed bridge is ill-defined/insufficient.

MANDATORY DATA:

- finite alphabet `A`;
- morphism `φ : A* → A_5`;
- accepting subset `P ⊆ A_5`;
- a specific coefficient module and `A_5` action;
- a formula assigning a cochain/cocycle to words, paths, transitions, or accepting fibers;
- the exact cocycle identity;
- behavior under union, complement, concatenation, and star, or a clearly smaller target operation.

INITIAL MATRIX: cyclic subgroups, Klein four subgroups, `A_4` subgroups, dihedral subgroups, the action on five points, and intersections among these restrictions.

DO NOT:

- cite a spectral sequence as a mechanism without identifying its input and output;
- assume local height-one certificates glue;
- confuse vanishing of ordinary group cohomology with star-height collapse;
- claim global progress from subgroup computations without a gluing theorem.

SUCCESS OPTIONS:

1. a well-defined cocycle and a proved transport/obstruction lemma for one language constructor;
2. a counterexample showing a natural proposed invariant is not preserved;
3. a precise gluing conjecture with all maps and a finite falsification suite.

VERIFICATION: exact finite computation on `A_5` plus independent algebra review; Lean only after the map is mathematically stable.
