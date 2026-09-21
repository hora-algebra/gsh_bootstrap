# Which rows of the residual have a commutative subgroup of index two?
#
# `coverage_le60.g` decides C3 in its *split* form: it asks for a commutative
# normal `A` with `G/A` elementary abelian 2 AND a complement. But `PST-GRP-03`
# speaks of DIVISORS, and the non-split index-two case reduces to the split one
# by a classical embedding: if `A <= G` is commutative of index two then
# Krasner--Kaloujnine gives `G` into `A wr C2 = (A x A) : C2`, which is
# commutative-by-elementary-abelian-2 and split. So a group with a commutative
# subgroup of index two lies in the PST-GRP-03 class whether or not its own
# extension splits, and the split test is stronger than the theorem needs.
#
# This program measures the gap: it reports every row of the committed residual
# table that has a commutative subgroup of index two. Those rows are settled by
# `PST-GRP-03` and should not be in the residual.
#
# Read-only with respect to the repository: it prints, and writes nothing.
#
#   gap -q -b < scripts/gap/index_two_krasner_kaloujnine.g

# An index-two subgroup is automatically normal, so scanning the normal
# subgroups loses nothing and is much cheaper than all subgroups.
AbelianIndexTwo := function(G)
  local N;
  for N in NormalSubgroups(G) do
    if Index(G, N) = 2 and IsAbelian(N) then
      return N;
    fi;
  od;
  return fail;
end;

# The residual of `COVER-LE60-RESIDUAL-01`, transcribed from
# data/experiments/coverage_le60.tsv (verdict UNRESOLVED, order <= 60).
RESIDUAL := [
  [20,3],[21,1],[24,3],[24,12],[32,6],[32,7],[32,8],[32,15],[32,44],
  [36,9],[39,1],[40,3],[40,12],[42,1],[42,2],[48,3],[48,28],[48,29],
  [48,30],[48,32],[48,33],[48,48],[52,3],[54,5],[54,6],[54,8],[55,1],
  [56,11],[57,1],[60,5],[60,6],[60,7] ];

hits := 0;
Print("residual rows examined: ", Length(RESIDUAL), "\n");
for r in RESIDUAL do
  G := SmallGroup(r[1], r[2]);
  N := AbelianIndexTwo(G);
  if N <> fail then
    hits := hits + 1;
    Print("  SmallGroup(", r[1], ", ", r[2], ") = ",
          StructureDescription(G), "\n");
    Print("    commutative subgroup of index two: ", StructureDescription(N),
          ", order ", Size(N), "\n");
    Print("    nilpotency class of G: ", NilpotencyClassOfGroup(G),
          "   (PST-GRP-02 needs at most 2)\n");
    Print("    split: ", ComplementClassesRepresentatives(G, N) <> [],
          "   (C3 as implemented needs true)\n");
  fi;
od;
Print("rows settled by PST-GRP-03 through Krasner--Kaloujnine: ", hits, "\n");

# Positive control: the criterion must fire on a group everyone agrees is in
# the class, and must not fire on one that is not.
control := SmallGroup(8, 3);            # D_8, cyclic subgroup of index two
Print("control D_8 (expect a hit): ",
      AbelianIndexTwo(control) <> fail, "\n");
control := SmallGroup(12, 3);           # A_4 has no subgroup of order 6 at all
Print("control A_4 (expect no hit): ",
      AbelianIndexTwo(control) = fail, "\n");
QUIT;
