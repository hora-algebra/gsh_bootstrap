# Coverage audit for every finite group of order at most 60.
#
# QUESTION.  For which groups G of order <= 60 does an *audited* height-one
# theorem already apply?  "Applies to G" means the full solution for G:
#
#     for every finite alphabet, every monoid morphism phi : Sigma* -> G and
#     every accepting subset P subseteq G, the language phi^{-1}(P) has
#     generalized star-height at most one.
#
# The complement of the covered set is the exact list of problems that still
# need a direct attack.  Failing every criterion below is a statement about
# THIS criterion list.  It is NEVER a claim that the group has height >= 2:
# no lower-bound tool exists (research rule 1 of README.md).
#
# CRITERIA.  Each is sufficient, and each names its ledger row.
#
#   C1  G abelian                              PST-GRP-01   (CITED)
#   C2  G nilpotent of class <= 2              PST-GRP-02   (CITED)
#   C3  G = A : E split, A abelian,
#       E elementary abelian 2-group           PST-GRP-03   (CITED)
#   C4  G dicyclic (incl. generalized
#       quaternion)                            DICM-EMB-01  (PROVED here)
#   C5  G = A4                                 A4-ALLLANG-01 (PROVED here)
#   R1  G non-monolithic, and two proper
#       quotients through distinct minimal
#       normal subgroups are covered           SUBDIRECT-RED-01 (PROVED here)
#                                              + L-TRANS-001 (PROVED here)
#
# R1 is applied to a fixpoint.  Justification: distinct minimal normal
# subgroups intersect trivially (their intersection is normal and properly
# contained in each), so a non-monolithic G embeds subdirectly in G/N1 x G/N2
# with both quotients proper.  SUBDIRECT-RED-01 closes the height-one class
# under finite direct products and L-TRANS-001 under injective morphisms, so G
# is covered as soon as both quotients are.
#
# C3 is the *split* form of PST-GRP-03, which speaks of divisors and is
# therefore wider.  Using the narrower test can only move a group from covered
# to unresolved, never the reverse, so the unresolved list is an upper bound on
# the real one.  Same for C4, which tests G itself rather than its divisors.
#
# EXTERNAL DEPENDENCY.  Completeness of the enumeration is GAP's SmallGroups
# library, not something computed here.  That is a CITED input, and the ledger
# row records it as such.  What this program computes is the verdict of each
# criterion on each enumerated group.
#
# Run:  gap -q -b scripts/gap/coverage_le60.g > data/experiments/coverage_le60.tsv

MaxOrder := 60;

IsElemAb2 := function(G)
  return IsElementaryAbelian(G) and (Size(G) = 1 or PrimePGroup(G) = 2);
end;

# C3: some abelian normal A with G/A elementary abelian 2 and the extension split.
SplitAbelianByElemAb2 := function(G)
  local N;
  for N in NormalSubgroups(G) do
    if IsAbelian(N) and IsElemAb2(FactorGroup(G, N)) then
      if Size(N) = Size(G) then return true; fi;
      if ComplementClassesRepresentatives(G, N) <> [] then return true; fi;
    fi;
  od;
  return false;
end;

# C4: dicyclic of order 4n, n >= 2 -- generators x,y with
# |x| = 2n, y^2 = x^n, and x^y = x^-1.  Generalized quaternion is the case n
# a power of 2.
IsDicyclicGrp := function(G)
  local n, C, x, y, elsC;
  if Size(G) mod 4 <> 0 then return false; fi;
  n := Size(G) / 4;
  if n < 2 then return false; fi;
  for C in NormalSubgroups(G) do
    if IsCyclic(C) and Size(C) = 2 * n then
      # A cyclic subgroup of index two and a unique involution do NOT
      # characterise Dic_n when n has several prime factors.  At order 60 that
      # shortcut mislabels C5 x Dic_3 and C3 x Dic_5 as Dic_15.  Check the
      # defining inversion action and square relation instead.
      elsC := Elements(C);
      for x in elsC do
        if Order(x) = 2 * n then
          for y in Difference(Elements(G), elsC) do
            if y ^ 2 = x ^ n and x ^ y = x ^ -1 then return true; fi;
          od;
        fi;
      od;
    fi;
  od;
  return false;
end;

# The phase group of the mechanism of RESULTS.md 5.5: the cyclic quotient of a
# split extension of an abelian normal subgroup.  Reported for the unresolved
# groups because F20-FULL-OBS-01 localized the failure of that mechanism to the
# phase group being composite, and C7C3-FULL-01 passed with a prime one.  The
# largest such abelian normal subgroup is reported, so the phase group is the
# smallest cyclic quotient of that shape.
PhaseGroupOrder := function(G)
  local N, best;
  best := fail;
  for N in NormalSubgroups(G) do
    if IsAbelian(N) and IsCyclic(FactorGroup(G, N)) and Size(N) < Size(G) then
      if ComplementClassesRepresentatives(G, N) <> [] then
        if best = fail or Size(N) > Size(best) then best := N; fi;
      fi;
    fi;
  od;
  if best = fail then return [0, "-"]; fi;
  return [Size(G) / Size(best), StructureDescription(best)];
end;

base := NewDictionary([1, 1], true);
ids := [];
for n in [1 .. MaxOrder] do
  for i in [1 .. NumberSmallGroups(n)] do
    G := SmallGroup(n, i);
    why := fail;
    if IsAbelian(G) then why := "C1-abelian";
    elif IsNilpotent(G) and NilpotencyClassOfGroup(G) <= 2 then why := "C2-nilpotent2";
    elif SplitAbelianByElemAb2(G) then why := "C3-AsemiE";
    elif IsDicyclicGrp(G) then why := "C4-dicyclic";
    elif n = 12 and i = 3 then why := "C5-A4";
    fi;
    AddDictionary(base, [n, i], why);
    Add(ids, [n, i]);
  od;
od;

# R1 to a fixpoint.
changed := true;
rounds := 0;
while changed do
  changed := false;
  rounds := rounds + 1;
  for k in ids do
    if LookupDictionary(base, k) = fail then
      G := SmallGroup(k[1], k[2]);
      mins := MinimalNormalSubgroups(G);
      if Length(mins) >= 2 then
        ok := false;
        for a in [1 .. Length(mins)] do
          for b in [a + 1 .. Length(mins)] do
            if LookupDictionary(base, IdGroup(FactorGroup(G, mins[a]))) <> fail and
               LookupDictionary(base, IdGroup(FactorGroup(G, mins[b]))) <> fail then
              ok := true;
            fi;
          od;
        od;
        if ok then
          AddDictionary(base, k, "R1-subdirect");
          changed := true;
        fi;
      fi;
    fi;
  od;
od;

Print("# coverage of finite groups of order <= ", MaxOrder, "\n");
Print("# enumeration: GAP SmallGroups library (CITED, external)\n");
Print("# fixpoint rounds for R1: ", rounds, "\n");
Print("# UNRESOLVED means: not covered by C1-C5/R1. NOT a height >= 2 claim.\n");
Print("order\tid\tstructure\tverdict\tmonolithic\tphase\tabelian_normal\n");
for k in ids do
  G := SmallGroup(k[1], k[2]);
  why := LookupDictionary(base, k);
  if why = fail then why := "UNRESOLVED"; fi;
  ph := PhaseGroupOrder(G);
  Print(k[1], "\t", k[2], "\t", StructureDescription(G), "\t", why, "\t",
        Length(MinimalNormalSubgroups(G)) = 1, "\t", ph[1], "\t", ph[2], "\n");
od;
QUIT;
