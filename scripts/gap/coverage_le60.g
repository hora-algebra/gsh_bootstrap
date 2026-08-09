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
#   C6  A <= G abelian of index two,
#       split or not                           PST-GRP-03   (CITED)
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
# C6 closes one measured gap between C3 and the theorem it implements: for
# index two the split hypothesis of C3 is not needed.  If A <= G is abelian of
# index two, the Krasner--Kaloujnine embedding sends G into
# A wr C2 = (A x A) : C2, which is split abelian-by-elementary-abelian-2, so G
# *divides* a group of the C3 class and PST-GRP-03 applies whether or not G
# itself splits over A.  (Index two forces normality, so scanning the normal
# subgroups loses nothing.)  C6 is applied as a separate sweep AFTER C1-C5 and
# the first R1 fixpoint, so every group those criteria already covered keeps
# its verdict and the diff against the previous table is exactly the rows the
# wider criterion newly settles.  The same embedding is formalized in Lean in
# GSH/Groups/IndexTwoEmbedding.lean (merged via PR #56).
#
# EXTERNAL DEPENDENCY.  Completeness of the enumeration is GAP's SmallGroups
# library, not something computed here.  That is a CITED input, and the ledger
# row records it as such.  What this program computes is the verdict of each
# criterion on each enumerated group.
#
# Run:  gap -q -b scripts/gap/coverage_le60.g > data/experiments/coverage_le60.tsv
# This also writes the multiplication-table witness file named below.  GAP is
# used only to *produce* the finite objects and candidate witnesses; the Python
# checker re-verifies every group axiom and every sufficient criterion without
# calling GAP.

MaxOrder := 60;
WitnessFile := "data/experiments/coverage_le60_witnesses.jsonl";

OrderedElements := function(G)
  return Concatenation([One(G)], Difference(Elements(G), [One(G)]));
end;

SubgroupIndices := function(G, H)
  local els;
  els := OrderedElements(G);
  return SortedList(List(Elements(H), z -> Position(els, z) - 1));
end;

IsElemAb2 := function(G)
  return IsElementaryAbelian(G) and (Size(G) = 1 or PrimePGroup(G) = 2);
end;

# C3: return a witness [A,E] for G = A : E, or fail.
SplitAbelianByElemAb2Witness := function(G)
  local N, complements;
  for N in NormalSubgroups(G) do
    if Size(N) < Size(G) and IsAbelian(N) and IsElemAb2(FactorGroup(G, N)) then
      complements := ComplementClassesRepresentatives(G, N);
      if complements <> [] then return [N, complements[1]]; fi;
    fi;
  od;
  return fail;
end;

# C6: an abelian subgroup of index two, split or not.  An index-two subgroup
# is automatically normal, so scanning NormalSubgroups is complete.
AbelianIndexTwoWitness := function(G)
  local N;
  for N in NormalSubgroups(G) do
    if 2 * Size(N) = Size(G) and IsAbelian(N) then
      return N;
    fi;
  od;
  return fail;
end;

# C4: dicyclic of order 4n, n >= 2 -- generators x,y with
# |x| = 2n, y^2 = x^n, and x^y = x^-1.  Generalized quaternion is the case n
# a power of 2.
DicyclicWitness := function(G)
  local n, C, x, y, elsC;
  if Size(G) mod 4 <> 0 then return fail; fi;
  n := Size(G) / 4;
  if n < 2 then return fail; fi;
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
            if y ^ 2 = x ^ n and x ^ y = x ^ -1 then return [x, y]; fi;
          od;
        fi;
      od;
    fi;
  od;
  return fail;
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
witnesses := NewDictionary([1, 1], true);
ids := [];
for n in [1 .. MaxOrder] do
  for i in [1 .. NumberSmallGroups(n)] do
    G := SmallGroup(n, i);
    why := fail;
    proof := fail;
    if IsAbelian(G) then
      why := "C1-abelian";
      proof := [];
    elif IsNilpotent(G) and NilpotencyClassOfGroup(G) <= 2 then
      why := "C2-nilpotent2";
      proof := [];
    else
      proof := SplitAbelianByElemAb2Witness(G);
      if proof <> fail then
        why := "C3-AsemiE";
      else
        proof := DicyclicWitness(G);
        if proof <> fail then
          why := "C4-dicyclic";
        elif n = 12 and i = 3 then
          why := "C5-A4";
          proof := [];
        fi;
      fi;
    fi;
    AddDictionary(base, [n, i], why);
    if why <> fail then
      elsForWitness := OrderedElements(G);
      if why = "C3-AsemiE" then
        proof := [SubgroupIndices(G, proof[1]), SubgroupIndices(G, proof[2])];
      elif why = "C4-dicyclic" then
        proof := [Position(elsForWitness, proof[1]) - 1,
                  Position(elsForWitness, proof[2]) - 1];
      fi;
      AddDictionary(witnesses, [n, i], proof);
    fi;
    Add(ids, [n, i]);
  od;
od;

# R1 to a fixpoint.  A function because it runs twice: once over the C1-C5
# verdicts, and once more after the C6 sweep below, in case a newly covered
# group enables a further subdirect reduction.  It only mutates the two
# dictionaries; the group-key list is read-only.
ApplyR1Fixpoint := function()
  local changed, rounds, k, G, mins, ok, chosen, a, b;
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
          chosen := fail;
          for a in [1 .. Length(mins)] do
            for b in [a + 1 .. Length(mins)] do
              if LookupDictionary(base, IdGroup(FactorGroup(G, mins[a]))) <> fail and
                 LookupDictionary(base, IdGroup(FactorGroup(G, mins[b]))) <> fail then
                ok := true;
                chosen := [mins[a], mins[b]];
                break;
              fi;
            od;
            if ok then break; fi;
          od;
          if ok then
            chosen := [SubgroupIndices(G, chosen[1]), SubgroupIndices(G, chosen[2])];
            AddDictionary(base, k, "R1-subdirect");
            AddDictionary(witnesses, k, chosen);
            changed := true;
          fi;
        fi;
      fi;
    od;
  od;
  return rounds;
end;

rounds := ApplyR1Fixpoint();

# C6 sweep over the rows C1-C5/R1 left unresolved.  Kept out of the main
# criterion chain on purpose: dicyclic groups and several R1-covered groups
# also have abelian index-two subgroups, and running C6 first would relabel
# rows that are already covered.  Applied last, the diff against the previous
# table is exactly the rows the wider criterion newly settles.
for k in ids do
  if LookupDictionary(base, k) = fail then
    G := SmallGroup(k[1], k[2]);
    proof := AbelianIndexTwoWitness(G);
    if proof <> fail then
      AddDictionary(base, k, "C6-KKindex2");
      AddDictionary(witnesses, k, SubgroupIndices(G, proof));
    fi;
  fi;
od;

rounds := rounds + ApplyR1Fixpoint();

# ---------------------------------------------------------------------------
# Machine-readable positive witnesses.  Element 0 is always the identity.
# Multiplication tables are flattened row-major.  R1 carries two explicit
# surjective homomorphisms into already-covered smaller group tables; the
# Python checker verifies the maps and the trivial intersection of their
# kernels, so it does not trust quotient names or IdGroup labels.
# ---------------------------------------------------------------------------

PrintJsonIntList := function(out, values)
  local j;
  PrintTo(out, "[");
  for j in [1 .. Length(values)] do
    if j > 1 then PrintTo(out, ","); fi;
    PrintTo(out, values[j]);
  od;
  PrintTo(out, "]");
end;

PrintJsonIntLists := function(out, rows)
  local j;
  PrintTo(out, "[");
  for j in [1 .. Length(rows)] do
    if j > 1 then PrintTo(out, ","); fi;
    PrintJsonIntList(out, rows[j]);
  od;
  PrintTo(out, "]");
end;

PrintQuotientWitness := function(out, G, els, normalIndices)
  local N, natural, Q, qid, target, iso, targetEls, mapping;
  N := Subgroup(G, List(normalIndices, j -> els[j + 1]));
  natural := NaturalHomomorphismByNormalSubgroup(G, N);
  Q := Image(natural);
  qid := IdGroup(Q);
  target := SmallGroup(qid[1], qid[2]);
  if LookupDictionary(base, qid) = fail then
    Error("R1 target is not covered: ", qid);
  fi;
  if Size(target) >= Size(G) then
    Error("R1 target is not proper: ", qid);
  fi;
  iso := IsomorphismGroups(Q, target);
  if iso = fail then Error("cannot identify quotient target: ", qid); fi;
  targetEls := OrderedElements(target);
  mapping := List(els, g -> Position(targetEls, Image(iso, Image(natural, g))) - 1);
  PrintTo(out, "{\"target\":[", qid[1], ",", qid[2], "],\"map\":");
  PrintJsonIntList(out, mapping);
  PrintTo(out, "}");
end;

PrintPositiveWitness := function(out, k)
  local G, why, proof, els, flat, x, y, normal, complement, iso, images;
  G := SmallGroup(k[1], k[2]);
  why := LookupDictionary(base, k);
  proof := LookupDictionary(witnesses, k);
  els := OrderedElements(G);
  flat := [];
  for x in els do
    for y in els do
      Add(flat, Position(els, x * y) - 1);
    od;
  od;

  PrintTo(out, "{\"order\":", k[1], ",\"id\":", k[2],
          ",\"verdict\":\"", why, "\",\"mul\":");
  PrintJsonIntList(out, flat);
  PrintTo(out, ",\"witness\":");

  if why = "C1-abelian" or why = "C2-nilpotent2" then
    PrintTo(out, "{}");
  elif why = "C3-AsemiE" then
    normal := proof[1];
    complement := proof[2];
    PrintTo(out, "{\"normal\":");
    PrintJsonIntList(out, normal);
    PrintTo(out, ",\"complement\":");
    PrintJsonIntList(out, complement);
    PrintTo(out, "}");
  elif why = "C4-dicyclic" then
    PrintTo(out, "{\"x\":", proof[1], ",\"y\":", proof[2], "}");
  elif why = "C6-KKindex2" then
    PrintTo(out, "{\"subgroup\":");
    PrintJsonIntList(out, proof);
    PrintTo(out, "}");
  elif why = "C5-A4" then
    iso := IsomorphismGroups(G, AlternatingGroup(4));
    if iso = fail then Error("cannot construct A4 witness"); fi;
    images := List(els, g -> List([1 .. 4], z -> z ^ Image(iso, g) - 1));
    PrintTo(out, "{\"permutation_images\":");
    PrintJsonIntLists(out, images);
    PrintTo(out, "}");
  elif why = "R1-subdirect" then
    PrintTo(out, "{\"quotients\":[");
    PrintQuotientWitness(out, G, els, proof[1]);
    PrintTo(out, ",");
    PrintQuotientWitness(out, G, els, proof[2]);
    PrintTo(out, "]}");
  else
    Error("no witness printer for verdict: ", why);
  fi;
  PrintTo(out, "}\n");
end;

positiveIds := Filtered(ids, k -> LookupDictionary(base, k) <> fail);
witnessOut := OutputTextFile(WitnessFile, false);
SetPrintFormattingStatus(witnessOut, false);
PrintTo(witnessOut, "{\"schema\":\"gsh-small-group-witness-v1\",",
        "\"max_order\":", MaxOrder, ",\"positive_groups\":",
        Length(positiveIds), "}\n");
for k in positiveIds do PrintPositiveWitness(witnessOut, k); od;
CloseStream(witnessOut);

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
