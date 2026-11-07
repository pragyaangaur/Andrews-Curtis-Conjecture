# Export, for each finite group in the list, the data the diameter engine needs:
#   order m, multiplication table (0-based), maximal normal subgroups,
#   maximal subgroups, generators of Aut(G) as permutations of element indices.
# Everything is deterministic.  Called as: gap -q -b export.g
# Output directory: data/<name>/

MakeGroups := function()
  local L;
  L := [];
  Add(L, rec(name := "A5", g := AlternatingGroup(5)));
  Add(L, rec(name := "SL2_5", g := SL(2,5)));
  Add(L, rec(name := "PSL2_7", g := PSL(2,7)));
  Add(L, rec(name := "SL2_7", g := SL(2,7)));
  Add(L, rec(name := "A6", g := AlternatingGroup(6)));
  Add(L, rec(name := "PSL2_8", g := PSL(2,8)));
  Add(L, rec(name := "PSL2_11", g := PSL(2,11)));
  Add(L, rec(name := "SL2_9_2A6", g := SL(2,9)));
  Add(L, rec(name := "PSL2_13", g := PSL(2,13)));
  Add(L, rec(name := "ThreeA6", g := PerfectGroup(IsPermGroup, 1080, 1)));
  Add(L, rec(name := "PSL2_17", g := PSL(2,17)));
  Add(L, rec(name := "A7", g := AlternatingGroup(7)));
  Add(L, rec(name := "A5xA5", g := DirectProduct(AlternatingGroup(5), AlternatingGroup(5))));
  return L;
end;

WriteInts := function(fname, ints)
  local s, i;
  s := "";
  for i in ints do
    Append(s, String(i));
    Append(s, "\n");
  od;
  PrintTo(fname, s);
end;

ExportOne := function(name, G)
  local dir, els, idx, m, mul, i, j, row, s, ns, ms, A, agens, perms, phi, p, f;
  dir := Concatenation("data/", name);
  Exec(Concatenation("mkdir -p ", dir));
  els := Elements(G);
  m := Length(els);
  idx := NewDictionary(els[1], true);
  for i in [1..m] do
    AddDictionary(idx, els[i], i);
  od;
  # multiplication table, 0-based, one row per line, space separated
  mul := [];
  s := "";
  for i in [1..m] do
    row := [];
    for j in [1..m] do
      Add(row, String(LookupDictionary(idx, els[i] * els[j]) - 1));
    od;
    Append(s, JoinStringsWithSeparator(row, " "));
    Append(s, "\n");
  od;
  f := Concatenation(dir, "/mult.txt");
  PrintTo(f, s);
  PrintTo(Concatenation(dir, "/order.txt"), Concatenation(String(m), "\n"));
  # maximal normal subgroups
  ns := MaximalNormalSubgroups(G);
  s := "";
  for i in [1..Length(ns)] do
    Append(s, JoinStringsWithSeparator(List(Elements(ns[i]), x -> String(LookupDictionary(idx, x) - 1)), " "));
    Append(s, "\n");
  od;
  PrintTo(Concatenation(dir, "/maxnorm.txt"), s);
  # maximal subgroups (ordinary generation)
  ms := MaximalSubgroups(G);
  s := "";
  for i in [1..Length(ms)] do
    Append(s, JoinStringsWithSeparator(List(Elements(ms[i]), x -> String(LookupDictionary(idx, x) - 1)), " "));
    Append(s, "\n");
  od;
  PrintTo(Concatenation(dir, "/maxsub.txt"), s);
  # Aut(G) generators as permutations of element indices (0-based images)
  A := AutomorphismGroup(G);
  agens := GeneratorsOfGroup(A);
  if Length(agens) > 12 then
    agens := agens{[1..12]};
  fi;
  s := "";
  for phi in agens do
    perms := List(els, x -> LookupDictionary(idx, Image(phi, x)) - 1);
    Append(s, JoinStringsWithSeparator(List(perms, String), " "));
    Append(s, "\n");
  od;
  PrintTo(Concatenation(dir, "/aut.txt"), s);
  PrintTo(Concatenation(dir, "/info.txt"),
          Concatenation(name, " order ", String(m), " maxnorm ",
                        String(Length(ns)), " maxsub ", String(Length(ms)),
                        " autgens ", String(Length(agens)), "\n"));
end;

for r in MakeGroups() do
  Print("# exporting ", r.name, "\n");
  ExportOne(r.name, r.g);
od;
QUIT;
