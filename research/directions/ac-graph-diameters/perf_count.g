total := 0;
for n in [2..720] do
  k := NumberPerfectGroups(n);
  if k > 0 then
    Print(n, " ", k, "\n");
    total := total + k;
  fi;
od;
Print("total perfect groups of order at most 720: ", total, "\n");
QUIT;
