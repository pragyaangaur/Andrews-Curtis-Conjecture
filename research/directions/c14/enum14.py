#!/usr/bin/env python3
"""Size of the Havas-Ramsay canonical list at total relator length 14,
computed with the Round-1 code (survey/computational/enum_check.py) as a
cross-check, plus the step (D) redundancy count."""
import sys, time
sys.path.insert(0, '/workspace/nucleus/work/projects/p-fc9666b4f6c54fa380c9a84775ed7397/repo/survey/computational')
import enum_check as E
t0=time.time()
l=14
rows=E.per_length(l)
a=E.step_a(rows)
b=E.step_b(a)
c=E.step_c(b)
d=E.step_d(c)
print("l = %d: rows %d | (A) %d | (B) %d | (C) %d | (D) %d   [%.1f s]"%(l,len(rows),len(a),len(b),len(c),len(d),time.time()-t0))
# how many (D) discards are not already excluded by (A),(B),(C)?
dset=set(d)
disc=[t for t in c if t not in dset]
print("(D) discards from the (C) list: %d"%len(disc))
for t in disc[:20]:
    print("   ",E.C.show_pres(t), "det", E.C.det(t))
