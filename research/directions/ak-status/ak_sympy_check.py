"""Independent check that AK(1) presents the trivial group, using sympy.

sympy has its own Todd-Coxeter implementation, unrelated to coset2.py, so this
is a cross-check of the smallest member of the family.  For AK(2) and larger
sympy raised RecursionError under its default limit and did not finish within
200 seconds once the limit was raised, so this script checks AK(1) only and
prints nothing about the other members.
"""
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup

F, x, y = free_group("x y")
rels = [x**1 * (y**2)**-1, x*y*x*y**-1*x**-1*y**-1]
order = FpGroup(F, rels).order(strategy="relator_based")
print("AK(1): order of the presented group =", order)
print("AK(1) TRIVIAL" if order == 1 else "AK(1) NOT TRIVIAL")
