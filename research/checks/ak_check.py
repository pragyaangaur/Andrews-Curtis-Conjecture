#!/usr/bin/env python3
"""Checks for the OPEN_QUESTIONS note.

Claim checked here: the Akbulut-Kirby presentations AK(n) and the tested
Miller-Schupp presentations MS(n,w) present the trivial group.

Method.  Todd-Coxeter enumeration of the cosets of the cyclic subgroup <y>.
If [G:<y>] = 1 then G = <y> is cyclic; a cyclic group equals its own
abelianization, and these presentations have trivial abelianization (checked
below by exponent sums), so G is trivial.  This avoids a full coset
enumeration of G over the trivial subgroup, which is far slower.

Run:  python3 ak_check.py
"""
import sys
from todd_coxeter import index_of_subgroup

X, Y = 1, 2


def ak(n):
    """<x,y | xyx = yxy, x^n = y^(n+1)>."""
    return [(X, Y, X, -Y, -X, -Y), (X,) * n + (-Y,) * (n + 1)]


def ms(n, w):
    """<x,y | x^-1 y^n x = y^(n+1), x = w>."""
    return [(-X,) + (Y,) * n + (X,) + (-Y,) * (n + 1),
            (X,) + tuple(-g for g in reversed(w))]


def exponent_sums(relators):
    """Return the 2 x m matrix of exponent sums of the relators, as rows."""
    return [(sum(1 for g in r if g == X) - sum(1 for g in r if g == -X),
             sum(1 for g in r if g == Y) - sum(1 for g in r if g == -Y))
            for r in relators]


def det2(rows):
    (a, b), (c, d) = rows[0], rows[1]
    return a * d - b * c


def main():
    ok = True

    # --- adversarial control: 2 generators, 1 relator, non-trivial group ----
    try:
        r = index_of_subgroup(2, [(X, Y, X, -Y, -X, -Y)], [(Y,)], 5000)
        print(f"FAIL <x,y|xyx=yxy>: [G:<y>] = {r}, expected the enumeration "
              f"to run out of cosets (the group is infinite)")
        ok = False
    except RuntimeError:
        print("PASS <x,y|xyx=yxy>: [G:<y>] is infinite, as expected "
              "(no spurious collapse)")

    # --- Akbulut-Kirby ----------------------------------------------------
    for n in range(1, 6):
        rels = ak(n)
        rows = exponent_sums(rels)
        det = det2(rows)
        ab = "trivial" if abs(det) == 1 else f"nontrivial (det {det})"
        try:
            iy = index_of_subgroup(2, rels, [(Y,)], 5000)
            ix = index_of_subgroup(2, rels, [(X,)], 5000)
        except RuntimeError as exc:
            print(f"FAIL AK({n}): {exc}")
            ok = False
            continue
        good = (iy == 1 and ix == 1 and abs(det) == 1)
        ok = ok and good
        print(f"{'PASS' if good else 'FAIL'} AK({n}) = <x,y | xyx=yxy, "
              f"x^{n}=y^{n+1}>: abelianization {ab}, [G:<y>]={iy}, [G:<x>]={ix}"
              f" => G is cyclic, hence trivial")

    # --- Miller-Schupp ----------------------------------------------------
    ms_cases = [
        (1, (Y,), "MS(1,y)"),
        (1, (Y, -X, -Y, X), "MS(1,y^-1x^-1yx)"),
        (2, (-Y, -X, -Y, X, Y), "MS(2,y^-1x^-1yxy)"),
    ]
    for n, w, label in ms_cases:
        rels = ms(n, w)
        rows = exponent_sums(rels)
        det = det2(rows)
        try:
            iy = index_of_subgroup(2, rels, [(Y,)], 5000)
        except RuntimeError as exc:
            print(f"FAIL {label}: {exc}")
            ok = False
            continue
        good = (iy == 1 and abs(det) == 1)
        ok = ok and good
        print(f"{'PASS' if good else 'FAIL'} {label}: abelianization "
              f"{'trivial' if abs(det)==1 else 'nontrivial'}, [G:<y>]={iy}"
              f" => trivial")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
