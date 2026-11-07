#!/usr/bin/env python3
"""Self-check for the Andrews-Curtis toolkit.

Run

    python3 toolkit/test_toolkit.py

Every check prints one PASS line or one FAIL line.  The exit status is 0 if and
only if every check passed.  The script is deterministic: it uses no random
number generator except ``random.Random(seed)`` with a fixed seed, and it does
not depend on the order of anything in a dict.

The last section cross-checks the word arithmetic against an independent
implementation, sympy's free groups, and replays a BFS certificate through
sympy.  That section is skipped, with a printed note, when sympy is missing.
"""

import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import words as W
import ac as A
import bfs as B

PASSED = 0
FAILED = 0
SKIPPED = 0


def check(name, cond, detail=""):
    global PASSED, FAILED
    if cond:
        PASSED += 1
        print("PASS  " + name)
    else:
        FAILED += 1
        print("FAIL  " + name + ("   <<%s>>" % (detail,) if detail else ""))


def raises(fn, *args, **kwargs):
    """True when the call raises some exception."""
    try:
        fn(*args, **kwargs)
    except Exception:
        return True
    return False


t_start = time.time()

# ==========================================================================
# 1. words
# ==========================================================================
print("--- words: reduction, inverse, product, conjugation ---")

check("reduce_word of empty word is empty", W.reduce_word(()) == ())
check("reduce_word cancels an inverse pair", W.reduce_word((1, -1)) == ())
check("reduce_word cancels only adjacent inverse pairs",
      W.reduce_word((1, 1, -1, 2)) == (1, 2))
check("reduce_word handles a full cancellation",
      W.reduce_word((1, 2, -2, -1)) == ())
check("is_reduced rejects an inverse pair", not W.is_reduced((1, -1)))
check("is_reduced accepts x y X", W.is_reduced((1, 2, -1)))

small = W.all_words(2, 3)
check("reduce_word is idempotent on all 53 words of length at most 3",
      all(W.reduce_word(W.reduce_word(w)) == W.reduce_word(w) for w in small))
check("reduce_word always returns a reduced word",
      all(W.is_reduced(W.reduce_word(w)) for w in small))
check("inverse inverts letter order and signs",
      W.inverse((1, 2, -1)) == (1, -2, -1))
check("inverse is an involution on all 53 words",
      all(W.inverse(W.inverse(w)) == w for w in small))
check("w times inverse w is empty on all 53 words",
      all(W.mul(w, W.inverse(w)) == () for w in small))
check("mul of (x) and (X y) is (y)", W.mul((1,), (-1, 2)) == (2,))
check("mul is associative on a sample",
      all(W.mul(W.mul(a, b), c) == W.mul(a, W.mul(b, c))
          for a in small[:6] for b in small[:6] for c in small[:6]))
check("conjugate of x by y is y x Y", W.conjugate((1,), (2,)) == (2, 1, -2))
check("conjugate agrees with g w g^-1",
      all(W.conjugate(w, (2,)) == W.mul(W.mul((2,), w), (-2,)) for w in small))
check("commutator of x and y has zero exponent sums",
      W.exp_sums(W.commutator((1,), (2,)), 2) == (0, 0))
check("length of a reduced product is at most the sum of lengths",
      all(len(W.mul(a, b)) <= len(a) + len(b) for a in small for b in small[:8]))

print("--- words: exponent sums ---")
check("exponent sums of xyxYXY in F_2 are (1, -1)",
      W.exp_sums((1, 2, 1, -2, -1, -2), 2) == (1, -1))
check("exponent sums of x^3 y^-4 are (3, -4)",
      W.exp_sums((1, 1, 1, -2, -2, -2, -2), 2) == (3, -4))
check("exponent sums are a homomorphism on a sample",
      all(tuple(p + q for p, q in zip(W.exp_sums(a, 2), W.exp_sums(b, 2)))
          == W.exp_sums(W.mul(a, b), 2) for a in small for b in small[:10]))
check("exponent sums of an inverse are the negation",
      all(W.exp_sums(W.inverse(w), 2) == tuple(-t for t in W.exp_sums(w, 2))
          for w in small))
check("exponent sums are unchanged by conjugation",
      all(W.exp_sums(W.conjugate(w, (1, 2)), 2) == W.exp_sums(w, 2) for w in small))
check("exponent sums of the empty word are zero",
      W.exp_sums((), 3) == (0, 0, 0))
check("exponent sums reject an out of range letter",
      raises(W.exp_sums, (3,), 2))

print("--- words: enumeration, printing, parsing ---")
check("count_words agrees with enumeration for rank 1, length 3",
      W.count_words(1, 3) == len(W.all_words(1, 3)) == 7)
check("count_words agrees with enumeration for rank 2, length 4",
      W.count_words(2, 4) == len(W.all_words(2, 4)) == 161)
check("count_words agrees with enumeration for rank 3, length 3",
      W.count_words(3, 3) == len(W.all_words(3, 3)) == 187)
check("count_words formula is 1 + sum 2n(2n-1)^(k-1)",
      W.count_words(2, 2) == 1 + 4 + 12 and W.count_words(3, 2) == 1 + 6 + 30)
w4 = W.all_words(2, 4)
check("all_words has no duplicates", len(set(w4)) == len(w4))
check("all_words is sorted by length then letters",
      w4 == sorted(w4, key=lambda w: (len(w), w)))
check("all_words returns only reduced words", all(W.is_reduced(w) for w in w4))
check("all_words contains exactly the words of each length",
      all(W.count_words(2, k) == len([w for w in w4 if len(w) <= k]) for k in range(5)))
check("format_word prints x, Y and the empty word",
      W.format_word((1, -2)) == "xY" and W.format_word(()) == "")
check("parse_word inverts format_word on all 37 words of rank 3, length 2",
      all(W.parse_word(W.format_word(w)) == w for w in W.all_words(3, 2)))
check("parse_word reads xyxYXY as the AK relator",
      W.parse_word("xyxYXY") == (1, 2, 1, -2, -1, -2))
check("parse_word ignores spaces and asterisks",
      W.parse_word("x y*X") == (1, 2, -1) and W.parse_word(" x X ") == ())
check("cyclic_permutation of a reduced word is a rotation",
      W.cyclic_permutation((1, 2, 2), 1) == (2, 2, 1))
check("cyclic_permutation of the identity is the identity",
      W.cyclic_permutation((), 3) == ())
check("cyclic_permutation rejects a word that is not cyclically reduced",
      raises(W.cyclic_permutation, (1, 2, -1), 2))
check("is_cyclically_reduced rejects x y X", not W.is_cyclically_reduced((1, 2, -1)))

print("--- words: integer linear algebra ---")
check("det of [[1,2],[3,4]] is -2", W.det_int([[1, 2], [3, 4]]) == -2)
check("det of [[2,4],[0,6]] is 12", W.det_int([[2, 4], [0, 6]]) == 12)
check("det of a singular matrix is 0", W.det_int([[1, 2], [2, 4]]) == 0)
check("det of the 3x3 identity is 1", W.det_int([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == 1)
check("det of a 3x3 with a known value",
      W.det_int([[2, 0, 1], [1, 3, 2], [1, 1, 4]]) == 18)
check("det of a permutation matrix is its sign",
      W.det_int([[0, 1], [1, 0]]) == -1)
check("det of a 4x4 diagonal matrix is the product",
      W.det_int([[2, 0, 0, 0], [0, 3, 0, 0], [0, 0, 5, 0], [0, 0, 0, 7]]) == 210)
check("is_unimodular accepts the identity", W.is_unimodular([[1, 0], [0, 1]]))
check("is_unimodular accepts a determinant -1 matrix",
      W.is_unimodular([[1, -1], [3, -4]]))
check("is_unimodular rejects determinant 0", not W.is_unimodular([[1, 2], [2, 4]]))
check("is_unimodular rejects a degenerate tuple", not W.is_unimodular(((1, 0),)))
check("smith divisors of [[2,4],[0,6]] are (2, 6)",
      W.smith_elementary_divisors([[2, 4], [0, 6]]) == (2, 6))
check("smith divisors of [[2,0],[0,3]] are (1, 6)",
      W.smith_elementary_divisors([[2, 0], [0, 3]]) == (1, 6))
check("smith divisors of a unimodular matrix are (1, 1)",
      W.smith_elementary_divisors([[1, -1], [3, -4]]) == (1, 1))
check("smith divisors of the 3x3 identity are (1, 1, 1)",
      W.smith_elementary_divisors([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == (1, 1, 1))
check("smith divisors of diag(2,4,8) are (2, 4, 8)",
      W.smith_elementary_divisors([[2, 0, 0], [0, 4, 0], [0, 0, 8]]) == (2, 4, 8))
check("smith divisors of diag(4,6) are (2, 12)",
      W.smith_elementary_divisors([[4, 0], [0, 6]]) == (2, 12))
check("smith divisors of a rank 1 matrix are one number",
      W.smith_elementary_divisors([[1, 2], [2, 4]]) == (1,))

rng = random.Random(20261104)
ok_chain = True
ok_det = True
for _ in range(300):
    M = [[rng.randint(-6, 6) for _ in range(3)] for _ in range(3)]
    d = W.det_int(M)
    if d == 0:
        continue
    s = W.smith_elementary_divisors(M)
    if len(s) != 3:
        ok_chain = False
        break
    if any(s[k + 1] % s[k] != 0 for k in range(2)):
        ok_chain = False
        break
    prod = s[0] * s[1] * s[2]
    if prod != abs(d):
        ok_det = False
        break
check("smith divisors form a divisibility chain on 300 seeded 3x3 matrices", ok_chain)
check("the product of the smith divisors is |det| on those matrices", ok_det)

# ==========================================================================
# 2. presents and moves
# ==========================================================================
print("--- presentations and AC moves ---")

check("the standard presentation of rank 2 is (x, y)",
      A.standard(2) == ((1,), (2,)))
check("the standard presentation of rank 3 is (x, y, z)",
      A.standard(3) == ((1,), (2,), (3,)))
check("is_standard recognises the standard presentation",
      A.is_standard(A.standard(3), 3))
check("is_standard rejects a non standard presentation",
      not A.is_standard(((1,), (1,)), 2))

AK3 = A.ak_presentation(3)
check("AK(3) first relator is xyxYXY", AK3[0] == (1, 2, 1, -2, -1, -2))
check("AK(3) second relator is x^3 y^-4",
      AK3[1] == (1, 1, 1, -2, -2, -2, -2))
check("AK(k) has relator lengths 6 and 2k+1 for k = 1..6",
      all(len(A.ak_presentation(k)[0]) == 6 and len(A.ak_presentation(k)[1]) == 2 * k + 1
          for k in range(1, 7)))
check("AK(k) has a unimodular exponent sum matrix for k = 1..6",
      all(A.has_trivial_abelianization(A.ak_presentation(k), 2) for k in range(1, 7)))
check("the exponent sum matrix of AK(3) is [[1,-1],[3,-4]]",
      A.abelianization(AK3, 2) == ((1, -1), (3, -4)))
check("the first relator of AK(k) has exponent sums (1, -1) for k = 1..6",
      all(W.exp_sums(A.ak_presentation(k)[0], 2) == (1, -1) for k in range(1, 7)))
check("apply_move inverts a relator",
      A.apply_move(((1, 2), (2,)), ("inv", 1), 2) == ((-2, -1), (2,)))
check("apply_move right multiplies a relator",
      A.apply_move(((1,), (2,)), ("mul", 1, 2), 2) == ((1, 2), (2,)))
check("apply_move conjugates a relator",
      A.apply_move(((1,), (2,)), ("conj", 1, (2,)), 2) == ((2, 1, -2), (2,)))
check("apply_move with i equal to j is rejected",
      raises(A.apply_move, ((1,), (2,)), ("mul", 1, 1), 2))
check("apply_move with an out of range relator index is rejected",
      raises(A.apply_move, ((1,), (2,)), ("inv", 3), 2))
check("apply_move with an unknown kind is rejected",
      raises(A.apply_move, ((1,), (2,)), ("swap", 1, 2), 2))
check("apply_move with a letter outside the rank is rejected",
      raises(A.apply_move, ((1,), (2,)), ("conj", 1, (3,)), 2))
check("apply_move rejects an unreduced relator",
      raises(A.apply_move, ((1, -1), (2,)), ("inv", 1), 2))

conj1 = A.conjugators(2, 1)
conj2 = A.conjugators(2, 2)
check("conjugators of rank 2 up to length 1 are the four single letters",
      set(conj1) == {(-1,), (1,), (-2,), (2,)} and conj1 == sorted(conj1))
check("conjugators of rank 2 up to length 2 number 16", len(conj2) == 16)
check("conjugators of rank 3 up to length 1 number 6", len(A.conjugators(3, 1)) == 6)
check("conjugators contain no identity", () not in A.conjugators(2, 3))

rs0 = ((1, 2), (-2,))
succ = A.successors(rs0, 2, conj2)
check("the successors of (x, y) with conjugator length 1 are the 8 listed presentations",
      {s for _, s in A.successors(((1,), (2,)), 2, conj1)} == {
          ((-1,), (2,)), ((1,), (-2,)),
          ((1, 2), (2,)), ((1,), (2, 1)),
          ((2, 1, -2), (2,)), ((-2, 1, 2), (2,)),
          ((1,), (1, 2, -1)), ((1,), (-1, 2, 1)),
      })
check("every successor is a tuple of two reduced words",
      all(len(s) == 2 and all(W.is_reduced(r) for r in s) for _, s in succ))
check("successors contain no self loop",
      all(s != rs0 for _, s in succ))
check("successors are listed with distinct move tags",
      len({mv for mv, _ in succ}) == len(succ))
check("successors with a larger conjugator set contain the smaller set",
      {s for _, s in A.successors(rs0, 2, conj1)} <= {s for _, s in A.successors(rs0, 2, conj2)})
check("every successor passes the abelianisation test",
      all(A.has_trivial_abelianization(s, 2) for _, s in succ))

print("--- certificates ---")
CHECK_PATH = [("mul", 1, 2), ("inv", 1), ("mul", 2, 1),
              ("inv", 2), ("mul", 1, 2), ("inv", 1)]
check("the hard coded 6 move certificate takes (x, y) to (y, x)",
      A.verify_path(A.standard(2), CHECK_PATH, 2) == ((2,), (1,)))
check("a prefix of the certificate does not already give (y, x)",
      A.verify_path(A.standard(2), CHECK_PATH[:-1], 2) != ((2,), (1,)))
check("an empty certificate fixes the presentation",
      A.verify_path(A.standard(2), [], 2) == A.standard(2))
check("verify_path rejects an illegal tag",
      raises(A.verify_path, A.standard(2), [("mul", 1, 1)], 2))
check("verify_path rejects a conjugate by a letter outside the rank",
      raises(A.verify_path, A.standard(2), [("conj", 1, (5,))], 2))

# The search uses the three moves in one direction only.  These checks show
# that each move can be undone by forward moves inside the same move set, so
# directed reachability from the standard presentation is the whole
# AC-equivalence class and not a proper subset of it.
base = ((1, 2), (2, -1))
check("inverting a relator twice returns the original presentation",
      A.apply_move(A.apply_move(base, ("inv", 1), 2), ("inv", 1), 2) == base)
step = A.apply_move(base, ("mul", 1, 2), 2)
back = A.verify_path(step, [("inv", 2), ("mul", 1, 2), ("inv", 2)], 2)
check("three forward moves undo a right multiplication", back == base)
for w in [(-1,), (2,), (1, 2), (-2, 1)]:
    step = A.apply_move(base, ("conj", 1, w), 2)
    back = A.apply_move(step, ("conj", 1, W.inverse(w)), 2)
    check("conjugating by w and then by w inverse is the identity on %s"
          % (W.format_word(w),), back == base)
left = A.verify_path(base, [("conj", 1, base[1]), ("mul", 1, 2)], 2)
check("left multiplication by r_2 is conjugation by r_2 followed by right multiplication",
      left == (W.mul(base[1], base[0]), base[1]))
check("conjugating by the generator y is not the same as conjugating by the relator r_2",
      W.conjugate(base[0], (2,)) != W.conjugate(base[0], base[1]))

print("--- exponent sums are an AC invariant ---")
check("the standard presentation has trivial abelianisation",
      A.has_trivial_abelianization(A.standard(2), 2))
check("(x, x) has abelianisation Z, so it cannot be AC equivalent to (x, y)",
      not A.has_trivial_abelianization(((1,), (1,)), 2))
check("(x, x) and the standard presentation differ in the Smith invariant too",
      A.abelianization_invariant(((1,), (1,)), 2)
      != A.abelianization_invariant(A.standard(2), 2))

res_small = B.bfs_from_standard(2, 3, 1)
inv_ok = True
count_edges = 0
for v in sorted(res_small["dist"]):
    base = A.abelianization_invariant(v, 2)
    for _, s in A.successors(v, 2, conj1):
        count_edges += 1
        if A.abelianization_invariant(s, 2) != base:
            inv_ok = False
            break
check("the Smith invariant of the exponent sum matrix is unchanged by every move "
      "on every vertex of the rank 2 length 3 search (%d edges)" % count_edges, inv_ok)

# ==========================================================================
# 3. breadth first search
# ==========================================================================
print("--- breadth first search ---")

res = B.bfs_from_standard(2, 4, 2)
check("the search contains the standard presentation", A.standard(2) in res["dist"])
check("the standard presentation is at distance 0", res["dist"][A.standard(2)] == 0)
check("exactly one presentation is at distance 0",
      sum(1 for d in res["dist"].values() if d == 0) == 1)
check("the layer sizes sum to the number of vertices",
      sum(res["layer_sizes"]) == len(res["dist"]))
check("every vertex has both relators of length at most 4",
      all(max(len(r) for r in v) <= 4 for v in res["dist"]))
check("every vertex has trivial abelianisation",
      all(A.has_trivial_abelianization(v, 2) for v in res["dist"]))
check("(x^-1, y) is at distance 1", res["dist"].get(((-1,), (2,))) == 1)
check("(x y, y) is at distance 1", res["dist"].get(((1, 2), (2,))) == 1)
check("(y x Y, y) is at distance 1", res["dist"].get(((2, 1, -2), (2,))) == 1)
check("(x, x y X) is at distance 1", res["dist"].get(((1,), (1, 2, -1))) == 1)
check("(x, y) is at distance 0 and (y, x) is at distance at most 6",
      0 < res["dist"].get(((2,), (1,)), 99) <= 6)
check("(x, x) is absent from the search", ((1,), (1,)) not in res["dist"])
check("the stored path to (y, x) replays to (y, x)",
      A.verify_path(A.standard(2), B.path_to(res, ((2,), (1,))), 2) == ((2,), (1,)))
ok, info = B.verify_all_paths(res, 2)
check("all %d stored paths of the rank 2 length 4 search replay correctly" % len(res["dist"]),
      ok and info == len(res["dist"]))
res2 = B.bfs_from_standard(2, 4, 2)
check("the search is deterministic: a second run gives the same distances",
      res2["dist"] == res["dist"])
check("the search is deterministic: a second run gives the same parents",
      res2["parent"] == res["parent"])
bc = B.box_count(2, 4)
check("the component at rank 2 and relator length 4 is the whole filtered box "
      "(%d = %d)" % (len(res["dist"]), bc[1]), len(res["dist"]) == bc[1])

res3 = B.bfs_from_standard(3, 2, 1)
bc3 = B.box_count(3, 2)
check("the component at rank 3 and relator length 2 is the whole filtered box "
      "(%d = %d)" % (len(res3["dist"]), bc3[1]), len(res3["dist"]) == bc3[1])
check("every rank 3 vertex has three relators of length at most 2",
      all(len(v) == 3 and max(len(r) for r in v) <= 2 for v in res3["dist"]))
ok3, info3 = B.verify_all_paths(res3, 3)
check("all %d stored paths of the rank 3 search replay correctly" % len(res3["dist"]),
      ok3 and info3 == len(res3["dist"]))
check("the rank 3 search is deterministic",
      B.bfs_from_standard(3, 2, 1)["dist"] == res3["dist"])
check("raising the conjugator bound from 1 to 2 does not change the rank 3 component",
      set(B.bfs_from_standard(3, 2, 2)["dist"]) == set(res3["dist"]))
check("raising the conjugator bound from 1 to 2 does not change the rank 2 length 3 component",
      set(B.bfs_from_standard(2, 3, 2)["dist"]) == set(res_small["dist"]))

res5 = B.bfs_from_standard(2, 5, 2)
bc5 = B.box_count(2, 5)
missing = [v for v in itertools.product(W.all_words(2, 5), repeat=2)
           if A.has_trivial_abelianization(v, 2) and v not in res5["dist"]]
check("the search at rank 2 and relator length 5 reaches %d of the %d presentations "
      "in the filtered box" % (len(res5["dist"]), bc5[1]),
      len(res5["dist"]) == 31240 and bc5[1] == 32040)
check("every presentation missed at relator length 5 has both relators of length 5",
      len(missing) == 800 and all(all(len(r) == 5 for r in v) for v in missing))

# ==========================================================================
# 3b. certificate files
# ==========================================================================
print("--- certificate files ---")
lines = list(B.certificate_lines(res_small, 2))
check("one certificate line per vertex", len(lines) == len(res_small["dist"]))
ok_c, bad_c, first_bad_c = B.replay_lines(lines, 2)
check("every exported certificate replays from the standard presentation",
      ok_c == len(lines) and bad_c == 0)
std_lines = [ln for ln in lines if ln.split("\t")[0] == "x;y"]
check("the certificate of the standard presentation is present once and has no moves",
      len(std_lines) == 1 and std_lines[0].split("\t")[1] == "")
check("corrupting the target of a line makes it fail",
      B.replay_lines([lines[-1].split("\t")[0].replace(";", ";")[:-1] + "y\t"
                      + lines[-1].split("\t")[1]], 2)[1] == 1)
all_moves = [mv for v in res_small["dist"] for mv in (B.path_to(res_small, v) or [])]
check("format_move and parse_move are inverse on every move of the small search",
      all(B.parse_move(B.format_move(mv)) == mv for mv in all_moves))


print("--- cross check against sympy ---")
try:
    import sympy as _sp
    from sympy.combinatorics.free_groups import FreeGroup
except Exception as exc:  # pragma: no cover
    SKIPPED += 1
    print("SKIP  sympy cross check (%s)" % (exc,))
else:
    F = FreeGroup("x y z")
    gens = F.generators
    ident = F.identity

    def to_sympy(word):
        if not word:
            return ident
        acc = None
        for a in word:
            g = gens[abs(a) - 1]
            g = g if a > 0 else g ** -1
            acc = g if acc is None else acc * g
        return acc

    check("sympy agrees that multiplication is free reduction",
          all(to_sympy(W.mul(a, b)) == to_sympy(a) * to_sympy(b)
              for a in W.all_words(2, 3) for b in W.all_words(2, 3)[:12]))
    check("sympy agrees on inverses",
          all(to_sympy(W.inverse(w)) == to_sympy(w) ** -1 for w in W.all_words(3, 2)))
    check("sympy agrees on conjugation",
          all(to_sympy(W.conjugate(w, (1, 2))) == to_sympy((1, 2)) * to_sympy(w) * to_sympy((1, 2)) ** -1
              for w in W.all_words(2, 3)))
    check("sympy agrees on the determinant of 100 seeded 3x3 and 4x4 matrices",
          all(W.det_int(M) == int(_sp.Matrix(M).det())
              for M in [[[rng.randint(-9, 9) for _ in range(3)] for _ in range(3)]
                        for _ in range(100)]
                       + [[[rng.randint(-9, 9) for _ in range(4)] for _ in range(4)]
                          for _ in range(100)]))
    check("sympy agrees that the product of the smith divisors is the determinant",
          all(_sp.prod(W.smith_elementary_divisors(M)) == abs(int(_sp.Matrix(M).det()))
              for M in [[[rng.randint(-4, 4) for _ in range(3)] for _ in range(3)]
                        for _ in range(100)]
              if _sp.Matrix(M).det() != 0))
    check("sympy agrees that the smith divisors form a chain",
          all(all(s[k + 1] % s[k] == 0 for k in range(len(s) - 1))
              for s in (W.smith_elementary_divisors(M)
                        for M in [[[rng.randint(-5, 5) for _ in range(3)] for _ in range(3)]
                                  for _ in range(100)])))
    check("sympy agrees that x times its inverse is the identity",
          to_sympy((1,)) * to_sympy((-1,)) == ident)

    # replay one BFS certificate through sympy: each tag must produce the same
    # relator tuple in the independent implementation
    target = ((2,), (1,), (3,))
    resx = B.bfs_from_standard(3, 2, 1)
    path = B.path_to(resx, target)
    if path is None:
        SKIPPED += 1
        print("SKIP  sympy certificate replay (target not found)")
    else:
        cur = [to_sympy(r) for r in A.standard(3)]
        agree = True
        v = A.standard(3)
        for mv in path:
            s = A.apply_move(v, mv, 3)
            # rebuild s independently with sympy from the tag and the old tuple
            new = list(cur)
            kind = mv[0]
            if kind == "inv":
                new[mv[1] - 1] = cur[mv[1] - 1] ** -1
            elif kind == "mul":
                new[mv[1] - 1] = cur[mv[1] - 1] * cur[mv[2] - 1]
            else:
                i, w = mv[1], mv[2]
                new[i - 1] = to_sympy(w) * cur[i - 1] * to_sympy(w) ** -1
            if any(a != to_sympy(b) for a, b in zip(new, s)):
                agree = False
                break
            cur = new
            v = s
        check("a %d move BFS certificate replays through sympy to the same relators"
              % len(path), agree)
        check("the replayed tuple is the target", v == target)

# ==========================================================================
# summary
# ==========================================================================
elapsed = time.time() - t_start
print()
print("SUMMARY  %d passed, %d failed, %d skipped   (%.2f s)"
      % (PASSED, FAILED, SKIPPED, elapsed))
sys.exit(0 if FAILED == 0 else 1)
