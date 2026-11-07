"""Exact integer checks for survey/topology.md.

Words in F_2 are tuples of nonzero integers, where k>0 means x_k and k<0 means x_k^{-1}.
Run with:  python3 topology_check.py
Every printed number is exact integer arithmetic; the script uses only the python standard library.
"""
from math import gcd


def reduce_word(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def inv(w):
    return tuple(-g for g in reversed(w))


def mul(a, b):
    return reduce_word(tuple(a) + tuple(b))


def conj(w, g):
    return mul(mul(g, w), inv(g))


def exp_sums(w, rank=2):
    v = [0] * rank
    for g in w:
        v[abs(g) - 1] += 1 if g > 0 else -1
    return tuple(v)


def det2(m):
    return m[0][0] * m[1][1] - m[1][0] * m[0][1]


def snf_diag_det(M):
    """Smith diagonal of a 2x2 integer matrix: first entry the gcd of all entries,
    second entry |det| divided by the first. Exact, no library needed."""
    assert len(M) == 2 and len(M[0]) == 2
    d = det2(M)
    g1 = 0
    for row in M:
        for e in row:
            g1 = gcd(g1, abs(e))
    if g1 == 0:
        return [0, 0], 0
    assert d % g1 == 0, (M, g1, d)
    return [g1, abs(d) // g1], d


def ak_relators(m, n):
    """Relators of <x,y | xyx = yxy, x^m = y^n>, as words in F_2."""
    r1 = (1, 2, 1) + inv((2, 1, 2))
    r2 = (1,) * m + (-2,) * n
    return [reduce_word(r1), reduce_word(r2)]


print("== check 1: relators of <x,y | xyx = yxy, x^m = y^n> and their exponent sums")
r1, r2 = ak_relators(3, 4)
print("  r1 = xyx(yxy)^-1 reduces to", r1, " exponent sums", exp_sums(r1))
print("  r2 = x^3 y^-4 reduces to", r2, " exponent sums", exp_sums(r2))
assert exp_sums(r1) == (1, -1), exp_sums(r1)
assert exp_sums(r2) == (3, -4), exp_sums(r2)
print("  PASS: exponent sums of the two relators are (1,-1) and (m,-n)")

print("== check 2: exponent-sum matrix and determinant of the AK family")
bad = []
for m in range(2, 9):
    for n in range(2, 9):
        rs = ak_relators(m, n)
        M = [list(exp_sums(r)) for r in rs]
        d = det2(M)
        if (abs(d) == 1) != (abs(m - n) == 1):
            bad.append((m, n, d))
        print(f"  m={m} n={n} matrix={M} det={d} unimodular={abs(d)==1}")
assert not bad, bad
print("  PASS: det = m - n, so the abelianisation is trivial exactly when m = n +- 1")

print("== check 3: Smith normal form of AK(3) and of Akbulut-Kirby's 4-sphere presentation")
for name, (m, n) in [("AK(3) = <x,y | xyx=yxy, x^3=y^4>", (3, 4)),
                     ("Akbulut-Kirby 1985 = <x,y | xyx=yxy, x^5=y^4>", (5, 4)),
                     ("Gersten case = <x,y | xyx=yxy, x^2=y^3>", (2, 3))]:
    rs = ak_relators(m, n)
    M = [list(exp_sums(r)) for r in rs]
    diag, d = snf_diag_det(M)
    print(f"  {name}: matrix={M} det={d} Smith diagonal={diag}")
    assert abs(d) == 1 and all(abs(x) == 1 for x in diag)
print("  PASS: all three have trivial abelianisation, so H_1 of the standard 2-complex is 0")
print("  PASS: chi = 1 - 2 + 2 = 1 and b_0 = 1, b_1 = 0 give b_2 = 0, so the complex is acyclic")

print("== check 4: the relation module of a trivial group is free of rank n (rank 2 here)")
print("  For <x,y | r1, r2> presenting the trivial group, R = F_2 and R/[R,R] = Z^2.")
print("  The two relators give a 2-element generating set of Z^2, whose Smith form is (1,1).")
for m, n in [(3, 4), (5, 4)]:
    rs = ak_relators(m, n)
    M = [list(exp_sums(r)) for r in rs]
    diag, d = snf_diag_det(M)
    assert diag == [1, 1], (m, n, diag)
print("  PASS: Smith diagonal is (1,1) in both cases, so the relator images generate Z^2")

print("== check 5: conjugation leaves exponent sums alone")
for m, n in [(3, 4), (5, 4)]:
    r1, r2 = ak_relators(m, n)
    for g in [(1,), (2, -1), (1, 2, 1, 2), (2, 2, 1)]:
        assert exp_sums(conj(r1, g)) == exp_sums(r1)
        assert exp_sums(conj(r2, g)) == exp_sums(r2)
print("  PASS: exponent sums of both relators are unchanged by all four conjugators tested")

print("== check 6: the indexing convention of the Akbulut-Kirby family")
# The problem's AK(n) is <x,y | xyx = yxy, x^n = y^(n+1)>.  Swap x and y: the first relator
# becomes the inverse of the first relator, and the second becomes y^n x^(-n-1), which is a
# cyclic permutation of x^(-n-1) y^n.  Both operations preserve the normal closure, so the two
# presentations define the same group.  Here the swap is done by the map 1 -> 2, 2 -> 1.


def swap(w):
    return tuple({1: 2, 2: 1}[abs(g)] * (1 if g > 0 else -1) for g in w)


def cyclic_permutations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def conjugate_or_inverse(u, v):
    """True if v is a cyclic permutation of u or of u^-1."""
    for c in cyclic_permutations(u) + cyclic_permutations(inv(u)):
        if c == v:
            return True
    return False


for m, n in [(3, 4), (4, 5), (5, 4)]:
    base = ak_relators(m, n)                       # our AK(m) with exponent m and n
    sw = [reduce_word(swap(r)) for r in base]      # the same relators after swapping x and y
    target = ak_relators(n, m)                     # the family with the exponent roles exchanged
    assert conjugate_or_inverse(sw[0], target[0]), (m, n, sw[0], target[0])
    assert conjugate_or_inverse(sw[1], target[1]), (m, n, sw[1], target[1])
    print(f"  AK({m}) with x,y swapped has the same normal closures as the family member with "
          f"exponents ({n},{m})")
print("  PASS: the two indexing conventions differ by a relabelling of the generators")

print("ALL CHECKS PASSED")
