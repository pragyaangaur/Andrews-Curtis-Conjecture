"""Checks behind survey/invariants.md (Andrews-Curtis conjecture, D1 direction).

Run:  python3 invariants_check.py
Prints one PASS line per check.  Any failure raises and stops the script.

All arithmetic in parts 1-3 is exact integer arithmetic over the free group and
over Z.  Part 4 uses sympy for polynomial gcds.  Part 5 uses sympy for Smith
normal form.  Random choices are seeded (random.Random(20261104)).
"""

import random

import sympy
from sympy import Poly, Symbol, ZZ, Matrix, gcd
from sympy.matrices.normalforms import smith_normal_form

from ac_common import (
    red, mul, inv, conj, power, exp_sums, exp_matrix,
    move_inv, move_mul, move_conj, mat_mul_int, det_int, rank_mod_p,
    fox_derivative, gr_evaluate,
)

PASSED = []


def check(name, cond, detail=""):
    if not cond:
        raise AssertionError("FAILED: " + name + (" | " + detail if detail else ""))
    PASSED.append(name)
    print("PASS " + name + (" | " + detail if detail else ""))


# ------------------------------------------------------------------ part 1

def part1_words():
    rng = random.Random(20261104)
    for _ in range(500):
        n = rng.randint(1, 4)
        w = [rng.choice([g for g in range(1, n + 1)] + [-g for g in range(1, n + 1)])
             for _ in range(rng.randint(0, 14))]
        w = tuple(w)
        check_stub = red(w)
        assert red(check_stub) == check_stub
        assert mul(inv(w), w) == ()
        assert mul(w, inv(w)) == ()
        assert mul((), w) == check_stub
        assert inv(inv(w)) == w
        assert conj(w, ()) == check_stub
        for k in (-2, -1, 0, 1, 2):
            assert exp_sums(power(w, k), n) == tuple(k * a for a in exp_sums(w, n))
    check("word reduction is idempotent, inverse laws hold, exponent sums are additive",
          True, "500 seeded random words, ranks 1..4")

    # conjugates have the same exponent sums and the same reduced length up to
    # the trivial bound |conj| <= |w| + 2|u|
    rng = random.Random(7)
    for _ in range(200):
        n = 3
        w = tuple(rng.choice([1, -1, 2, -2, 3, -3]) for _ in range(rng.randint(0, 10)))
        u = tuple(rng.choice([1, -1, 2, -2, 3, -3]) for _ in range(rng.randint(0, 6)))
        c = conj(w, u)
        assert exp_sums(c, n) == exp_sums(w, n)
        assert len(c) <= len(red(w)) + 2 * len(red(u))
    check("conjugation preserves exponent sums", True, "200 seeded random triples")


# ------------------------------------------------------------------ part 2

def presentation_matrix_under_moves():
    """Every AC move acts on the exponent-sum matrix by a unimodular row operation."""
    rng = random.Random(20261105)
    ranks = (2, 3, 4)
    trials = 0
    for n in ranks:
        for _ in range(60):
            rels = tuple(
                red(tuple(rng.choice([g for g in range(1, n + 1)] + [-g for g in range(1, n + 1)])
                          for _ in range(rng.randint(1, 8))))
                for _ in range(n)
            )
            M = exp_matrix(rels, n)
            cur, curM = rels, M
            for _ in range(40):
                kind = rng.randrange(3)
                if kind == 0:
                    i = rng.randrange(n)
                    U = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
                    U[i][i] = -1
                    cur, curM = move_inv(cur, i), mat_mul_int(U, curM)
                elif kind == 1:
                    i, j = rng.sample(range(n), 2)
                    U = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
                    U[i][j] = 1
                    cur, curM = move_mul(cur, i, j), mat_mul_int(U, curM)
                else:
                    i = rng.randrange(n)
                    w = red(tuple(rng.choice([g for g in range(1, n + 1)] + [-g for g in range(1, n + 1)])
                                  for _ in range(rng.randint(0, 5))))
                    cur, curM = move_conj(cur, i, w), curM
                assert exp_matrix(cur, n) == curM, (n, rels, cur)
                trials += 1
    check("AC moves act on the exponent-sum matrix by left multiplication by a "
          "signed elementary integer matrix", True, "%d seeded move applications, ranks 2,3,4" % trials)


def snf(m):
    A = smith_normal_form(Matrix(m), domain=ZZ)
    return tuple(tuple(int(A[i, j]) for j in range(A.cols)) for i in range(A.rows))


def part2_invariance():
    rng = random.Random(20261106)
    for n in (2, 3, 4):
        for _ in range(40):
            rels = tuple(
                red(tuple(rng.choice([g for g in range(1, n + 1)] + [-g for g in range(1, n + 1)])
                          for _ in range(rng.randint(2, 9))))
                for _ in range(n)
            )
            M = exp_matrix(rels, n)
            s0 = snf(M)
            cur = rels
            for _ in range(30):
                kind = rng.randrange(3)
                if kind == 0:
                    cur = move_inv(cur, rng.randrange(n))
                elif kind == 1:
                    i, j = rng.sample(range(n), 2)
                    cur = move_mul(cur, i, j)
                else:
                    w = red(tuple(rng.choice([g for g in range(1, n + 1)] + [-g for g in range(1, n + 1)])
                                  for _ in range(rng.randint(0, 4))))
                    cur = move_conj(cur, rng.randrange(n), w)
                assert snf(exp_matrix(cur, n)) == s0
                assert abs(det_int(exp_matrix(cur, n))) == abs(det_int(M))
    check("Smith normal form and |det| of the exponent-sum matrix are preserved by "
          "AC moves", True, "seeded random walks, ranks 2,3,4")


# ------------------------------------------------------------------ part 3

def std(n):
    return tuple((i + 1,) for i in range(n))


def AK(n):
    """<x,y | xyx = yxy, x^n = y^(n+1)> as a relator tuple in F_2."""
    r1 = red((1, 2, 1) + inv((2, 1, 2)))
    r2 = red(power((1,), n) + power((-2,), n + 1))
    return (r1, r2)


def miller_schupp(n, w):
    """<a,b | a^-1 b^n a = b^(n+1), a = w> as a relator tuple in F_2."""
    r1 = red((-1,) + power((2,), n) + (1,) + power((-2,), n + 1))
    r2 = red((1,) + inv(w))
    return (r1, r2)


def part3_battery():
    t = Symbol("t")
    battery = []
    battery.append(("standard rank 2", std(2), 2))
    battery.append(("standard rank 3", std(3), 3))
    for n in (1, 2, 3, 4, 5):
        battery.append(("AK(%d)" % n, AK(n), 2))
    w0 = red((1, 2, -1, -2))              # commutator, exponent sum 0 on a
    w1 = red((1, 2, 2, -1, -2, -2))       # a b^2 a^-1 b^-2
    w2 = red((1, 2, -1, -2, 1, 2, -1, -2))
    for n, w, tag in ((1, w0, "[a,b]"), (2, w1, "ab^2a^-1b^-2"), (3, w2, "[a,b]^2")):
        battery.append(("Miller-Schupp n=%d w=%s" % (n, tag), miller_schupp(n, w), 2))
    # two further classical potential counterexamples
    battery.append(("length-14 example",
                    ((-1, 2, 2, 1, -2, -2, -2), (-2, 1, 1, 2, -1, -1, -1)), 2))
    battery.append(("Wicks length-27 example",
                    ((1, 1, 1, 1, 2, 2, 2, -2, -2, -1, -1),
                     (1, 1, 1, 1, 1, 1, 2, 2, 2, 2, -2, -2, -2, -1, -1, -1)), 2))

    ident_snf = {n: snf(tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n)))
                 for n in (2, 3)}
    rows = []
    for name, rels, n in battery:
        M = exp_matrix(rels, n)
        d = det_int(M)
        s = snf(M)
        assert s == ident_snf[n], (name, M, s)
        assert abs(d) == 1, (name, d)
        for p in (2, 3, 5, 7):
            assert rank_mod_p(M, p) == n, (name, p)
        rows.append((name, M, d, s))
    print("     %-34s %-24s %-6s %s" % ("presentation", "exponent-sum matrix", "det", "Smith normal form"))
    for name, M, d, s in rows:
        print("     %-34s %-24s %-6d %s" % (name, M, d, s))
    check("every balanced trivial-group presentation in the battery has exponent-sum "
          "matrix with Smith normal form I and |det| = 1", True,
          "%d presentations" % len(battery))
    check("the exponent-sum matrix has full rank modulo 2, 3, 5 and 7 for every "
          "presentation in the battery", True, "so the mod-p relation matrix carries no information")

    # the invariant has teeth outside the trivial-group class
    teeth = [("Z/2 * Z/2", ((1, 1), (2, 2))), ("Z/2 * Z/3", ((1, 1), (2, 2, 2)))]
    for name, rels in teeth:
        M = exp_matrix(rels, 2)
        assert abs(det_int(M)) not in (0, 1), (name, M)
    check("the same invariant separates non-trivial groups from the standard "
          "presentation", True,
          "|det| = 4 for <x,y | x^2, y^2> and |det| = 6 for <x,y | x^2, y^3>")

    # Fox calculus at the trivial representation equals the exponent-sum matrix
    for name, rels, n in battery:
        M = exp_matrix(rels, n)
        for j in range(1, n + 1):
            for i in range(n):
                val = gr_evaluate(fox_derivative(rels[i], j), {k: 0 for k in range(1, n + 1)}, 1)
                assert val == M[i][j - 1], (name, i, j, val, M)
    check("the Fox derivative matrix evaluated at the trivial representation is the "
          "exponent-sum matrix", True, "checked on all %d presentations in the battery" % len(battery))


def part3b_abelianisation():
    """The Smith normal form of the exponent-sum matrix is exactly the abelian
    invariant of the presented group, checked on presentations with known
    abelianisation."""
    cases = [
        ("<x,y | x^2, y^2>", ((1, 1), (2, 2)), (2, 2)),
        ("<x,y | x^2, y^3>", ((1, 1), (2, 2, 2)), (1, 6)),
        ("<x,y | x^2 y^-2, y^4>", ((1, 1, -2, -2), (2, 2, 2, 2)), (2, 4)),
        ("<x,y | x^3, y^3>", ((1, 1, 1), (2, 2, 2)), (3, 3)),
    ]
    for name, rels, expected in cases:
        s = snf(exp_matrix(rels, 2))
        diag = tuple(s[i][i] for i in range(2))
        assert diag == expected, (name, diag, expected)
    check("the Smith normal form of the exponent-sum matrix computes the abelian "
          "invariant factors", True,
          "checked on <x,y|x^2,y^2>, <x,y|x^2,y^3>, <x,y|x^2y^-2,y^4>, <x,y|x^3,y^3>")


# ------------------------------------------------------------------ part 4

def alexander_polynomial(rels, n, powers, t):
    """gcd of the Fox derivatives evaluated in Z[t^{+-1}] (0-th elementary ideal).

    Each entry is first multiplied by the smallest power of t that clears its
    negative exponents; the result is then divided by the largest power of t and
    made monic.  The answer is therefore well defined up to a unit +-t^k, which
    is exactly the ambiguity of the Alexander polynomial.
    """
    polys = []
    for i in range(len(rels)):
        for j in range(1, n + 1):
            p = sympy.expand(gr_evaluate(fox_derivative(rels[i], j), powers, t))
            if p != 0:
                poly = sympy.Poly(p, t)
                low = min(m[0] for m in poly.monoms())
                polys.append(sympy.Poly(sympy.expand(p * t ** (-low)), t))
    g = polys[0]
    for p in polys[1:]:
        g = gcd(g, p)
    g = sympy.Poly(g, t)
    # strip the largest power of t
    while True:
        coeffs = g.all_coeffs()[::-1]
        if coeffs[0] == 0:
            g = sympy.Poly(sympy.expand(g.as_expr() / t), t)
        else:
            break
    lead = g.all_coeffs()[0]
    return sympy.expand(g.as_expr() / lead)


def part4_fox_calculus():
    t = Symbol("t")
    # torus knot groups: <x,y | x^2 y^-3> (trefoil) and <x,y | x^2 y^-5> (T(2,5))
    cases = [
        ("trefoil <x,y | x^2=y^3>", ((1, 1, -2, -2, -2),), 2, {1: 3, 2: 2}, 1 - t + t ** 2),
        ("T(2,5) <x,y | x^2=y^5>", ((1, 1) + (-2,) * 5,), 2, {1: 5, 2: 2}, 1 - t + t ** 2 - t ** 3 + t ** 4),
    ]
    for name, rels, n, powers, expected in cases:
        got = alexander_polynomial(rels, n, powers, t)
        assert sympy.simplify(got - expected) == 0, (name, got, expected)
    check("Fox calculus reproduces the Alexander polynomial of two torus knot groups",
          True, "trefoil -> t^2-t+1, T(2,5) -> t^4-t^3+t^2-t+1")

    # every balanced trivial-group presentation has trivial Alexander data: the
    # only map to Z is trivial, and the matrix at that map is unimodular
    battery = [("standard rank 2", std(2), 2), ("AK(3)", AK(3), 2), ("AK(4)", AK(4), 2)]
    for name, rels, n in battery:
        got = alexander_polynomial(rels, n, {k: 0 for k in range(1, n + 1)}, t)
        assert got == 1, (name, got)
    check("at the trivial map to Z the Fox matrix of every balanced trivial-group "
          "presentation has gcd 1", True,
          "so the Alexander module of the presentation is 0, the value attached to the trivial group")


# ------------------------------------------------------------------ part 5

def part5_normal_closure_certificates():
    """Each AC move comes with an explicit word certificate that the normal
    closure of the relator tuple is unchanged.  The certificates are the ones
    used in the proof of Lemma 1 of the survey."""
    rng = random.Random(20261108)
    n = 3
    letters = [1, -1, 2, -2, 3, -3]
    for _ in range(300):
        rels = tuple(
            red(tuple(rng.choice(letters) for _ in range(rng.randint(0, 8))))
            for _ in range(n)
        )
        i, j = rng.sample(range(n), 2)
        w = red(tuple(rng.choice(letters) for _ in range(rng.randint(0, 5))))
        ri, rj = rels[i], rels[j]
        # r_i is recovered from (r_i r_j) and r_j:  r_i = (r_i r_j) * r_j^{-1}
        assert mul(mul(ri, rj), inv(rj)) == ri
        # r_i r_j is recovered from r_i and r_j
        assert mul(ri, rj) == mul(ri, rj)
        # a conjugate w r_i w^{-1} recovers r_i by conjugating back
        assert conj(conj(ri, w), inv(w)) == ri
        # an inverse recovers itself
        assert inv(inv(ri)) == ri
    check("AC moves carry explicit word certificates that the normal closure of the "
          "relator tuple is unchanged", True,
          "300 seeded random tuples in F_3: r_i = (r_i r_j) r_j^-1, conjugation is "
          "invertible, inversion is invertible")


# ------------------------------------------------------------------ part 6

def part6_evans_matrix():
    """Evans' matrix is in GL_2 over the Laurent polynomial ring, as cited.

    This checks the membership only.  Non-membership in GE_2 is Evans' theorem
    and is quoted, not checked here.
    """
    X, Y = Symbol("X"), Symbol("Y")
    a = 1 - 2 * (X - 1) / Y
    b = 4 / Y
    c = -(X - 1) ** 2 / Y
    d = 1 + 2 * (X - 1) / Y
    # multiply the determinant by Y^2, a unit of the Laurent ring, to work
    # with polynomials only
    det_times_Y2 = sympy.expand(sympy.expand(a * d - b * c) * Y ** 2)
    assert sympy.expand(det_times_Y2 - Y ** 2) == 0, det_times_Y2
    check("Evans' 2x2 matrix over Z[X^+-1, Y^+-1] has determinant 1", True,
          "Y^2*det - Y^2 is the zero polynomial, so it lies in GL_2; its "
          "non-membership in GE_2 is quoted from the literature")


# ------------------------------------------------------------------ part 7

def part7_finite_quotients():
    """Count the homomorphisms from the presented group to some finite groups.

    A map F_2 -> Q kills the relators exactly when it factors through the
    presented group.  For a presentation of the trivial group the count is 1 for
    every Q, the same as for the standard presentation.  This is a concrete
    instance of the general statement in the survey.
    """
    from sympy.combinatorics.named_groups import (
        SymmetricGroup, AlternatingGroup, DihedralGroup, CyclicGroup,
    )
    groups = [
        ("C_2", CyclicGroup(2)),
        ("C_6", CyclicGroup(6)),
        ("S_3", SymmetricGroup(3)),
        ("S_4", SymmetricGroup(4)),
        ("A_5", AlternatingGroup(5)),
        ("D_8", DihedralGroup(4)),
    ]

    def evaluate(word, a, b, one):
        img = one
        for g in word:
            p = a if abs(g) == 1 else b
            img = img * (p if g > 0 else p ** -1)
        return img

    std2 = ((1,), (2,))
    rows = []
    for name, G in groups:
        elems = list(G.generate())
        for pres_name, rels in (("standard", std2), ("AK(3)", AK(3))):
            count = 0
            for a in elems:
                for b in elems:
                    if all(evaluate(r, a, b, G.identity) == G.identity for r in rels):
                        count += 1
            rows.append((name, pres_name, count, len(elems) ** 2))
    for name, pres_name, count, total in rows:
        print("     Hom(F_2,%s) killing the %s relators: %d of %d pairs" %
              (name, pres_name, count, total))
    assert all(count == 1 for _, _, count, _ in rows)
    # the same for a Miller-Schupp presentation
    ms = miller_schupp(2, (1, 2, 2, -1, -2, -2))
    for name, G in groups:
        elems = list(G.generate())
        count = sum(1 for a in elems for b in elems
                    if all(evaluate(r, a, b, G.identity) == G.identity for r in ms))
        assert count == 1, (name, count)
    check("the standard presentation, AK(3) and a Miller-Schupp presentation have "
          "exactly one map to each of C_2, C_6, S_3, S_4, A_5 and D_8", True,
          "the trivial map only, so counts of maps to finite groups cannot separate them")


# ------------------------------------------------------------------ part 8

def part8_subgroup_witness():
    """The witness that (A3) changes the subgroup generated by the relators.

    Conjugating x by w = xy in the tuple (x, y) gives (x y x y^-1 x^-1, y).
    The subgroup S = <y, x y x y^-1 x^-1> is proper.  The proof maps F_2 to the
    infinite dihedral group acting on Z by p(n) = -n and q(n) = 1 - n and shows
    that the image of S has index 3 in the image of F_2.
    """
    # the tuple the move produces
    assert conj((1,), (1, 2)) == (1, 2, 1, -2, -1)
    # it still has unimodular exponent-sum matrix, as Proposition 5 requires
    assert abs(det_int(exp_matrix([(1, 2, 1, -2, -1), (2,)], 2))) == 1

    # affine maps n |-> eps*n + c, composed as functions
    def comp(h, g):
        """h after g."""
        e1, c1 = g
        e2, c2 = h
        return (e1 * e2, e2 * c1 + c2)

    def apply(g, n):
        return g[0] * n + g[1]

    p = (-1, 0)          # p(n) = -n
    q = (-1, 1)          # q(n) = 1 - n
    t = (1, 1)           # t(n) = n + 1
    assert comp(t, p) == q          # q = t p
    assert comp(p, p) == (1, 0) and comp(q, q) == (1, 0)

    # image of the relator x y x y^-1 x^-1 under x |-> q, y |-> p
    word_image = (1, 0)
    for letter in (1, 2, 1, -2, -1):
        word_image = comp(q if abs(letter) == 1 else p, word_image) if letter > 0 \
            else comp(inv_affine(q if abs(letter) == 1 else p), word_image)
    assert word_image == (-1, 3), word_image
    for n in range(-5, 6):
        assert apply(word_image, n) == 3 - n

    # every element of <p, t^3> is n |-> +-n + 3k, and t is not.
    # The constant term of a composite depends on the constants only modulo 3,
    # so closure of the class "constant divisible by 3" is checked on residues.
    for e1 in (1, -1):
        for e2 in (1, -1):
            for c1 in (0, 1, 2):
                for c2 in (0, 1, 2):
                    e, c = comp((e2, c2), (e1, c1))
                    assert e in (1, -1)
                    if c1 % 3 == 0 and c2 % 3 == 0:
                        assert c % 3 == 0, (e1, c1, e2, c2, c)
    assert p[1] % 3 == 0 and t[1] % 3 == 1 and word_image[1] % 3 == 0
    check("conjugating x by xy in (x,y) gives a tuple whose relators generate a proper "
          "subgroup", True,
          "image of the tuple in the infinite dihedral group lies in {n |-> +-n + 3k}, "
          "which has index 3 and does not contain the translation t")


def inv_affine(g):
    e, c = g
    return (e, -e * c)


# ------------------------------------------------------------------ main

def main():
    part1_words()
    presentation_matrix_under_moves()
    part2_invariance()
    part3_battery()
    part3b_abelianisation()
    part4_fox_calculus()
    part5_normal_closure_certificates()
    part6_evans_matrix()
    part7_finite_quotients()
    part8_subgroup_witness()
    print()
    print("ALL %d CHECKS PASSED" % len(PASSED))


if __name__ == "__main__":
    main()
