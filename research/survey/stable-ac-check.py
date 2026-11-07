#!/usr/bin/env python3
"""Deterministic checks for the stable Andrews-Curtis (AC) move set.

Nothing here is a new mathematical claim.  The script exists to make the
definitions used in survey/stable-ac.md executable and to check, on small
explicit examples, three things:

  1. that an explicit sequence of the five stable AC moves really does take
     the stated presentation to the empty one, so the example is certified
     to present the trivial group (AC moves are Tietze transformations);
  2. that the side condition on the deletion move (AC5) is enforced, and
     that dropping it would be unsound;
  3. that every move preserves the abelianisation of the presented group,
     computed by Smith normal form.  This is a genuine cross-check of the
     move implementation: a bug that changed the group would be caught.

Run:  python3 stable_ac_check.py
No dependencies outside the Python standard library.  Deterministic: the
only randomness is random.Random(20240601).
"""

import random

# ---------------------------------------------------------------- free group
# A word in F_n is a tuple of nonzero ints.  The int k means generator
# |k|, with exponent +1 if k > 0 and -1 if k < 0.

def reduce_word(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def mul(a, b):
    return reduce_word(tuple(a) + tuple(b))


def inv(a):
    return tuple(-x for x in reversed(a))


def conj(w, r):
    """w * r * w^{-1}"""
    return mul(mul(w, r), inv(w))


def expvec(w, n):
    v = [0] * n
    for a in w:
        v[abs(a) - 1] += 1 if a > 0 else -1
    return v


def word_str(w):
    if not w:
        return "1"
    return "".join(("x%d" % abs(a)) + ("" if a > 0 else "^-1") for a in w)


def pres_str(p):
    n, rels = p
    gens = ",".join("x%d" % (i + 1) for i in range(n))
    return "<%s | %s>" % (gens, ", ".join(word_str(r) for r in rels))

# ------------------------------------------------------------- presentations
# A presentation is a pair (n, rels): n >= 0 generators x_1..x_n and a tuple
# of relators, each a reduced word in F_n.  Balanced means len(rels) == n.

def check_valid(p):
    n, rels = p
    assert n >= 0
    assert len(rels) == n, "presentation must be balanced"
    for r in rels:
        assert r == reduce_word(r), "relator not reduced: %r" % (r,)
        for a in r:
            assert 1 <= abs(a) <= n, "letter out of range in %r" % (r,)
    return True


class IllegalMove(Exception):
    pass


def do_move(p, mv):
    """Apply one stable AC move.  Raises IllegalMove if the move is not legal."""
    n, rels = p
    kind = mv[0]
    if kind == "AC1":                     # r_i -> r_i^{-1}
        i = mv[1]
        if not (0 <= i < len(rels)):
            raise IllegalMove("AC1 index out of range")
        new = list(rels)
        new[i] = inv(rels[i])
        return (n, tuple(new))
    if kind == "AC2":                     # r_i -> r_i r_j, i != j
        i, j = mv[1], mv[2]
        if not (0 <= i < len(rels) and 0 <= j < len(rels)):
            raise IllegalMove("AC2 index out of range")
        if i == j:
            raise IllegalMove("AC2 needs i != j")
        new = list(rels)
        new[i] = mul(rels[i], rels[j])
        return (n, tuple(new))
    if kind == "AC3":                     # r_i -> w r_i w^{-1}
        i, w = mv[1], tuple(mv[2])
        if not (0 <= i < len(rels)):
            raise IllegalMove("AC3 index out of range")
        if w != reduce_word(w):
            raise IllegalMove("AC3 conjugator not reduced")
        for a in w:
            if not (1 <= abs(a) <= n):
                raise IllegalMove("AC3 conjugator uses a missing generator")
        new = list(rels)
        new[i] = conj(w, rels[i])
        return (n, tuple(new))
    if kind == "AC4":                     # add generator x_{n+1} and relator x_{n+1}
        if mv[1:] != ():
            raise IllegalMove("AC4 takes no arguments")
        new_rels = rels + ((n + 1,),)
        return (n + 1, new_rels)
    if kind == "AC5":                     # inverse of AC4, with its side condition
        i = mv[1]
        if not (0 <= i < len(rels)):
            raise IllegalMove("AC5 index out of range")
        r = rels[i]
        if len(r) != 1 or r[0] < 0:
            raise IllegalMove("AC5 needs a relator that is a single generator")
        j = r[0]
        for k, other in enumerate(rels):
            if k == i:
                continue
            if any(abs(a) == j for a in other):
                raise IllegalMove(
                    "AC5 refused: generator x%d occurs in another relator" % j)
        new_rels = []
        for k, other in enumerate(rels):
            if k == i:
                continue
            new_rels.append(tuple(a - 1 if a > j else (a + 1 if a < -j else a)
                                  for a in other))
        return (n - 1, tuple(new_rels))
    raise IllegalMove("unknown move %r" % (mv,))


def replay(p, moves, verbose=False):
    for k, mv in enumerate(moves):
        p = do_move(p, mv)
        check_valid(p)
        if verbose:
            print("   %2d. %-28s %s" % (k + 1, str(mv), pres_str(p)))
    return p

# ------------------------------------------- smith normal form over Z (small)

def smith_invariants(mat):
    """Return (rank, invariant factors > 1) of an integer matrix' cokernel."""
    if not mat:
        return 0, []
    m = [list(row) for row in mat]
    rows, cols = len(m), len(m[0])
    t = 0
    while t < min(rows, cols):
        # find a nonzero entry in the remaining block
        piv = None
        for i in range(t, rows):
            for j in range(t, cols):
                if m[i][j] != 0 and (piv is None or abs(m[i][j]) < abs(m[piv[0]][piv[1]])):
                    piv = (i, j)
        if piv is None:
            break
        i, j = piv
        m[t], m[i] = m[i], m[t]
        for row in m:
            row[t], row[j] = row[j], row[t]
        progress = True
        while progress:
            progress = False
            for i in range(t + 1, rows):
                if m[i][t] != 0:
                    q = m[i][t] // m[t][t]
                    for k in range(t, cols):
                        m[i][k] -= q * m[t][k]
                    if m[i][t] != 0:
                        m[t], m[i] = m[i], m[t]
                        progress = True
                        break
            if progress:
                continue
            for j in range(t + 1, cols):
                if m[t][j] != 0:
                    q = m[t][j] // m[t][t]
                    for k in range(t, rows):
                        m[k][j] -= q * m[k][t]
                    if m[t][j] != 0:
                        for row in m:
                            row[t], row[j] = row[j], row[t]
                        progress = True
                        break
            if progress:
                continue
            done = True
            for i in range(t + 1, rows):
                for j in range(t + 1, cols):
                    if m[i][j] % m[t][t] != 0:
                        for k in range(t, cols):
                            m[t][k] += m[i][k]
                        done = False
                        break
                if not done:
                    break
            if not done:
                progress = True
        t += 1
    diag = [abs(m[i][i]) for i in range(t)]
    rank = sum(1 for d in diag if d != 0)
    return rank, [d for d in diag if d > 1]


def abelianisation(p):
    """Isomorphism type of the abelianisation: (free rank, torsion factors)."""
    n, rels = p
    mat = [expvec(r, n) for r in rels]
    if not mat:
        return n, []
    rank, inv = smith_invariants(mat)
    return n - rank, inv


def ab_str(a):
    fr, tor = a
    parts = []
    if fr:
        parts.append("Z" + ("^%d" % fr if fr > 1 else ""))
    parts += ["Z/%d" % d for d in tor]
    return " x ".join(parts) if parts else "trivial"

# ---------------------------------------------------------------------- tests

FAILED = []


def check(name, cond, detail=""):
    if cond:
        print("PASS  %s%s" % (name, ("  [" + detail + "]") if detail else ""))
    else:
        print("FAIL  %s%s" % (name, ("  [" + detail + "]") if detail else ""))
        FAILED.append(name)


def main():
    print("stable Andrews-Curtis move checks; python3, stdlib only")
    print("=" * 74)

    # ---- 0. Smith normal form self-tests -------------------------------
    print("\n[0] Smith normal form self-tests")
    check("snf diag(2,3) = diag(1,6)", smith_invariants([[2, 0], [0, 3]]) == (2, [6]),
          str(smith_invariants([[2, 0], [0, 3]])))
    check("snf [[2,4],[6,8]] = diag(2,4)", smith_invariants([[2, 4], [6, 8]]) == (2, [2, 4]),
          str(smith_invariants([[2, 4], [6, 8]])))
    check("snf [[1]] = diag(1)", smith_invariants([[1]]) == (1, []))
    check("snf [[0]] is rank 0", smith_invariants([[0]]) == (0, []))

    # ---- 1. the standard presentation is stably AC-trivial -------------
    print("\n[1] standard balanced presentation, rank 3, reduced to the empty one")
    std3 = (3, ((1,), (2,), (3,)))
    check_valid(std3)
    print("   start: %s" % pres_str(std3))
    moves = [("AC5", 2), ("AC5", 1), ("AC5", 0)]
    end = replay(std3, moves, verbose=True)
    check("standard rank 3 --> empty presentation", end == (0, ()))
    check("abelianisation preserved along the way",
          abelianisation(end) == (0, []))

    # ---- 2. a non-standard example, with a conjugation step ------------
    print("\n[2] <x1,x2 | x1, x1 x2> reduced to the empty presentation")
    p = (2, ((1,), (1, 2)))
    check_valid(p)
    print("   start: %s" % pres_str(p))
    moves = [
        ("AC1", 0),                # r0 = x1     -> x1^-1
        ("AC2", 1, 0),             # r1 = x1 x2  -> x1 x2 x1^-1
        ("AC1", 0),                # r0 = x1^-1  -> x1
        ("AC3", 1, (-1,)),         # conjugate r1 by x1^-1, giving x2
        ("AC5", 1),                # delete the pair (x2, x2)
        ("AC5", 0),                # delete the pair (x1, x1)
    ]
    end = replay(p, moves, verbose=True)
    check("<x1,x2 | x1, x1 x2> --> empty", end == (0, ()))

    # ---- 3. the AC5 side condition is essential ------------------------
    print("\n[3] the deletion move refuses an illegal deletion")
    p = (2, ((1,), (1, 2)))
    try:
        do_move(p, ("AC5", 0))
        check("AC5 rejects deleting x1 while x1 occurs in x1 x2", False,
              "deletion was accepted")
    except IllegalMove as e:
        check("AC5 rejects deleting x1 while x1 occurs in x1 x2", True, str(e))
    # and the legal deletion in the same presentation is accepted once the
    # other relator no longer mentions x1
    p2 = (2, ((1,), (2,)))
    check("AC5 accepts a legal deletion", do_move(p2, ("AC5", 0)) == (1, ((1,),)))

    # ---- 4. a second, independent example ------------------------------
    print("\n[4] <x1,x2 | x1, x1^-1 x2> reduced to the empty presentation")
    p = (2, ((1,), (-1, 2)))
    print("   start: %s" % pres_str(p))
    moves = [("AC2", 1, 0), ("AC3", 1, (1,)), ("AC5", 1), ("AC5", 0)]
    end = replay(p, moves, verbose=True)
    check("<x1,x2 | x1, x1^-1 x2> --> empty", end == (0, ()))

    # ---- 5. every move preserves the abelianisation --------------------
    print("\n[5] abelianisation is invariant along move sequences")
    rng = random.Random(20240601)
    ok = True
    trials = 0
    for _ in range(400):
        n = rng.randint(1, 3)
        rels = []
        for _ in range(n):
            L = rng.randint(0, 5)
            rels.append(tuple(rng.choice([1, -1]) * rng.randint(1, n) for _ in range(L)))
        p = (n, tuple(reduce_word(r) for r in rels))
        before = abelianisation(p)
        for _ in range(4):
            kind = rng.choice(["AC1", "AC2", "AC3", "AC4"])
            if kind == "AC1":
                mv = ("AC1", rng.randrange(n))
            elif kind == "AC2":
                if n < 2:
                    continue
                i = rng.randrange(n)
                j = rng.randrange(n - 1)
                if j >= i:
                    j += 1
                mv = ("AC2", i, j)
            elif kind == "AC3":
                L = rng.randint(0, 3)
                w = reduce_word(tuple(rng.choice([1, -1]) * rng.randint(1, n)
                                      for _ in range(L)))
                mv = ("AC3", rng.randrange(n), w)
            else:
                mv = ("AC4",)
            p = do_move(p, mv)
            n = p[0]
            trials += 1
            if abelianisation(p) != before:
                ok = False
    check("abelianisation unchanged over %d random legal moves" % trials, ok)

    # ---- 6. conjugation by a word = iterated conjugation by letters ----
    print("\n[6] AC3 with an arbitrary word equals iterated AC3 by generators")
    rng = random.Random(7)
    ok = True
    for _ in range(200):
        n = 2
        r = tuple(rng.choice([1, -1]) * rng.randint(1, n) for _ in range(rng.randint(0, 5)))
        r = reduce_word(r)
        w = reduce_word(tuple(rng.choice([1, -1]) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 4))))
        p = (n, (r, (2,)))
        direct = do_move(p, ("AC3", 0, w))
        step = p
        for a in reversed(w):            # w r w^-1 = a1 (a2 (.. r ..) a2^-1) a1^-1
            step = do_move(step, ("AC3", 0, (a,)))
        ok = ok and direct == step
    check("iterated single-generator conjugations reproduce the word move", ok)

    # ---- 7. AC4 then AC5 is a round trip -------------------------------
    print("\n[7] stabilise then destabilise is the identity")
    p = (2, ((1, 2), (-2, 1, 1)))
    check("AC4 followed by AC5 returns the original presentation",
          do_move(do_move(p, ("AC4",)), ("AC5", 2)) == p)

    # ---- 8. a famous suspect, for the record ---------------------------
    print("\n[8] data for AK(3) = <x,y | xyx = yxy, x^3 = y^4>")
    x, y = 1, 2
    r1 = reduce_word(mul(mul((x, y, x), inv((y, x, y))), ()))
    r2 = reduce_word((x, x, x, -y, -y, -y, -y))
    ak3 = (2, (r1, r2))
    check_valid(ak3)
    print("   %s  with r1 = %s, r2 = %s" % (pres_str(ak3), word_str(r1), word_str(r2)))
    M = [expvec(r1, 2), expvec(r2, 2)]
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    print("   exponent-sum matrix %s, determinant %d" % (M, det))
    check("AK(3) exponent-sum matrix is unimodular", abs(det) == 1, "det = %d" % det)
    check("AK(3) abelianisation is trivial", abelianisation(ak3) == (0, []),
          ab_str(abelianisation(ak3)))
    print("   note: trivial abelianisation is necessary, not sufficient, for the")
    print("   group to be trivial; this script makes no claim about that group.")

    print("\n" + "=" * 74)
    if FAILED:
        print("FAILED: %d check(s): %s" % (len(FAILED), ", ".join(FAILED)))
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
