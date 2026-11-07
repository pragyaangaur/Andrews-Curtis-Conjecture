#!/usr/bin/env python3
"""Checks for survey/special-classes.md -- Andrews-Curtis conjecture, direction D9, member m1.

A free-group word is a tuple of nonzero integers: 1 means x, -1 means x^-1,
2 means y, -2 means y^-1, 3 means z, -3 means z^-1, and so on.  Rank n uses
letters +-1 .. +-n.  A relator tuple is a tuple of words of length n.

Every computation here is exact integer arithmetic on reduced words.  The only
randomness is random.Random(SEED) with the fixed SEED printed at the start.

Checks (each prints a PASS or FAIL line):

  T1  Lemma 2: two entries of a relator tuple can be interchanged, ranks 2, 3.
  T2  Lemma 5: a generator relator lets one delete that letter from another
      relator, leaving the other entries untouched, ranks 2, 3.
  T3  Theorem 6, Corollary 7: every rank-2 tuple (x, w) whose y-exponent sum is
      +-1 is carried to the standard tuple by an explicit move sequence.
  T4  Corollary 8: every signed permutation of the generators of rank 2, 3, 4 is
      carried to the standard tuple by an explicit move sequence.
  T5  Lemma 4: |det| and the row lattice of the exponent-sum matrix are
      invariant under the AC moves.
  T6  The published 19-line reduction of AK(2) (Miasnikov, IJAC 9 (1999)
      671-686) replays line by line, and seven more moves reach (x, y).
  T7  Exponent-sum matrices of AK(2) and AK(3) are unimodular, and two tuples
      presenting Z have determinant 0.
  T8  Corollary 7 with a first relator that is a nontrivial conjugate of x.
  T9  Theorem 6 at rank 3: one generator relator lets the two other entries be
      reduced to their rho-images while the generator relator stays in place.

Usage: python3 special_classes_check.py
Exit status is 0 exactly when every check passed.
"""

import itertools
import random
import sys

SEED = 20261104


# ---------------------------------------------------------------- words

def reduce_word(w):
    """Free reduction of a word given as a tuple of nonzero ints."""
    out = []
    for letter in w:
        if letter == 0:
            raise ValueError("letter 0 is not a generator letter")
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inv(w):
    return tuple(-letter for letter in reversed(w))


def mul(u, v):
    return reduce_word(tuple(u) + tuple(v))


def conj(w, g):
    """g w g^-1."""
    return mul(mul(g, w), inv(g))


def expsum(w, n):
    """Exponent-sum vector: the image of w in Z^n."""
    v = [0] * n
    for letter in w:
        v[abs(letter) - 1] += 1 if letter > 0 else -1
    return tuple(v)


def is_reduced(w):
    return all(w[i] != -w[i + 1] for i in range(len(w) - 1))


def cyclic_reduce(w):
    """Return (p, c) with w = p c p^-1 and c cyclically reduced."""
    p = []
    while len(w) >= 1 and w[0] == -w[-1]:
        p.append(w[0])
        w = w[1:-1]
    return tuple(p), tuple(w)


def rotations(c):
    return [c[k:] + c[:k] for k in range(len(c))] if c else [()]


def cyclic_key(w):
    """Canonical form of the conjugacy class of a reduced word w.

    Two reduced words are conjugate in a free group if and only if their
    cyclically reduced forms are cyclic permutations of each other or of each
    other's inverse.
    """
    _, c = cyclic_reduce(w)
    return min(rotations(c) + rotations(inv(c)))


def conjugator(w, target):
    """Return g with g w g^-1 = target, or None if none was found."""
    p, c = cyclic_reduce(w)
    p2, c2 = cyclic_reduce(target)
    best = None
    for k in range(len(c)):
        if c[k:] + c[:k] == c2:
            best = inv(c[:k])
            break
    if best is None:
        return None
    g = mul(p2, best)
    g = mul(g, inv(p))
    if conj(w, g) == reduce_word(target):
        return g
    return None


def as_letters(s):
    """Turn a string such as 'a B a b A B' into a word (a=1, b=2, c=3)."""
    table = {"a": 1, "b": 2, "c": 3, "A": -1, "B": -2, "C": -3}
    return tuple(table[ch] for ch in s.split())


# ---------------------------------------------------------------- moves

# A move is ('inv', i), ('mul', i, j) with i != j, or ('conj', i, g). It
# replaces entry i of the tuple, exactly as in the three AC moves:
#   (1) r_i -> r_i^-1
#   (2) r_i -> r_i r_j       (i != j)
#   (3) r_i -> g r_i g^-1    (g any word in the generators)

def apply_move(t, move):
    t = list(t)
    kind = move[0]
    if kind == "inv":
        i = move[1]
        _check_index(len(t), i)
        t[i] = inv(t[i])
    elif kind == "mul":
        i, j = move[1], move[2]
        _check_index(len(t), i)
        _check_index(len(t), j)
        if i == j:
            raise ValueError("move (2) requires i != j")
        t[i] = mul(t[i], t[j])
    elif kind == "conj":
        i, g = move[1], move[2]
        _check_index(len(t), i)
        g = reduce_word(tuple(g))
        t[i] = conj(t[i], g)
    else:
        raise ValueError("unknown move %r" % (move,))
    return tuple(t)


def _check_index(n, i):
    if not (0 <= i < n):
        raise ValueError("entry index out of range")


def apply_moves(t, moves):
    for move in moves:
        t = apply_move(t, move)
    return t


# ---------------------------------------------------------------- checks

FAILED = []


def check(name, condition, detail=""):
    if condition:
        print("PASS %-3s %s" % (name, detail))
    else:
        print("FAIL %-3s %s" % (name, detail))
        FAILED.append(name)


def random_word(rng, rank, maxlen):
    """A random reduced word of length at most maxlen over the given rank."""
    length = rng.randrange(maxlen + 1)
    letters = ([k for k in range(1, rank + 1)] + [-k for k in range(1, rank + 1)])
    w = []
    for _ in range(length):
        while True:
            letter = rng.choice(letters)
            if not w or w[-1] != -letter:
                break
        w.append(letter)
    return tuple(w)


def swap_moves(a):
    """Elementary moves taking (a, b, rest) to (b, a, rest); Lemma 2.

    (a,b) -> (ab,b) -> (ab,a^-1) -> (aba^-1,a^-1) -> (aba^-1,a) -> (b,a).
    The second step multiplies r_2 by r_1^-1, which is three elementary moves
    (invert r_1, multiply, invert r_1 back), so the swap costs seven moves.
    """
    return [("mul", 0, 1),
            ("inv", 0), ("mul", 1, 0), ("inv", 0),
            ("mul", 0, 1),
            ("inv", 1),
            ("conj", 0, inv(a))]


def test_T1_permutation(rng):
    ok = True
    detail = ""
    for trial in range(200):
        rank = 2 if trial % 2 == 0 else 3
        a = random_word(rng, rank, 5)
        b = random_word(rng, rank, 5)
        rest = tuple(random_word(rng, rank, 3) for _ in range(rank - 2))
        start = (a, b) + rest
        end = apply_moves(start, swap_moves(a))
        if end != (b, a) + rest:
            ok = False
            detail = "rank %d, a=%s b=%s gave %s" % (rank, a, b, end)
            break
    check("T1", ok, detail or "Lemma 2 replayed on 200 random tuples (7 moves each)")


def delete_generator_letters(t, idx, gen=1, relator=0):
    """Delete every +-gen letter from entry idx, given entry relator = (gen,).

    A letter eps = +-gen at position k is removed in three moves, with x = gen,
    r = u x^eps v:
        r -> x^eps v u -> x^eps v u x^-eps -> v u
    by conjugation by u^-1, multiplication by x^-eps, conjugation by x^-eps.
    """
    t = list(t)
    moves = []
    if t[relator] != (gen,):
        raise ValueError("entry %d is not the generator letter" % relator)
    while True:
        w = t[idx]
        pos = next((k for k, letter in enumerate(w) if abs(letter) == gen), None)
        if pos is None:
            break
        u, eps, v = w[:pos], w[pos], w[pos + 1:]
        m1 = ("conj", idx, inv(u))
        t = list(apply_move(tuple(t), m1))
        moves.append(m1)
        if eps > 0:
            t = list(apply_move(tuple(t), ("inv", relator)))
            m = ("mul", idx, relator)
            t = list(apply_move(tuple(t), m))
            t = list(apply_move(tuple(t), ("inv", relator)))
            moves += [("inv", relator), m, ("inv", relator)]
        else:
            m = ("mul", idx, relator)
            t = list(apply_move(tuple(t), m))
            moves.append(m)
        m3 = ("conj", idx, (-eps,))
        t = list(apply_move(tuple(t), m3))
        moves.append(m3)
    return tuple(t), moves


def test_T2_deletion(rng):
    ok = True
    detail = ""
    for trial in range(120):
        rank = 2 if trial % 2 == 0 else 3
        r = random_word(rng, rank, 9)
        rest = tuple(random_word(rng, rank, 6) for _ in range(rank - 2))
        start = ((1,), r) + rest
        t, moves = delete_generator_letters(start, 1)
        rho = reduce_word(tuple(letter for letter in r if abs(letter) != 1))
        got = t[1]
        if got != rho:
            if cyclic_key(got) != cyclic_key(rho):
                ok = False
                detail = "rank %d, r=%s gave %s, not conjugate to %s" % (rank, r, got, rho)
                break
            g = conjugator(got, rho)
            if g is None:
                ok = False
                detail = "rank %d, r=%s: no conjugator from %s to %s" % (rank, r, got, rho)
                break
            fix = ("conj", 1, g)
            t = apply_move(t, fix)
            moves.append(fix)
        if t[1] != rho or t[0] != (1,) or t[2:] != rest:
            ok = False
            detail = "rank %d, r=%s ended %s" % (rank, r, t)
            break
    check("T2", ok, detail or "Lemma 5 replayed on 120 random relators (ranks 2, 3)")


def test_T3_rank2_generator_relator():
    limit = 8
    words = []
    for length in range(limit + 1):
        for w in itertools.product((-2, -1, 1, 2), repeat=length):
            if is_reduced(w):
                words.append(w)
    tested = 0
    longest = 0
    for w in words:
        if expsum(w, 2)[1] not in (1, -1):
            continue
        t, moves = delete_generator_letters(((1,), w), 1)
        if t[1] not in ((2,), (-2,)):
            check("T3", False, "w=%s gave %s" % (w, t))
            return
        if t[1] == (-2,):
            moves.append(("inv", 1))
            t = apply_move(t, ("inv", 1))
        if t != ((1,), (2,)):
            check("T3", False, "w=%s ended %s" % (w, t))
            return
        tested += 1
        longest = max(longest, len(moves))
    check("T3", True,
          "%d tuples (x, w) with |w| <= %d and y-exponent sum +-1, longest chain %d moves"
          % (tested, limit, longest))


def swap_entries(t, i, j):
    """Apply Lemma 2 to entries i and j of t."""
    a = t[i]
    moves = [("mul", i, j),
             ("inv", i), ("mul", j, i), ("inv", i),
             ("mul", i, j), ("inv", j), ("conj", i, inv(a))]
    return apply_moves(t, moves), moves


def test_T4_signed_permutations():
    ok = True
    detail = ""
    standard = tuple((k,) for k in range(1, 5))
    for rank in (2, 3, 4):
        for perm in itertools.permutations(range(1, rank + 1)):
            for signs in itertools.product((1, -1), repeat=rank):
                t = tuple((signs[k] * perm[k],) for k in range(rank))
                for i in range(rank):
                    j = next(k for k in range(i, rank) if abs(t[k][0]) == i + 1)
                    if j != i:
                        t, _ = swap_entries(t, i, j)
                    if t[i] == (-(i + 1),):
                        t = apply_move(t, ("inv", i))
                if t != standard[:rank]:
                    ok = False
                    detail = "rank %d: %s ended %s" % (rank, t, t)
                    break
    check("T4", ok, detail or "all signed permutations of rank 2, 3, 4 reach the standard tuple")


def exponent_matrix(t, n):
    return [list(expsum(w, n)) for w in t]


def det_of_int_matrix(m):
    """Exact determinant by fraction-free Bareiss elimination."""
    m = [row[:] for row in m]
    n = len(m)
    if n == 0:
        return 1
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if pivot is None:
                return 0
            m[k], m[pivot] = m[pivot], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
        for i in range(k + 1, n):
            m[i][k] = 0
    return sign * m[n - 1][n - 1]


def rows_in_lattice(a, b):
    """Every row of b lies in the Z-row-lattice of a (square a with det != 0).

    The test is that b * a^-1 is integral; a^-1 = adj(a)/det(a), so everything
    below is exact integer arithmetic.
    """
    n = len(a)
    det = det_of_int_matrix(a)
    if det == 0:
        return False
    adj_t = [[0] * n for _ in range(n)]
    for j in range(n):
        for i in range(n):
            minor = [[a[r][c] for c in range(n) if c != j] for r in range(n) if r != i]
            cof = det_of_int_matrix(minor) if n > 1 else 1
            if (i + j) % 2:
                cof = -cof
            adj_t[j][i] = cof
    for row in b:
        for j in range(n):
            total = sum(row[i] * adj_t[i][j] for i in range(n))
            if total % det != 0:
                return False
    return True


def random_move(rng, t):
    n = len(t)
    kind = rng.choice(("inv", "mul", "conj"))
    i = rng.randrange(n)
    if kind == "inv":
        return ("inv", i)
    if kind == "mul":
        j = rng.randrange(n - 1)
        if j >= i:
            j += 1
        return ("mul", i, j)
    return ("conj", i, random_word(rng, n, 3))


def test_T5_exponent_sums(rng):
    ok = True
    detail = ""
    for trial in range(60):
        n = 2 if trial % 2 == 0 else 3
        t = tuple(random_word(rng, n, 6) for _ in range(n))
        a0 = exponent_matrix(t, n)
        d0 = abs(det_of_int_matrix(a0))
        for _ in range(25):
            t = apply_move(t, random_move(rng, t))
        a1 = exponent_matrix(t, n)
        d1 = abs(det_of_int_matrix(a1))
        if d0 != d1:
            ok = False
            detail = "|det| changed %d -> %d" % (d0, d1)
            break
        if d0 != 0 and not (rows_in_lattice(a0, a1) and rows_in_lattice(a1, a0)):
            ok = False
            detail = "row lattice changed at rank %d" % n
            break
    check("T5", ok, detail or "|det| and row lattice preserved along 60 walks of 25 moves")


def test_T6_ak2_replay():
    """Replay the published 19-line reduction of AK(2) from Miasnikov (1999)."""
    a, b = 1, 2
    r0 = as_letters("a a B B B")          # a^2 b^-3
    r1 = as_letters("a b a B A B")        # a b a b^-1 a^-1 b^-1
    script = [
        (("inv", 0), "b b b A A", None),
        (("mul", 1, 0), None, "a b a B A b b A A"),
        (("conj", 1, (-a,)), None, "b a B A b b A"),
        (("conj", 1, (-b,)), None, "a B A b b A b"),
        (("conj", 0, (-a,)), "A b b b A", None),
        (("mul", 0, 1), "A b b A b b A b", None),
        (("conj", 1, (-b,)), None, "B a B A b b A b b"),
        (("mul", 1, 0), None, "B a B A b b A b b A b b A b b A b"),
        (("conj", 1, as_letters("b A b")), None, "A b b A b b A b b A b"),
        (("inv", 0), "B a B B a B B a", None),
        (("mul", 1, 0), None, "A b b"),
        (("mul", 0, 1), "B a B B a", None),
        (("mul", 0, 1), "B a", None),
        (("mul", 0, 1), "b", None),
        (("inv", 0), "B", None),
        (("mul", 1, 0), None, "A b"),
        (("mul", 1, 0), None, "A"),
        (("inv", 1), None, "a"),
        (("inv", 0), "b", None),
    ]
    t = (r0, r1)
    for k, (move, want0, want1) in enumerate(script, start=1):
        t = apply_move(t, move)
        if want0 is not None and t[0] != as_letters(want0):
            check("T6", False, "line %d: r0 = %s, expected %s" % (k, t[0], as_letters(want0)))
            return
        if want1 is not None and t[1] != as_letters(want1):
            check("T6", False, "line %d: r1 = %s, expected %s" % (k, t[1], as_letters(want1)))
            return
    t = apply_moves(t, swap_moves(t[0]))
    if t != ((a,), (b,)):
        check("T6", False, "final tuple %s is not the standard one" % (t,))
        return
    check("T6", True, "19 published lines replay exactly, then 7 moves give (a, b)")


def test_T7_named_families():
    ak2 = (as_letters("a a B B B"), as_letters("a b a B A B"))
    ak3 = (as_letters("a b a B A B"), as_letters("a a a B B B B"))
    d2 = det_of_int_matrix(exponent_matrix(ak2, 2))
    d3 = det_of_int_matrix(exponent_matrix(ak3, 2))
    # two tuples presenting Z, which Lemma 4(d) says cannot be AC-standard
    nonstd1 = ((1,), ())                          # (x, 1) at rank 2
    nonstd2 = (as_letters("a b A B"), (2,))       # ([x,y], y) at rank 2
    e1 = det_of_int_matrix(exponent_matrix(nonstd1, 2))
    e2 = det_of_int_matrix(exponent_matrix(nonstd2, 2))
    check("T7", abs(d2) == 1 and abs(d3) == 1 and e1 == 0 and e2 == 0,
          "det AK(2) = %d, det AK(3) = %d, det(x,1) = %d, det([x,y],y) = %d"
          % (d2, d3, e1, e2))


def test_T8_conjugate_relator(rng):
    """Corollary 7 with a relator conjugate to a generator rather than equal to one."""
    ok = True
    detail = ""
    tested = 0
    for trial in range(600):
        w = random_word(rng, 2, 4)
        r1 = conj((1,), w)
        if r1 == (1,):
            continue
        r2 = random_word(rng, 2, 6)
        if expsum(r2, 2)[1] not in (1, -1):
            continue
        t = (r1, r2)
        if r1 == (-1,):
            t = apply_move(t, ("inv", 0))
        else:
            g = conjugator(r1, (1,))
            if g is None:
                ok = False
                detail = "no conjugator from %s to x" % (r1,)
                break
            t = apply_move(t, ("conj", 0, g))
        if t[0] != (1,):
            ok = False
            detail = "conjugation gave %s, expected x" % (t[0],)
            break
        t, _ = delete_generator_letters(t, 1)
        if t[1] not in ((2,), (-2,)):
            ok = False
            detail = "r2=%s gave %s" % (r2, t[1])
            break
        if t[1] == (-2,):
            t = apply_move(t, ("inv", 1))
        if t != ((1,), (2,)):
            ok = False
            detail = "r1=%s r2=%s ended %s" % (r1, r2, t)
            break
        tested += 1
    check("T8", ok, detail or "Corollary 7 with r_1 conjugate to x, %d random cases" % tested)


def test_T9_rank3_two_entries(rng):
    """Theorem 6 at rank 3: reduce both other entries, keeping the generator relator."""
    ok = True
    detail = ""
    for trial in range(80):
        r2 = random_word(rng, 3, 7)
        r3 = random_word(rng, 3, 7)
        t = ((1,), r2, r3)
        targets = [reduce_word(tuple(letter for letter in w if abs(letter) != 1))
                   for w in (r2, r3)]
        for idx in (1, 2):
            t, _ = delete_generator_letters(t, idx)
        for idx, target in zip((1, 2), targets):
            if t[idx] != target:
                if cyclic_key(t[idx]) != cyclic_key(target):
                    ok = False
                    detail = "entry %d: %s is not conjugate to %s" % (idx, t[idx], target)
                    break
                g = conjugator(t[idx], target)
                if g is None:
                    ok = False
                    detail = "entry %d: no conjugator from %s to %s" % (idx, t[idx], target)
                    break
                t = apply_move(t, ("conj", idx, g))
            if t[idx] != target:
                ok = False
                detail = "entry %d ended %s" % (idx, t[idx])
                break
        if not ok:
            break
        if t[0] != (1,):
            ok = False
            detail = "the generator relator changed to %s" % (t[0],)
            break
    check("T9", ok, detail or "Theorem 6 at rank 3, 80 random pairs of relators, other entries fixed")


def main():
    rng = random.Random(SEED)
    print("special_classes_check.py  (seed %d)" % SEED)
    test_T1_permutation(rng)
    test_T2_deletion(rng)
    test_T3_rank2_generator_relator()
    test_T4_signed_permutations()
    test_T5_exponent_sums(rng)
    test_T6_ak2_replay()
    test_T7_named_families()
    test_T8_conjugate_relator(rng)
    test_T9_rank3_two_entries(rng)
    print()
    if FAILED:
        print("FAILED: %s" % ", ".join(sorted(set(FAILED))))
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
