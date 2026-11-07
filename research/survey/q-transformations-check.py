#!/usr/bin/env python3
"""Checks supporting survey/q-transformations.md (member m10, swarm smw2fzjic).

Deterministic: every random choice uses random.Random(SEED).
Run:  python3 q-transformations-check.py
Each check prints "PASS <name>: <detail>" or "FAIL <name>: <detail>".

Data
----
A word in the free group F_n on x_1..x_n is a tuple of nonzero ints: the int k
is the letter x_k, -k is x_k^{-1}. A presentation is a pair (n, T) with n
generators and T a tuple of relators.

Basic moves, exactly the Q-transformations (26) of Hog-Angeloni-Metzler,
LMS Lecture Note Ser. 197, Ch. I, p. 21 (also Barmak, Algebr. Geom. Topol. 25
(2025) 345-355, moves (i)-(iii)):
  conj  R_j -> w R_j w^{-1}                   (26)a
  inv   R_j -> R_j^{-1}                       (26)b
  mulR  R_j -> R_j R_k, k != j                (26)c, right
Derived from these, and expanded into them where used:
  R_j -> R_k R_j  is  conj(R_j, R_k) then mulR(j,k);
  R_j -> R_j R_k^{-1} is inv(k), mulR(j,k), inv(k).
Q* adds (27), the elementary Nielsen transformations of the generators;
Q** adds (28), prolongation by a generator a with relator a, and its inverse.
"""
import random
import sys
from collections import deque

SEED = 20240601


# -------------------------------------------------------------- free group
def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def mul(a, b):
    return red(tuple(a) + tuple(b))


def inv(a):
    return tuple(-x for x in reversed(a))


def conj(w, c):
    """c w c^{-1}."""
    return mul(mul(c, w), inv(c))


def expsums(w, n):
    v = [0] * n
    for a in w:
        v[abs(a) - 1] += 1 if a > 0 else -1
    return tuple(v)


def normalise(P):
    return (P[0], tuple(red(r) for r in P[1]))


def is_standard(P):
    n, T = P
    return T == tuple((i + 1,) for i in range(n))


# ------------------------------------------------------- basic Q moves
def apply_move(P, mv):
    n, T = P
    kind = mv[0]
    if kind == "conj":
        _, j, w = mv
        return (n, T[:j] + (conj(T[j], w),) + T[j + 1:])
    if kind == "inv":
        _, j = mv
        return (n, T[:j] + (inv(T[j]),) + T[j + 1:])
    if kind == "mulR":
        _, j, k = mv
        assert j != k
        return (n, T[:j] + (mul(T[j], T[k]),) + T[j + 1:])
    raise ValueError(mv)


def basic_moves(P, conjlen=1):
    """All one-step Q moves on P, conjugators of length at most conjlen."""
    n, T = P
    out = []
    for j in range(n):
        out.append(("inv", j))
        for k in range(n):
            if k != j:
                out.append(("mulR", j, k))
    if conjlen:
        for w in words_up_to(n, conjlen):
            for j in range(n):
                out.append(("conj", j, w))
    return out


_WORDS = {}


def words_up_to(n, L):
    key = (n, L)
    if key not in _WORDS:
        out, cur = [()], [()]
        for _ in range(L):
            nxt = []
            for w in cur:
                for g in range(1, n + 1):
                    nxt.append(w + (g,))
                    nxt.append(w + (-g,))
            out.extend(nxt)
            cur = nxt
        _WORDS[key] = out
    return _WORDS[key]


# --------------------------------------------------- Q* and Q** moves
def nielsen_maps(n):
    """Elementary Nielsen transformations (27), as images of x_1..x_n."""
    out = []
    for i in range(n):
        base = [((g + 1),) for g in range(n)]
        im = list(base)
        im[i] = (-(i + 1),)
        out.append(tuple(im))
        for j in range(n):
            if j != i:
                im = list(base)
                im[i] = ((i + 1), (j + 1))
                out.append(tuple(im))
                im = list(base)
                im[i] = ((j + 1), (i + 1))
                out.append(tuple(im))
    return out


def apply_aut(images, w):
    out = ()
    for a in w:
        img = images[abs(a) - 1]
        out = mul(out, img if a > 0 else inv(img))
    return out


def qstar_move(P, images):
    n, T = P
    return (n, tuple(apply_aut(images, r) for r in T))


def prolong(P):
    n, T = P
    return (n + 1, T + ((n + 1,),))


def retract(P):
    n, T = P
    if n == 0 or not T or T[-1] != (n,):
        return None
    for r in T[:-1]:
        if n in [abs(a) for a in r]:
            return None
    return (n - 1, T[:-1])


# ------------------------------------------- Todd-Coxeter: order of the group
class TooBig(Exception):
    pass


def group_order(P, cap=100000):
    """Order of the group presented by P, by coset enumeration of the trivial
    subgroup; None if the enumeration needs more than cap cosets (infinite
    group, typically)."""
    n, T = P
    if n == 0:
        return 1
    par = [0]
    rows = {0: [-1] * (2 * n)}
    co = deque()
    work = deque((0, t) for t in range(len(T)))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    def mirror(i):
        return i ^ 1

    def idx(g, s):
        return 2 * g + (0 if s > 0 else 1)

    def push_relators(c):
        for t in range(len(T)):
            work.append((c, t))

    def merge(a, b):
        ra, rb = find(a), find(b)
        if ra == rb:
            return
        if ra > rb:
            ra, rb = rb, ra
        for i in range(2 * n):
            va, vb = rows[ra][i], rows[rb][i]
            if va == -1:
                rows[ra][i] = vb
            elif vb != -1 and find(va) != find(vb):
                co.append((va, vb))
        par[rb] = ra
        del rows[rb]
        push_relators(ra)

    def define(c, i):
        d = len(par)
        if d >= cap:
            raise TooBig
        par.append(d)
        rows[d] = [-1] * (2 * n)
        rows[c][i] = d
        rows[d][mirror(i)] = c
        push_relators(d)
        return d

    def step(c, i):
        v = rows[c][i]
        return define(c, i) if v == -1 else find(v)

    try:
        while True:
            while co:
                a, b = co.popleft()
                merge(a, b)
            if work:
                c, t = work.popleft()
                c = find(c)
                cur = c
                for a in T[t]:
                    cur = step(cur, idx(abs(a) - 1, 1 if a > 0 else -1))
                if find(cur) != find(c):
                    merge(c, cur)
                continue
            # table must be total: close it under all generators
            opened = False
            for c in list(rows):
                for i in range(2 * n):
                    if rows[c][i] == -1:
                        define(c, i)
                        opened = True
                        break
                if opened:
                    break
            if not opened:
                break
    except TooBig:
        return None
    return len(rows)


# ---------------------------------------------------------- linear algebra
def snf_diag(M):
    from sympy import Matrix, ZZ
    from sympy.matrices.normalforms import smith_normal_form
    S = smith_normal_form(Matrix(M), domain=ZZ)
    return tuple(int(S[i, i]) for i in range(min(S.shape)))


def expsum_matrix(P):
    n, T = P
    return [list(expsums(r, n)) for r in T]


def det2(M):
    return M[0][0] * M[1][1] - M[0][1] * M[1][0]


# --------------------------------------------- constructive reduction (lemma)
def reduce_presentation(P):
    """Explicit sequence of basic Q moves from P to the standard presentation.

    Hypothesis: relators 0..n-2 are single generators x_1..x_{n-1} up to sign
    and the exponent sum of x_n in the last relator is +-1 (so, if the group is
    trivial, P is AC-trivial).

    If the last relator is w = u x_g^{e} v with g < n, the letter x_g^{e} is
    deleted by left multiplication with the conjugate u x_g^{-e} u^{-1} of the
    relator x_g. That is six (four if e = -1) basic moves: invert and conjugate
    the helper relator x_g, conjugate and right multiply the relator w, then
    undo the two moves on the helper.
    """
    n, T = normalise(P)
    T = list(T)
    moves = []

    def do(mv):
        moves.append(mv)
        nonlocal T
        T = list(apply_move((n, tuple(T)), mv)[1])

    for j in range(n - 1):
        r = T[j]
        assert r in ((j + 1,), (-(j + 1),)), ("hypothesis fails", j, r)
        if r == (-(j + 1),):
            do(("inv", j))
    w = T[n - 1]
    guard = 0
    while any(abs(a) < n for a in w):
        guard += 1
        if guard > 5000:
            return None
        pos = next(k for k, a in enumerate(w) if abs(a) < n)
        a = w[pos]
        g = abs(a) - 1
        e = 1 if a > 0 else -1
        u, v = w[:pos], w[pos + 1:]
        flipped = e == 1
        if flipped:
            do(("inv", g))                  # helper x_g -> x_g^{-1}
        do(("conj", g, u))                  # helper -> u x_g^{-e} u^{-1} =: c
        do(("conj", n - 1, T[g]))           # w -> c w c^{-1}
        do(("mulR", n - 1, g))              # -> c w
        do(("conj", g, inv(u)))             # helper -> x_g^{-e}
        if flipped:
            do(("inv", g))                  # helper -> x_g
        w = T[n - 1]
        assert w == red(u + v), (w, red(u + v))
    e = expsums(w, n)[n - 1]
    if e not in (1, -1):
        return None
    if e == -1:
        do(("inv", n - 1))
    return moves, (n, tuple(T))


def replay(P, moves):
    cur = normalise(P)
    for mv in moves:
        cur = apply_move(cur, mv)
    return cur


# ------------------------------------------------------------------- checks
def main():
    rng = random.Random(SEED)
    fails = 0

    def report(name, ok, detail=""):
        nonlocal fails
        if not ok:
            fails += 1
        print(("PASS " if ok else "FAIL ") + name + (": " + detail if detail else ""))

    cases = [
        (red((1, -1, 2)), (2,)),
        (mul((1, 2), (-2, -1)), ()),
        (inv((1, 2, -1)), (1, -2, -1)),
        (conj((1,), (2,)), (2, 1, -2)),
        (expsums((1, 1, -1, 2, 2, -2), 2), (1, 1)),
        (red((1, -1)), ()),
    ]
    report("word_arithmetic", all(g == w for g, w in cases), "%d cases" % len(cases))

    AK3 = (2, (red((1, 2, 1) + inv((2, 1, 2))), red((1, 1, 1) + (-2, -2, -2, -2))))
    S3 = (2, ((1, 1), (2, 2), red((1, 2, 1, 2, 1, 2))))
    A5 = (2, ((1, 1), (2, 2, 2), red((1, 2) * 5)))
    Z5Z5 = (2, ((1, 1, 1, 1, 1), (2, 2, 2, 2, 2), red((1, 2, -1, -2))))

    ok, det = True, []
    for name, P in [("S3", S3), ("A5", A5), ("AK3", AK3), ("Z5xZ5", Z5Z5)]:
        base = snf_diag(expsum_matrix(P))
        cur = P
        for _ in range(40):
            cur = apply_move(cur, rng.choice(basic_moves(cur, conjlen=1)))
        got = snf_diag(expsum_matrix(cur))
        ok = ok and got == base
        det.append("%s %s" % (name, base))
    report("q_moves_preserve_expsum_snf", ok, "; ".join(det))

    ok, det = True, []
    for name, P, expect in [("S3", S3, 6), ("A5", A5, 60), ("Z5xZ5", Z5Z5, 25), ("AK3", AK3, 1)]:
        before = group_order(P)
        cur = P
        for _ in range(12):
            cur = apply_move(cur, rng.choice(basic_moves(cur, conjlen=1)))
        after = group_order(cur)
        good = before == after == expect
        ok = ok and good
        det.append("%s %s->%s (want %d)" % (name, before, after, expect))
    report("q_moves_preserve_group_order", ok, "; ".join(det))

    ok, det = True, []
    for name, P, expect in [("S3", S3, 6), ("A5", A5, 60), ("Z5xZ5", Z5Z5, 25)]:
        cur = P
        imgs = nielsen_maps(P[0])
        for _ in range(6):
            cur = qstar_move(cur, rng.choice(imgs))
        got = group_order(cur)
        ok = ok and got == expect
        det.append("%s -> %s" % (name, got))
    report("qstar_moves_preserve_group_order", ok, "; ".join(det))

    ok, det = True, []
    for name, P, expect in [("S3", S3, 6), ("Z5xZ5", Z5Z5, 25)]:
        q = prolong(P)
        a = group_order(q)
        back = retract(q)
        b = group_order(back) if back else None
        ok = ok and a == b == expect
        det.append("%s prolonged %s retracted %s" % (name, a, b))
    report("prolongation_preserves_group_order", ok, "; ".join(det))

    ok, det = True, []
    for nn in range(1, 7):
        r1 = red((1, 2, 1) + inv((2, 1, 2)))
        r2 = red((1,) * nn + (-2,) * (nn + 1))
        d = det2(expsum_matrix((2, (r1, r2))))
        ok = ok and abs(d) == 1
        det.append("AK(%d) det=%d" % (nn, d))
    report("AK_abelianization_trivial", ok, "; ".join(det))

    ok, det = True, []
    instances = [
        ("n=2 w=y x^2 y x^-1 y^-1", (2, ((1,), red((2, 1, 1, 2, -1, -2))))),
        ("n=2 w=y^-1 x y x y", (2, ((1,), red((-2, 1, 2, 1, 2))))),
        ("n=3 w=x1 x2 x3 x2^-1", (3, ((1,), (2,), red((1, 2, 3, -2))))),
    ]
    for name, P in instances:
        out = reduce_presentation(P)
        if out is None:
            ok = False
            det.append("%s: no reduction" % name)
            continue
        moves, end = out
        good = is_standard(end) and replay(P, moves) == end
        ok = ok and good
        det.append("%s: %d moves, %s" % (name, len(moves), "standard" if is_standard(end) else str(end)))
    report("constructive_reduction_instances", ok, "; ".join(det))

    ok, det = True, []
    for name, P, expect in [("<x|x^2>", (1, ((1, 1),)), 2),
                            ("<x|x^3>", (1, ((1, 1, 1),)), 3),
                            ("<x,y|y> infinite", (2, ((2,),)), None),
                            ("<x,y|xy> infinite", (2, (red((1, 2)),)), None)]:
        got = group_order(P, cap=5000)
        ok = ok and got == expect
        det.append("%s -> %s" % (name, got))
    report("group_order_sanity", ok, "; ".join(det))

    print()
    print("ALL 8 CHECKS PASSED" if fails == 0 else "%d CHECK(S) FAILED" % fails)
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
