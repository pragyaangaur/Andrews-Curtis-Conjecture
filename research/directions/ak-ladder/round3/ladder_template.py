"""A uniform construction of the ladder step MS(n,w_k) -> MS(n,w_(k+1)).

Relator 1 is A = x^-1 y^n x y^-(n+1), relator 2 is B_k = x^-1 y^-k x^-1 y x y.
Put u = x^-1 y^n x.  Then

    c = (u B_k u^-1)^-1 B_(k+1)

lies in the normal closure N(A) of A in F_2: it is trivial in the quotient
G = <x,y | A>, which hnf.py decides by Britton reduction (G is the ascending
HNN extension <y,t | t y^n t^-1 = y^(n+1)> with t = x^-1).

The moves used are: conjugate relator 2 by u (one move), then multiply relator
2 by a product of conjugates of relator 1, and no final conjugation.  That
sequence is legal because multiplying relator 2 by w A^p w^-1 is
conj(1,w), mul(2,1)^p, conj(1,w^-1) (with inv(1) twice when p < 0), and it
leaves relator 1 equal to A at the end.

The factorization of c into conjugates of A is computed from the Britton
reduction, using three exact identities (all checked by the assertion in
factor_check below):

 (s=-1,q>0) x^-1 y^(nq) x y^(-(n+1)q)       = prod_{j<q} (y^((n+1)j) A y^(-(n+1)j))
             (because x^-1 y^(nq) x = prod_{j<q} (x^-1 y^n x) as words)
 (P)     x y^((n+1)q) x^-1 y^(-nq)          = prod_{j<q} (y^(jn) x) A^-1 (y^(jn) x)^-1
 (N)     x y^(-(n+1)r) x^-1 y^(nr)          = prod_{j<r} (y^(-(j+1)n) x) A (y^(-(j+1)n) x)^-1

so every correction is an explicit product of conjugates of A, with no search.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))


import acx
import hnf


def A_of(n):
    return (-1,) + tuple([2] * n) + (1,) + tuple([-2] * (n + 1))


def ypow(e):
    return tuple([2] * e) if e >= 0 else tuple([-2] * (-e))


def first_redex(c, n):
    for i in range(len(c)):
        if c[i] in (1, -1):
            s = c[i]
            j = i + 1
            m = 0
            while j < len(c) and c[j] in (2, -2):
                m += 1 if c[j] == 2 else -1
                j += 1
            if m != 0 and j < len(c) and c[j] == -s:
                if (s == -1 and m % n == 0) or (s == 1 and m % (n + 1) == 0):
                    return (i, j + 1, s, m)
    return None


def factors_of(c, n, trace=False):
    """Exact factorization of c in N(A_n): list of (W, p) with factor W A^p W^-1."""
    out = []
    c = hnf.reduce_free(c)
    while c:
        r = first_redex(c, n)
        if r is None:
            raise ValueError("word not Britton-reducible, so not in N(A): %r" % (c,))
        i, j, s, m = r
        P, Q = c[:i], c[j:]
        if s == -1:
            q = m // n
            e = m * (n + 1) // n
            if q > 0:
                for jj in range(q):
                    out.append((hnf.reduce_free(P + tuple([2] * ((n + 1) * jj))), 1))
            else:
                for jj in range(-q):
                    out.append((hnf.reduce_free(P + tuple([-2] * ((n + 1) * (jj + 1)))), -1))
            c = hnf.reduce_free(P + ypow(e) + Q)
            if trace:
                print("   [x^-1 y^%d x] -> y^%d  q=%d from P=%s" % (m, e, q, P))
        else:
            q = m // (n + 1)
            e = m * n // (n + 1)
            if q > 0:
                for jj in range(q):
                    out.append((hnf.reduce_free(P + tuple([2] * (jj * n)) + (1,)), -1))
            else:
                for jj in range(-q):
                    out.append((hnf.reduce_free(P + tuple([-2] * ((jj + 1) * n)) + (1,)), 1))
            c = hnf.reduce_free(P + ypow(e) + Q)
            if trace:
                print("   [x y^%d x^-1] -> y^%d  %d factors from P=%s" % (m, e, abs(q), P))
    return out


def factor_check(c, n, fs):
    """Assert c = product of the factors, as reduced words."""
    A = A_of(n)
    prod = ()
    for W, p in fs:
        f = hnf.reduce_free(tuple(W) + (tuple(A) * p if p >= 0 else tuple(hnf.inv(A)) * (-p)))
        f = hnf.reduce_free(f + tuple(hnf.inv(W)))
        prod = hnf.mul(prod, f)
    return prod == hnf.reduce_free(c)


def factor_moves(W, p):
    mv = []
    if W:
        mv.append(("conj", 1, tuple(W)))
    if p < 0:
        mv.append(("inv", 1))
    for _ in range(abs(p)):
        mv.append(("mul", 2, 1))
    if p < 0:
        mv.append(("inv", 1))
    if W:
        mv.append(("conj", 1, hnf.inv(W)))
    return mv


def correction(n, k, u=None):
    Bk = acx.ms(n, acx.w_word(k))[1]
    Bk1 = acx.ms(n, acx.w_word(k + 1))[1]
    if u is None:
        u = (-1,) + tuple([2] * n) + (1,)
    return u, hnf.mul(hnf.inv(hnf.mul(hnf.mul(u, Bk), hnf.inv(u))), Bk1)


def ladder_cert(n, k, u=None, trace=False):
    A = A_of(n)
    u, c = correction(n, k, u)
    if hnf.reduce_G(c, n) != ():
        return None
    fs = factors_of(c, n, trace=trace)
    if not factor_check(c, n, fs):
        raise AssertionError("factorization is not exact for n=%d k=%d" % (n, k))
    mv = [("conj", 2, u)]
    for W, p in fs:
        mv.extend(factor_moves(W, p))
    return mv


def check(n, k, u=None, trace=False):
    start = acx.ms(n, acx.w_word(k))
    target = acx.ms(n, acx.w_word(k + 1))
    mv = ladder_cert(n, k, u, trace)
    if mv is None:
        return ("NOT-IN-NA", 0, 0)
    rs = tuple(start)
    maxlen = acx.total_length(rs)
    for m in mv:
        rs = acx.apply_move(rs, m, 2)
        maxlen = max(maxlen, acx.total_length(rs))
    return (rs == tuple(target), len(mv), maxlen)


if __name__ == "__main__":
    import sys
    ns = [int(a) for a in sys.argv[1:]] or list(range(3, 9))
    bad = []
    for n in ns:
        for k in range(1, n - 1):
            ok, nmv, mx = check(n, k)
            print("n=%2d k=%2d  moves %3d  max total %3d  replay %s"
                  % (n, k, nmv, mx, ok), flush=True)
            if not ok:
                bad.append((n, k))
    print("all ok" if not bad else "FAILED %r" % (bad,))


def uniform_moves(n):
    """The ten-move ladder template, with k nowhere in it.

    Verified to take MS(n,w_k) to MS(n,w_(k+1)) for every k with 1 <= k <= n-2,
    for n = 3..60.  The three blocks multiply relator 2 by A, by
    (y^n x^-1 y^-(n+1) x) A (y^n x^-1 y^-(n+1) x)^-1, and by
    (y^-1) A^-1 (y^-1)^-1, after conjugating relator 2 by x^-1 y^n x.
    """
    A = A_of(n)
    u = (-1,) + tuple([2] * n) + (1,)
    W2 = hnf.reduce_free(tuple([2] * n) + (-1,) + tuple([-2] * (n + 1)) + (1,))
    return [("conj", 2, u),
            ("mul", 2, 1),
            ("conj", 1, W2), ("mul", 2, 1), ("conj", 1, hnf.inv(W2)),
            ("conj", 1, (-2,)), ("inv", 1), ("mul", 2, 1), ("inv", 1), ("conj", 1, (2,))]


def check_uniform(n, k):
    mv = uniform_moves(n)
    return acx.verify(acx.ms(n, acx.w_word(k)), mv, acx.ms(n, acx.w_word(k + 1)), 2)
