"""One entry point that reproduces every claim of the final ak-ladder report.

  python3 check_all.py            # everything (about 30 s)
  python3 check_all.py quick      # the ladder only (about 5 s)

Sections
  1. the draft's own checks (test_acx, patterns, ladder table, cert replay)
  2. the four exact word identities behind the uniform ladder step
  3. the uniform ladder step MS(n,w_k) -> MS(n,w_(k+1)) for n <= NMAX, all k
  4. the composed end-to-end chain AK(n) -> P(n) for n <= NCHAIN
Nothing here uses randomness; every check is exact word arithmetic.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))


import sys
import time

import acx
import hnf
import ladder_template as lt

NMAX = 60
NCHAIN = 30


def show(w):
    return "".join({1: "x", 2: "y", -1: "X", -2: "Y"}[a] for a in w)


def sec_identities(nmax=30, qmax=10):
    """The four identities: x^s y^m x^-s y^-e as a product of conjugates of A."""
    bad = []
    for n in range(2, nmax + 1):
        A = lt.A_of(n)
        Ai = hnf.inv(A)
        for q in range(1, qmax + 1):
            # (s=-1, m>0):  x^-1 y^(nq) x y^(-(n+1)q) = prod (y^((n+1)j) A y^(-(n+1)j))
            h = hnf.reduce_free((-1,) + tuple([2] * (n * q)) + (1,) + tuple([-2] * ((n + 1) * q)))
            prod = ()
            for j in range(q):
                W = tuple([2] * ((n + 1) * j))
                prod = hnf.mul(prod, hnf.reduce_free(W + A + hnf.inv(W)))
            if prod != h:
                bad.append(("s-1,q>0", n, q))
            # (s=-1, m<0):  product over y^(-(n+1)(j+1)) A^-1 ...
            h = hnf.reduce_free((-1,) + tuple([-2] * (n * q)) + (1,) + tuple([2] * ((n + 1) * q)))
            prod = ()
            for j in range(q):
                W = tuple([-2] * ((n + 1) * (j + 1)))
                prod = hnf.mul(prod, hnf.reduce_free(W + Ai + hnf.inv(W)))
            if prod != h:
                bad.append(("s-1,q<0", n, q))
            # (s=+1, m>0):  x y^((n+1)q) x^-1 y^(-nq) = product over y^(jn) x A^-1 ...
            h = hnf.reduce_free((1,) + tuple([2] * ((n + 1) * q)) + (-1,) + tuple([-2] * (n * q)))
            prod = ()
            for j in range(q):
                W = hnf.reduce_free(tuple([2] * (j * n)) + (1,))
                prod = hnf.mul(prod, hnf.reduce_free(W + Ai + hnf.inv(W)))
            if prod != h:
                bad.append(("s+1,q>0", n, q))
            # (s=+1, m<0):  x y^(-(n+1)q) x^-1 y^(nq) = product over y^(-(j+1)n) x A ...
            h = hnf.reduce_free((1,) + tuple([-2] * ((n + 1) * q)) + (-1,) + tuple([2] * (n * q)))
            prod = ()
            for j in range(q):
                W = hnf.reduce_free(tuple([-2] * ((j + 1) * n)) + (1,))
                prod = hnf.mul(prod, hnf.reduce_free(W + A + hnf.inv(W)))
            if prod != h:
                bad.append(("s+1,q<0", n, q))
    print("2. four identities, n = 2..%d, |q| <= %d: %s"
          % (nmax, qmax, "PASS" if not bad else "FAIL %r" % bad[:5]))
    return not bad


def sec_uniform(nmax=NMAX):
    """The explicit ten-move template of Theorem 1, k absent from the move list."""
    bad = []
    for n in range(3, nmax + 1):
        for k in range(1, n - 1):
            if not lt.check_uniform(n, k):
                bad.append((n, k))
    print("3b. one ten-move list per n (k does not appear), n = 3..%d, all k: %s"
          % (nmax, "PASS" if not bad else "FAIL %r" % bad[:5]))
    return not bad


def sec_ladder(nmax=NMAX):
    bad = []
    worst = 0
    count = 0
    for n in range(3, nmax + 1):
        for k in range(1, n - 1):
            ok, nmv, mx = lt.check(n, k)
            count += 1
            worst = max(worst, mx - acx.total_length(acx.ms(n, acx.w_word(k))))
            if ok is not True:
                bad.append((n, k))
    print("3. ladder step MS(n,w_k)->MS(n,w_(k+1)), n = 3..%d, all k: %d certificates, %s"
          % (nmax, count, "PASS" if not bad else "FAIL %r" % bad[:5]))
    print("   every certificate has 10 moves; largest excess of the total length over the start: %d"
          % worst)
    return not bad


def sec_chain(nchain=NCHAIN):
    import chain_all
    bad = []
    rows = []
    for n in range(2, nchain + 1):
        mv = chain_all.full_chain(n)
        start, target = acx.ak(n), acx.p_form(n)
        ok = acx.verify(start, mv, target, 2)
        rs = tuple(start)
        mx = acx.total_length(rs)
        for m in mv:
            rs = acx.apply_move(rs, m, 2)
            mx = max(mx, acx.total_length(rs))
        rows.append((n, acx.total_length(start), acx.total_length(target), len(mv), mx, ok))
        if not ok:
            bad.append(n)
    print("4. composed chain AK(n) -> P(n), n = 2..%d: %s" % (nchain, "PASS" if not bad else "FAIL %r" % bad))
    for r in rows:
        if r[0] in (2, 3, 4, 5, 6, 7, 8, 9, 12, 20, 30) or r[0] == nchain:
            print("   n=%2d |AK|=%2d |P|=%2d moves=%3d max total=%3d replay=%s" % r)
    return not bad


def main():
    quick = "quick" in sys.argv
    t0 = time.time()
    ok = sec_identities() and sec_ladder() and sec_uniform()
    if not quick:
        ok = sec_chain() and ok
    print("%s   total %.1f s" % ("ALL CHECKS PASS" if ok else "SOME CHECK FAILED", time.time() - t0))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
