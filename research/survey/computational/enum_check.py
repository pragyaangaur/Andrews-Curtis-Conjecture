#!/usr/bin/env python3
"""enum_check.py -- reconstruct the canonical enumeration of Havas and Ramsay
(IJAC 13 (2003) 61-68, Sec. 4, steps (A)-(D)) and classify the resulting lists.

Their reported list sizes for total relator length l = 10, 11, 12, 13 are
20, 104, 204 and 1400 respectively.  This script recomputes them from the
description in the paper and then asks, for l <= 12, whether each listed
presentation is AC-trivial (with a certificate) or has a nontrivial finite
quotient.  Deterministic; no randomness.

    python3 enum_check.py [cap]

The optional argument is the total relator length bound used for the ball of
the standard presentation (default 13).
"""

import sys
from collections import Counter

import census as C


def variants_words(r):
    rots = C.rotations(r) if r else [()]
    return set(rots) | set(C.inv(x) for x in rots)


def contained(u, v):
    """Some cyclic permutation or inverse of v occurs contiguously in some cyclic
    permutation or inverse of u."""
    for x in variants_words(u):
        for y in variants_words(v):
            if len(y) <= len(x):
                for k in range(len(x) - len(y) + 1):
                    if x[k:k + len(y)] == y:
                        return True
    return False


def xi_eq_xj_pow(r):
    """r, up to cyclic permutation and inversion, is x_i y^m with x_i in {a,A},
    y in {b,B}, or vice versa (step (D) of the paper)."""
    for x in variants_words(r):
        if len(x) <= 1:
            return True
        cnt = Counter(x)
        for single, c in cnt.items():
            if c != 1:
                continue
            others = [z for z in cnt if z != single]
            if len(others) == 1 and abs(others[0]) != abs(single):
                return True
    return False


def per_length(l):
    cache = {}
    rows = []
    for l1 in range(1, l // 2 + 1):
        l2 = l - l1
        for k in (l1, l2):
            if k not in cache:
                cache[k] = C.canonical_words(k)
        for w1 in cache[l1]:
            for w2 in cache[l2]:
                if l1 == l2 and w2 < w1:
                    continue
                rows.append((w1, w2))
    return rows


def step_a(rows):
    """each generator occurs, relators distinct and nonempty, canonical forms."""
    return [t for t in rows
            if all(any(abs(x) == g for r in t for x in r) for g in (1, 2))
            and t[0] != t[1]]


def step_b(rows):
    """abelianized relators with determinant +-1 only."""
    return [t for t in rows if abs(C.det(t)) == 1]


def step_c(rows):
    """discard if one relator is contained in the other."""
    return [t for t in rows if not (contained(t[0], t[1]) or contained(t[1], t[0]))]


def step_d(rows):
    """discard if a relator reads x_i = x_j^m."""
    return [t for t in rows if not (xi_eq_xj_pow(t[0]) or xi_eq_xj_pow(t[1]))]


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    print("=" * 78)
    print("Reconstruction of the canonical lists of Havas-Ramsay (2003), Sec. 4")
    print("  published sizes for l = 10, 11, 12, 13: 20, 104, 204, 1400")
    lists = {}
    for l in (10, 11, 12, 13):
        rows = per_length(l)
        a = step_a(rows)
        b = step_b(a)
        c = step_c(b)
        d = step_d(c)
        lists[l] = d
        print("  l = %2d: canonical %6d | (A) %6d | (B) %6d | (C) %5d | (D) %5d %s"
              % (l, len(rows), len(a), len(b), len(c), len(d),
                 "MATCH" if len(d) == {10: 20, 11: 104, 12: 204, 13: 1400}[l]
                 else "differs from published"))

    print("=" * 78)
    print("Classification of the l = 10, 11, 12 lists, ball of total length <= %d" % cap)
    info = C.ball_with_parents(cap)
    B = {t: v[0] for t, v in info.items()}
    print("  ball size %d" % len(B))
    for l in (10, 11, 12):
        tally = {'ac': 0, 'quot': 0, 'unres': 0}
        quirks = []
        for t in lists[l]:
            if C.in_ball(t, B)[0] is not None:
                if C.certificate(t, info) is None:
                    tally['unres'] += 1
                    quirks.append(('no certificate', t))
                else:
                    tally['ac'] += 1
                continue
            w = C.quotient_witness(t)
            if w is not None:
                tally['quot'] += 1
                quirks.append((w, t))
            else:
                tally['unres'] += 1
                quirks.append(('unresolved', t))
        print("  l = %2d: %4d presentations | AC-trivial with certificate %4d | "
              "nontrivial by finite quotient %d | unresolved %d"
              % (l, len(lists[l]), tally['ac'], tally['quot'], tally['unres']))
        for q in quirks:
            if q[0] != 'unresolved':
                print("      %-28s %s" % (str(q[0]), C.show_pres(q[1])))
    return 0


if __name__ == '__main__':
    sys.exit(main())
