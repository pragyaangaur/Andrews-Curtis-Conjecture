"""Todd-Coxeter coset enumeration over the trivial subgroup.

Run:  python3 triviality_check.py

For a finitely presented group G the trivial subgroup has index |G|.  If the
enumeration of the cosets of the trivial subgroup closes with one coset, then
G is trivial.  The script also checks two nonzero indices (60 and 25) as
controls that the enumeration is not biased towards the answer 1.  Every deduction of Todd-Coxeter is valid in every quotient, so a
one-coset closure is a proof that |G| = 1.  Failing to close within the limits
proves nothing and is reported as "no result".

This is an independent check of the triviality claims used in
survey/invariants.md for the AK(n) and Miller-Schupp presentations.
"""

import sys


def tc_index(rels, n, limit=300000, max_steps=4000000):
    """Return (live cosets or None, steps).  None means a limit was hit."""
    table = [dict()]
    parent = [0]
    coincidences = []

    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c

    def live_count():
        return len({find(c) for c in range(len(table))})

    def set_entry(c, g, d):
        c, d = find(c), find(d)
        if c == d:
            return
        old = table[c].get(g)
        if old is None:
            table[c][g] = d
            if -g not in table[d]:
                table[d][-g] = c
            else:
                coincidences.append((find(table[d][-g]), c))
        else:
            if find(old) != d:
                coincidences.append((find(old), d))

    def define(c, g):
        c = find(c)
        d = len(table)
        table.append({})
        parent.append(d)
        table[c][g] = d
        table[d][-g] = c
        return d

    def merge(a, b):
        a, b = find(a), find(b)
        if a == b:
            return
        if a > b:
            a, b = b, a
        parent[b] = a
        items = list(table[b].items())
        table[b] = {}
        for g, d in items:
            set_entry(a, g, d)

    steps = 0
    changed = True
    while changed:
        changed = False
        while coincidences:
            a, b = coincidences.pop()
            if find(a) != find(b):
                merge(a, b)
                changed = True
        for r in rels:
            for c0 in range(len(table)):
                if find(c0) != c0:
                    continue
                c = c0
                for g in r:
                    c = find(c)
                    if g in table[c]:
                        c = find(table[c][g])
                    else:
                        c = define(c, g)
                        changed = True
                steps += 1
                if find(c) != find(c0):
                    coincidences.append((find(c), find(c0)))
                    changed = True
                if live_count() > limit or steps > max_steps:
                    return None, steps
        while coincidences:
            a, b = coincidences.pop()
            if find(a) != find(b):
                merge(a, b)
                changed = True
    return live_count(), steps


def std(n):
    return tuple((i + 1,) for i in range(n))


def power(w, k):
    out = ()
    for _ in range(abs(k)):
        out = out + (w if k > 0 else tuple(-g for g in reversed(w)))
    return out


def AK(n):
    r1 = (1, 2, 1) + (-2, -1, -2)
    r2 = power((1,), n) + power((-2,), n + 1)
    return (r1, r2)


def miller_schupp(n, w):
    r1 = (-1,) + power((2,), n) + (1,) + power((-2,), n + 1)
    r2 = (1,) + tuple(-g for g in reversed(w))
    return (r1, r2)


def main():
    checks = [
        # (name, relators, rank, expected index or None for "no result")
        ("<x | x^5>", ((1, 1, 1, 1, 1),), 1, 5),
        ("<x | x^5, x^3>", ((1, 1, 1, 1, 1), (1, 1, 1)), 1, 1),
        ("<x,y | x, y>", std(2), 2, 1),
        ("<x,y | x^2, y^3, (xy)^5>  (A_5)", ((1, 1), (2, 2, 2), (1, 2, 1, 2, 1, 2, 1, 2, 1, 2)), 2, 60),
        ("AK(1)", AK(1), 2, 1),
        ("AK(2)", AK(2), 2, 1),
        ("AK(3)", AK(3), 2, 1),
        ("AK(4)", AK(4), 2, 1),
        ("AK(5)", AK(5), 2, 1),
        ("AK(6)", AK(6), 2, 1),
        ("Miller-Schupp n=1 w=[a,b]", miller_schupp(1, (1, 2, -1, -2)), 2, 1),
        ("Miller-Schupp n=2 w=a b^2 a^-1 b^-2", miller_schupp(2, (1, 2, 2, -1, -2, -2)), 2, 1),
        ("Miller-Schupp n=3 w=[a,b]^2", miller_schupp(3, (1, 2, -1, -2, 1, 2, -1, -2)), 2, 1),
        ("length-14 example", ((-1, 2, 2, 1, -2, -2, -2), (-2, 1, 1, 2, -1, -1, -1)), 2, 1),
        ("Wicks length-27 example", ((1, 1, 1, 1, 2, 2, 2, -2, -2, -1, -1),
                                      (1, 1, 1, 1, 1, 1, 2, 2, 2, 2, -2, -2, -2, -1, -1, -1)), 2, 1),
        # Metzler's pair: same normal closure, same group of order 25, not Q-equivalent
        ("Metzler pair (1)  <x,y|x^5,y^5,[x,y]>", ((1, 1, 1, 1, 1), (2, 2, 2, 2, 2), (1, 2, -1, -2)), 2, 25),
        ("Metzler pair (2)  <x,y|x^5,y^5,[x^2,y]>", ((1, 1, 1, 1, 1), (2, 2, 2, 2, 2), (1, 1, 2, -1, -1, -2)), 2, 25),
    ]
    failures = 0
    for name, rels, n, expected in checks:
        got, steps = tc_index(rels, n)
        if got is None:
            print("NO RESULT %-40s limit hit after %d scans" % (name, steps))
            failures += 1
        elif got == expected:
            print("PASS %-40s index = %d (expected %d), %d scans" % (name, got, expected, steps))
        else:
            print("FAIL %-40s index = %d (expected %d), %d scans" % (name, got, expected, steps))
            failures += 1
    print()
    if failures:
        print("%d check(s) did not pass" % failures)
        return 1
    print("ALL TODD-COXETER CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
