#!/usr/bin/env python3
"""Independent replay of the Carreras certificate format (round-3, member m8).

Written from the JSON specification only: words are lists of signed integers,
free reduction cancels adjacent inverse letters, and the four move types are
invert i, conj i g (a single signed generator), mul i j s (s = +-1) and
cycle i k (left rotation).  Nothing is imported from the artifact under test.

Equivalence mode requires the terminal tuple to equal the declared "reached"
tuple and that tuple to lie in the orbit of "target" under relator swap,
relator inversion and cyclic rotation, which are AC-derivable symmetries.
"""
import json
import sys


def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out


def inv(w):
    return [-a for a in reversed(w)]


def move(R, mv):
    op = mv[0]
    if op == "invert":
        i = mv[1]
        if not 0 <= i < len(R):
            return False
        R[i] = red(inv(R[i]))
    elif op == "conj":
        i, g = mv[1], mv[2]
        if not 0 <= i < len(R) or g == 0:
            return False
        R[i] = red([g] + R[i] + [-g])
    elif op == "mul":
        i, j, s = mv[1], mv[2], mv[3]
        if not 0 <= i < len(R) or not 0 <= j < len(R) or i == j or s not in (1, -1):
            return False
        R[i] = red(R[i] + (R[j] if s == 1 else inv(R[j])))
    elif op == "cycle":
        i, k = mv[1], mv[2]
        if not 0 <= i < len(R) or not R[i]:
            return False
        k %= len(R[i])
        R[i] = red(R[i][k:] + R[i][:k])
    else:
        return False
    return True


def orbit(r1, r2):
    out = set()
    for a in (list(r1), inv(r1)):
        for b in (list(r2), inv(r2)):
            for ka in range(max(len(a), 1)):
                ra = tuple(a[ka:] + a[:ka])
                for kb in range(max(len(b), 1)):
                    rb = tuple(b[kb:] + b[:kb])
                    out.add((ra, rb))
                    out.add((rb, ra))
    return out


def check(path):
    cert = json.load(open(path))
    R = [red(list(r)) for r in cert["initial"]]
    for step, mv in enumerate(cert["moves"]):
        if not move(R, mv):
            return path, False, "illegal move at step %d: %r" % (step, mv)
    term = [list(r) for r in R]
    if term != cert.get("reached"):
        return path, False, "terminal does not equal reached"
    ok = (tuple(term[0]), tuple(term[1])) in orbit(cert["target"][0], cert["target"][1])
    if not ok:
        return path, False, "reached not in the target orbit"
    return path, True, "%d moves, terminal equals reached, reached in target orbit" % len(cert["moves"])


if __name__ == "__main__":
    bad = 0
    for p in sys.argv[1:]:
        path, ok, msg = check(p)
        print(("PASS " if ok else "FAIL ") + path.split("/")[-1] + ": " + msg)
        bad += 0 if ok else 1
    print("failed: %d of %d" % (bad, len(sys.argv) - 1))
    sys.exit(1 if bad else 0)
