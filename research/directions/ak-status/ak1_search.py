"""Bounded breadth-first search in the Andrews-Curtis graph at rank 2.

Words are tuples of nonzero ints; i means generator x_i, -i its inverse.
The three AC moves are applied to a pair (r1, r2) of reduced words:
  (AC1) replace r_i by its inverse,
  (AC2) replace r_i by r_i * r_j or r_i * r_j^-1, i != j,
  (AC3) replace r_i by w r_i w^-1 for a word w of length at most CL.
No reordering of the pair is used.  Everything is deterministic (BFS, fixed
order of neighbours, fixed bounds).

Goal: decide whether AK(1) = <x,y | x = y^2, xyx = yxy>, i.e. the tuple
(x y^-2, x y x y^-1 x^-1 y^-1), is AC-equivalent to (x, y).
"""
import itertools
import sys

X, Y = 1, 2

def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)

def inv(w):
    return tuple(-a for a in reversed(w))

def mul(u, v):
    return red(u + v)

def conj(w, u):
    return mul(mul(w, u), inv(w))

def conj_words(maxlen):
    """All reduced words in x,y of length at most maxlen, deterministic order."""
    out = [()]
    cur = [()]
    for _ in range(maxlen):
        nxt = []
        for w in cur:
            for a in (X, Y, -X, -Y):
                nw = red(w + (a,))
                nxt.append(nw)
        out.extend(nxt)
        cur = nxt
    seen = set()
    res = []
    for w in out:
        if w not in seen:
            seen.add(w)
            res.append(w)
    return res

def neighbours(state, k, conjugs, maxlen):
    r = list(state)
    for i in (0, 1):
        j = 1 - i
        cands = []
        cands.append(inv(r[i]))
        for e in (1, -1):
            cands.append(mul(r[i], r[j] if e == 1 else inv(r[j])))
        for w in conjugs:
            cands.append(conj(w, r[i]))
        for c in cands:
            if len(c) <= maxlen:
                new = list(r)
                new[i] = c
                yield tuple(new)

def search(start, goal, maxlen=10, cl=2, cap=3000000, depth=14):
    conjugs = conj_words(cl)
    frontier = {start}
    seen = {start}
    parent = {start: None}
    for d in range(1, depth + 1):
        nxt = set()
        for s in frontier:
            for t in neighbours(s, 2, conjugs, maxlen):
                if t not in seen:
                    seen.add(t)
                    parent[t] = (s, d)
                    nxt.add(t)
                    if t == goal:
                        return d, seen, parent, goal
                if len(seen) > cap:
                    return None, seen, parent, None
        frontier = nxt
        print("  depth %2d: %8d new states, %8d total" % (d, len(nxt), len(seen)))
        sys.stdout.flush()
        if not nxt:
            break
    return None, seen, parent, None

def replay(start, path):
    """Check a claimed tuple sequence against the three moves."""
    def ok_step(a, b):
        if len(a) != len(b):
            return False
        for i in (0, 1):
            j = 1 - i
            if a[i] == b[i] and a[j] == b[j]:
                continue
            if b[j] != a[j]:
                return False
            # AC1
            if b[i] == inv(a[i]):
                continue
            # AC2
            if b[i] == mul(a[i], a[j]) or b[i] == mul(a[i], inv(a[j])):
                continue
            # AC3: b_i = w a_i w^-1 for some w
            found = False
            for w in [()] + [t for k in range(1, 9) for t in itertools.product((1, 2, -1, -2), repeat=k)]:
                if b[i] == conj(w, a[i]):
                    found = True
                    break
            if found:
                continue
            return False
        return True
    assert path[0] == start
    for a, b in zip(path, path[1:]):
        assert ok_step(a, b), (a, b)
    return True

if __name__ == "__main__":
    start = ((X,), (Y,))
    ak1 = (red((X, -Y, -Y)), red((X, Y, X, -Y, -X, -Y)))
    ak2 = (red((X, X, -Y, -Y, -Y)), red((X, Y, X, -Y, -X, -Y)))
    print("AK(1) =", ak1)
    print("AK(2) =", ak2)
    print("BFS from the standard presentation, relator length <= 10, conjugator length <= 2")
    d, seen, parent, hit = search(start, ak1, maxlen=10, cl=2, cap=3000000, depth=14)
    if hit is not None:
        # rebuild path
        path = []
        cur = hit
        while cur is not None:
            path.append(cur)
            p = parent[cur]
            cur = None if p is None else p[0]
        path.reverse()
        print("FOUND AK(1) at AC distance", d, "with", len(path) - 1, "moves")
        for idx, st in enumerate(path):
            print("  %2d: %s" % (idx, st))
        print("replay check:", replay(start, path))
    else:
        print("NOT FOUND within the bounds")
