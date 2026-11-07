"""Todd-Coxeter coset enumeration, HLT/Felsch hybrid, with coincidence queue.

Words are lists of nonzero integers: i > 0 means generator x_i, -i its inverse.
We enumerate cosets of the trivial subgroup, so the number of cosets is the
order of the presented group; a completed enumeration with one coset certifies
that the group is trivial.  Termination for infinite groups does not happen,
so the work is bounded by integer limits and the outcome is then "LIMIT"
(nothing is decided).

Outcomes: ("TRIVIAL",1) ("FINITE",m) ("LIMIT",live cosets at the bound).
"""


def reduce_word(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out


def invert_word(w):
    return [-a for a in reversed(w)]


def enumerate_cosets(n, relators, max_cosets=300000, max_passes=100000):
    cols = 2 * n
    rows = [[-1] * cols]
    parent = [0]
    queue = []
    stats = {"defines": 0, "merges": 0, "passes": 0, "created": 1}

    def col(a):
        return a - 1 if a > 0 else n + (-a - 1)

    def opp(k):
        return (k + n) % cols

    def letter(k):
        return (k + 1) if k < n else -(k - n) - 1

    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c

    def add():
        rows.append([-1] * cols)
        parent.append(len(parent))
        stats["created"] += 1
        return len(parent) - 1

    def assign(c, a, d):
        """Record the consequence c*a = d, queueing any coincidence it forces."""
        c = find(c)
        d = find(d)
        if c == d:
            return
        k = col(a)
        ko = opp(k)
        e = rows[c][k]
        if e != -1:
            e = find(e)
            if e != d:
                queue.append((e, d))
            return
        f = rows[d][ko]
        if f != -1:
            f = find(f)
            if f != c:
                queue.append((f, c))
            return
        rows[c][k] = d
        rows[d][ko] = c
        stats["defines"] += 1

    def merge(a, b):
        a, b = find(a), find(b)
        if a == b:
            return False
        if b < a:
            a, b = b, a
        parent[b] = a
        stats["merges"] += 1
        for k in range(cols):
            d = rows[b][k]
            if d != -1:
                assign(a, letter(k), d)
        rows[b] = [-1] * cols
        return True

    rels = []
    for r in relators:
        r = reduce_word(list(r))
        if r:
            rels.append(tuple(r))
            rels.append(tuple(invert_word(r)))

    def drain():
        changed = False
        while queue:
            a, b = queue.pop()
            if merge(a, b):
                changed = True
        return changed

    def scan(rel, c0):
        """Trace rel from coset c0, defining new cosets as needed."""
        c = find(c0)
        cur = c
        m = len(rel)
        changed = False
        for i, a in enumerate(rel):
            k = col(a)
            d = rows[cur][k]
            d = -1 if d == -1 else find(d)
            last = (i == m - 1)
            if d == -1:
                if last:
                    if cur == c:
                        assign(cur, a, c)
                    else:
                        nd = add()
                        assign(cur, a, nd)
                        queue.append((nd, c))
                    return True
                nd = add()
                assign(cur, a, nd)
                cur = nd
                changed = True
            else:
                if last:
                    if d != c:
                        queue.append((d, c))
                        return True
                cur = d
        return changed

    def activity():
        return stats["defines"] + stats["merges"] + stats["created"]

    while True:
        stats["passes"] += 1
        if stats["passes"] > max_passes or len(parent) > max_cosets:
            return "LIMIT", sum(1 for c in range(len(parent)) if find(c) == c), stats
        before = activity()
        drain()
        for rel in rels:
            for c0 in range(len(rows)):
                if find(c0) != c0:
                    continue
                scan(rel, c0)
                drain()
                if len(parent) > max_cosets:
                    return "LIMIT", sum(1 for c in range(len(parent)) if find(c) == c), stats
        if activity() > before:
            continue
        # no relator was violated and nothing was forced: any remaining hole in a
        # live row means the table is not yet a group action; fill one hole and go on
        hole = None
        for c in range(len(rows)):
            if find(c) != c:
                continue
            if -1 in rows[c]:
                hole = c
                break
        if hole is None:
            return "COMPLETE", sum(1 for c in range(len(parent)) if find(c) == c), stats
        k = rows[hole].index(-1)
        nd = add()
        assign(hole, letter(k), nd)


def run(name, n, relators, max_cosets=300000, max_passes=100000, verbose=True):
    status, m, stats = enumerate_cosets(n, relators, max_cosets, max_passes)
    if status == "COMPLETE":
        verdict = "TRIVIAL" if m == 1 else "FINITE"
    else:
        verdict = "LIMIT"
    if verbose:
        print("%-44s %-8s cosets=%-7d created=%-7d passes=%-6d defines=%-7d merges=%d"
              % (name, verdict, m, stats["created"], stats["passes"],
                 stats["defines"], stats["merges"]))
    return verdict, m, stats


def ak(n):
    """AK(n) = <x,y | x^n = y^(n+1), xyx = yxy>."""
    return [[1] * n + [-2] * (n + 1), [1, 2, 1, -2, -1, -2]]


W_STAR = [-2, 1, 2, -1]                  # y^-1 x y x^-1
W_K = lambda k: [-2] * k + [-1, 1, 2]    # y^-k x^-1 y x y


def ms(n, w):
    """MS(n,w) = <x,y | x^-1 y^n x = y^(n+1), x = w>."""
    return [[-1] + [2] * n + [1] + [-2] * (n + 1), [-1] + list(w)]


TESTS = [
    ("<x,y | x, y>", 2, [[1], [2]], ("TRIVIAL", 1)),
    ("Klein four <x,y | x^2, y^2, [x,y]>", 2, [[1, 1], [2, 2], [1, 2, -1, -2]], ("FINITE", 4)),
    ("C12 = <x | x^12>", 1, [[1] * 12], ("FINITE", 12)),
    ("S3 = <x,y | x^2, y^3, (xy)^2>", 2, [[1, 1], [2, 2, 2], [1, 2, 1, 2]], ("FINITE", 6)),
    ("A5 = <x,y | x^2, y^3, (xy)^5>", 2, [[1, 1], [2, 2, 2], [1, 2] * 5], ("FINITE", 60)),
    ("<x,y | x^3, y^3, (xy)^3> (A4? no: <3,3,3>)", 2, [[1] * 3, [2] * 3, [1, 2] * 3], None),
    ("<x,y | x^2 = y^3> (infinite)", 2, [[1, 1, -2, -2, -2]], ("LIMIT", None)),
    ("MS example <x,y | x^-1 y x = y^2, y^-1 x y = x^2>", 2,
     [[-1, 2, 1, -2, -2], [-2, 1, 2, -1, -1]], ("TRIVIAL", 1)),
    ("Baumslag-Solitar BS(1,2) (infinite)", 2, [[-2, 1, 2, -1, -1]], ("LIMIT", None)),
]


def main():
    print("Validation set (groups of known order):")
    ok = True
    for name, n, rels, expected in TESTS:
        verdict, m, _ = run(name, n, rels)
        if expected is None:
            continue
        good = verdict == expected[0] and (expected[1] is None or m == expected[1])
        print("      expected %s %s -> %s" % (expected[0], expected[1], "PASS" if good else "FAIL"))
        ok = ok and good
    print()
    print("Akbulut-Kirby AK(n) = <x,y | x^n = y^(n+1), xyx = yxy>:")
    for n in range(1, 11):
        run("AK(%d)" % n, 2, ak(n))
    print()
    print("Miller-Schupp MS(n,w_*), w_* = y^-1 x y x^-1:")
    for n in range(1, 7):
        run("MS(%d,w_*)" % n, 2, ms(n, W_STAR))
    print()
    print("Miller-Schupp MS(2,w_k), w_k = y^-k x^-1 y x y:")
    for k in range(0, 4):
        run("MS(2,w_%d)" % k, 2, ms(2, W_K(k)))
    print()
    print("ALL VALIDATION PASS" if ok else "VALIDATION FAILURE")


if __name__ == "__main__":
    main()
