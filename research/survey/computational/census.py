#!/usr/bin/env python3
"""census.py -- independent replay of published Andrews-Curtis chains, plus an
exhaustive census of small balanced 2-generator presentations.

Deterministic: no randomness, no wall-clock cutoffs.  Run with

    python3 census.py

Words in the free group F2 on generators a, b are tuples of integers:
+1 = a, -1 = a^-1, +2 = b, -2 = b^-1.  A presentation of rank 2 is a pair of
relators (w1, w2).

The three AC moves used here (Havas-Ramsay 2003, Sec. 1, with their restricted
conjugation) are
    inv i     : r_i -> r_i^{-1}
    mul i j   : r_i -> r_i r_j          (i != j)
    conj i g  : r_i -> g r_i g^{-1}     (g a generator or its inverse)
The accepted moves are reported separately from arbitrary conjugation by a
word, which is a succession of conj moves.
"""

import itertools
import sys
from collections import deque

A, Ai, B, Bi = 1, -1, 2, -2
GEN = (A, Ai, B, Bi)
LETTER = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
KIND = {'a': 1, 'A': -1, 'b': 2, 'B': -2}


# ---------------------------------------------------------------- words
def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def mul(u, v):
    return red(tuple(u) + tuple(v))


def inv(u):
    return tuple(-x for x in reversed(u))


def conj(w, r):
    return mul(mul(w, r), inv(w))


def show(w):
    return ''.join(LETTER[x] for x in w) if w else 'e'


def show_pres(t):
    return '(' + ','.join(show(x) for x in t) + ')'


def parse(s):
    return tuple(KIND[c] for c in s)


def rotations(w):
    n = len(w)
    return [w[k:] + w[:k] for k in range(n)]


def cyclic_reduce(w):
    w = red(w)
    while w and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def exps(w):
    """exponent sums in (a, b)."""
    return (sum(1 for x in w if x == A) - sum(1 for x in w if x == Ai),
            sum(1 for x in w if x == B) - sum(1 for x in w if x == Bi))


def det(t):
    (p, q), (r, s) = exps(t[0]), exps(t[1])
    return p * s - q * r


def total_len(t):
    return sum(len(x) for x in t)


# ---------------------------------------------------------------- moves
def moves(t):
    """All AC moves of the restricted kind, in a fixed order."""
    t = list(t)
    n = len(t)
    for i in range(n):
        u = list(t)
        u[i] = inv(t[i])
        yield ('inv', i, None), tuple(u)
        for j in range(n):
            if i != j:
                u = list(t)
                u[i] = mul(t[i], t[j])
                yield ('mul', i, j), tuple(u)
        for g in GEN:
            u = list(t)
            u[i] = conj((g,), t[i])
            yield ('conj', i, g), tuple(u)


def classify_step(u, v):
    """How is v obtained from u by a single move (or by one further kind)?

    Returns a short string, or None if no single move of the three kinds does it.
    'conj-word' means v = w u_i w^-1 for some word w, which is a succession of
    conj moves and is not counted as one move.
    """
    for tag, w in moves(u):
        if w == v:
            return tag[0] if tag[0] != 'conj' else 'conj-gen'
    for i in range(len(u)):
        if all(u[k] == v[k] for k in range(len(u)) if k != i):
            a, b = u[i], v[i]
            if cyc_conjugate(a, b):
                return 'conj-word'
    return None


def cyc_conjugate(a, b):
    """Is b = w a w^-1 for some word w?  True iff b is a cyclic rotation of a
    (both cyclically reduced) with matching exponents, or a is empty and b empty.
    """
    if len(a) != len(b):
        return False
    if not a:
        return True
    if cyclic_reduce(a) != a or cyclic_reduce(b) != b:
        a, b = cyclic_reduce(a), cyclic_reduce(b)
        if len(a) != len(b):
            return False
    return b in rotations(a)


def replay(start, chain, name):
    """Verify a published chain arrow by arrow."""
    cur = start
    print("replay: %s  (%d arrows, start %s, total length %d)"
          % (name, len(chain), show_pres(start), total_len(start)))
    counts = {}
    ok = True
    maxlen = total_len(start)
    for k, nxt in enumerate(chain, 1):
        kind = classify_step(cur, nxt)
        if kind is None:
            print("  FAIL at move %d: %s -> %s" % (k, show_pres(cur), show_pres(nxt)))
            ok = False
            break
        counts[kind] = counts.get(kind, 0) + 1
        maxlen = max(maxlen, total_len(nxt))
        cur = nxt
    if ok:
        print("  PASS all %d arrows; steps by kind %s; max total length %d; end %s"
              % (len(chain), counts, maxlen, show_pres(cur)))
    return ok


# ---------------------------------------------------------------- finite groups
def perm_compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def perm_closure(gens):
    idp = tuple(range(len(gens[0])))
    elems = {idp}
    frontier = [idp]
    while frontier:
        new = []
        for e in frontier:
            for g in gens:
                f = perm_compose(e, g)
                if f not in elems:
                    elems.add(f)
                    new.append(f)
        frontier = new
    return sorted(elems)


def make_table(elems, mult):
    index = {e: i for i, e in enumerate(elems)}
    return [[index[mult(e, f)] for f in elems] for e in elems]


def quat_mul(x, y):
    (a, b), (c, d) = x, y
    return ((a + (c if b == 0 else -c)) % 4, (b + d) % 2)


Q8_ELEMS = [(a, b) for b in (0, 1) for a in range(4)]
Q8_TABLE = make_table(Q8_ELEMS, quat_mul)


def perm_table(gens):
    els = perm_closure(gens)
    return els, make_table(els, perm_compose)


GROUPS = []
for name, gens in (
        ('S3', [(1, 0, 2), (0, 2, 1)]),
        ('D8', [(1, 2, 3, 0), (1, 0, 3, 2)]),
        ('A4', [(1, 2, 0, 3), (1, 0, 3, 2)]),
        ('S4', [(1, 2, 3, 0), (1, 0, 2, 3)]),
        ('A5', [(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)]),
):
    els, tab = perm_table(gens)
    GROUPS.append((name, len(els), tab))
GROUPS.insert(2, ('Q8', 8, Q8_TABLE))


def inverse_index(tab):
    """given a multiplication table, list the inverse of each element."""
    n = len(tab)
    invs = [None] * n
    for i in range(n):
        for k in range(n):
            if tab[i][k] == 0:
                invs[i] = k
                break
    return invs


for _name, _n, _tab in GROUPS:
    assert _n == len(_tab)


def eval_rel(r, tab, invs, ia, ib):
    idx = 0
    for x in r:
        if x == A:
            idx = tab[idx][ia]
        elif x == Ai:
            idx = tab[idx][invs[ia]]
        elif x == B:
            idx = tab[idx][ib]
        else:
            idx = tab[idx][invs[ib]]
    return idx


def quotient_witness(t):
    """Search for a homomorphism to a small group with nontrivial image.

    Returns (name, order, ia, ib) or None.  A witness proves the presented
    group is nontrivial.
    """
    for name, n, tab in GROUPS:
        invs = inverse_index(tab)
        for ia in range(n):
            for ib in range(n):
                if ia == 0 and ib == 0:
                    continue
                if all(eval_rel(r, tab, invs, ia, ib) == 0 for r in t):
                    return (name, n, ia, ib)
    return None


# ---------------------------------------------------------------- ball of the standard presentation
STANDARD = ((A,), (B,))


def ball(cap):
    """All tuples AC-reachable from the standard presentation with total relator
    length at most cap, breadth first, with the depth of each."""
    seen = {STANDARD: 0}
    q = deque([STANDARD])
    while q:
        t = q.popleft()
        for _tag, u in moves(t):
            if total_len(u) <= cap and u not in seen:
                seen[u] = seen[t] + 1
                q.append(u)
    return seen


def ball_with_parents(cap):
    """As ball, but each tuple carries (depth, parent, tag)."""
    info = {STANDARD: (0, None, None)}
    q = deque([STANDARD])
    while q:
        t = q.popleft()
        for tag, u in moves(t):
            if total_len(u) <= cap and u not in info:
                info[u] = (info[t][0] + 1, t, tag)
                q.append(u)
    return info


def inverse_move_sequence(u, tag):
    """Moves that undo 'tag' applied to the tuple u (producing the parent)."""
    if tag[0] == 'inv':
        return [('inv', tag[1], None)]
    if tag[0] == 'mul':
        i, j = tag[1], tag[2]
        return [('inv', j, None), ('mul', i, j), ('inv', j, None)]
    return [('conj', tag[1], -tag[2])]


def apply_move(t, mv):
    kind, i, arg = mv
    t = list(t)
    if kind == 'inv':
        t[i] = inv(t[i])
    elif kind == 'mul':
        t[i] = mul(t[i], t[arg])
    else:
        g = (arg,) if isinstance(arg, int) else tuple(arg)
        t[i] = conj(g, t[i])
    return tuple(t)


def path_to_standard(info, v):
    """Explicit move list taking v to the standard tuple."""
    seq = []
    cur = v
    while info[cur][1] is not None:
        depth, par, tag = info[cur]
        seq.extend(inverse_move_sequence(cur, tag))
        cur = par
    return seq


def symmetry_moves(p, v):
    """Moves (plus a relator reordering) taking p to v, where v is one of the
    word_variants of p.  Returns (permutation, moves) or None."""
    for perm in itertools.permutations(range(len(p))):
        q = [p[i] for i in perm]
        mv = []
        ok = True
        for i in range(len(q)):
            r = q[i]
            target = v[i]
            # find (invert?, rotation k) with target = rot_k(r) or inv(rot_k(r))
            found = None
            for k in range(len(r)) if r else [0]:
                rot = (r[k:] + r[:k]) if r else ()
                if rot == target:
                    found = (False, k)
                    break
                if inv(rot) == target:
                    found = (True, k)
                    break
            if found is None:
                ok = False
                break
            inverts, k = found
            if inverts:
                mv.append(('inv', i, None))
            if k:
                prefix = r[:k]
                # conj by c1 then c2 composes to conj by c2 c1, so to conjugate
                # by prefix^-1 = -prefix[-1] ... -prefix[0] apply -prefix[0]
                # first and -prefix[-1] last.
                for letter in prefix:
                    mv.append(('conj', i, -letter))
        if ok:
            return perm, mv
    return None


def certificate(p, info):
    """A certificate taking p to the standard tuple, or None.

    Returns (perm, moves) where perm is the reordering of the relators of p (a
    presentation is a set of relators, so reordering is notational) and moves is
    an explicit list of AC moves.  The certificate is re-simulated here and
    accepted only if it ends exactly at ((a), (b)).
    """
    for v in sorted(variants(p)):
        if v in info:
            sym = symmetry_moves(p, v)
            if sym is None:
                continue
            perm, mv1 = sym
            mv = mv1 + path_to_standard(info, v)
            cur = tuple(p[i] for i in perm)
            for m in mv:
                cur = apply_move(cur, m)
            if cur == STANDARD:
                return perm, mv
    return None


def word_variants(r):
    """Words obtained from r by cyclic permutation and by inversion.

    Cyclic permutation is conjugation by a prefix word, and inversion is an AC
    move, so replacing a relator by any of these preserves AC-equivalence.
    """
    rots = rotations(r) if r else [()]
    return set(rots) | set(inv(x) for x in rots)


def variants(t):
    """All tuples obtained by reordering relators and replacing each relator by a
    cyclically permuted or inverted word."""
    out = set()
    for perm in itertools.permutations(range(len(t))):
        p = tuple(t[i] for i in perm)
        choices = [sorted(word_variants(r)) for r in p]
        for combo in itertools.product(*choices):
            out.add(tuple(combo))
    return out


def in_ball(t, B):
    for v in variants(t):
        if v in B:
            return v, B[v]
    return None, None


# ---------------------------------------------------------------- enumeration
def canonical_words(k):
    """Words of length k, freely and cyclically reduced, minimal under cyclic
    rotation and inversion of the whole word.  One representative per class."""
    out = []
    for w in itertools.product((A, Ai, B, Bi), repeat=k):
        if red(w) != w:
            continue
        if w[0] == -w[-1]:
            continue
        cands = rotations(w) + [inv(r) for r in rotations(w)]
        if w == min(cands):
            out.append(w)
    return out


def presentations(lmax):
    """Canonical balanced 2-generator presentations with total relator length
    at most lmax, one representative per class under relator order, cyclic
    rotation and relator inversion."""
    cache = {}
    for l in range(2, lmax + 1):
        for l1 in range(1, l // 2 + 1):
            l2 = l - l1
            for k in (l1, l2):
                if k not in cache:
                    cache[k] = canonical_words(k)
            for w1 in cache[l1]:
                for w2 in cache[l2]:
                    if l1 == l2 and w2 < w1:
                        continue
                    yield (w1, w2)


# ---------------------------------------------------------------- main
def main():
    ok = True
    print("=" * 78)
    print("PART 1  word arithmetic")
    checks = [
        (mul((A, Ai), ()), (), 'a a^-1 = 1'),
        (mul((A, B, Bi, Ai), ()), (), 'a b b^-1 a^-1 = 1'),
        (inv(inv((A, B, Ai))), red((A, B, Ai)), 'involution of inverse'),
        (conj((A,), (B,)), (A, B, Ai), 'conjugation of b by a'),
        (mul((A, B), inv((A, B))), (), 'word times its inverse'),
        (red((A, B, Ai)), (A, B, Ai), 'no cancellation available'),
    ]
    for got, want, name in checks:
        status = 'PASS' if got == want else 'FAIL'
        if got != want:
            ok = False
        print("  %s %-32s got %s want %s" % (status, name, show(got), show(want)))

    print("=" * 78)
    print("PART 2  each move is undone by moves")
    tests = [((A, B), (Ai, B)), ((A,), (B,)), ((A, B, Ai, B), (A,))]
    undo = {
        'inv': lambda i, j: [('inv', i)],          # move is its own reverse
    }
    cnt = 0
    for t in tests:
        for tag, u in moves(t):
            if tag[0] == 'inv':
                rev = [('inv', tag[1])]
            elif tag[0] == 'mul':
                i, j = tag[1], tag[2]
                rev = [('inv', j), ('mul', i, j), ('inv', j)]
            else:
                rev = [('conj', tag[1], -tag[2])]
            cur = u
            for r in rev:
                nxt = [x for x in cur]
                if r[0] == 'inv':
                    nxt[r[1]] = inv(nxt[r[1]])
                elif r[0] == 'mul':
                    nxt[r[1]] = mul(nxt[r[1]], nxt[r[2]])
                else:
                    nxt[r[1]] = conj((r[2],), nxt[r[1]])
                cur = tuple(nxt)
            cnt += 1
            if cur != t:
                ok = False
                print("  FAIL reverse of %s on %s gave %s" % (tag, show_pres(t), show_pres(cur)))
    print("  PASS all %d single moves are undone by the listed move sequences" % cnt)

    print("=" * 78)
    print("PART 3  replay of chains printed in Havas-Ramsay, IJAC 13 (2003) 61-68")

    # Sec. 2, length 10 example <a,b | ab = a^2, ba = b^2>, relators abAA and AbaBB.
    c1 = ["ABabA,AbaBB", "AABab,AbaBB", "AABab,BAbaB", "AB,BAbaB", "BA,BAbaB",
          "BA,bABab", "BA,bAB", "BA,baB", "BA,a", "B,a", "b,a"]
    chain1 = [tuple(parse(x) for x in step.split(',')) for step in c1]
    ok &= replay((parse('BabAA'), parse('AbaBB')), chain1, 'Sec. 2, 11 moves')

    # Sec. 3, AK(2) = <a,b | a^2 = b^3, aba = bab>, table 14 moves.
    c2 = ["aBBBa,BAbaBBa", "aBBBa,AbaBBaB", "aBBaBBaB,AbaBBaB",
          "aBBaBBaB,bAbbABa", "aBBaBBaB,abAbbAB", "aBBaBBaB,BabAbbA",
          "aBBaBBaB,BaBaB", "BBaBBaBa,BaBaB", "BBaBBaBa,bAbAb",
          "BBaBBaBa,AbAbb", "BBa,AbAbb", "BBa,Ab", "B,Ab", "B,A"]
    chain2 = [tuple(parse(x) for x in step.split(',')) for step in c2]
    ok &= replay((parse('aBBBa'), parse('BAbabA')), chain2, 'Sec. 3, AK(2), 14 moves')

    # Sec. 4, 32 moves relating the two length 13 representatives.
    c3raw = ("baBBBBaaB,AbabAB|baBBBBaaB,AbaBBBaaB|bAAbbbbAB,AbaBBBaaB|"
             "AbAAbbbbABa,AbaBBBaaB|AbAAbaaB,AbaBBBaaB|AbAAbaaB,AAbaBBBaaBa|"
             "AbAAbaaB,AAbaBBaaB|AbAAbaaB,AAAbaBBaaBa|AbAAbaaB,AAAbaBaaB|"
             "AbAAbaaB,AAAAbaBaaBa|AbAAbaaB,AAAAbaaaB|BAbAAbaa,AAAAbaaaB|"
             "ABAbAAbaaa,AAAAbaaaB|bABAbAAbaaaB,AAAAbaaaB|bABAbAAbaaaB,bAAABaaaa|"
             "bABAbaa,bAAABaaaa|AbABAbaaa,bAAABaaaa|bAbABAbaaaB,bAAABaaaa|"
             "bAbABaaa,bAAABaaaa|AbAbABaaaa,bAAABaaaa|AbAbABaaaa,AAAAbaaaB|"
             "AbAbaaB,AAAAbaaaB|BAbAbaa,AAAAbaaaB|ABAbAbaaa,AAAAbaaaB|"
             "bABAbAbaaaB,AAAAbaaaB|bABAbAbaaaB,bAAABaaaa|bABAbaaa,bAAABaaaa|"
             "bbABAbaaaB,bAAABaaaa|bbABaaa,bAAABaaaa|AAAbaBB,bAAABaaaa|"
             "AAAbaBB,abAAABaaa|AAAbaBB,abAABB")
    c3 = [tuple(parse(x) for x in step.split(',')) for step in c3raw.split('|')]
    ok &= replay((parse('aBBBBaa'), parse('AbabAB')), c3, 'Sec. 4, 32 moves')

    # Miasnikov 1999, IJAC 9(6) 671-686, Sec. 5: printed chain for AK(2).
    raw = [('inv', 0), ('mul', 1, 0), ('conj', 1, parse('A')), ('conj', 1, parse('B')),
           ('conj', 0, parse('A')), ('mul', 0, 1), ('conj', 1, parse('B')), ('mul', 1, 0),
           ('conj', 1, parse('bAb')), ('inv', 0), ('mul', 1, 0), ('mul', 0, 1), ('mul', 0, 1),
           ('mul', 0, 1), ('inv', 0), ('mul', 1, 0), ('mul', 1, 0), ('inv', 1), ('inv', 0)]
    mv = [(m[0], m[1], m[2] if len(m) > 2 else None) for m in raw]
    cur = (parse('aaBBB'), parse('abaBAB'))
    elementary = 0
    top = total_len(cur)
    for kind, i, arg in mv:
        if kind == 'conj':
            for letter in arg:
                cur = apply_move(cur, ('conj', i, letter))
                elementary += 1
                top = max(top, total_len(cur))
        else:
            cur = apply_move(cur, (kind, i, arg))
            elementary += 1
            top = max(top, total_len(cur))
    print("replay: Miasnikov 1999, AK(2), 19 printed steps from (aaBBB,abaBAB)")
    print("  %d elementary moves; max total length %d; end %s"
          % (elementary, top, show_pres(cur)))
    if cur == ((B,), (A,)) and elementary == 21 and top == 25:
        print("  PASS end point (b^-1,a^-1), 21 elementary moves, peak length 25")
        print("       (peak 25 agrees with Havas-Ramsay 2003 Sec. 3)")
    else:
        ok = False
        print("  FAIL unexpected end point or counts")

    print("=" * 78)
    print("PART 4  exhaustive census of canonical balanced presentations, rank 2")
    lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    certfile = sys.argv[3] if len(sys.argv) > 3 else None
    info = ball_with_parents(cap)
    B_ = {t: v[0] for t, v in info.items()}
    print("  ball of the standard presentation: total length <= %d, %d tuples" % (cap, len(B_)))
    bad = [t for t in B_ if abs(det(t)) != 1]
    print("  invariant check: tuples in the ball with |exponent-sum determinant| != 1: %d" % len(bad))
    if bad:
        ok = False
        print("  FAIL invariant check, example", show_pres(bad[0]))
    by_depth = {}
    for d in B_.values():
        by_depth[d] = by_depth.get(d, 0) + 1
    print("  ball size by depth: %s" % {d: by_depth[d] for d in sorted(by_depth)})

    tally = {'ac': 0, 'ab': 0, 'quot': 0, 'unres': 0}
    contradicts = []
    unresolved = []
    ac_rows = []
    maxdepth = 0
    pres = list(presentations(lmax))
    for t in pres:
        if abs(det(t)) != 1:
            tally['ab'] += 1
            continue
        v, d = in_ball(t, B_)
        w = quotient_witness(t)
        if v is not None and w is not None:
            contradicts.append((t, v, d, w))
            continue
        if v is not None:
            cert = certificate(t, info)
            if cert is None:
                print("  FAIL could not build a certificate for", show_pres(t))
                ok = False
                tally['unres'] += 1
                unresolved.append(t)
                continue
            perm, mv = cert
            tally['ac'] += 1
            maxdepth = max(maxdepth, d)
            ac_rows.append((t, perm, mv, d))
            if certfile:
                pass
        elif w is not None:
            tally['quot'] += 1
        else:
            tally['unres'] += 1
            unresolved.append(t)
    print("  canonical presentations with total length <= %d: %d" % (lmax, len(pres)))
    print("    nontrivial, exponent-sum determinant not +-1 : %d" % tally['ab'])
    print("    nontrivial, explicit finite quotient          : %d" % tally['quot'])
    print("    AC-trivial, certificate built and replayed    : %d" % tally['ac'])
    print("    unresolved                                    : %d" % tally['unres'])
    print("    contradictions (in ball AND nontrivial quotient): %d" % len(contradicts))
    for c in contradicts[:5]:
        print("      CONTRADICTION", show_pres(c[0]), 'in ball at depth', c[2], 'witness', c[3])
    if contradicts:
        ok = False
        print("  FAIL consistency check")
    else:
        print("  PASS no presentation is both AC-trivial by the ball and certified nontrivial")
    if ac_rows:
        lens = [len(r[2]) for r in ac_rows]
        print("    certificate lengths (number of single moves, including the")
        print("    conjugations that realise cyclic permutation): min %d, max %d, mean %.2f"
              % (min(lens), max(lens), sum(lens) / len(lens)))
    if certfile and ac_rows:
        with open(certfile, 'w') as f:
            f.write("# AC certificates produced by census.py, radius %d, ball cap %d\n" % (lmax, cap))
            f.write("# columns: relator1 relator2 | relator order perm | moves separated by ';'\n")
            f.write("# a move is: inv i   or   mul i j   or   conj i g   (g = 1,-1,2,-2)\n")
            f.write("# apply the moves to the tuple reordered by perm; the result is (a,b)\n")
            for t, perm, mv, d in ac_rows:
                ms = ' ; '.join('%s %d %s' % (m[0], m[1], m[2] if m[2] is not None else '')
                                for m in mv)
                f.write("%s %s | %d %d | %s\n" % (show(t[0]), show(t[1]), perm[0], perm[1], ms))
        print("  certificates written to %s (%d rows)" % (certfile, len(ac_rows)))
    if unresolved:
        print("  first unresolved presentations (up to 10):")
        for t in unresolved[:10]:
            print("    ", show_pres(t))
    if tally['unres'] == 0:
        print("  PASS every canonical presentation at total length <= %d is resolved" % lmax)
    else:
        print("  NOTE %d presentations are not resolved at this radius" % tally['unres'])

    print("=" * 78)
    print("PART 5  unconstrained breadth-first levels from (BabAA, AbaBB)")
    depth_max = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    start = (parse('BabAA'), parse('AbaBB'))
    seen2 = {start: 0}
    q2 = deque([start])
    while q2:
        t = q2.popleft()
        d = seen2[t]
        if d >= depth_max:
            continue
        for _tag, u in moves(t):
            if u not in seen2:
                seen2[u] = d + 1
                q2.append(u)
    layers = {}
    for d in seen2.values():
        layers[d] = layers.get(d, 0) + 1
    got = [layers.get(d, 0) for d in range(depth_max + 1)]
    published = [1, 12, 101, 782, 5906, 44048, 326200, 2406914]
    print("  levels 0..%d reached: %s" % (depth_max, got))
    print("  published, Havas-Ramsay 2003 Sec. 2, levels 0..7: %s" % published[:depth_max + 1])
    if got == published[:depth_max + 1]:
        print("  PASS matches the published level counts exactly")
    else:
        ok = False
        print("  FAIL does not match the published level counts")

    print("=" * 78)
    print("OVERALL", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
