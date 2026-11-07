#!/usr/bin/env python3
"""c14lib.py -- rank-2 words, AC moves, and breadth-first balls, written for the
length-14 census.  Words are tuples of nonzero ints, 1 = a, -1 = A, 2 = b, -2 = B.
A presentation is a pair of words (r1, r2).  Tuples are packed exactly into one
int so that set membership is exact and cheap:

    key = len1 | len2 << 4 | code1 << 8 | code2 << (8 + 3*len1)

with code(w) = sum d_i * 8**i, d_i = 0,1,2,3 for a, A, b, B.  Since len1+len2
is at most the cap, the key is at most 8 + 3*cap bits and the packing is
injective.
"""

A, Ai, B, Bi = 1, -1, 2, -2
LETTER = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
DIGIT = {1: 0, -1: 1, 2: 2, -2: 3}
UNDIGIT = {0: 1, 1: -1, 2: 2, 3: -2}
POW8 = [1]
for _i in range(20):
    POW8.append(POW8[-1] * 8)


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


def tlen(t):
    return len(t[0]) + len(t[1])


def rotations(w):
    n = len(w)
    return [w[k:] + w[:k] for k in range(n)] if n else [()]


def cyclic_reduce(w):
    w = red(w)
    while w and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def exps(w):
    return (w.count(A) - w.count(Ai), w.count(B) - w.count(Bi))


def det(t):
    (p, q), (r, s) = exps(t[0]), exps(t[1])
    return p * s - q * r


BYTE_OF = {1: 1, -1: 2, 2: 3, -2: 4}
BY_CACHE = {}


def as_bytes(w):
    """A byte string with one byte per letter, for fast cyclic subword tests."""
    b = BY_CACHE.get(w)
    if b is None:
        b = bytes(BYTE_OF[x] for x in w)
        BY_CACHE[w] = b
    return b


def word_variants(r):
    """relator variants under cyclic permutation and inversion"""
    rots = rotations(r)
    out = set(rots)
    for x in rots:
        out.add(inv(x))
    return out


def canon_word(w):
    """canonical representative of the set {rotations and inverses of w}"""
    if not w:
        return ()
    return min(word_variants(w))


def canon_pres(t):
    """canonical form under relator order, cyclic rotation and inversion"""
    x, y = canon_word(t[0]), canon_word(t[1])
    if (len(y), y) < (len(x), x):
        x, y = y, x
    return (x, y)


# ---------------------------------------------------------------- packing
def code(w):
    c = 0
    for i, x in enumerate(w):
        c += DIGIT[x] * POW8[i]
    return c


def decode(c, n):
    return tuple(UNDIGIT[(c // POW8[i]) % 8] for i in range(n))


def pack(t):
    w1, w2 = t
    return (len(w1) | (len(w2) << 4) | (code(w1) << 8)
            | (code(w2) << (8 + 3 * len(w1))))


def unpack(k):
    l1 = k & 15
    l2 = (k >> 4) & 15
    c1 = (k >> 8) & (POW8[l1] - 1) if l1 else 0
    c2 = k >> (8 + 3 * l1)
    return (decode(c1, l1), decode(c2, l2))


# ---------------------------------------------------------------- moves
def moves(t):
    """The 12 restricted AC moves, in a fixed order: invert a relator,
    conjugate it by a generator or its inverse, multiply it on the right by the
    other relator.  These are exactly the moves implemented by apply()."""
    r1, r2 = t
    for i in (0, 1):
        x, y = (r1, r2) if i == 0 else (r2, r1)
        yield (i, 0, 0), ((inv(x), y) if i == 0 else (y, inv(x)))
        for g in (A, Ai, B, Bi):
            c = conj((g,), x)
            yield (i, 1, g), ((c, y) if i == 0 else (y, c))
    yield (0, 2, 0), (mul(r1, r2), r2)
    yield (1, 2, 0), (r1, mul(r2, r1))


def apply_move(t, mv):
    i, kind, arg = mv
    r = list(t)
    if kind == 0:
        r[i] = inv(r[i])
    elif kind == 1:
        r[i] = conj((arg,), r[i])
    else:
        r[i] = mul(r[i], r[1 - i])
    return (r[0], r[1])


def ball(cap, start=((A,), (B,))):
    """Depth map of the AC ball of `start` with total relator length at most cap."""
    s = pack(start)
    depth = {s: 0}
    frontier = [start]
    d = 0
    while frontier:
        nxt = []
        d += 1
        for t in frontier:
            for _tag, u in moves(t):
                if len(u[0]) + len(u[1]) <= cap:
                    k = pack(u)
                    if k not in depth:
                        depth[k] = d
                        nxt.append(u)
        frontier = nxt
    return depth


KIND = {'a': 1, 'A': -1, 'b': 2, 'B': -2}


def parse_w(s):
    return tuple(KIND[c] for c in s)


def fmt_pres(t):
    return ','.join(show(w) if w else 'e' for w in t)


def parse_pres(s):
    """'BAABa,BBBBAbA' -> pair of words"""
    a, b = s.split(',')
    return (parse_w(a), parse_w(b))


# ---------------------------------------------------------------- ball files
def save_ball(depth, path):
    import numpy as np
    ks = np.fromiter(depth.keys(), dtype=np.int64, count=len(depth))
    vs = np.fromiter(depth.values(), dtype=np.uint8, count=len(depth))
    np.savez_compressed(path, keys=ks, depths=vs)


def load_ball(path):
    import numpy as np
    z = np.load(path)
    ks = z['keys'].tolist()
    vs = z['depths'].tolist()
    return dict(zip(ks, vs))
