#!/usr/bin/env python3
"""Containment reduction, ball membership, and certificate construction.

A move is a triple (i, kind, arg):
    (i, 0, 0)     invert relator i
    (i, 1, g)     conjugate relator i by the generator g
    (i, 2, 0)     multiply relator i on the right by the other relator
The same triples are what c14lib.moves yields, so apply() and moves() agree.
"""
import c14lib as L

VAR_CACHE = {}


# ------------------------------------------------------------ step (C) test
def contained_in(u, v):
    """Is some cyclic permutation or inverse of v a contiguous cyclic subword
    of u?  Requires 0 < |v| <= |u|."""
    if not v or len(v) > len(u):
        return False
    uu = L.as_bytes(u + u)
    for x in L.word_variants(v):
        if L.as_bytes(x) in uu:
            return True
    return False


def containment(t):
    """(index of the containing relator, index of the contained relator) or None."""
    if contained_in(t[0], t[1]):
        return (0, 1)
    if contained_in(t[1], t[0]):
        return (1, 0)
    return None


def xi_eq_xj_pow(r):
    """Is r, up to cyclic permutation and inversion, of the form x_i x_j^m with
    i != j, that is, does r have exactly one letter of one generator and only
    the other generator besides?  (Havers-Ramsay step (D).)"""
    for x in L.word_variants(r):
        if len(x) <= 1:
            return True
        seen = {}
        for z in x:
            seen[z] = seen.get(z, 0) + 1
        for single, c in seen.items():
            if c != 1:
                continue
            others = [z for z in seen if z != single]
            if len(others) == 1 and abs(others[0]) != abs(single):
                return True
    return False


# ------------------------------------------------------------ moves
def apply(t, mv):
    i, kind, arg = mv
    r = list(t)
    if kind == 0:
        r[i] = L.inv(r[i])
    elif kind == 1:
        r[i] = L.conj((arg,), r[i])
    else:
        r[i] = L.mul(r[i], r[1 - i])
    return (r[0], r[1])


def apply_all(t, mvs):
    for m in mvs:
        t = apply(t, m)
    return t


def rot_k(w, k):
    k %= len(w) if w else 1
    return w[k:] + w[:k]


def moves_to_variant(i, r, target):
    """Moves on relator i taking r to target, where target is a cyclic
    permutation of r or of its inverse.  Returns a list or None."""
    for eps in (0, 1):
        base = L.inv(r) if eps else r
        if not base:
            if target == ():
                return [(i, 0, 0)] if eps else []
            continue
        for k in range(len(base)):
            if rot_k(base, k) == target:
                mv = ([(i, 0, 0)] if eps else [])
                mv += [(i, 1, -p) for p in base[:k]]
                return mv
    return None


# ------------------------------------------------------------ containment step
def reduce_step(t, idx):
    """One containment reduction: t[1-idx] contains t[idx].  Returns (new tuple,
    moves) with strictly smaller total length, or None."""
    big = t[1 - idx]
    small = t[idx]
    for x in sorted(L.word_variants(small)):
        if not x or len(x) > len(big):
            continue
        for k in range(len(big)):
            if rot_k(big, k)[:len(x)] != x:
                continue
            mv1 = moves_to_variant(idx, small, L.inv(x))
            if mv1 is None:
                continue
            mv2 = [(1 - idx, 1, -p) for p in big[:k]]
            mv3 = [(1 - idx, 2, 0)]
            mv4 = [(1 - idx, 1, -p) for p in x]
            mv = mv1 + mv2 + mv3 + mv4
            cur = apply_all(t, mv)
            if sum(len(z) for z in cur) < sum(len(z) for z in t):
                return cur, mv
    return None


def full_reduce(t):
    """Reduce by containments until none is left.  Returns (tuple, moves)."""
    cur = t
    chain = []
    while True:
        c = containment(cur)
        if c is None:
            return cur, chain
        r = reduce_step(cur, c[1])
        if r is None:
            return cur, chain
        cur, mv = r
        chain = chain + mv


# ------------------------------------------------------------ ball membership
def variants_word(w):
    if w not in VAR_CACHE:
        VAR_CACHE[w] = sorted(L.word_variants(w))
    return VAR_CACHE[w]


def best_variant(t, depth):
    """(base tuple, variant of least depth): base is t or the swap of its
    relators, and the variant lies in the ball."""
    best = None
    bestd = None
    for perm in (0, 1):
        base = t if perm == 0 else (t[1], t[0])
        for a in variants_word(base[0]):
            for b in variants_word(base[1]):
                d = depth.get(L.pack((a, b)))
                if d is not None and (bestd is None or d < bestd):
                    best = (base, (a, b))
                    bestd = d
    return best


def descend(depth, v):
    """Descent in the ball from v to the start.  The move set is not symmetric
    (the inverse of a multiplication is a three-move sequence), so both single
    moves and three-move back-steps are tried."""
    mv = []
    cur = v
    while depth[L.pack(cur)] > 0:
        d = depth[L.pack(cur)] - 1
        found = None
        for m, u in L.moves(cur):
            if depth.get(L.pack(u)) == d:
                found = ([m], u)
                break
        if found is None:
            for j in (0, 1):
                seq = [(j, 0, 0), (1 - j, 2, 0), (j, 0, 0)]
                u = apply_all(cur, seq)
                if depth.get(L.pack(u)) == d:
                    found = (seq, u)
                    break
        if found is None:
            return None
        mv = mv + list(found[0])
        cur = found[1]
    return mv


def symmetry_moves(t, v):
    """Moves taking t to v, where v[i] is a cyclic permutation of t[i] or of its
    inverse; None if that is not the case."""
    mv = []
    for i in (0, 1):
        m = moves_to_variant(i, t[i], v[i])
        if m is None:
            return None
        mv = mv + m
    return mv


def certificate(t, depth):
    """(start tuple, moves) taking the start tuple to the standard tuple, or
    (None, None).  The start tuple is t or the swap of its relators: the relator
    order is notational and the move set is symmetric in it."""
    bv = best_variant(t, depth)
    if bv is None:
        return None, None
    base, v = bv
    mv1 = symmetry_moves(base, v)
    if mv1 is None:
        return None, None
    mv2 = descend(depth, v)
    if mv2 is None:
        return None, None
    mv = list(mv1) + list(mv2)
    if apply_all(base, mv) != ((1,), (2,)):
        return None, None
    return base, mv


# ------------------------------------------------------------ certificate text
TOK_LETTER = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}


def mv_token(m):
    i, kind, arg = m
    if kind == 0:
        return 'i%d' % i
    if kind == 1:
        return 'c%d%s' % (i, TOK_LETTER[arg])
    return 'm%d' % i


def write_cert(f, start, moves, end_label):
    f.write('%s|%s|%s\n' % (L.fmt_pres(start),
                            ' '.join(mv_token(m) for m in moves), end_label))
