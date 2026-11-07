"""f2.py -- rank-2 free-group words, the twelve restricted AC moves, class keys.

Written from the specifications in
  directions/resisters/push.c        (move table, class key)
  directions/resisters/round4/acx.c  (class key, letter codes)
The letter codes follow acx.c: a=0 A=1 b=2 B=3, inverse is code XOR 1.

A word is a tuple of nonzero ints: a=1, A=-1, b=2, B=-2.
A pair (presentation) is a tuple (r0, r1) of words.

Move indices (push.c convention):
  0    invert r0
  1-4  conjugate r0 by a, A, b, B
  5    invert r1
  6-9  conjugate r1 by a, A, b, B
  10   r0 := r0 * r1   (freely reduced)
  11   r1 := r1 * r0
"""
LETTER = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
INV = {1: -1, -1: 1, 2: -2, -2: 2}


def parse(s):
    out = []
    for ch in s:
        if ch in 'aAbB':
            out.append({'a': 1, 'A': -1, 'b': 2, 'B': -2}[ch])
        elif ch == 'e':
            break
        else:
            raise ValueError('bad letter %r in %r' % (ch, s))
    return tuple(out)


def show(w):
    return ''.join(LETTER[x] for x in w) if w else 'e'


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(-x for x in reversed(w))


def mul(u, v):
    return reduce(tuple(u) + tuple(v))


def conj(w, g):
    """g w g^{-1}, freely reduced."""
    return reduce(tuple(g) + tuple(w) + inv(g))


def is_cyclic_reduced(w):
    return not w or w[0] != -w[-1]


def cycred(w):
    a, b = 0, len(w) - 1
    while b > a and w[a] == -w[b]:
        a += 1
        b -= 1
    return tuple(w[a:b + 1])


def rotations(w):
    n = len(w)
    return [tuple(w[i:] + w[:i]) for i in range(n)]


def least_rotation(w):
    if not w:
        return ()
    return min(rotations(w))


# --- class key, exactly push.c / acx.c -------------------------------------
# byte map: a->3, A->2, b->4, B->1 ; compare bytes lexicographically.
BYTE = {1: 3, -1: 2, 2: 4, -2: 1}
UNBYTE = {3: 1, 2: -1, 4: 2, 1: -2}


def least_form(w):
    c = cycred(w)
    if not c:
        return ()
    f = tuple(BYTE[x] for x in c)
    g = tuple(5 - BYTE[x] for x in reversed(c))
    return min(rotations(f) + rotations(g))


def class_key(pair):
    """canonical form of a pair: each relator to its least form, then sorted.
    Preserved by conjugation, inversion and relator swap."""
    a = least_form(pair[0])
    b = least_form(pair[1])
    return tuple(sorted((a, b), key=lambda w: (len(w), w)))


def key_str(pair):
    out = []
    for w in class_key(pair):
        s = ''.join({3: 'a', 2: 'A', 4: 'b', 1: 'B'}[x] for x in w)
        out.append(s if s else 'e')
    return ','.join(out)


def key_of_str(s):
    return class_key(parse_pair(s))


def key_str_from_key(k):
    out = []
    for w in k:
        s = ''.join({3: 'a', 2: 'A', 4: 'b', 1: 'B'}[x] for x in w)
        out.append(s if s else 'e')
    return ','.join(out)


# --- the twelve restricted moves -------------------------------------------
CONJ_LETTERS = (1, -1, 2, -2)


def moves(pair):
    """yield (move index, new pair) for the twelve restricted moves."""
    r0, r1 = pair
    yield 0, (inv(r0), r1)
    for i, g in enumerate(CONJ_LETTERS):
        yield 1 + i, (conj(r0, (g,)), r1)
    yield 5, (r0, inv(r1))
    for i, g in enumerate(CONJ_LETTERS):
        yield 6 + i, (r0, conj(r1, (g,)))
    yield 10, (mul(r0, r1), r1)
    yield 11, (r0, mul(r1, r0))


def step(pair, m):
    for idx, nxt in moves(pair):
        if idx == m:
            return nxt
    raise ValueError('bad move %r' % (m,))


def apply_path(pair, path):
    cur = pair
    for m in path:
        cur = step(cur, m)
    return cur


def total_len(pair):
    return len(pair[0]) + len(pair[1])


def replay(start, target, path):
    """walk the path, returning (end, peak total length, list of states)."""
    cur = start
    peak = total_len(cur)
    states = [cur]
    for m in path:
        cur = step(cur, m)
        states.append(cur)
        peak = max(peak, total_len(cur))
    if cur != target:
        raise ValueError('replay ends at %s, not %s' % (show_pair(cur), show_pair(target)))
    return cur, peak, states


def show_pair(pair):
    return '%s,%s' % (show(pair[0]), show(pair[1]))


def parse_pair(s):
    a, b = s.split(',')
    return (parse(a), parse(b))


REV = {0: [0], 5: [5], 1: [2], 2: [1], 3: [4], 4: [3],
       6: [7], 7: [6], 8: [9], 9: [8], 10: [5, 10, 5], 11: [0, 11, 0]}


def reverse_path(path):
    """the inverse walk: each move replaced by an explicit sequence of the
    twelve that undoes it (conjugation by g is undone by conjugation by g^-1,
    multiplication by r_j is undone by inverting r_j, multiplying, inverting
    back)."""
    out = []
    for m in reversed(path):
        out.extend(REV[m])
    return out
