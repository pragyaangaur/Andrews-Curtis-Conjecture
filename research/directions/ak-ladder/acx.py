"""Independent Andrews-Curtis engine (m3, Round 2, direction E-ladder).

Written from scratch for directions/ak-ladder/; it shares no code with
toolkit/.  A word in F_n is a tuple of nonzero ints; i is x_i and -i is
x_i^{-1}.  A presentation is a tuple of n reduced words in F_n.

Moves on the tuple (r_1,...,r_n), 1-based i != j, w any word in F_n:

    ('inv',  i)      r_i -> r_i^{-1}
    ('mul',  i, j)   r_i -> r_i r_j          (right multiplication)
    ('mulL', i, j)   r_i -> r_j r_i          (left multiplication; two
                                              forward moves when needed)
    ('conj', i, w)   r_i -> w r_i w^{-1}

The three forward moves used in certificates are inv, mul and conj; mulL is
offered only as a derived convenience and each use of it is expanded into
forward moves when a certificate is written out.  Actually simpler: the
verifier accepts exactly inv, mul, conj, and search only generates those.
"""

from itertools import product


# ---------------------------------------------------------------- words

def is_reduced(w):
    for k in range(len(w) - 1):
        if w[k] == -w[k + 1]:
            return False
    return True


def reduce_word(w):
    out = []
    for a in w:
        if a == 0:
            raise ValueError("0 is not a letter")
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inverse(w):
    return tuple(-a for a in reversed(w))


def mul(a, b):
    return reduce_word(tuple(a) + tuple(b))


def conj(w, r):
    """w r w^{-1}"""
    return mul(mul(w, r), inverse(w))


def exp_sum(w, n):
    return tuple(sum(1 for a in w if a == g) - sum(1 for a in w if a == -g)
                 for g in range(1, n + 1))


def conj_cyclic(w, k):
    """The conjugate of w by its length-k prefix (a cyclic permutation)."""
    p = tuple(w[:k])
    return mul(mul(p, w), inverse(p))


# ---------------------------------------------------------------- moves

def apply_move(rs, move, n):
    kind = move[0]
    t = list(rs)
    if kind == "inv":
        i = move[1]
        t[i - 1] = inverse(t[i - 1])
    elif kind == "mul":
        i, j = move[1], move[2]
        if i == j:
            raise ValueError("mul needs i != j")
        t[i - 1] = mul(t[i - 1], t[j - 1])
    elif kind == "conj":
        i, w = move[1], move[2]
        t[i - 1] = conj(reduce_word(w), t[i - 1])
    else:
        raise ValueError("unknown move %r" % (move,))
    return tuple(t)


def verify(start, moves, target, n=None):
    """Replay moves from start; return True iff the result is target."""
    if n is None:
        n = len(start)
    rs = tuple(start)
    for m in moves:
        rs = apply_move(rs, m, n)
    return rs == tuple(target)


def total_length(rs):
    return sum(len(r) for r in rs)


# ---------------------------------------------------------------- families

XYX = (1, 2, 1, -2, -1, -2)          # x y x y^-1 x^-1 y^-1


def ak(n):
    """AK(n) = <x,y | xyx = yxy, x^n = y^{n+1}> as a rank-2 tuple."""
    return (XYX, tuple([1] * n) + tuple([-2] * (n + 1)))


def ms(n, w):
    """MS(n,w) = <x,y | x^-1 y^n x = y^(n+1), x = w> as a rank-2 tuple."""
    return (reduce_word((-1,) + tuple([2] * n) + (1,) + tuple([-2] * (n + 1))),
            reduce_word((-1,) + tuple(w)))


def w_word(k):
    """w_k = y^-k x^-1 y x y."""
    return tuple([-2] * k) + (-1, 2, 1, 2)


def n11(n):
    """Shehper et al. length n+11 presentation, as a rank-2 tuple.

    <x,y | y^-1 x^2 y = x y^-1 x,  y x y = x y^(n-1) x>
    """
    a = (-2, 1, 1, 2)                    # y^-1 x^2 y
    b = (1, -2, 1)                       # x y^-1 x
    t1 = mul(a, inverse(b))              # a b^-1
    c = (2, 1, 2)                        # y x y
    d = (1,) + tuple([2] * (n - 1)) + (1,)   # x y^(n-1) x
    t2 = mul(c, inverse(d))
    return (t1, t2)


# ---------------------------------------------------------------- search

def words_up_to(n, maxlen):
    """All reduced words in F_n of length <= maxlen, ordered by length."""
    out = []
    for L in range(maxlen + 1):
        for w in product(*[range(1, n + 1)] * L):
            for signs in product((1, -1), repeat=L):
                cand = tuple(s * g for s, g in zip(signs, w))
                if is_reduced(cand):
                    out.append(cand)
    return out


def successors(rs, n, conjs):
    """All one-move successors, in a fixed order: inv, mul, conj."""
    out = []
    for i in range(1, n + 1):
        out.append((("inv", i), apply_move(rs, ("inv", i), n)))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if i != j:
                out.append((("mul", i, j), apply_move(rs, ("mul", i, j), n)))
    for i in range(1, n + 1):
        for w in conjs:
            out.append((("conj", i, w), apply_move(rs, ("conj", i, w), n)))
    return out


def bfs(start, target, n=None, max_depth=12, max_total=40, conjs=None,
        max_nodes=2000000):
    """Breadth-first search from start, with a total length cap.

    Returns (depth, moves) or None if the target is not reached within the
    caps.  Deterministic: successors come in a fixed order and the frontier is
    a list.
    """
    if n is None:
        n = len(start)
    if conjs is None:
        conjs = words_up_to(n, 2)
    seen = {tuple(start)}
    frontier = [(tuple(start), ())]
    nodes = 0
    for depth in range(max_depth + 1):
        nxt = []
        for rs, path in frontier:
            if rs == tuple(target):
                return (len(path), path)
            if len(path) >= max_depth:
                continue
            for m, nrs in successors(rs, n, conjs):
                nodes += 1
                if nodes > max_nodes:
                    return None
                if nrs in seen or total_length(nrs) > max_total:
                    continue
                seen.add(nrs)
                nxt.append((nrs, path + (m,)))
        frontier = nxt
        if not frontier:
            break
    for rs, path in frontier:
        if rs == tuple(target):
            return (len(path), path)
    return None


def p_form(n):
    """The length n+11 presentation exactly as stated in Theorem t:n+11.

    <x,y | x^-1 y x = x y x^-1 y,  x y^(n-1) x = y x y>
    """
    a = (-1, 2, 1)                      # x^-1 y x
    b = (1, 2, -1, 2)                   # x y x^-1 y
    t1 = mul(a, inverse(b))
    c = (1,) + tuple([2] * (n - 1)) + (1,)   # x y^(n-1) x
    d = (2, 1, 2)                       # y x y
    t2 = mul(c, inverse(d))
    return (t1, t2)
