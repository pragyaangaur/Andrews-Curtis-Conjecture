"""Andrews-Curtis moves on a tuple of relators of the free group F_n.

A presentation is a tuple ``rs`` of n reduced words in F_n, the i-th entry
being the relator r_i.  The three AC moves are, for 1 <= i, j <= n, i != j:

    ('inv',  i)        r_i -> r_i^{-1}
    ('mul',  i, j)     r_i -> r_i r_j
    ('conj', i, w)     r_i -> w r_i w^{-1}

A move tag is exactly one of these tuples, so a sequence of tags is a
machine-checkable certificate that two presentations are AC-equivalent: replay
the tags and compare.  See ``verify_path``.

Positions i, j are 1-based and index r_1, ..., r_n.

Nothing here is random or heuristic.  Written for Python 3.12.
"""

from __future__ import annotations

import words as W


# --------------------------------------------------------------------------
# presentations
# --------------------------------------------------------------------------

def check_presentation(rs, n):
    """Raise ValueError unless rs is a tuple of n reduced words in F_n."""
    if not isinstance(rs, tuple):
        raise ValueError("a presentation must be a tuple of words")
    if len(rs) != n:
        raise ValueError("expected %d relators, got %d" % (n, len(rs)))
    for r in rs:
        W.check_word(r, n)
        if not W.is_reduced(r):
            raise ValueError("relator %r is not reduced" % (r,))
    return rs


def standard(n):
    """The standard presentation of the trivial group: (x_1, ..., x_n)."""
    return tuple((g,) for g in W.generators(n))


def is_standard(rs, n):
    """True when rs is exactly the standard presentation of rank n."""
    return tuple(rs) == standard(n)


def ak_presentation(k):
    """AK(k) = <x, y | x y x = y x y, x^k = y^{k+1}> as a rank-2 tuple.

    Source of the family: Akbulut and Kirby, "A potential smooth counterexample
    in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and
    the Andrews-Curtis conjecture", Topology 24 (1985) 375-380.
    """
    if k < 1:
        raise ValueError("k must be positive")
    first = W.parse_word("xyxYXY")
    second = W.mul(tuple([1] * k), tuple([-2] * (k + 1)))
    return (first, second)


# --------------------------------------------------------------------------
# moves
# --------------------------------------------------------------------------

def apply_move(rs, move, n):
    """Apply one AC move tag to rs and return the new reduced tuple.

    The move is applied to the presentation as it stands, so callers must apply
    tags one at a time in order.
    """
    check_presentation(rs, n)
    kind = move[0]
    t = list(rs)
    if kind == "inv":
        (i,) = move[1:]
        _check_pos(i, n)
        t[i - 1] = W.inverse(t[i - 1])
    elif kind == "mul":
        i, j = move[1], move[2]
        _check_pos(i, n)
        _check_pos(j, n)
        if i == j:
            raise ValueError("mul needs i != j")
        t[i - 1] = W.mul(t[i - 1], t[j - 1])
    elif kind == "conj":
        i, w = move[1], move[2]
        _check_pos(i, n)
        W.check_word(w, n)
        w = W.reduce_word(w)
        t[i - 1] = W.conjugate(t[i - 1], w)
    else:
        raise ValueError("unknown move kind %r" % (kind,))
    return tuple(t)


def _check_pos(i, n):
    if not (1 <= i <= n):
        raise ValueError("relator index %r out of range 1..%d" % (i, n))


def conjugators(n, max_conj_len):
    """All non-identity reduced words of length at most max_conj_len, ordered.

    The identity is excluded because conjugating by it changes nothing.
    """
    return [w for w in W.all_words(n, max_conj_len) if w]


def successors(rs, n, conj_list):
    """All successors of rs under one AC move, as a list of (move, new_tuple).

    ``conj_list`` is an explicit list of conjugators, so the edge set is
    exactly determined by the caller.  The order is fixed: all inversions, then
    all right multiplications, then all conjugations in the order of conj_list.
    Moves that leave the tuple unchanged are dropped.
    """
    check_presentation(rs, n)
    out = []
    for i in range(1, n + 1):
        mv = ("inv", i)
        out.append((mv, apply_move(rs, mv, n)))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if i == j:
                continue
            mv = ("mul", i, j)
            out.append((mv, apply_move(rs, mv, n)))
    for i in range(1, n + 1):
        for w in conj_list:
            mv = ("conj", i, w)
            out.append((mv, apply_move(rs, mv, n)))
    return [(mv, s) for mv, s in out if s != rs]


def verify_path(start, moves, n):
    """Replay a list of move tags from start and return the final presentation.

    Every tag is applied by ``apply_move``, which validates it, so a tag list
    that replays without raising is a certificate of AC-equivalence.
    """
    rs = start
    for mv in moves:
        rs = apply_move(rs, mv, n)
    return rs


# --------------------------------------------------------------------------
# invariants of the relator tuple
# --------------------------------------------------------------------------

def abelianization(rs, n):
    """The exponent-sum matrix of rs, an n x n integer matrix.

    Under the AC moves this changes by left multiplication by an element of
    GL_n(Z): ('inv', i) negates row i, ('mul', i, j) adds row j to row i, and
    ('conj', i, w) leaves every row unchanged.  Hence the subgroup of Z^n
    generated by the rows, and in particular the Smith normal form, is an
    AC-invariant of the presentation.
    """
    return W.exp_sum_matrix(rs, n)


def abelianization_invariant(rs, n):
    """Smith normal form of the exponent-sum matrix: unchanged by AC moves."""
    return W.smith_elementary_divisors(abelianization(rs, n))


def has_trivial_abelianization(rs, n):
    """True when the abelianisation of the presentation is the trivial group.

    Equivalent to the exponent-sum matrix having determinant +1 or -1.  The
    standard presentation passes this test and every presentation reached from
    it by AC moves passes it too, so failing the test is a proof of
    non-equivalence.
    """
    return W.is_unimodular(abelianization(rs, n))


def relator_lengths(rs):
    """The multiset of relator lengths, as a sorted tuple."""
    return tuple(sorted(len(r) for r in rs))
