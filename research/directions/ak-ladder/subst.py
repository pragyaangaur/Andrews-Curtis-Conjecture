"""Overlap-substitution moves: the AC-level content of a relational substitution.

Mechanism (proved in notes.md and checked in code below).  Let (r_1,...,r_n) be
the current relator tuple.  Suppose r_i, read cyclically, is u b for a word u,
and suppose a cyclic conjugate t of r_j^{eps} (j != i, eps = +-1) has the form
t = v u^{-1} as a word.  Then the tuple with r_i replaced by the cyclic word
v b is AC-equivalent to the current tuple, by the four forward moves

    conj j  w          (r_j -> t, w = the rotation prefix)
    conj i  t          (r_i -> t r_i t^{-1})
    mul   i j          (        t r_i)
    conj j  w^{-1}     (restore r_j)

followed by reduction; a cyclic rotation of r_i is itself a forward move
(conj i by a prefix of r_i).

Consequently, at AC level the only "substitution of a relation into a relator"
that is legal in one step replaces a word u by the complementary word v of a
cyclic conjugate of another relator.  Products of conjugates are not available
as blocks, because a multiplication can add only one conjugate at a time and
the tuple, hence the set of usable conjugates, changes with every move.
"""

import acx


def rotations(w):
    """All cyclic conjugates of the reduced word w, as words."""
    out = []
    for k in range(len(w)):
        out.append(acx.conj_cyclic(w, k))
    return out


def rotation_moves(rs, n):
    """r_i -> any cyclic conjugate of r_i, with the certificate moves."""
    out = []
    for i in range(1, n + 1):
        r = rs[i - 1]
        for k in range(1, len(r)):
            p = tuple(r[:k])
            moves = (("conj", i, p),)
            out.append((moves, acx.apply_move(rs, ("conj", i, p), n)))
    return out


def substitution_moves(rs, n, max_results=None):
    """All one-substitution successors of rs, with certificate moves.

    A successor comes with a list of forward-move tags that realises exactly
    that change starting from rs.
    """
    out = []
    for i in range(1, n + 1):
        ri = rs[i - 1]
        for j in range(1, n + 1):
            if i == j:
                continue
            rj = rs[j - 1]
            for eps in (1, -1):
                qe = rj if eps == 1 else acx.inverse(rj)
                for k, c in enumerate(rotations(qe)):
                    if not c:
                        continue
                    prefix = tuple(qe[:k])
                    # t = c = v u^{-1}
                    for s in range(0, len(c)):
                        v = c[:s]
                        u = acx.inverse(c[s:])
                        if not u:
                            continue
                        if len(u) > len(ri):
                            continue
                        if ri[:len(u)] != u:
                            continue
                        rest = ri[len(u):]
                        newr = acx.mul(v, rest)
                        if len(newr) == 0:
                            continue        # an empty relator is not allowed here
                        t = c
                        head = () if eps == 1 else (("inv", j),)
                        tail = () if eps == 1 else (("inv", j),)
                        moves = head + (
                            ("conj", j, prefix),
                            ("conj", i, t),
                            ("mul", i, j),
                            ("conj", j, acx.inverse(prefix)),
                        ) + tail
                        newrs = list(rs)
                        newrs[i - 1] = newr
                        out.append((moves, tuple(newrs)))
                        if max_results is not None and len(out) >= max_results:
                            return out
    return out


def check_substitution_moves(rs, n, limit=40):
    """Every substitution move must be replayable by its stated moves."""
    bad = 0
    for moves, nrs in substitution_moves(rs, n)[:limit]:
        if not acx.verify(rs, moves, nrs, n):
            bad += 1
    return bad
