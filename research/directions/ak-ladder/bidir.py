"""Bidirectional ball search for AC certificates.

Forward search from the start tuple and backward search from the target tuple
use the same successor generator, because every Andrews-Curtis move is undone
by forward moves: inv(i) is its own inverse, conj(i,w) is undone by conj(i,w^-1)
and mul(i,j) is undone by inv(j), mul(i,j), inv(j).  When the two searches meet
the certificate is the forward path followed by the reversed backward path, and
the whole sequence is replayed by acx.verify.
"""

import sys
import time
import acx


def succ(rs, n, conjs):
    out = ball_like(rs, n, conjs)
    return out


def ball_like(rs, n, conjs):
    out = []
    for i in range(1, n + 1):
        out.append((("inv", i), acx.apply_move(rs, ("inv", i), n)))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if i == j:
                continue
            out.append((("mul", i, j), acx.apply_move(rs, ("mul", i, j), n)))
            t = acx.apply_move(rs, ("inv", j), n)
            t = acx.apply_move(t, ("mul", i, j), n)
            t = acx.apply_move(t, ("inv", j), n)
            out.append((("inv3", i, j), t))
    for i in range(1, n + 1):
        for w in conjs:
            out.append((("conj", i, w), acx.apply_move(rs, ("conj", i, w), n)))
    return out


def expand(move):
    if move[0] == "inv3":
        _, i, j = move
        return (("inv", j), ("mul", i, j), ("inv", j))
    if move[0] == "conj":
        return (move,)
    return (move,)


def invert_move(move):
    """Forward moves that undo `move`."""
    if move[0] == "inv":
        return (("inv", move[1]),)
    if move[0] == "conj":
        return (("conj", move[1], acx.inverse(tuple(move[2]))),)
    if move[0] == "mul":
        return (("inv", move[2]), ("mul", move[1], move[2]), ("inv", move[2]))
    if move[0] == "inv3":
        # ("inv3", i, j) means r_i -> r_i r_j^-1; its inverse is mul(i, j)
        return (("mul", move[1], move[2]),)
    raise ValueError(move)


def bidir(start, target, cap, depth, conj_len=2, max_states=6000000,
          verbose=True):
    start = tuple(start)
    target = tuple(target)
    n = len(start)
    conjs = [w for w in acx.words_up_to(n, conj_len) if w]
    if start == target:
        return ()
    F = {start: None}
    B = {target: None}
    frontF = [start]
    frontB = [target]
    df = db = 0
    while frontF and frontB:
        if len(frontF) <= len(frontB) and df < depth:
            df += 1
            nxt = []
            for rs in frontF:
                for mv, nrs in ball_like(rs, n, conjs):
                    if acx.total_length(nrs) > cap or nrs in F:
                        continue
                    F[nrs] = (rs, mv)
                    if nrs in B:
                        return assemble(F, B, nrs, n)
                    nxt.append(nrs)
                    if len(F) > max_states:
                        raise RuntimeError("state limit")
            frontF = nxt
            if verbose:
                print("F depth %2d  new %7d  visited %8d" % (df, len(nxt), len(F)),
                      flush=True)
        elif db < depth:
            db += 1
            nxt = []
            for rs in frontB:
                for mv, nrs in ball_like(rs, n, conjs):
                    if acx.total_length(nrs) > cap or nrs in B:
                        continue
                    B[nrs] = (rs, mv)
                    if nrs in F:
                        return assemble(F, B, nrs, n)
                    nxt.append(nrs)
                    if len(B) > max_states:
                        raise RuntimeError("state limit")
            frontB = nxt
            if verbose:
                print("B depth %2d  new %7d  visited %8d" % (db, len(nxt), len(B)),
                      flush=True)
        else:
            break
    return None


def assemble(F, B, meet, n):
    """Concatenate forward path start->meet with reversed path meet->target."""
    fwd = []
    cur = meet
    while F[cur] is not None:
        prev, mv = F[cur]
        fwd.append(mv)
        cur = prev
    fwd.reverse()
    bwd = []
    cur = meet
    while B[cur] is not None:
        child, mv = B[cur]
        # the move mv takes cur to child; undo it to go child -> cur
        bwd.append(invert_move(mv))
        cur = child
    moves = ()
    for m in fwd:
        moves += expand(m)
    for inv_seq in bwd:
        moves += inv_seq
    return moves


if __name__ == "__main__":
    which = sys.argv[1]
    cap = int(sys.argv[2])
    depth = int(sys.argv[3])
    if which == "ms3_1_2":
        start, target = acx.ms(3, acx.w_word(1)), acx.ms(3, acx.w_word(2))
    elif which == "ms4_1_2":
        start, target = acx.ms(4, acx.w_word(1)), acx.ms(4, acx.w_word(2))
    elif which == "ms5_1_2":
        start, target = acx.ms(5, acx.w_word(1)), acx.ms(5, acx.w_word(2))
    elif which == "ak5_ms5":
        start, target = acx.ak(5), acx.ms(5, acx.w_word(1))
    else:
        raise SystemExit("unknown %r" % which)
    t0 = time.time()
    mv = bidir(start, target, cap, depth)
    print("elapsed %.1f s" % (time.time() - t0))
    if mv is None:
        print("NOT FOUND")
        sys.exit(1)
    print("FOUND %d forward moves; replay %s"
          % (len(mv), acx.verify(start, mv, target, len(start))))
