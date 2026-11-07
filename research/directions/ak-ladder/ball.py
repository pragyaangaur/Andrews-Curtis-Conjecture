"""Ball search: exhaustive BFS from a tuple under all single AC moves, with a
total relator length cap, looking for a target tuple.

Every state keeps a back-pointer to its predecessor, so a hit yields an
explicit forward-move certificate, which is then replayed by acx.verify.

Conjugators are the reduced words of length at most conj_len.  Multiplying by
r_j^{-1} is generated as the three forward moves inv j, mul i j, inv j.
"""

import sys
import acx


def succ_with_moves(rs, n, conjs):
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
    return (move,)


def ball(start, target, cap, max_depth, conj_len=2, max_states=4000000,
         verbose=True):
    start = tuple(start)
    target = tuple(target)
    n = len(start)
    conjs = [w for w in acx.words_up_to(n, conj_len) if w]
    parent = {start: None}
    frontier = [start]
    if start == target:
        return []
    for depth in range(1, max_depth + 1):
        nxt = []
        for rs in frontier:
            for mv, nrs in succ_with_moves(rs, n, conjs):
                if acx.total_length(nrs) > cap:
                    continue
                if nrs in parent:
                    continue
                parent[nrs] = (rs, mv)
                if nrs == target:
                    path = []
                    cur = nrs
                    while parent[cur] is not None:
                        prev, m = parent[cur]
                        path.append(m)
                        cur = prev
                    path.reverse()
                    moves = ()
                    for m in path:
                        moves += expand(m)
                    return moves
                nxt.append(nrs)
                if len(parent) > max_states:
                    if verbose:
                        print("state limit at depth", depth, "visited", len(parent))
                    return None
        if verbose:
            print("depth %2d  new %7d  visited %8d" % (depth, len(nxt), len(parent)),
                  flush=True)
        frontier = nxt
        if not frontier:
            break
    return None


def main():
    what = sys.argv[1]
    cap = int(sys.argv[2])
    depth = int(sys.argv[3])
    conj_len = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    if what == "ms3_2_to_n11":
        start, target = acx.ms(3, acx.w_word(2)), acx.n11(3)
    elif what == "ms3_1_to_2":
        start, target = acx.ms(3, acx.w_word(1)), acx.ms(3, acx.w_word(2))
    elif what == "ak3_to_n11":
        start, target = acx.ak(3), acx.n11(3)
    elif what == "ms4_3_to_n11":
        start, target = acx.ms(4, acx.w_word(3)), acx.n11(4)
    else:
        raise SystemExit("unknown job %r" % what)
    print("start ", start, "total", acx.total_length(start))
    print("target", target, "total", acx.total_length(target))
    moves = ball(start, target, cap, depth, conj_len)
    if moves is None:
        print("NOT FOUND: no certificate within depth %d and total length cap %d"
              % (depth, cap))
        return 1
    ok = acx.verify(start, moves, target, len(start))
    print("FOUND certificate with %d forward moves; replay ok = %s" % (len(moves), ok))
    for m in moves:
        print("   ", m)
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
