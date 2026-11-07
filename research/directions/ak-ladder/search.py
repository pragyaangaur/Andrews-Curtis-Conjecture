"""Beam and greedy searches for length reduction inside the AK(n) ladder.

Deterministic: all randomness comes from random.Random(seed) with a seed that
is passed in and printed, and no dict ordering is relied on.
"""

import random
import sys
import acx


def conjs_of(n, maxlen):
    return [w for w in acx.words_up_to(n, maxlen) if w]


def succ_list(rs, n, conjs):
    """Successors: inv, right multiplication by r_j and by r_j^-1, conj."""
    out = []
    for i in range(1, n + 1):
        out.append((("inv", i), acx.apply_move(rs, ("inv", i), n)))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if i == j:
                continue
            out.append((("mul", i, j), acx.apply_move(rs, ("mul", i, j), n)))
            # right multiplication by r_j^-1, as three forward moves
            m1 = ("inv", j)
            t1 = acx.apply_move(rs, m1, n)
            m2 = ("mul", i, j)
            t2 = acx.apply_move(t1, m2, n)
            m3 = ("inv", j)
            out.append((("inv+mul+inv", i, j), acx.apply_move(t2, m3, n)))
    for i in range(1, n + 1):
        for w in conjs:
            out.append((("conj", i, w), acx.apply_move(rs, ("conj", i, w), n)))
    return out


def expand_move(move):
    """Expand a compound tag into forward-move tags."""
    if move[0] == "inv+mul+inv":
        _, i, j = move
        return (("inv", j), ("mul", i, j), ("inv", j))
    return (move,)


def beam(start, n, conjs, beam_width, rounds, max_total, rng, target=None,
         verbose=False):
    """Beam search keeping the beam_width states of least total length.

    Returns the list of states visited best-first for diagnostics, and, if the
    total length ever drops below max_total (or the target is hit), the path.
    """
    start_t = tuple(start)
    cur = [(acx.total_length(start_t), start_t, ())]
    best_len = acx.total_length(start_t)
    best_path = ()
    best_state = start_t
    seen = {start_t}
    for r in range(rounds):
        cand = []
        for L, rs, path in cur:
            for m, nrs in succ_list(rs, n, conjs):
                if acx.total_length(nrs) > max_total:
                    continue
                if nrs in seen:
                    continue
                seen.add(nrs)
                cand.append((acx.total_length(nrs), nrs, path + expand_move(m)))
        if not cand:
            break
        cand.sort(key=lambda t: (t[0], t[1]))
        # keep a beam of the best states, plus a seeded random tail for
        # diversification
        head = cand[:beam_width]
        tail = cand[beam_width:]
        if tail:
            rng.shuffle(tail)
            head = head + tail[:max(1, beam_width // 8)]
        cur = [(L, rs, p) for (L, rs, p) in head]
        for L, rs, p in head:
            if L < best_len:
                best_len, best_path, best_state = L, p, rs
        if verbose and (r % 10 == 0 or best_len < acx.total_length(start_t)):
            print("round %3d  best total length %2d  (frontier %d)"
                  % (r, best_len, len(cur)))
        if target is not None and any(rs == tuple(target) for _, rs, _ in head):
            for L, rs, p in head:
                if rs == tuple(target):
                    return best_len, best_state, p, True
        if best_len < acx.total_length(start_t):
            break
    return best_len, best_state, best_path, best_len < acx.total_length(start)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    beam_width = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    conj_len = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 20261104
    target = acx.n11(n) if len(sys.argv) > 6 and sys.argv[6] == "target" else None
    conjs = conjs_of(2, conj_len)
    rng = random.Random(seed)
    start = acx.ak(n)
    L0 = acx.total_length(start)
    cap = L0 + (n if target is None else 2)
    best_len, best_state, path, hit = beam(
        start, 2, conjs, beam_width, rounds, cap, rng, target=target,
        verbose=True)
    print("n=%d start length %d  best found %d  moves %d" %
          (n, L0, best_len, len(path)))
    print("best state:", best_state)
    print("hit target:", hit)


if __name__ == "__main__":
    main()
