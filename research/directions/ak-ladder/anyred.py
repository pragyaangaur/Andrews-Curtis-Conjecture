"""Find any length-reducing tuple reachable from AK(n) inside a length cap.

Target is a predicate (total length strictly below the start length) rather
than a fixed tuple, so this is the cheapest route to a certified length
reduction for a ladder rung.
"""

import json
import os
import sys
import time
import acx
import bidir


def any_shorter(n, cap, depth, max_states=4000000, verbose=True):
    start = acx.ak(n)
    L0 = acx.total_length(start)
    conjs = [w for w in acx.words_up_to(2, 2) if w]
    parent = {start: None}
    frontier = [start]
    for d in range(1, depth + 1):
        nxt = []
        for rs in frontier:
            for mv, nrs in bidir.ball_like(rs, 2, conjs):
                if acx.total_length(nrs) > cap:
                    continue
                if nrs in parent:
                    continue
                parent[nrs] = (rs, mv)
                if acx.total_length(nrs) < L0:
                    path = []
                    cur = nrs
                    while parent[cur] is not None:
                        prev, m = parent[cur]
                        path.append(m)
                        cur = prev
                    path.reverse()
                    moves = ()
                    for m in path:
                        moves += bidir.expand(m)
                    return moves, nrs, len(parent)
                nxt.append(nrs)
                if len(parent) > max_states:
                    if verbose:
                        print("state limit at depth %d" % d, flush=True)
                    return None, None, len(parent)
        if verbose:
            print("depth %2d  new %7d  visited %8d" % (d, len(nxt), len(parent)),
                  flush=True)
        frontier = nxt
        if not frontier:
            break
    return None, None, len(parent)


def main():
    ns = [int(a) for a in sys.argv[1:]] or [5]
    for n in ns:
        for slack in (1, 2):
            cap = acx.total_length(acx.ak(n)) + slack
            t0 = time.time()
            mv, end, seen = any_shorter(n, cap, 18)
            print("n=%d cap=%d  %s  (%.1f s, %d states)"
                  % (n, cap,
                     "FOUND %d moves, reached length %d" % (len(mv), acx.total_length(end))
                     if mv else "no shorter tuple",
                     time.time() - t0, seen), flush=True)
            if mv:
                ok = acx.verify(acx.ak(n), mv, end, 2)
                os.makedirs("certs", exist_ok=True)
                with open("certs/ak%d_shorten.json" % n, "w") as f:
                    json.dump({"job": "ak%d_shorten" % n,
                               "start": [list(r) for r in acx.ak(n)],
                               "target": [list(r) for r in end],
                               "moves": [list(m) for m in mv],
                               "cap": cap, "replay_ok": ok}, f, indent=1)
                print("   replay", ok, "target", end)
                break


if __name__ == "__main__":
    main()
