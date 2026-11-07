"""Exact depth profile of the length landscape around AK(n).

For each n and each depth d, breadth-first search over ALL single Andrews-Curtis
moves (inv, right multiplication by r_j or r_j^-1, conjugation by a reduced word
of length at most conj_len) with a total-length cap, recording

  * the number of distinct tuples at distance exactly d,
  * the minimum total relator length among them,
  * whether any tuple at distance <= d has total length below 2n+7.

Results are written to profile.json (append per n, one line each) so that a
long run can be checkpointed.  Deterministic: successors are generated in a
fixed order and nothing depends on dict ordering.
"""

import json
import sys
import time
import acx

CACHE = {}


def conjs_of(n, maxlen):
    key = (n, maxlen)
    if key not in CACHE:
        CACHE[key] = [w for w in acx.words_up_to(n, maxlen) if w]
    return CACHE[key]


def succ(rs, n, conjs):
    out = []
    for i in range(1, n + 1):
        out.append(acx.apply_move(rs, ("inv", i), n))
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if i == j:
                continue
            out.append(acx.apply_move(rs, ("mul", i, j), n))
            t = acx.apply_move(rs, ("inv", j), n)
            t = acx.apply_move(t, ("mul", i, j), n)
            t = acx.apply_move(t, ("inv", j), n)
            out.append(t)
    for i in range(1, n + 1):
        for w in conjs:
            out.append(acx.apply_move(rs, ("conj", i, w), n))
    return out


def profile(n, max_depth, conj_len, cap_slack, max_states):
    conjs = conjs_of(2, conj_len)
    start = acx.ak(n)
    L0 = acx.total_length(start)
    cap = L0 + cap_slack
    seen = {start}
    frontier = [start]
    rows = []
    best = L0
    t0 = time.time()
    for d in range(1, max_depth + 1):
        nxt = []
        for rs in frontier:
            for nrs in succ(rs, 2, conjs):
                if acx.total_length(nrs) > cap:
                    continue
                if nrs in seen:
                    continue
                seen.add(nrs)
                nxt.append(nrs)
                L = acx.total_length(nrs)
                if L < best:
                    best = L
        rows.append({"n": n, "depth": d, "states_at_depth": len(nxt),
                     "min_total": min((acx.total_length(t) for t in nxt),
                                      default=None),
                     "best_total": best, "visited": len(seen),
                     "seconds": round(time.time() - t0, 1)})
        print(rows[-1], flush=True)
        frontier = nxt
        if not frontier or len(seen) > max_states:
            break
    return {"n": n, "start_total": L0, "cap": cap, "conj_len": conj_len,
            "rows": rows}


def main():
    n = int(sys.argv[1])
    max_depth = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    conj_len = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    cap_slack = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    max_states = int(sys.argv[5]) if len(sys.argv) > 5 else 3000000
    out = profile(n, max_depth, conj_len, cap_slack, max_states)
    with open("profile_n%02d.json" % n, "w") as f:
        json.dump(out, f, indent=1)
    print("written profile_n%02d.json" % n)


if __name__ == "__main__":
    main()
