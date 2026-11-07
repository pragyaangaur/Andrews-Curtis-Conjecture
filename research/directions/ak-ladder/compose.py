"""Compose the stored step certificates into one chain per ladder rung.

For n = 2, ..., 5 the chain runs

    AK(n) -> MS(n,w_1) -> MS(n,w_2) -> ... -> MS(n,w_{n-1}) -> P(n)

where P(n) is the length-(n+1+10) presentation stated in Theorem t:n+11 of
arXiv:2408.15332v2.  The composed move list is replayed as a single sequence by
acx and by verify_cert.py, so the composition is not taken on trust.
"""

import glob
import json
import os
import sys
import acx


def load(job):
    path = "certs/%s.json" % job
    if not os.path.exists(path):
        return None
    with open(path) as f:
        d = json.load(f)
    return [tuple(m) for m in d["moves"]]


def compose(n):
    steps = []
    jobs = ["ak%d_to_ms%d_w1" % (n, n)]
    for k in range(1, n - 1):
        jobs.append("ms%d_w%d_to_w%d" % (n, k, k + 1))
    jobs.append("ms%d_w%d_to_P%d" % (n, n - 1, n))
    moves = []
    for j in jobs:
        m = load(j)
        if m is None:
            print("n=%d: missing step %s" % (n, j))
            return None
        steps.append((j, len(m)))
        moves += m
    start, target = acx.ak(n), acx.p_form(n)
    ok = acx.verify(start, moves, target, 2)
    rs = acx.ak(n)
    lens = [acx.total_length(rs)]
    for m in moves:
        rs = acx.apply_move(rs, m, 2)
        lens.append(acx.total_length(rs))
    out = {"job": "chain_ak%d_to_P%d" % (n, n),
           "start": [list(r) for r in start],
           "target": [list(r) for r in target],
           "moves": [list(m) for m in moves],
           "steps": steps,
           "start_length": acx.total_length(start),
           "final_length": acx.total_length(target),
           "max_length_on_path": max(lens),
           "min_length_after_start": min(lens),
           "replay_ok": ok}
    with open("certs/chain_ak%d_to_P%d.json" % (n, n), "w") as f:
        json.dump(out, f, indent=1)
    print("n=%d: %d moves, %d -> %d, max on path %d, replay %s"
          % (n, len(moves), out["start_length"], out["final_length"],
             out["max_length_on_path"], ok))
    return out


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [2, 3, 4, 5]
    bad = 0
    for n in ns:
        r = compose(n)
        if r is None or not r["replay_ok"]:
            bad += 1
    print("composed %d chains, %d failed" % (len(ns), bad))
    sys.exit(0 if bad == 0 else 1)
