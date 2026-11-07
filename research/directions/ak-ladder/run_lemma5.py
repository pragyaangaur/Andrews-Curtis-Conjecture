"""Loop: the Lemma-5 step of Shehper et al. for n = 3, 4, ..., 12.

For each n the statement is MS(n, w_{n-1}) ~ AC <the n+11 tuple>, where
w_k = y^-k x^-1 y x y.  The paper proves it by rewriting relations; here each
instance is turned into an explicit forward-move certificate by exhaustive
ball search and replayed.  Also runs the k -> k+1 step for the same n, whose
certificates would make the chain AK(n) ~ MS(n,w_1) ~ ... ~ n11(n) explicit.
"""

import json
import os
import sys
import time
import acx
import ball


def run(job, start, target, cap, depth, conj_len=2, max_states=3000000):
    t0 = time.time()
    moves = ball.ball(start, target, cap, depth, conj_len, max_states,
                      verbose=False)
    secs = round(time.time() - t0, 1)
    if moves is None:
        print("NOT FOUND  %-24s cap %2d depth %2d  (%.1f s)"
              % (job, cap, depth, secs), flush=True)
        return None
    ok = acx.verify(start, moves, target, len(start))
    print("FOUND      %-24s %3d moves  replay %s  (%.1f s)"
          % (job, len(moves), ok, secs), flush=True)
    os.makedirs("certs", exist_ok=True)
    with open("certs/%s.json" % job, "w") as f:
        json.dump({"job": job,
                   "start": [list(r) for r in start],
                   "target": [list(r) for r in target],
                   "moves": [list(m) for m in moves],
                   "cap": cap, "depth": depth, "conj_len": conj_len,
                   "seconds": secs, "replay_ok": ok}, f, indent=1)
    return moves


def main():
    ns = [int(a) for a in sys.argv[1:]] or list(range(3, 13))
    depth = 20
    for n in ns:
        start = acx.ms(n, acx.w_word(n - 1))
        target = acx.n11(n)
        cap = acx.total_length(start) + 1
        run("ms%d_w%d_to_n11" % (n, n - 1), start, target, cap, depth)
    for n in ns:
        for k in range(1, n - 1):
            start = acx.ms(n, acx.w_word(k))
            target = acx.ms(n, acx.w_word(k + 1))
            cap = acx.total_length(start) + 2
            run("ms%d_w%d_to_w%d" % (n, k, k + 1), start, target, cap, 14)


if __name__ == "__main__":
    main()
