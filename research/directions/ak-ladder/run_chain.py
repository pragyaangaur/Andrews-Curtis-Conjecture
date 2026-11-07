"""Build the full certificate chain AK(n) ~ AC MS(n,w_1) ~ ... ~ n11(n).

Each step is an exhaustive ball search with an exact total-length cap and
depth; on success the step certificate is stored and replayed, and the whole
composition is replayed as one sequence.
"""

import json
import os
import sys
import time
import acx
import ball


def step(job, start, target, cap, depth, conj_len=2, max_states=4000000):
    t0 = time.time()
    mv = ball.ball(start, target, cap, depth, conj_len, max_states, verbose=False)
    secs = round(time.time() - t0, 1)
    if mv is None:
        print("  NOT FOUND %-22s cap %2d depth %2d (%.1f s)"
              % (job, cap, depth, secs), flush=True)
        return None
    ok = acx.verify(start, mv, target, len(start))
    print("  FOUND     %-22s %3d moves  replay %s (%.1f s)"
          % (job, len(mv), ok, secs), flush=True)
    os.makedirs("certs", exist_ok=True)
    with open("certs/%s.json" % job, "w") as f:
        json.dump({"job": job, "start": [list(r) for r in start],
                   "target": [list(r) for r in target],
                   "moves": [list(m) for m in mv],
                   "cap": cap, "depth": depth, "conj_len": conj_len,
                   "seconds": secs, "replay_ok": ok}, f, indent=1)
    return list(mv)


def chain(n, depth_mid=24, depth_end=22):
    print("=== chain for n = %d" % n, flush=True)
    seq = []
    cur = acx.ak(n)
    tg = acx.ms(n, acx.w_word(1))
    mv = step("ak%d_to_ms%d_w1" % (n, n), cur, tg,
              max(acx.total_length(cur), acx.total_length(tg)) + 2, depth_mid)
    if mv is None:
        return None
    seq += mv
    cur = tg
    for k in range(1, n - 1):
        tg = acx.ms(n, acx.w_word(k + 1))
        mv = step("ms%d_w%d_to_w%d" % (n, k, k + 1), cur, tg,
                  max(acx.total_length(cur), acx.total_length(tg)) + 2, depth_mid)
        if mv is None:
            return None
        seq += mv
        cur = tg
    tg = acx.n11(n)
    mv = step("ms%d_w%d_to_n11" % (n, n - 1), cur, tg,
              acx.total_length(cur) + 1, depth_end)
    if mv is None:
        return None
    seq += mv
    full_ok = acx.verify(acx.ak(n), seq, acx.n11(n), 2)
    print("  COMPOSED  AK(%d) -> n11(%d): %d forward moves, replay %s"
          % (n, n, len(seq), full_ok), flush=True)
    with open("certs/chain_ak%d_to_n11.json" % n, "w") as f:
        json.dump({"job": "chain_ak%d_to_n11" % n,
                   "start": [list(r) for r in acx.ak(n)],
                   "target": [list(r) for r in acx.n11(n)],
                   "moves": [list(m) for m in seq],
                   "length": acx.total_length(acx.ak(n)),
                   "target_length": acx.total_length(acx.n11(n)),
                   "replay_ok": full_ok}, f, indent=1)
    return seq


if __name__ == "__main__":
    for n in [int(a) for a in sys.argv[1:]] or [3, 4]:
        chain(n)
