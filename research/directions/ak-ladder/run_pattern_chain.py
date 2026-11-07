"""End-to-end certificates AK(n) ~ AC P(n) using the two uniform patterns.

Step 0 (AK(n) to MS(n,w_1)) and the last step (MS(n,w_(n-1)) to P(n)) are given
by explicit move templates that do not depend on any search: the first has
2n+9 moves and was checked for n = 4..30, the second has 9 moves and was
checked for n = 3..30.  Only the middle steps MS(n,w_k) to MS(n,w_(k+1)) are
searched, by the bidirectional search.
"""

import json
import os
import sys
import time
import acx
import bidir


def mms_pattern(n):
    mv = [("inv", 1), ("conj", 1, (-2, -1)), ("conj", 2, tuple([-1] * (n - 1))),
          ("mul", 1, 2), ("inv", 1), ("mul", 2, 1), ("inv", 1),
          ("conj", 2, (-1,)), ("inv", 1)]
    for _ in range(n - 1):
        mv += [("mul", 1, 2), ("conj", 1, (1,))]
    mv = mv[:-1] + [("conj", 1, (2, 1)), ("inv", 2), ("inv", 1)]
    return mv


def lemma5_pattern():
    return [("inv", 2), ("conj", 1, (-2, 1)), ("conj", 2, (1, 2)), ("mul", 1, 2),
            ("inv", 1), ("conj", 2, (-1, 2)), ("mul", 1, 2), ("inv", 1),
            ("conj", 2, (1,))]


def middle(n, k, slack=4, depth=20, max_states=4000000):
    st = acx.ms(n, acx.w_word(k))
    tg = acx.ms(n, acx.w_word(k + 1))
    cap = max(acx.total_length(st), acx.total_length(tg)) + slack
    t0 = time.time()
    try:
        mv = bidir.bidir(st, tg, cap, depth, 2, max_states, verbose=False)
    except RuntimeError as exc:
        print("  ABORTED  ms%d_w%d_to_w%d  %s (%.1f s)"
              % (n, k, k + 1, exc, time.time() - t0), flush=True)
        return None
    secs = round(time.time() - t0, 1)
    if mv is None:
        print("  NOT FOUND ms%d_w%d_to_w%d cap %d depth %d (%.1f s)"
              % (n, k, k + 1, cap, depth, secs), flush=True)
        return None
    ok = acx.verify(st, mv, tg, 2)
    print("  FOUND     ms%d_w%d_to_w%d %3d moves replay %s (%.1f s)"
          % (n, k, k + 1, len(mv), ok, secs), flush=True)
    os.makedirs("certs", exist_ok=True)
    with open("certs/ms%d_w%d_to_w%d.json" % (n, k, k + 1), "w") as f:
        json.dump({"job": "ms%d_w%d_to_w%d" % (n, k, k + 1),
                   "start": [list(r) for r in st],
                   "target": [list(r) for r in tg],
                   "moves": [list(m) for m in mv], "cap": cap, "depth": depth,
                   "conj_len": 2, "seconds": secs, "replay_ok": ok}, f, indent=1)
    return list(mv)


def chain(n, slack=4, depth=20):
    print("=== chain for n = %d" % n, flush=True)
    seq = list(mms_pattern(n))
    if not acx.verify(acx.ak(n), seq, acx.ms(n, acx.w_word(1)), 2):
        print("  pattern step fails at n=%d" % n)
        return None
    for k in range(1, n - 1):
        mv = middle(n, k, slack, depth)
        if mv is None:
            return None
        seq += mv
    tail = lemma5_pattern()
    if not acx.verify(acx.ms(n, acx.w_word(n - 1)), tail, acx.p_form(n), 2):
        print("  Lemma-5 pattern fails at n=%d" % n)
        return None
    seq += tail
    ok = acx.verify(acx.ak(n), seq, acx.p_form(n), 2)
    rs = acx.ak(n)
    lens = [acx.total_length(rs)]
    for m in seq:
        rs = acx.apply_move(rs, m, 2)
        lens.append(acx.total_length(rs))
    print("  COMPOSED  AK(%d) -> P(%d): %d moves, %d -> %d, max %d, replay %s"
          % (n, n, len(seq), lens[0], lens[-1], max(lens), ok), flush=True)
    with open("certs/chain_ak%d_to_P%d.json" % (n, n), "w") as f:
        json.dump({"job": "chain_ak%d_to_P%d" % (n, n),
                   "start": [list(r) for r in acx.ak(n)],
                   "target": [list(r) for r in acx.p_form(n)],
                   "moves": [list(m) for m in seq],
                   "start_length": lens[0], "final_length": lens[-1],
                   "max_length_on_path": max(lens), "replay_ok": ok}, f, indent=1)
    return seq


if __name__ == "__main__":
    args = [a for a in sys.argv[1:]]
    slack, depth, ns = 4, 20, []
    for a in args:
        if a.startswith("slack="):
            slack = int(a.split("=")[1])
        elif a.startswith("depth="):
            depth = int(a.split("=")[1])
        else:
            ns.append(int(a))
    for n in ns:
        chain(n, slack, depth)
