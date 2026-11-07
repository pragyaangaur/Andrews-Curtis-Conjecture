"""End-to-end certificates AK(n) ~ P(n) for every n in a range, built from
three components, all of them uniform in n:

  (A)  AK(n) -> MS(n,w_1)        2n+9 moves  (patterns.mms_pattern)
  (L)  MS(n,w_k) -> MS(n,w_(k+1)) 10 moves each, k = 1..n-2 (ladder_template)
  (B)  MS(n,w_(n-1)) -> P(n)      9 moves    (patterns.lemma5_pattern)

The ladder steps are NOT searched: each is built from the Britton reduction of
an explicit correction word, see ladder_template.py.  Every assembled chain is
replayed by acx.verify before it is accepted.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))


import json
import os
import sys
import time

import acx
import patterns
import ladder_template as lt


def full_chain(n):
    start = acx.ak(n)
    moves = list(patterns.mms_pattern(n))
    for k in range(1, n - 1):
        mv = lt.ladder_cert(n, k)
        if mv is None:
            return None
        moves.extend(mv)
    moves.extend(patterns.lemma5_pattern())
    return moves


def main():
    ns = [int(a) for a in sys.argv[1:]] or list(range(2, 9))
    os.makedirs("certs", exist_ok=True)
    for n in ns:
        t0 = time.time()
        mv = full_chain(n)
        if mv is None:
            print("n=%2d  NO CERTIFICATE" % n, flush=True)
            continue
        start, target = acx.ak(n), acx.p_form(n)
        ok = acx.verify(start, mv, target, 2)
        rs = tuple(start)
        maxlen = acx.total_length(rs)
        for m in mv:
            rs = acx.apply_move(rs, m, 2)
            maxlen = max(maxlen, acx.total_length(rs))
        print("n=%2d  |AK|=%2d |P|=%2d  moves %3d  max total %3d  replay %s  (%.2f s)"
              % (n, acx.total_length(start), acx.total_length(target), len(mv), maxlen, ok,
                 time.time() - t0), flush=True)
        if ok:
            fn = "certs/chain_uniform_%d.json" % n
            with open(fn, "w") as f:
                json.dump({"job": "chain_uniform_n%d" % n,
                           "start": [list(r) for r in start],
                           "target": [list(r) for r in target],
                           "moves": [list(m)[:2] + [list(m[2])] if m[0] == "conj" else list(m)
                                     for m in mv],
                           "construction": "patterns.mms_pattern + ladder_template.ladder_cert + patterns.lemma5_pattern",
                           "replay_ok": ok}, f, indent=1)


if __name__ == "__main__":
    main()
