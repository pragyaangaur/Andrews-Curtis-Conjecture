"""Bounded attempt to trivialise the length-reduced forms P(n) = n+11.

P(n) is AC-equivalent to AK(n) (chain_all.py), so a successful trivialisation
of P(n) for n = 3 would prove AK(3) AC-trivial, which is open.  What this
script produces is a bounded negative: an exhaustive statement about all
tuples of total relator length at most `cap` reachable from P(n) in at most
`depth` moves, with conjugators of length at most `clen`.

Reported for every box: the number of tuples reached, the smallest relator
length seen, the smallest total length seen, and whether the standard tuple
(x,y) (or its inverse/conjugate forms of length 1) was reached.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))


import sys
import time

import acx


def rank2_basis(rs):
    """True if the two relators are a basis of F_2, i.e. the tuple is
    AC-equivalent to the standard tuple <x,y | x, y> by inspection."""
    return all(len(r) == 1 for r in rs)


def search(start, cap, depth, clen=2, max_states=3000000, verbose=True):
    n = len(start)
    conjs = [w for w in acx.words_up_to(n, clen) if w]
    start = tuple(tuple(r) for r in start)
    seen = {start}
    frontier = [start]
    best_rel = min(len(r) for r in start)
    best_tot = acx.total_length(start)
    arg_best = start
    found = rank2_basis(start)
    t0 = time.time()
    for d in range(depth):
        nxt = []
        for rs in frontier:
            for m, nrs in acx.successors(rs, n, conjs):
                if nrs in seen or acx.total_length(nrs) > cap:
                    continue
                seen.add(nrs)
                nxt.append(nrs)
                br = min(len(r) for r in nrs)
                if br < best_rel:
                    best_rel = br
                    arg_best = nrs
                bt = acx.total_length(nrs)
                if bt < best_tot:
                    best_tot = bt
                if rank2_basis(nrs):
                    found = True
        frontier = nxt
        if verbose:
            print("  depth %2d: new %8d  total %9d  best relator %2d  best total %2d  (%.1f s)"
                  % (d + 1, len(nxt), len(seen), best_rel, best_tot, time.time() - t0),
                  flush=True)
        if len(seen) > max_states:
            print("  state cap %d reached at depth %d" % (max_states, d + 1), flush=True)
            break
        if not frontier:
            break
    return dict(states=len(seen), best_rel=best_rel, best_tot=best_tot,
                arg_best=arg_best, standard=found, depth=depth, cap=cap)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    depth = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    start = acx.p_form(n)
    print("P(%d) start %r  total %d" % (n, start, acx.total_length(start)))
    r = search(start, cap, depth)
    print("RESULT n=%d cap=%d depth=%d: %r" % (n, cap, depth, r))
