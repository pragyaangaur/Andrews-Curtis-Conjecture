"""Full closure of a tuple under rotation and overlap-substitution moves.

The point: this move set is a subset of the three Andrews-Curtis moves (see
subst.py for the expansion of every substitution into four forward moves), so
anything not in the closure is not reachable by these particular AC paths.  If
the closure is finite and small, the "substitute a derived relation into a
relator" style of proof cannot be doing what it appears to do.
"""

import sys
import json
import acx
import subst


def closure(start, total_cap, max_states=2000000, verbose=True):
    start = tuple(start)
    seen = {start}
    frontier = [start]
    depth = 0
    while frontier:
        depth += 1
        nxt = []
        for rs in frontier:
            for mv, nrs in (subst.substitution_moves(rs, len(rs)) +
                            subst.rotation_moves(rs, len(rs))):
                if acx.total_length(nrs) > total_cap:
                    continue
                if nrs in seen:
                    continue
                seen.add(nrs)
                nxt.append(nrs)
                if len(seen) > max_states:
                    if verbose:
                        print("state limit reached at depth", depth)
                    return seen, depth, True
        if verbose:
            print("depth %2d  new %6d  closure %8d" % (depth, len(nxt), len(seen)))
        frontier = nxt
    return seen, depth, False


def main():
    kind = sys.argv[1] if len(sys.argv) > 1 else "ms3"
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    if kind == "ms3":
        start = acx.ms(3, acx.w_word(1))
        targets = {"ms(3,w_2)": acx.ms(3, acx.w_word(2)),
                   "ms(3,w_3)": acx.ms(3, acx.w_word(3)),
                   "n11(3)": acx.n11(3), "AK(3)": acx.ak(3)}
    else:
        start = acx.ms(4, acx.w_word(1))
        targets = {"ms(4,w_2)": acx.ms(4, acx.w_word(2)),
                   "n11(4)": acx.n11(4), "AK(4)": acx.ak(4)}
    print("start", start, "length", acx.total_length(start))
    seen, depth, truncated = closure(start, cap)
    print("closure size %d, depth %d, truncated %s" % (len(seen), depth, truncated))
    for name, t in targets.items():
        print("  target %-12s in closure: %s" % (name, tuple(t) in seen))
    with open("closure_%s_cap%d.json" % (kind, cap), "w") as f:
        json.dump({"start": [list(r) for r in start], "size": len(seen),
                   "depth": depth, "truncated": truncated,
                   "targets": {k: (tuple(v) in seen) for k, v in
                               targets.items()}}, f, indent=1)


if __name__ == "__main__":
    main()
