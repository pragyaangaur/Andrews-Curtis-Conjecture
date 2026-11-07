"""Substitution-search: BFS over rotation and overlap-substitution moves.

Usage:  python3 subst_search.py n k_start k_goal max_depth max_nodes
        python3 subst_search.py n ak target    (start AK(n), target the n+11 tuple)

Every state is a tuple of reduced words.  The move set is a subset of the three
Andrews-Curtis moves (each move comes with its explicit expansion, see
subst.py), so any path found is a valid certificate.
"""

import sys
import json
import acx
import subst


def bfs(start, target, max_depth, max_nodes, total_cap, verbose=True):
    start = tuple(start)
    target = tuple(target)
    if start == target:
        return []
    seen = {start}
    frontier = [(start, ())]
    nodes = 1
    for depth in range(1, max_depth + 1):
        nxt = []
        for rs, path in frontier:
            moves = subst.substitution_moves(rs, len(rs))
            moves += subst.rotation_moves(rs, len(rs))
            for mv, nrs in moves:
                if acx.total_length(nrs) > total_cap:
                    continue
                if nrs in seen:
                    continue
                nodes += 1
                if nodes > max_nodes:
                    if verbose:
                        print("node limit %d reached at depth %d" % (max_nodes, depth))
                    return None
                newpath = path + mv
                if nrs == target:
                    return newpath
                seen.add(nrs)
                nxt.append((nrs, newpath))
        if verbose:
            print("depth %2d  frontier %6d  visited %8d" % (depth, len(nxt), len(seen)))
        frontier = nxt
        if not frontier:
            break
    return None


def main():
    args = sys.argv[1:]
    n = int(args[0])
    if args[1] == "ak":
        start = acx.ak(n)
        target = acx.n11(n)
    else:
        k0, k1 = int(args[1]), int(args[2])
        start = acx.ms(n, acx.w_word(k0))
        target = acx.ms(n, acx.w_word(k1))
    max_depth = int(args[-2]) if len(args) >= 4 else 8
    max_nodes = int(args[-1]) if len(args) >= 4 else 200000
    cap = max(acx.total_length(start), acx.total_length(target)) + 6
    print("start ", start, "len", acx.total_length(start))
    print("target", target, "len", acx.total_length(target))
    path = bfs(start, target, max_depth, max_nodes, cap)
    if path is None:
        print("NOT FOUND within depth %d, %d nodes, total length cap %d"
              % (max_depth, max_nodes, cap))
        return 1
    ok = acx.verify(start, path, target, n)
    print("FOUND a path of %d forward moves; verified: %s" % (len(path), ok))
    for m in path:
        print("   ", m)
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
