#!/usr/bin/env python3
"""deep_search.py -- bounded depth-first search for AC proofs of the l = 12
presentations that the length-13 ball of census.py does not reach.

Deterministic: fixed move order, no randomness, node budgets counted in
expansions.  Any proof found is emitted in the certificate format of census.py
and re-verified by check_certs.py.

    python3 deep_search.py [cap] [max_depth] [budget]
"""

import sys

import census as C
import enum_check as E


def is_standard(t):
    if C.total_len(t) != 2:
        return False
    e = sorted((abs(x) for x in C.exps(t[0]) + C.exps(t[1])))
    return e == [0, 1] and all(len(r) == 1 for r in t)


def deep_proof(t0, cap, max_depth, budget):
    """Iterative deepening depth-first search.  Returns (moves, nodes) or (None, nodes)."""
    nodes = 0
    for limit in range(1, max_depth + 1):
        visited = {t0: 0}
        best = [None]

        def dfs(t, depth, path):
            nonlocal nodes
            if nodes > budget:
                return False
            if is_standard(t):
                best[0] = list(path)
                return True
            if depth == limit:
                return False
            nodes += 1
            children = []
            for tag, u in C.moves(t):
                if C.total_len(u) > cap:
                    continue
                if u in visited and visited[u] <= depth + 1:
                    continue
                children.append((C.total_len(u), str(tag), tag, u))
            children.sort()
            for _l, _s, tag, u in children:
                old = visited.get(u)
                visited[u] = depth + 1
                path.append(tag)
                if dfs(u, depth + 1, path):
                    return True
                path.pop()
                if old is None:
                    del visited[u]
                else:
                    visited[u] = old
                if nodes > budget:
                    return False
            return False

        if dfs(t0, 0, []):
            return best[0], nodes
        if nodes > budget:
            break
    return None, nodes


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    max_depth = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    budget = int(sys.argv[3]) if len(sys.argv) > 3 else 3000000
    l = 12
    rows = E.step_d(E.step_c(E.step_b(E.step_a(E.per_length(l)))))
    info = C.ball_with_parents(13)
    B = {t: v[0] for t, v in info.items()}
    todo = []
    for t in rows:
        if C.in_ball(t, B)[0] is not None:
            continue
        if C.quotient_witness(t) is not None:
            continue
        todo.append(t)
    print("l = %d: %d presentations on the reconstructed list, %d need a deeper search"
          % (l, len(rows), len(todo)))
    out = []
    for t in todo:
        mv, nodes = deep_proof(t, cap, max_depth, budget)
        if mv is None:
            print("  %s : NO PROOF within cap %d, depth %d, budget %d (%d nodes)"
                  % (C.show_pres(t), cap, max_depth, budget, nodes))
            continue
        # rebuild the certificate in the format of check_certs.py
        cur = t
        ok = True
        for m in mv:
            cur = C.apply_move(cur, m)
        ok = is_standard(cur)
        print("  %s : proof of %d moves, cap %d, depth %d, %d nodes, verified %s"
              % (C.show_pres(t), len(mv), cap, max_depth, nodes, 'YES' if ok else 'NO'))
        if ok:
            out.append((t, (0, 1), mv))
    if out:
        with open('certs_deep_l12.txt', 'w') as f:
            f.write("# AC certificates for the l = 12 list, from deep_search.py\n")
            f.write("# columns: relator1 relator2 | relator order perm | moves separated by ';'\n")
            f.write("# a move is: inv i   or   mul i j   or   conj i g   (g = 1,-1,2,-2)\n")
            for t, perm, mv in out:
                ms = ' ; '.join('%s %d %s' % (m[0], m[1], m[2] if m[2] is not None else '')
                                for m in mv)
                f.write("%s %s | %d %d | %s\n" % (C.show(t[0]), C.show(t[1]), perm[0], perm[1], ms))
        print("  wrote %d certificates to certs_deep_l12.txt" % len(out))
    return 0


if __name__ == '__main__':
    sys.exit(main())
