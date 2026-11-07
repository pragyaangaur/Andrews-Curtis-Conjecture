#!/usr/bin/env python3
"""Check for survey/dynnikov.md.

Two purely graph-theoretic statements used in the proof of Lemma 3.1
(cases-k-lem) of I. Dynnikov, "On Zeeman's collapsibility conjecture for
non-standard polyhedra", arXiv:2608.23331v1, Section 3.

The lemma's proof reduces to: G is a connected simple 3-regular graph (the
link of a true vertex v of a 2-polyhedron whose true edges all have degree 3,
whose true vertices are all true, and which has no separating vertex); if G
has two vertex-disjoint cycles then condition (K5) holds; otherwise a
shortest cycle s of length m is taken and the argument concludes m <= 4 and
G is K_4, K_{3,3}, or the triangular prism.

(S1) Every connected simple cubic graph other than K_4, K_{3,3} and the
     triangular prism contains two vertex-disjoint cycles.
(S2) For every connected simple cubic graph G, every shortest cycle s with
     G - s acyclic has length at most 4.

(S1) and (S2) are checked exhaustively against nauty's geng for all connected
cubic graphs on 4,6,...,NMAX vertices.  Deterministic; no random choices.
The three facts about special trees quoted in the same proof are proved by
hand in survey/dynnikov.md (degree count; longest-path argument).

Run:  python3 survey/dynnikov_check.py [NMAX]      (default NMAX = 16)
"""
import itertools
import subprocess
import sys


def graph6_decode(line):
    """Decode a graph6 string into (n, adjacency sets)."""
    n = line[0] - 63
    bits = []
    for ch in line[1:]:
        v = ch - 63
        bits.extend([(v >> k) & 1 for k in (5, 4, 3, 2, 1, 0)])
    adj = [set() for _ in range(n)]
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i].add(j)
                adj[j].add(i)
            idx += 1
    return n, adj


def cycles_through(adj, n):
    """All simple cycles of an undirected graph, each once (as a vertex set list)."""
    out = []
    for start in range(n):
        stack = [(start, (start,))]
        while stack:
            v, path = stack.pop()
            for w in adj[v]:
                if w == start and len(path) >= 3:
                    out.append(path)
                elif w > start and w not in path:
                    stack.append((w, path + (w,)))
    return out


def has_two_disjoint_cycles(adj, n, cycles):
    sets = [frozenset(c) for c in cycles]
    for a, b in itertools.combinations(sets, 2):
        if not (a & b):
            return True
    return False


def closure_acyclic(adj, n, cyc):
    """Is the subgraph induced by V \\ cyc acyclic?  (cycle vertices deleted)"""
    keep = [v for v in range(n) if v not in cyc]
    parent = {v: v for v in keep}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for v in keep:
        for w in adj[v]:
            if w in parent and v < w:
                rv, rw = find(v), find(w)
                if rv == rw:
                    return False
                parent[rv] = rw
    return True


def shortest_cycle_length(adj, n, cycles):
    return min(len(c) for c in cycles)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    if nmax % 2:
        nmax += 1
    prism = [{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5},
             {0, 3}, {1, 4}, {2, 5}]
    k33 = [{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5},
           {2, 3}, {2, 4}, {2, 5}]
    k4 = [{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]
    known = [k4, k33, prism]
    total = 0
    s1_fail = []
    s2_fail = []
    for n in range(4, nmax + 1, 2):
        gen = subprocess.run(["nauty-geng", "-c", "-d3", "-D3", str(n)],
                             capture_output=True, text=True, check=True)
        lines = [ln for ln in gen.stdout.split("\n") if ln and not ln.startswith(">")]
        for ln in lines:
            nn, adj = graph6_decode(ln.encode("ascii"))
            assert nn == n
            total += 1
            cycles = cycles_through(adj, n)
            edges = frozenset(frozenset((v, w)) for v in range(n) for w in adj[v])
            is_known = any(edges == frozenset(frozenset(e) for e in g) for g in known)
            two = has_two_disjoint_cycles(adj, n, cycles)
            if not two and not is_known:
                s1_fail.append((n, ln, "two_disjoint=%s" % two))
            m = shortest_cycle_length(adj, n, cycles)
            for c in cycles:
                if len(c) != m:
                    continue
                if closure_acyclic(adj, n, set(c)) and m > 4:
                    s2_fail.append((n, ln, m))
                    break
    print("graphs checked:", total, "for n =", 4, "to", nmax, "step 2")
    print("(S1) connected cubic graphs outside {K_4, K_{3,3}, prism} without "
          "two vertex-disjoint cycles:", len(s1_fail))
    for f in s1_fail[:5]:
        print("    FAIL", f)
    print("(S2) shortest cycles whose deletion leaves a forest and whose "
          "length exceeds 4:", len(s2_fail))
    for f in s2_fail[:5]:
        print("    FAIL", f)
    print("OVERALL", "PASS" if not s1_fail and not s2_fail else "FAIL")


if __name__ == "__main__":
    main()
