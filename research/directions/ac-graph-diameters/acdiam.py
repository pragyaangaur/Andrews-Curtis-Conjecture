#!/usr/bin/env python3
"""Exact diameters of the Andrews-Curtis graph Delta_k(G) of a finite group.

Definitions (Borovik, Lubotzky, Myasnikov, "The Finitary Andrews-Curtis
Conjecture", Progr. Math. 248 (2005) 15-30, Section 1; quoted in
survey/nielsen.md, Section 2.2):

  vertices of Delta_k(G) : the normally generating k-tuples (x_1,...,x_k);
  moves, with S = G    : (1) x_i -> x_i x_j^{+-1}   (i != j)
                         (2) x_i -> x_j^{+-1} x_i   (i != j)
                         (3) x_i -> x_i^{-1}
                         (4) x_i -> w^{-1} x_i w    for w in S.

The diameter is computed exactly, not bounded.  H = Aut(G) x S_k acts on
Delta_k(G) by graph automorphisms, so the eccentricity of a vertex depends
only on its H-orbit; one exact BFS per orbit gives every eccentricity and the
maximum is the diameter.  The distance distribution follows from the orbit
sizes and the per-orbit level counts.

Deterministic.  Needs numpy only.

  python3 acdiam.py --group data/A5 --k 2 --mode normal
"""

import argparse
import json
import os
import time

import numpy as np


def read_wrapped(path):
    """GAP breaks long printed lines with a backslash; undo that."""
    txt = open(path).read()
    return txt.replace("\\\n", "")


def load_group(d):
    m = int(open(os.path.join(d, "order.txt")).read().split()[0])
    rows = read_wrapped(os.path.join(d, "mult.txt")).strip().split("\n")
    mul = np.array([[int(t) for t in r.split()] for r in rows], dtype=np.int32)
    assert mul.shape == (m, m), (mul.shape, m)
    ident = [e for e in range(m) if all(mul[e, x] == x and mul[x, e] == x
                                       for x in range(m))]
    assert len(ident) == 1, ident
    one = ident[0]
    inv = np.zeros(m, dtype=np.int64)
    for x in range(m):
        cand = np.nonzero((mul[x] == one) & (mul[:, x] == one))[0]
        assert len(cand) == 1, (x, cand)
        inv[x] = cand[0]
    assert all(mul[x, inv[x]] == one and mul[inv[x], x] == one for x in range(m))

    def sublist(fname):
        out = []
        path = os.path.join(d, fname)
        if os.path.exists(path):
            for line in read_wrapped(path).split("\n"):
                line = line.strip()
                if line:
                    out.append(np.array([int(t) for t in line.split()], dtype=np.int64))
        return out

    return dict(name=os.path.basename(d.rstrip("/")), m=m, mul=mul, inv=inv, one=one,
                maxnorm=sublist("maxnorm.txt"), maxsub=sublist("maxsub.txt"),
                aut=sublist("aut.txt"))


def decode(codes, m, k):
    return [((codes // (m ** i)) % m).astype(np.int64) for i in range(k)]


def encode(cols, m, k):
    c = np.zeros(cols[0].shape, dtype=np.int64)
    for i in range(k):
        c = c + cols[i] * (m ** i)
    return c


def conj_table(gr):
    """conj[w][x] = w^-1 x w"""
    m, mul, inv = gr["m"], gr["mul"], gr["inv"]
    return [mul[mul[inv[w]], w].astype(np.int64) for w in range(m)]


def bad_mask(gr, k, mode):
    """codes that are NOT vertices: every entry inside one forbidden subgroup."""
    m = gr["m"]
    bad = np.zeros(m ** k, dtype=bool)
    subs = gr["maxnorm"] if mode == "normal" else gr["maxsub"]
    for N in subs:
        grids = np.meshgrid(*[N for _ in range(k)], indexing="ij")
        codes = encode([g.reshape(-1) for g in grids], m, k)
        bad[codes] = True
    return bad


MOVE_FLAGS = {
    # moveset: (number of multiplication variants, inversion allowed, conjugation allowed)
    "blm": (4, True, True),
    "free": (1, True, True),
    "nielsen": (4, True, False),
    "prg": (2, False, False),
    "prg_inv": (2, True, False),
}


def expand(frontier, gr, k, visited, conj, moveset="blm"):
    m, mul, inv = gr["m"], gr["mul"], gr["inv"]
    nreps, do_inv, do_conj = MOVE_FLAGS[moveset]
    cols = decode(frontier, m, k)
    out = []
    for i in range(k):
        ci = cols[i]
        pi = m ** i
        base = frontier - ci * pi
        if do_inv:
            cand = base + inv[ci] * pi                      # (3)
            mask = ~visited[cand]
            if mask.any():
                c2 = cand[mask]
                visited[c2] = True
                out.append(c2)
        for j in range(k):
            if j == i:
                continue
            cj = cols[j]
            if nreps == 4:
                reps = (mul[ci, cj], mul[ci, inv[cj]],
                        mul[cj, ci], mul[inv[cj], ci])
            elif nreps == 2:
                reps = (mul[ci, cj], mul[ci, inv[cj]])
            else:
                reps = (mul[ci, cj],)
            for nc in reps:
                cand = base + nc * pi
                mask = ~visited[cand]
                if mask.any():
                    c2 = cand[mask]
                    visited[c2] = True
                    out.append(c2)
        if do_conj:
            for w in range(m):
                nc = conj[w][ci]
                cand = base + nc * pi
                mask = ~visited[cand]
                if mask.any():
                    c2 = cand[mask]
                    visited[c2] = True
                    out.append(c2)
    if not out:
        return np.zeros(0, dtype=np.int64)
    return np.unique(np.concatenate(out))


def all_neighbours(tup, gr, k, moveset="blm"):
    """python-level neighbour list of one tuple (for certificate replay)"""
    m, mul, inv = gr["m"], gr["mul"], gr["inv"]
    out = []
    nreps, do_inv, do_conj = MOVE_FLAGS[moveset]
    for i in range(k):
        xi = int(tup[i])
        if do_inv:
            t = list(tup)
            t[i] = int(inv[xi])
            out.append(tuple(t))
        for j in range(k):
            if j == i:
                continue
            xj = int(tup[j])
            nreps = MOVE_FLAGS[moveset][0]
            if nreps == 4:
                vals = [int(mul[xi, xj]), int(mul[xi, inv[xj]]),
                        int(mul[xj, xi]), int(mul[inv[xj], xi])]
            elif nreps == 2:
                vals = [int(mul[xi, xj]), int(mul[xi, inv[xj]])]
            else:
                vals = [int(mul[xi, xj])]
            for v in vals:
                t = list(tup)
                t[i] = v
                out.append(tuple(t))
        if do_conj:
            for w in range(m):
                t = list(tup)
                t[i] = int(mul[mul[inv[w], xi], w])
                out.append(tuple(t))
    return out


def bfs(start, gr, k, mode, moveset="blm", work_cap=None):
    m = gr["m"]
    bad = bad_mask(gr, k, mode)
    if bad[start]:
        raise SystemExit("start is not a vertex")
    conj = conj_table(gr)
    visited = bad
    visited[start] = True
    frontier = np.array([start], dtype=np.int64)
    levels = [1]
    nreps, do_inv, do_conj = MOVE_FLAGS[moveset]
    per_vertex = k * ((1 if do_inv else 0) + nreps * (k - 1) + (m if do_conj else 0))
    work = 0
    while frontier.size:
        work += int(frontier.size) * per_vertex
        if work_cap is not None and work > work_cap:
            return dict(ecc=None, levels=levels, aborted=True, work=work)
        new = expand(frontier, gr, k, visited, conj, moveset)
        if not new.size:
            break
        levels.append(int(new.size))
        frontier = new
    return dict(ecc=len(levels) - 1, levels=levels, aborted=False, work=work)


def geodesic(start, target, gr, k, mode, moveset="blm"):
    """an exact shortest path start -> target, as a list of tuples, or None"""
    m = gr["m"]
    bad = bad_mask(gr, k, mode)
    seen = {start: None}
    frontier = [start]
    while frontier:
        nxt = []
        for code in frontier:
            tup = tuple(int(x[0]) for x in decode(np.array([code]), m, k))
            for nb in all_neighbours(tup, gr, k, moveset):
                nc = sum(nb[i] * (m ** i) for i in range(k))
                if nc in seen:
                    continue
                seen[nc] = code
                if nc == target:
                    path = [nb]
                    c = code
                    while c is not None:
                        path.append(tuple(int(x[0]) for x in decode(np.array([c]), m, k)))
                        c = seen[c]
                    path.reverse()
                    return path
                if not bad[nc]:
                    nxt.append(nc)
        frontier = nxt
    return None


def aut_perm_of_codes(gr, k, phi):
    m = gr["m"]
    codes = np.arange(m ** k, dtype=np.int64)
    cols = [phi[c] for c in decode(codes, m, k)]
    return encode(cols, m, k)


def orbits(gr, k, mode, verbose=True):
    """H-orbits on the code space, H = <Aut(G), coordinate permutations>.
    Returns (labels, counts, bad)."""
    m = gr["m"]
    size = m ** k
    bad = bad_mask(gr, k, mode)
    labels = np.arange(size, dtype=np.int64)
    gens = [aut_perm_of_codes(gr, k, phi) for phi in gr["aut"]]
    for i in range(k - 1):
        codes = np.arange(size, dtype=np.int64)
        cols = decode(codes, m, k)
        cols[i], cols[i + 1] = cols[i + 1], cols[i]
        gens.append(encode(cols, m, k))
    it = 0
    while True:
        it += 1
        new = labels.copy()
        for g in gens:
            np.minimum(new, labels[g], out=new)
        changed = int((new != labels).sum())
        labels = new
        if verbose:
            print("  orbit refinement %d: %d labels changed" % (it, changed), flush=True)
        if changed == 0:
            break
    uniq, lab, counts = np.unique(labels, return_inverse=True, return_counts=True)
    return lab.reshape(-1), counts, bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--mode", default="normal", choices=("normal", "generate"))
    ap.add_argument("--moveset", default="blm",
                    choices=("blm", "free", "nielsen", "prg", "prg_inv"))
    ap.add_argument("--max-orbits", type=int, default=10 ** 9)
    ap.add_argument("--work-cap", type=float, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    gr = load_group(args.group)
    m, k = gr["m"], args.k
    if m ** k > 2 * 10 ** 9:
        raise SystemExit("code space too large: %d" % (m ** k))
    t0 = time.time()
    print("group %s order %d k %d space %d mode %s moveset %s"
          % (gr["name"], m, k, m ** k, args.mode, args.moveset), flush=True)
    labels, counts, bad = orbits(gr, k, args.mode)
    nvert = int((~bad).sum())
    print("orbits of the whole space: %d ; vertices: %d ; %.1f s"
          % (len(counts), nvert, time.time() - t0), flush=True)
    vert = ~bad
    reps = {}
    for labset in np.unique(labels[vert]):
        codes = np.nonzero(vert & (labels == labset))[0]
        reps[int(labset)] = int(codes.min())
    print("distinct orbits meeting the vertex set: %d" % len(reps), flush=True)
    res = dict(group=gr["name"], m=m, k=k, mode=args.mode, moveset=args.moveset,
               nvertices=nvert, norbits=len(reps), orbits=[], diameter=None,
               aborted_orbits=0)
    order = sorted(reps.items(), key=lambda kv: kv[1])
    if len(order) > args.max_orbits:
        print("WARNING: %d orbits, only %d processed" % (len(order), args.max_orbits))
        order = order[:args.max_orbits]
    dist = {}
    diam = 0
    for labset, code in order:
        t1 = time.time()
        r = bfs(code, gr, k, args.mode, args.moveset, work_cap=args.work_cap)
        if r["aborted"]:
            print("  orbit %d start %d: ABORTED at work %g" % (labset, code, r["work"]),
                  flush=True)
            res["orbits"].append(dict(orbit=labset, start=code, ecc=None,
                                      levels=r["levels"]))
            res["aborted_orbits"] += 1
            continue
        for t, cnt in enumerate(r["levels"]):
            dist[t] = dist.get(t, 0) + cnt * int(counts[labset])
        diam = max(diam, r["ecc"])
        print("  orbit %d start %d size %d: ecc %d levels %s (%.1f s)"
              % (labset, code, int(counts[labset]), r["ecc"], r["levels"],
                 time.time() - t1), flush=True)
        res["orbits"].append(dict(orbit=labset, start=code, ecc=r["ecc"],
                                  levels=r["levels"], orbit_size=int(counts[labset])))
    res["diameter_exact"] = (res["aborted_orbits"] == 0 and len(order) == len(reps))
    res["diameter"] = diam
    res["distance_distribution"] = {str(t): int(dist[t]) for t in sorted(dist)}
    res["elapsed_s"] = time.time() - t0
    if args.out:
        open(args.out, "w").write(json.dumps(res, indent=1) + "\n")
    print(json.dumps({kk: res[kk] for kk in
                      ("group", "m", "k", "mode", "moveset", "nvertices", "norbits",
                       "diameter", "diameter_exact", "aborted_orbits",
                       "distance_distribution", "elapsed_s")}, indent=1))


if __name__ == "__main__":
    main()
