#!/usr/bin/env python3
"""Component-resolved diameters for move sets whose graph may be disconnected.

The vertex set and the H-orbits are as in acdiam.py.  Since an automorphism of
G maps a connected component of the graph onto a connected component (possibly
a different one), a component need not be a union of H-orbits; the component
partition is therefore computed on vertices, and inside each component the
eccentricity is read off from one BFS per orbit that the component meets
(eccentricity is orbit-invariant because the orbit is moved by graph
automorphisms).
"""
import argparse
import json
import sys
import time

import numpy as np

sys.path.insert(0, '.')
import acdiam


def component_partition(gr, k, mode, moveset, vert):
    """list of dicts: vertex array, orbit label set"""
    size = gr["m"] ** k
    done = np.zeros(size, dtype=bool)
    conj = acdiam.conj_table(gr)
    comps = []
    while True:
        left = np.nonzero(vert & ~done)[0]
        if left.size == 0:
            break
        start = int(left[0])
        visited = acdiam.bad_mask(gr, k, mode)
        visited[start] = True
        frontier = np.array([start], dtype=np.int64)
        got = [frontier]
        while frontier.size:
            new = acdiam.expand(frontier, gr, k, visited, conj, moveset)
            if new.size:
                got.append(new)
            frontier = new
        vs = np.unique(np.concatenate(got))
        done[vs] = True
        comps.append(vs)
    return comps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--mode", default="normal", choices=("normal", "generate"))
    ap.add_argument("--moveset", default="blm")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    gr = acdiam.load_group(args.group)
    m, k = gr["m"], args.k
    t0 = time.time()
    labels, counts, bad = acdiam.orbits(gr, k, args.mode, verbose=False)
    vert = ~bad
    comps = component_partition(gr, k, args.mode, args.moveset, vert)
    out = dict(group=gr["name"], m=m, k=k, mode=args.mode, moveset=args.moveset,
               nvertices=int(vert.sum()), norbits=int(len(np.unique(labels[vert]))),
               ncomponents=len(comps), components=[], elapsed_s=0.0)
    print("%s k=%d mode=%s moveset=%s V=%d components=%d"
          % (gr["name"], k, args.mode, args.moveset, int(vert.sum()), len(comps)),
          flush=True)
    for ci, vs in enumerate(comps):
        labs = np.unique(labels[vs])
        eccs = []
        for lab in labs:
            inorbit = vs[labels[vs] == lab]
            rep = int(inorbit.min())
            r = acdiam.bfs(rep, gr, k, args.mode, args.moveset)
            if sum(r["levels"]) != len(vs):
                print("  WARNING: orbit %d rep %d reaches %d of %d"
                      % (int(lab), rep, sum(r["levels"]), len(vs)), flush=True)
            eccs.append(r["ecc"])
        out["components"].append(dict(nvertices=int(len(vs)),
                                      norbits=int(len(labs)),
                                      diameter=int(max(eccs)),
                                      ecc_profile=sorted(set(int(e) for e in eccs))))
        print("  component %d: V=%d orbits=%d diameter=%d ecc=%s"
              % (ci, len(vs), len(labs), max(eccs), sorted(set(eccs))), flush=True)
    out["max_component_diameter"] = max(c["diameter"] for c in out["components"])
    out["elapsed_s"] = time.time() - t0
    if args.out:
        open(args.out, "w").write(json.dumps(out, indent=1) + "\n")
    print(json.dumps({kk: out[kk] for kk in ("group", "m", "k", "mode", "moveset",
                                            "nvertices", "ncomponents",
                                            "max_component_diameter", "elapsed_s")}))


if __name__ == "__main__":
    main()
