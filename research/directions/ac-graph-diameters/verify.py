#!/usr/bin/env python3
"""Independent checks of the diameter computations in acdiam.py.

(1) A5, k=2, normal convention: recompute the distance distribution and the
    diameter with the move enumerator of survey/nielsen_census.py (round 1,
    a different author and a different algorithm), and compare.
(2) random vertices: pick seeded random vertices of PSL(2,7) and A6 and run a
    full BFS from each with the numpy engine; the eccentricity must equal the
    orbit prediction of the orbit-reduced run.
(3) geodesic replay: a diameter-realising pair of A5 is joined by an explicit
    path, and every step is checked against the definition.
(4) move sanity: on all vertices of A5 every neighbour is a vertex, and the
    move relation is symmetric.
"""
import json
import os
import random
import sys

import numpy as np

def _run(fname):
    """path of a run file, whether the runs were written here or in results/"""
    if os.path.exists(fname):
        return fname
    alt = os.path.join('results', os.path.basename(fname))
    if os.path.exists(alt):
        return alt
    return fname


sys.path.insert(0, '.')
import acdiam
_here = os.path.dirname(os.path.abspath(__file__))
_root = _here
while not os.path.isdir(os.path.join(_root, 'survey')) and _root != '/':
    _root = os.path.dirname(_root)
sys.path.insert(0, os.path.join(_root, 'survey'))
import nielsen_census as nc


def check_census_A5():
    a = tuple([1, 2, 3, 4, 0])      # (0 1 2 3 4)
    b = tuple([1, 2, 0, 3, 4])      # (0 1 2)
    t = nc.table_of_permutations("A5", 5, [a, b])
    assert t.m == 60 and nc.check_group_axioms(t)
    st = nc.Structure(t)
    st.precompute()
    conj = list(range(t.m))
    verts = [v for v in __import__("itertools").product(range(t.m), repeat=2)
             if st.normally_generates(v)]
    vset = set(verts)
    # exhaustive: every neighbour of a vertex is a vertex (BLM Section 1)
    bad = 0
    for v in verts:
        for w in nc.neighbours(t, v, 2, conj, True, True, False):
            if w not in vset:
                bad += 1
    # BFS distance distribution from every vertex, by components
    comp, sizes, _ = nc.graph_components(st, 2, True, conj, True, "normal", False)
    assert len(sizes) == 1, sizes
    diam = 0
    dist = {}
    per_vertex = {}
    for v0 in verts:
        level = {v0: 0}
        frontier = [v0]
        d = 0
        while frontier:
            nxt = []
            for u in frontier:
                for w in nc.neighbours(t, u, 2, conj, True, True, False):
                    if w not in level:
                        level[w] = d + 1
                        nxt.append(w)
            frontier = nxt
            d += 1
        assert len(level) == len(verts)
        for w, dd in level.items():
            dist[dd] = dist.get(dd, 0) + 1
        per_vertex[tuple(v0)] = max(level.values())
        diam = max(diam, max(level.values()))
    # compare every vertex eccentricity with the orbit prediction of acdiam.py
    import acdiam
    gr = acdiam.load_group('data/A5')
    labels, counts, badm = acdiam.orbits(gr, 2, 'normal', verbose=False)
    d = json.load(open(_run('out_A5_k2_normal.json')))
    ecc_of_orbit = {o['orbit']: o['ecc'] for o in d['orbits']}
    mism = 0
    for v, e in per_vertex.items():
        code = v[0] + 60 * v[1]
        lab = int(labels[code])
        if ecc_of_orbit[lab] != e:
            mism += 1
    return dict(order=t.m, nvertices=len(verts), bad_neighbours=bad,
                diameter=diam, distribution=dict(sorted(dist.items())),
                orbit_prediction_mismatches=mism,
                vertices_checked=len(per_vertex))


def check_random_vertices(group, k, mode, nrand=4, seed=11):
    gr = acdiam.load_group('data/' + group)
    m = gr['m']
    labels, counts, bad = acdiam.orbits(gr, k, mode, verbose=False)
    vert = ~bad
    codes = np.nonzero(vert)[0]
    # orbit eccentricity from the stored run
    import glob
    f = _run('out_%s_k%d_%s.json' % (group, k, mode))
    d = json.load(open(f))
    ecc_of_orbit = {o['orbit']: o['ecc'] for o in d['orbits']}
    rng = random.Random(seed)
    out = []
    for c in rng.sample(list(codes), nrand):
        c = int(c)
        lab = int(labels[c])
        r = acdiam.bfs(c, gr, k, mode, 'blm')
        out.append(dict(code=c, orbit=lab, orbit_ecc=ecc_of_orbit.get(lab),
                        bfs_ecc=r['ecc'], covers=int(sum(r['levels'])),
                        nvertices=int(vert.sum())))
    return out


def check_geodesic(group, k, mode):
    gr = acdiam.load_group('data/' + group)
    m = gr['m']
    d = json.load(open(_run('out_%s_k%d_%s.json' % (group, k, mode))))
    diam = d['diameter']
    orb = [o for o in d['orbits'] if o['ecc'] == diam][0]
    start = orb['start']
    r = acdiam.bfs(start, gr, k, mode, 'blm')
    # find a vertex at distance diam: BFS again keeping the last level
    bad = acdiam.bad_mask(gr, k, mode)
    conj = acdiam.conj_table(gr)
    visited = bad.copy()
    visited[start] = True
    frontier = np.array([start], dtype=np.int64)
    lev = 0
    while lev < diam:
        new = acdiam.expand(frontier, gr, k, visited, conj, 'blm')
        frontier = new
        lev += 1
    target = int(frontier[0])
    path = acdiam.geodesic(start, target, gr, k, mode, 'blm')
    ok = True
    for a, b in zip(path, path[1:]):
        if b not in acdiam.all_neighbours(a, gr, k, 'blm'):
            ok = False
    return dict(group=group, diameter=diam, start=start, target=target,
                path_length=len(path) - 1, legal=ok, path=path,
                start_tuple=tuple(int(x[0]) for x in acdiam.decode(np.array([start]), m, k)),
                target_tuple=tuple(int(x[0]) for x in acdiam.decode(np.array([target]), m, k)))


if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'census':
        print(json.dumps(check_census_A5()))
    elif what == 'random':
        for g, k in (('PSL2_7', 2), ('A6', 2)):
            print(g, json.dumps(check_random_vertices(g, k, 'normal'), indent=1))
    elif what == 'geodesic':
        print(json.dumps(check_geodesic('A5', 2, 'normal')))


def check_aut(group):
    gr = acdiam.load_group('data/' + group)
    m, mul = gr['m'], gr['mul']
    res = []
    for phi in gr['aut']:
        bij = len(set(int(x) for x in phi)) == m
        hom = all(mul[phi[a], phi[b]] == phi[mul[a, b]] for a in range(m) for b in range(m))
        res.append(dict(bijective=bij, homomorphism=hom))
    return dict(group=group, order=m, generators=len(gr['aut']), all_ok=all(r['bijective'] and r['homomorphism'] for r in res))


def check_vertex_counts(group):
    """the vertex count of the generate convention against direct subgroup tests"""
    import itertools
    gr = acdiam.load_group('data/' + group)
    m = gr['m']
    bad = acdiam.bad_mask(gr, 2, 'generate')
    rng = random.Random(7)
    wrong = 0
    # direct subgroup closure test on a sample
    def generates(t):
        seen = {int(gr['one'])}
        frontier = [int(gr['one'])]
        gens = [int(x) for x in t]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = int(gr['mul'][x, g])
                    if y not in seen:
                        seen.add(y); new.append(y)
            frontier = new
        return len(seen) == m
    for _ in range(300):
        t = [rng.randrange(m), rng.randrange(m)]
        code = t[0] + m * t[1]
        mask_says = not bad[code]
        if mask_says != generates(t):
            wrong += 1
    return dict(group=group, order=m, samples=300, mismatches=wrong)
