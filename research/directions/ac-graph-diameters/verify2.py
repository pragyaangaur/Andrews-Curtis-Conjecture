#!/usr/bin/env python3
"""A second independent check: the move enumerator of survey/nielsen_census.py
applied to the exported multiplication table of a group, with a full BFS from
seeded random vertices.  Compares the eccentricity and the whole level-size
vector with the orbit-reduced run of acdiam.py, and the vertex predicate with
the normal-closure test of the census code."""
import json
import os
import random
import sys

import numpy as np

sys.path.insert(0, '.')
import acdiam

_here = os.path.dirname(os.path.abspath(__file__))
_root = _here
while not os.path.isdir(os.path.join(_root, 'survey')) and _root != '/':
    _root = os.path.dirname(_root)
sys.path.insert(0, os.path.join(_root, 'survey'))
import nielsen_census as nc


def census_table(group):
    gr = acdiam.load_group('data/' + group)
    m = gr['m']
    elems = list(range(m))
    mul = [[int(gr['mul'][a, b]) for b in range(m)] for a in range(m)]
    return nc.Table(group, elems, mul, int(gr['one']))


def check(group, k=2, nrand=3, seed=3, vertex_sample=None):
    out = dict(group=group, k=k)
    t = census_table(group)
    st = nc.Structure(t)
    st.precompute()
    assert nc.check_group_axioms(t)
    m = t.m
    gr = acdiam.load_group('data/' + group)
    bad = acdiam.bad_mask(gr, k, 'normal')
    # vertex predicate agreement on a sample
    rng = random.Random(seed)
    if vertex_sample:
        codes = rng.sample(range(m ** k), vertex_sample)
        mism = 0
        for c in codes:
            tup = tuple(int(x[0]) for x in acdiam.decode(np.array([c]), m, k))
            if st.normally_generates(tup) != (not bad[c]):
                mism += 1
        out['vertex_predicate_samples'] = vertex_sample
        out['vertex_predicate_mismatches'] = mism
    d = json.load(open(_run('out_%s_k%d_normal.json' % (group, k))))
    ecc_of_orbit = {o['orbit']: o['ecc'] for o in d['orbits']}
    labels, counts, badm = acdiam.orbits(gr, k, 'normal', verbose=False)
    res = []
    for _ in range(nrand):
        c = rng.randrange(m ** k)
        while bad[c]:
            c = rng.randrange(m ** k)
        tup = tuple(int(x[0]) for x in acdiam.decode(np.array([c]), m, k))
        # full BFS with the census enumerator
        level = {tup: 0}
        frontier = [tup]
        dist = 0
        sizes = [1]
        while frontier:
            nxt = []
            for u in frontier:
                for w in nc.neighbours(t, u, k, list(range(m)), True, True):
                    if w not in level:
                        level[w] = dist + 1
                        nxt.append(w)
            if nxt:
                sizes.append(len(nxt))
            frontier = nxt
            dist += 1
        mine = acdiam.bfs(c, gr, k, 'normal', 'blm')
        res.append(dict(code=int(c), tuple=tup,
                        census_ecc=max(level.values()),
                        orbit_prediction=ecc_of_orbit[int(labels[c])],
                        engine_ecc=mine['ecc'],
                        census_level_sizes=sizes,
                        engine_level_sizes=mine['levels'],
                        levels_agree=(sizes == mine['levels']),
                        coverage=len(level), nvertices=int((~bad).sum())))
    out['vertices'] = res
    return out


def _run(fname):
    if os.path.exists(fname):
        return fname
    alt = os.path.join('results', os.path.basename(fname))
    return alt if os.path.exists(alt) else fname


if __name__ == '__main__':
    g = sys.argv[1] if len(sys.argv) > 1 else 'PSL2_7'
    ns = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    print(json.dumps(check(g, vertex_sample=2000), indent=1))
