#!/usr/bin/env python3
"""Explicit shortest paths for the diameter-realising pairs of section 5."""
import json
import sys

import numpy as np

sys.path.insert(0, '.')
import acdiam


def far_vertex(start, gr, k, mode, diam):
    bad = acdiam.bad_mask(gr, k, mode)
    conj = acdiam.conj_table(gr)
    visited = bad.copy()
    visited[start] = True
    frontier = np.array([start], dtype=np.int64)
    for _ in range(diam):
        frontier = acdiam.expand(frontier, gr, k, visited, conj, 'blm')
    return int(frontier[0])


def main(group, k, mode='normal'):
    gr = acdiam.load_group('data/' + group)
    m = gr['m']
    d = json.load(open('results/out_%s_k%d_%s.json' % (group, k, mode)))
    orb = [o for o in d['orbits'] if o['ecc'] == d['diameter']][0]
    start = orb['start']
    target = far_vertex(start, gr, k, mode, d['diameter'])
    path = acdiam.geodesic(start, target, gr, k, mode, 'blm')
    ok = all(b in acdiam.all_neighbours(a, gr, k, 'blm') for a, b in zip(path, path[1:]))
    out = dict(group=group, k=k, diameter=d['diameter'], start=start, target=target,
               length=len(path) - 1, all_steps_legal=ok, path=path)
    print(json.dumps(out))
    return out


if __name__ == '__main__':
    g = sys.argv[1] if len(sys.argv) > 1 else 'PSL2_7'
    kk = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    main(g, kk)
