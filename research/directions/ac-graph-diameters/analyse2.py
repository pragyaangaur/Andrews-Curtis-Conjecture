import glob, json, sys
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
import os

def row(f):
    d = json.load(open(f))
    gr = acdiam.load_group('data/' + d['group'])
    m, k = d['m'], d['k']
    one = gr['one']
    cov = all(sum(o['levels']) == d['nvertices'] for o in d['orbits'])
    tot = sum(d['distance_distribution'].values())
    # nondegenerate orbits: no coordinate equal to the identity
    maxdeg = 0
    maxnon = 0
    for o in d['orbits']:
        tup = tuple(int(x[0]) for x in acdiam.decode(np.array([o['start']]), m, k))
        if one in tup:
            maxdeg = max(maxdeg, o['ecc'])
        else:
            maxnon = max(maxnon, o['ecc'])
    # diameter-realising example
    arg = [o for o in d['orbits'] if o['ecc'] == d['diameter']][0]
    start = arg['start']
    st = tuple(int(x[0]) for x in acdiam.decode(np.array([start]), m, k))
    far = None
    if d['nvertices'] <= 300000:
        bad = acdiam.bad_mask(gr, k, d['mode'])
        conj = acdiam.conj_table(gr)
        visited = bad.copy(); visited[start] = True
        frontier = np.array([start], dtype=np.int64)
        lev = 0
        while lev < d['diameter']:
            new = acdiam.expand(frontier, gr, k, visited, conj, d['moveset'])
            frontier = new; lev += 1
        if frontier.size:
            far = tuple(int(x[0]) for x in acdiam.decode(np.array([int(frontier[0])]), m, k))
    return dict(f=f, group=d['group'], k=k, mode=d['mode'], mv=d['moveset'],
                V=d['nvertices'], orb=d['norbits'], diam=d['diameter'],
                exact=d['diameter_exact'], covers=cov, dist_ok=(tot == d['nvertices'] ** 2),
                max_ecc_degenerate=maxdeg, max_ecc_nondegenerate=maxnon,
                example=(st, far), orbit_sizes_of_diam_orbits=arg['orbit_size'])

rows = []
files = []
for pat in ('out_*_k?_*.json', os.path.join('results','out_*_k?_*.json')):
    files += glob.glob(pat)
for f in sorted(set(files)) + sorted(glob.glob('out_*_k?_normal.json')) + sorted(glob.glob('out_*_k?_gen.json')) + sorted(glob.glob('out_*_k?_free.json')) + sorted(glob.glob('out_*_k3_*.json')):
    try:
        rows.append(row(f))
    except Exception as e:
        print("skip", f, e)
seen = set()
out = []
for r in rows:
    key = (r['group'], r['k'], r['mode'], r['mv'])
    if key in seen:
        continue
    seen.add(key)
    out.append(r)
out.sort(key=lambda r: (r['mv'], r['mode'], r['k'], r['V']))
print("%-10s k mv     mode      V       orb diam exact cov distok deg nondeg example" % "")
for r in out:
    print("%-10s %d %-6s %-8s %-7d %-3d %-4d %-5s %-3s %-6s %-3d %-3d %s"
          % (r['group'], r['k'], r['mv'], r['mode'], r['V'], r['orb'], r['diam'],
             r['exact'], r['covers'], r['dist_ok'], r['max_ecc_degenerate'],
             r['max_ecc_nondegenerate'], r['example']))
json.dump(out, open('table.json', 'w'), indent=1)
