import glob, json, os

def _run(fname):
    """path of a run file, whether the runs were written here or in results/"""
    if os.path.exists(fname):
        return fname
    alt = os.path.join('results', os.path.basename(fname))
    if os.path.exists(alt):
        return alt
    return fname

order = [('A5',60),('SL2_5',120),('PSL2_7',168),('SL2_7',336),('A6',360),('PSL2_8',504),('PSL2_11',660),('SL2_9_2A6',720)]
pretty = {'A5':r'$A_5$','SL2_5':r'$SL(2,5)$','PSL2_7':r'$PSL(2,7)$','SL2_7':r'$SL(2,7)$','A6':r'$A_6$','PSL2_8':r'$PSL(2,8)$','PSL2_11':r'$PSL(2,11)$','SL2_9_2A6':r'$SL(2,9)=2.A_6$'}
def prof(d, key='orbits'):
    w = {}
    for o in d[key]:
        w[o['ecc']] = w.get(o['ecc'], 0) + o['orbit_size']
    return dict(sorted(w.items()))

# main table: Delta_k(G), BLM moves, normally generating tuples
L = []
L.append("| $G$ | order | $k$ | vertices | $H$-orbits | diameter | eccentricity profile (ecc: tuples) |")
L.append("| --- | --- | --- | --- | --- | --- | --- |")
for g, o in order:
    for k, suf in ((2,'normal'),(3,'normal')):
        f = 'out_%s_k%d_%s.json' % (g, k, suf)
        try:
            d = json.load(open(_run(f)))
        except FileNotFoundError:
            continue
        L.append("| %s | %d | %d | %d | %d | %d | %s |"
                 % (pretty[g], o, k, d['nvertices'], d['norbits'], d['diameter'],
                    ", ".join("%d: %d" % (e, c) for e, c in prof(d).items())))
open('results/main-table.md','w').write("\n".join(L) + "\n")
print("\n".join(L))

# free move set
L = []
L.append("| $G$ | order | $k$ | vertices | $H$-orbits | diameter |")
L.append("| --- | --- | --- | --- | --- | --- |")
for g, o in order:
    for k, suf, mv in ((2,'free','free'),(3,'free','free')):
        f = 'out_%s_k%d_%s.json' % (g, k, suf)
        try:
            d = json.load(open(_run(f)))
        except FileNotFoundError:
            continue
        L.append("| %s | %d | %d | %d | %d | %d |" % (pretty[g], o, k, d['nvertices'], d['norbits'], d['diameter']))
open('results/free-table.md','w').write("\n".join(L) + "\n")
print("\n".join(L))

# generate convention
L = []
L.append("| $G$ | order | vertices | $H$-orbits | diameter | eccentricity profile |")
L.append("| --- | --- | --- | --- | --- | --- |")
for g, o in order:
    d = json.load(open(_run('out_%s_k2_gen.json' % g)))
    L.append("| %s | %d | %d | %d | %d | %s |" % (pretty[g], o, d['nvertices'], d['norbits'], d['diameter'],
        ", ".join("%d: %d" % (e, c) for e, c in prof(d).items())))
open('results/generate-table.md','w').write("\n".join(L) + "\n")
print("\n".join(L))

# distributions for the smallest five
for g in ['A5','SL2_5','PSL2_7','SL2_7','A6','PSL2_8','PSL2_11','SL2_9_2A6']:
    d = json.load(open(_run('out_%s_k2_normal.json' % g)))
    dd = d['distance_distribution']
    print(g, "dist", {k: dd[k] for k in sorted(dd, key=int)})
