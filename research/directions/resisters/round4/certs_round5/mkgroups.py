"""mkgroups.py -- write per-group start/target files for the merge probes."""
import sys, collections, os
sys.path.insert(0, 'lib')
import f2, enc
from groups import rows

g = collections.defaultdict(list)
for r in rows:
    g[(r['bound'], r['size'])].append(r['pair'])
os.makedirs('work/g', exist_ok=True)
names = []
for i, k in enumerate(sorted(g, key=lambda k: -len(g[k]))):
    mem = g[k]
    tag = 'G%d_%d_%d' % (i, k[0], k[1])
    names.append((tag, k, mem))
    with open('work/g/%s_start.txt' % tag, 'w') as f:
        f.write('%s\t%s\n' % (mem[0], mem[0]))
    enc.write_targets('work/g/%s_tgt.u64' % tag, [f2.parse_pair(p) for p in mem[1:]])
    with open('work/g/%s_members.txt' % tag, 'w') as f:
        for p in mem:
            f.write('%s\t%s\n' % (p, p))
for tag, k, mem in names:
    print(tag, len(mem))
