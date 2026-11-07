import sys, collections
sys.path.insert(0, 'lib')
import f2

TSV = '/workspace/nucleus/work/projects/p-fc9666b4f6c54fa380c9a84775ed7397/repo/directions/resisters/round4/final_status_round4.tsv'

def load():
    rows = []
    for i, line in enumerate(open(TSV)):
        if i == 0:
            continue
        f = line.rstrip('\n').split('\t')
        rows.append(dict(pair=f[0], r3=f[2], bound=int(f[3]), size=int(f[4]), start=f[5]))
    return rows

rows = load()
print(len(rows), 'rows')
g = collections.defaultdict(list)
for r in rows:
    g[(r['bound'], r['size'])].append(r['pair'])
for k in sorted(g, key=lambda k: -len(g[k])):
    print(k, len(g[k]), g[k])
