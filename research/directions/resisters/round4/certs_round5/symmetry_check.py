"""symmetry_check.py -- machine check of the Sigma lemma and the orbit split.

Sigma = the 8 signed letter permutations of F_2 = F(a,b).  Each sigma extends
to words letter by letter.  The claim is that sigma is an automorphism of the
twelve-move graph: for every move index m there is an index pi(m) with
    sigma( step(P, m) ) = step( sigma(P), pi(m) )
for every pair P.  pi fixes 0, 5, 10, 11 and carries "conjugate relator i by
the letter g" to "conjugate relator i by the letter sigma(g)".
"""
import sys, itertools, random, collections
sys.path.insert(0, 'lib')
import f2, fall
from groups import rows

def sig_of_word(w, sig):
    ia, ib = sig
    m = {1: ia[0], -1: -ia[0], 2: ib[0], -2: -ib[0]}
    return tuple(m[x] for x in w)

def sig_of_pair(p, sig):
    return (sig_of_word(p[0], sig), sig_of_word(p[1], sig))

def pi(m, sig):
    if 1 <= m <= 4:
        g = f2.CONJ_LETTERS[m - 1]
        return 1 + f2.CONJ_LETTERS.index(fall.sigma_letter(g, sig))
    if 6 <= m <= 9:
        g = f2.CONJ_LETTERS[m - 6]
        return 6 + f2.CONJ_LETTERS.index(fall.sigma_letter(g, sig))
    return m

random.seed(20261105)
bad = 0
tests = 0
samples = []
for _ in range(400):
    p = (tuple(random.choice([1,-1,2,-2]) for _ in range(random.randint(0,7))),
         tuple(random.choice([1,-1,2,-2]) for _ in range(random.randint(0,7))))
    samples.append((f2.reduce(p[0]), f2.reduce(p[1])))
for p in samples:
    for sig in fall.SIGMA:
        for m in range(12):
            lhs = sig_of_pair(f2.step(p, m), sig)
            rhs = f2.step(sig_of_pair(p, sig), pi(m, sig))
            tests += 1
            if lhs != rhs:
                bad += 1
print('Sigma lemma: %d checks on 400 random pairs, %d failures' % (tests, bad))

# the same check on every pair of total length at most 4
small = []
for n0 in range(0, 4):
    for w0 in itertools.product([1,-1,2,-2], repeat=n0):
        if f2.reduce(w0) != tuple(w0): continue
        for n1 in range(0, 4 - n0):
            for w1 in itertools.product([1,-1,2,-2], repeat=n1):
                if f2.reduce(w1) != tuple(w1): continue
                small.append((tuple(w0), tuple(w1)))
bad2 = 0
for p in small:
    for sig in fall.SIGMA:
        for m in range(12):
            if sig_of_pair(f2.step(p, m), sig) != f2.step(sig_of_pair(p, sig), pi(m, sig)):
                bad2 += 1
print('Sigma lemma: %d pairs of total length at most 3, %d failures' % (len(small), bad2))

# orbit decomposition of the 66 by sigma acting on class keys
g = collections.defaultdict(list)
for r in rows:
    g[(r['bound'], r['size'])].append(r['pair'])
print()
print('orbit decomposition of the eight same-size blocks:')
for k in sorted(g, key=lambda k: -len(g[k])):
    mem = g[k]
    keys = {p: f2.key_str(f2.parse_pair(p)) for p in mem}
    keyto = {v: p for p, v in keys.items()}
    unassigned = set(mem)
    orbits = []
    while unassigned:
        p = sorted(unassigned)[0]
        orb = set()
        front = [p]
        while front:
            q = front.pop()
            if q in orb: continue
            orb.add(q)
            for sig in fall.SIGMA:
                kk = f2.key_str(sig_of_pair(f2.parse_pair(q), sig))
                if kk in keyto and keyto[kk] not in orb:
                    front.append(keyto[kk])
        orbits.append(sorted(orb))
        unassigned -= orb
    print('  block %-18s %d members, orbits of sizes %s' % (str(k), len(mem), [len(o) for o in orbits]))
    for o in orbits:
        if len(o) < len(mem):
            print('      orbit:', o)
