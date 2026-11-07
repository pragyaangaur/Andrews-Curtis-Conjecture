#!/usr/bin/env python3
"""Checks the two finite countermodels printed in A. Lisitsa, "Automated Reasoning for the
Andrews-Curtis Conjecture", AITP 2019 extended version (Zenodo 10.5281/zenodo.2555481),
Appendix, Theorem 1.

The claim there is: the equational theory EACT2~ (group axioms plus the AC-move axioms for
pairs of relators) does not derive the equality of the pair-encodings for the three listed
pairs of presentations.  A finite algebra satisfying every axiom but violating the equality
proves non-derivability in equational logic.  This script checks exactly that, by brute force.

Run: python3 countermodel_check.py
"""
import sys, itertools

def evaluate(word, alg):
    """value of a word in the algebra; uppercase letter = inverse of that letter"""
    v = alg['e']
    for c in word:
        x = alg['a'] if c.lower() == 'a' else alg['b']
        if c.isupper():
            x = alg['r'][x]
        v = alg['mul'][v][x]
    return v

def check_group_axioms(alg, name):
    n = alg['n']; mul = alg['mul']; e = alg['e']; r = alg['r']
    ok = True
    ok &= all(mul[mul[x][y]][z] == mul[x][mul[y][z]] for x, y, z in itertools.product(range(n), repeat=3))
    ok &= all(mul[x][e] == x and mul[e][x] == x for x in range(n))
    ok &= all(mul[x][r[x]] == e for x in range(n))
    ok &= all(mul[r[x]][x] == e for x in range(n))  # consequence, checked for information
    print('%s: group axioms (associativity, two-sided identity, left and right inverse): %s' % (name, ok))
    return ok

def check_ac_axioms(alg, name):
    n = alg['n']; mul = alg['mul']; f = alg['f']; r = alg['r']
    a1, a2 = alg['a'], alg['b']
    ok1 = all(f[x][y] == f[r[x]][y] for x, y in itertools.product(range(n), repeat=2))
    ok2 = all(f[x][y] == f[mul[x][y]][y] for x, y in itertools.product(range(n), repeat=2))
    ok3 = all(f[x][y] == f[x][mul[y][x]] for x, y in itertools.product(range(n), repeat=2))
    ok4 = all(f[x][y] == f[mul[mul[a1][x]][r[a1]]][y] and f[x][y] == f[mul[mul[a2][x]][r[a2]]][y]
              for x, y in itertools.product(range(n), repeat=2))
    # non-ground conjugation axiom of EACT2~ : f(x,y) = f((v.x).r(v), y) for every v
    ok5 = all(f[x][y] == f[mul[mul[v][x]][r[v]]][y]
              for v, x, y in itertools.product(range(n), repeat=3))
    print('%s: f(x,y)=f(r(x),y): %s | f(x,y)=f(x.y,y): %s | f(x,y)=f(x,y.x): %s' % (name, ok1, ok2, ok3))
    print('%s: ground conjugation axioms: %s | non-ground conjugation axiom: %s' % (name, ok4, ok5))
    return ok1 and ok2 and ok3 and ok4 and ok5

def models():
    m3 = {'n': 3,
          'mul': [[2, 0, 1], [0, 1, 2], [1, 2, 0]],
          'e': 1, 'a': 0, 'b': 0, 'r': [2, 1, 0],
          'f': [[0, 0, 0], [0, 1, 0], [0, 0, 0]]}
    m5 = {'n': 5,
          'mul': [[4, 3, 0, 2, 1], [3, 0, 1, 4, 2], [0, 1, 2, 3, 4], [2, 4, 3, 1, 0], [1, 2, 4, 0, 3]],
          'e': 2, 'a': 0, 'b': 1, 'r': [3, 4, 2, 0, 1],
          'f': [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]}
    return [('3-element model', m3), ('5-element model', m5)]

def main():
    allok = True
    for name, alg in models():
        allok &= check_group_axioms(alg, name)
        allok &= check_ac_axioms(alg, name)
    m3 = models()[0][1]; m5 = models()[1][1]
    # Theorem 1, case AT1: g = <a,b|aba,bba> versus its image under a->a, b->b^-1
    lhs = lambda A: (evaluate('aba', A), evaluate('bba', A))
    rhs = lambda A: (evaluate('aBa', A), evaluate('BBa', A))
    p, q = lhs(m3), rhs(m3)
    v = m3['f'][p[0]][p[1]] != m3['f'][q[0]][q[1]]
    print('AT1 (3-element model): f(aba,bba)=%d, f(aB a,B B a)=%d, inequality holds: %s'
          % (m3['f'][p[0]][p[1]], m3['f'][q[0]][q[1]], v)); allok &= v
    # case AT2: image under a->a, b->ba
    q2 = (evaluate('abaa', m3), evaluate('babaa', m3))
    v = m3['f'][p[0]][p[1]] != m3['f'][q2[0]][q2[1]]
    print('AT2 (3-element model): f(aba,bba)=%d, f(abaa,babaa)=%d, inequality holds: %s'
          % (m3['f'][p[0]][p[1]], m3['f'][q2[0]][q2[1]], v)); allok &= v
    # case AT3: g' = <a,b|aaba,bba> versus image under a->b, b->a
    p3 = (evaluate('aaba', m5), evaluate('bba', m5))
    q3 = (evaluate('bbab', m5), evaluate('aab', m5))
    v = m5['f'][p3[0]][p3[1]] != m5['f'][q3[0]][q3[1]]
    print('AT3 (5-element model): f(aaba,bba)=%d, f(bbab,aab)=%d, inequality holds: %s'
          % (m5['f'][p3[0]][p3[1]], m5['f'][q3[0]][q3[1]], v)); allok &= v
    print('RESULT: %s' % ('PASS: both printed algebras are models of the AC axioms and refute the three claimed equalities'
                          if allok else 'FAIL'))
    return 0 if allok else 1

if __name__ == '__main__':
    sys.exit(main())
