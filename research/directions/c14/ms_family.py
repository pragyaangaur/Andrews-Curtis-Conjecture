#!/usr/bin/env python3
"""The Miller-Schupp family MS(n,w) = <a,b | a^-1 b^n a = b^(n+1), a = w>,
canonicalised, and its intersection with the length-14 resisting set."""
import itertools, json, collections
import c14lib as L
import c14enum as E
import c14search as S

A, Ai, B, Bi = 1, -1, 2, -2
LETTERS = (1, -1, 2, -2)


def all_words(k):
    if k == 0:
        yield ()
        return
    for w in itertools.product(LETTERS, repeat=k):
        if L.red(w) == w:
            yield w


def ms_pres(n, w):
    r1 = L.red((Ai,) + (B,) * n + (A,) + (Bi,) * (n + 1))
    r2 = L.red((Ai,) + tuple(w))
    return (r1, r2)


def canon(t):
    return L.canon_pres((L.cyclic_reduce(t[0]), L.cyclic_reduce(t[1])))


def expsum_a(w):
    return w.count(1) - w.count(-1)


def main():
    for maxn, maxw in ((7, 7),):
        fam = {}
        for n in range(1, maxn + 1):
            for k in range(0, maxw + 1):
                for w in all_words(k):
                    c = canon(ms_pres(n, w))
                    fam.setdefault(c, (n, w))
        print('MS(n,w) with n <= %d, |w| <= %d: %d canonical presentations'
              % (maxn, maxw, len(fam)))
        fam0 = {c: v for c, v in fam.items() if expsum_a(v[1]) == 0}
        print('  of which exponent sum on a is zero: %d' % len(fam0))
        bylen = collections.Counter(sum(len(x) for x in c) for c in fam)
        print('  by total relator length:', dict(sorted(bylen.items())))
        bylen0 = collections.Counter(sum(len(x) for x in c) for c in fam0)
        print('  (exponent-sum-zero) by length:', dict(sorted(bylen0.items())))
        # length 14 part
        l14 = {c: v for c, v in fam.items() if sum(len(x) for x in c) == 14}
        l140 = {c: v for c, v in l14.items() if expsum_a(v[1]) == 0}
        print('length-14 MS presentations: %d (exponent-sum-zero: %d)'
              % (len(l14), len(l140)))
        with open('ms_family_%d_%d.txt' % (maxn, maxw), 'w') as f:
            for c in sorted(fam, key=lambda z: (sum(len(x) for x in z), L.fmt_pres(z))):
                f.write('%s | n=%d | w=%s\n' % (L.fmt_pres(c), fam[c][0], L.show(fam[c][1])))
        with open('ms_l14.txt', 'w') as f:
            for c in sorted(l14, key=L.fmt_pres):
                f.write('%s | n=%d | w=%s\n' % (L.fmt_pres(c), l14[c][0], L.show(l14[c][1])))
        return fam, l14, l140


if __name__ == '__main__':
    main()
