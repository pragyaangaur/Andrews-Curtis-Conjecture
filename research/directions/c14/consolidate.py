#!/usr/bin/env python3
"""consolidate.py -- final classification of every canonical rank-2 balanced
presentation with |exponent-sum determinant| = 1 and total relator length 12,
13 or 14.  Merges the stage files into final_classes.txt and final_summary.json.

Classes:
  ac-trivial          explicit certificate to the standard tuple
  ak3-equivalent      explicit certificate to AK(3) = <BABaba,BBBBaaa>
  nontrivial-...      determinant, finite quotient or computed group order
  resisting-exhausted-cap18   no AC proof with all intermediate total relator
                              lengths at most 18; the cap-18 component was
                              explored exhaustively (within the tuple budget)
  resisting-budget-cap18      the cap-18 exploration hit its tuple budget
  resisting-exhausted-cap17   exhaustive cap-17 exclusion
  resisting-budget-cap17      cap-17 exploration hit its budget
"""
import collections, json
import c14lib as L

ORDER = ['ac-trivial', 'ak3-equivalent', 'nontrivial', 'resisting']


def main():
    final = {}
    for lv in (12, 13, 14):
        for line in open('class_%d.txt' % lv):
            r = [x.strip() for x in line.strip().split(' | ')]
            if r[0].startswith('resisting'):
                final[r[1]] = ('resisting-cap14', lv)
            elif r[0].startswith('nontrivial'):
                final[r[1]] = (r[0], lv)
            else:
                final[r[1]] = ('ac-trivial', lv)
    stages = [('deep_15.txt', 15), ('mitm2_results.txt', 17),
              ('mitm17_results.txt', 17), ('mitm18_results.txt', 18),
              ('mitm19_results.txt', 19)]
    ex = {}
    for fname, cap in stages:
        for line in open(fname):
            r = [x.strip() for x in line.strip().split(' | ')]
            if len(r) < 3:
                continue
            t, kind = r[2], r[0]
            if kind.startswith('ac-trivial'):
                final[t] = ('ac-trivial', 'cap%d' % cap)
            elif kind.startswith('ak3'):
                final[t] = ('ak3-equivalent', 'cap%d' % cap)
            elif kind == 'resisting-exhausted':
                ex.setdefault(t, {})[cap] = True
            elif kind == 'resisting-budget':
                ex.setdefault(t, {}).setdefault(cap, False)
    for t, d in ex.items():
        if t in final and not final[t][0].startswith('resisting'):
            continue
        good = [c for c in d if d[c]]
        if good:
            final[t] = ('resisting-exhausted-cap%d' % max(good), 'cap%d' % max(d))
        else:
            final[t] = ('resisting-budget-cap%d' % max(d), 'cap%d' % max(d))
    tally = collections.Counter()
    byl = collections.defaultdict(collections.Counter)
    with open('final_classes.txt', 'w') as f:
        for t, (k, stage) in sorted(final.items(), key=lambda x: (len(x[0]), x[0])):
            lv = len(L.parse_pres(t)[0]) + len(L.parse_pres(t)[1])
            tally[k] += 1
            byl[lv][k] += 1
            f.write('%d | %s | %s\n' % (lv, k, t))
    print('total presentations classified: %d' % len(final))
    for lv in sorted(byl):
        tot = sum(byl[lv].values())
        print('L=%2d  total %6d   %s' % (lv, tot, dict(sorted(byl[lv].items()))))
    print()
    print(json.dumps(dict(sorted(tally.items())), indent=1))
    json.dump({'tally': dict(tally),
               'by_length': {str(k): dict(v) for k, v in byl.items()}},
              open('final_summary.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
