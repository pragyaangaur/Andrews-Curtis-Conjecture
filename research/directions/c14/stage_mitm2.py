#!/usr/bin/env python3
"""stage_mitm2.py BUDGET -- exhaustive exploration of the cap-17 component of
each resisting presentation below the standard tuple's cap-14 ball.

For every target the breadth-first exploration keeps the total relator length at
most 17 and stops only when the component is exhausted or BUDGET distinct tuples
have been seen.  If a visited tuple lies in the cap-14 ball of the standard
tuple, the certificate is written out; otherwise the record says whether the
component was exhausted (which settles that no AC-proof with all intermediate
lengths at most 17 exists) or the budget ran out.

Resumable: mitm2_results.txt is appended to, and finished targets are skipped.
"""
import sys, time, os, collections
import c14lib as L
import c14search as S

CAP = int(os.environ.get('MITM_CAP','17'))
AK3 = ((1, 1, 1, -2, -2, -2, -2), (1, 2, 1, -2, -1, -2))
RESULTS = 'mitm%d_results.txt' % CAP


def load_targets():
    done = set()
    import glob
    for src in glob.glob('mitm*_results.txt'):
        for line in open(src):
            p = line.split(' | ')
            if len(p) <= 2:
                continue
            kind = p[0].strip()
            if kind in ('ac-trivial', 'ak3-equivalent'):
                done.add(p[2].strip())
            elif src == 'mitm%d_results.txt' % CAP:
                done.add(p[2].strip())
    out = []
    for line in open('deep_15.txt'):
        r = line.strip().split(' | ')
        if not r[0].startswith('resisting'):
            continue
        if r[2] in done:
            continue
        out.append((int(r[1]), L.parse_pres(r[2])))
    return out


def explore(t, budget, depth14, depthak):
    parent = {t: (None, None)}
    frontier = [t]
    while frontier:
        nxt = []
        for u in frontier:
            for m, v in L.moves(u):
                if len(v[0]) + len(v[1]) > CAP or v in parent:
                    continue
                parent[v] = (u, m)
                if L.pack(v) in depth14:
                    return ('ac-trivial', path_to(parent, v), v, len(parent))
                if L.pack(v) in depthak:
                    return ('ak3-equivalent', path_to(parent, v), v, len(parent))
                nxt.append(v)
                if len(parent) >= budget:
                    return ('resisting-budget', None, None, len(parent))
        frontier = nxt
    return ('resisting-exhausted', None, None, len(parent))


def path_to(parent, v):
    mv = []
    cur = v
    while parent[cur][0] is not None:
        p, m = parent[cur]
        mv.append(m)
        cur = p
    mv.reverse()
    return mv


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 250000
    t0 = time.time()
    depth14 = L.load_ball('ball_14.npz')
    print('cap-14 ball: %d tuples' % len(depth14), flush=True)
    depthak = L.load_ball('ball_ak3_17.npz')
    print('AK(3) ball cap 17: %d tuples' % len(depthak), flush=True)
    targets = load_targets()
    print('targets: %d, budget %d' % (len(targets), budget), flush=True)
    tally = collections.Counter()
    with open('certs_mitm%d.txt' % CAP, 'a') as f, open(RESULTS, 'a') as g:
        for n, (lv, t) in enumerate(targets):
            kind, path, hit, seen = explore(t, budget, depth14, depthak)
            tally[kind] += 1
            if kind == 'ac-trivial':
                desc = S.descend(depth14, hit)
                full = path + desc
                if desc is None or S.apply_all(t, full) != ((1,), (2,)):
                    raise SystemExit('bad certificate for ' + L.fmt_pres(t))
                S.write_cert(f, t, full, 'std')
            elif kind == 'ak3-equivalent':
                desc = S.descend(depthak, hit)
                full = path + desc
                if desc is None or S.apply_all(t, full) != AK3:
                    raise SystemExit('bad ak3 certificate for ' + L.fmt_pres(t))
                S.write_cert(f, t, full, L.fmt_pres(AK3))
            g.write('%s | %d | %s | %d\n' % (kind, lv, L.fmt_pres(t), seen))
            f.flush(); g.flush()
            if (n + 1) % 25 == 0:
                print('  %d / %d  %.1f s  %s' % (n + 1, len(targets), time.time() - t0,
                                                 dict(tally)), flush=True)
    print('done %d  %.1f s  %s' % (len(targets), time.time() - t0, dict(tally)), flush=True)


if __name__ == '__main__':
    main()
