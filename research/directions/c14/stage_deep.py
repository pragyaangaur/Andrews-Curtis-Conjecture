#!/usr/bin/env python3
"""stage_deep.py CAP -- build (or load) the ball of the standard tuple capped at
CAP, then try to certify the current resisting set (class_14 resisters plus the
l = 13 resisters) against it.  Writes certs_deep_<CAP>.txt and reports."""
import sys, time, json, resource, os
import c14lib as L
import c14search as S

def log(*a):
    print(' '.join(str(x) for x in a), flush=True)

def resisters():
    out = []
    for lv in (13, 14):
        for line in open('class_%d.txt' % lv):
            r = line.strip().split(' | ')
            if r[0].startswith('resisting'):
                out.append((lv, L.parse_pres(r[1])))
    return out

def main():
    cap = int(sys.argv[1])
    t0 = time.time()
    ballpath = 'ball_%d.npz' % cap
    if os.path.exists(ballpath):
        depth = L.load_ball(ballpath)
        log('loaded', ballpath, len(depth))
    else:
        depth = L.ball(cap)
        log('ball cap %d: %d tuples  %.1f s  maxrss %.2f GB'
            % (cap, len(depth), time.time() - t0,
               resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6))
        L.save_ball(depth, ballpath)
    res = resisters()
    log('resisting candidates: %d' % len(res))
    hits = 0
    depths = {}
    with open('certs_deep_%d.txt' % cap, 'w') as f, \
            open('deep_%d.txt' % cap, 'w') as g:
        for lv, t in res:
            base, mv = S.certificate(t, depth)
            if mv is None:
                g.write('resisting | %d | %s\n' % (lv, L.fmt_pres(t)))
                continue
            if S.apply_all(base, mv) != ((1,), (2,)):
                raise SystemExit('bad certificate')
            hits += 1
            g.write('ac-trivial | %d | %s\n' % (lv, L.fmt_pres(t)))
            S.write_cert(f, base, mv, 'std')
            depths[len(mv)] = depths.get(len(mv), 0) + 1
    log('certified against the cap-%d ball: %d of %d' % (cap, hits, len(res)))
    log('total %.1f s' % (time.time() - t0))

if __name__ == '__main__':
    main()
