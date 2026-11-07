#!/usr/bin/env python3
"""stage_census.py L CAP [certfile] -- census of the canonical rank-2 balanced
presentations of total relator length exactly L, classified with the ball of the
standard tuple capped at total relator length CAP.

Output:
  certfile      'start|moves|std' lines, replayed by replay14.py
  class_L.txt   one line per presentation: class | start | reduced form
  summary_L.json
"""
import sys, time, json, resource, os
import c14lib as L
import c14enum as E
import c14search as S
import tc


def log(*a):
    print(' '.join(str(x) for x in a), flush=True)


def main():
    lv = int(sys.argv[1])
    cap = int(sys.argv[2])
    certpath = sys.argv[3] if len(sys.argv) > 3 else 'certs_%d.txt' % lv
    t0 = time.time()
    ballpath = 'ball_%d.npz' % cap
    log('=' * 70)
    log('census at total relator length %d, ball cap %d' % (lv, cap))
    pairs = [t for t in E.presentations_exact(lv) if abs(L.det(t)) == 1]
    log('canonical pairs with |det| = 1: %d' % len(pairs))
    c_list = [t for t in pairs if S.containment(t) is None]
    log('no containment (step C): %d' % len(c_list))
    d_list = [t for t in c_list if not (S.xi_eq_xj_pow(t[0]) or S.xi_eq_xj_pow(t[1]))]
    log('and no x_i = x_j^m (step D): %d' % len(d_list))
    if os.path.exists(ballpath):
        t1 = time.time()
        depth = L.load_ball(ballpath)
        log('loaded ball %s: %d tuples  %.1f s' % (ballpath, len(depth), time.time() - t1))
    else:
        t1 = time.time()
        depth = L.ball(cap)
        log('ball size %d  %.1f s' % (len(depth), time.time() - t1))
        L.save_ball(depth, ballpath)
    log('maxrss %.2f GB' % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6))

    res = {'certified': 0, 'certified_after_reduction': 0, 'quotient': 0,
           'tc_trivial': 0, 'tc_nontrivial': 0, 'unresolved': 0}
    t1 = time.time()
    with open(certpath, 'w') as f, open('class_%d.txt' % lv, 'w') as g:
        for n, t in enumerate(pairs):
            r, chain = S.full_reduce(t)
            rs, mv = S.certificate(r, depth)
            if mv is not None:
                if rs == r:
                    start, chain2 = t, list(chain)
                else:
                    start = (t[1], t[0])
                    chain2 = [(1 - i, k, a) for (i, k, a) in chain]
                full = chain2 + list(mv)
                if S.apply_all(start, chain2) != rs:
                    raise SystemExit('CHAIN FAILED for ' + L.fmt_pres(t))
                if S.apply_all(start, full) != ((1,), (2,)):
                    raise SystemExit('CERTIFICATE FAILED for ' + L.fmt_pres(t))
                if chain:
                    res['certified_after_reduction'] += 1
                else:
                    res['certified'] += 1
                S.write_cert(f, start, full, 'std')
                g.write('ac-trivial | %s | %s\n' % (L.fmt_pres(t), L.fmt_pres(r)))
                continue
            w = E.quotient_witness(r, names=('A5', 'SL25', 'PSL27'))
            if w is not None:
                res['quotient'] += 1
                hard = 'nontrivial-quotient-%s | %s | %s' % (w[0], L.fmt_pres(t), L.fmt_pres(r))
                g.write(hard + '\n')
                continue
            o = tc.order(r, 20000)
            if o == 1:
                res['tc_trivial'] += 1
                g.write('resisting-trivial-group | %s | %s\n' % (L.fmt_pres(t), L.fmt_pres(r)))
            elif o is not None:
                res['tc_nontrivial'] += 1
                g.write('nontrivial-order-%d | %s | %s\n' % (o, L.fmt_pres(t), L.fmt_pres(r)))
            else:
                res['unresolved'] += 1
                g.write('resisting-unknown-group | %s | %s\n' % (L.fmt_pres(t), L.fmt_pres(r)))
            if (n + 1) % 5000 == 0:
                log('  %d / %d  %.1f s %s' % (n + 1, len(pairs), time.time() - t1, res))
    log('classification pass %.1f s' % (time.time() - t1))
    log(json.dumps(res))
    with open('summary_%d.json' % lv, 'w') as f:
        json.dump({'L': lv, 'cap': cap, 'pairs': len(pairs), 'stepC': len(c_list),
                   'stepD': len(d_list), 'ball': len(depth), 'result': res}, f, indent=1)
    log('total %.1f s' % (time.time() - t0))
    return 0


if __name__ == '__main__':
    sys.exit(main())
