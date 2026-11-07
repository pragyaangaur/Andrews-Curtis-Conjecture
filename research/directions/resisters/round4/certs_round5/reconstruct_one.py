import sys, time
sys.path.insert(0, 'lib')
import f2, fall, backwalk

def reconstruct(wd, start, target, maxlayer=400, verbose=False):
    import os
    layers = {}
    def L(d):
        if d not in layers:
            layers[d] = backwalk.Layer(os.path.join(wd, 'layer_%05d.bin' % d))
        return layers[d]
    import enc as E
    d = backwalk.find_layer(wd, E.enc(target), maxlayer)
    if d is None:
        return None, None
    cur = target
    path = []
    for i in range(d - 1, -1, -1):
        Li = L(i)
        found = None
        for m, x in backwalk.preds(cur):
            if Li.has(E.enc(x)):
                found = (m, x); break
        if found is None:
            raise SystemExit('no predecessor at layer %d for %s' % (i, f2.show_pair(cur)))
        m, x = found
        path.append(m); cur = x
        if verbose and i % 20 == 0:
            print('   layer %d: %s' % (i, f2.show_pair(cur)))
    path.reverse()
    return path, d

if __name__ == '__main__':
    wd, s, t = sys.argv[1], sys.argv[2], sys.argv[3]
    start, target = f2.parse_pair(s), f2.parse_pair(t)
    t0 = time.time()
    path, d = reconstruct(wd, start, target)
    if path is None:
        print('NOT REACHED')
        raise SystemExit(1)
    end, peak, st = f2.replay(start, target, path)
    print('%s -> %s: %d moves (layer %d), peak %d, replay ok, %.1fs' % (s, t, len(path), d, peak, time.time()-t0))
    print('MOVES', ','.join(str(m) for m in path))
