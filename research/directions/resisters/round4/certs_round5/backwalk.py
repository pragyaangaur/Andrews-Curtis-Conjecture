"""backwalk.py -- reconstruct a forward path from a layer-by-layer BFS.

Predecessor set of a state y under the twelve restricted moves: for every move
index m there is at most one reduced pair x with move(x,m) = y, and it is
computed below.  Proof of uniqueness for mul is in report.md (multiply both
sides by the inverse of the unchanged relator in the free group).
"""
import sys, os, mmap, struct
sys.path.insert(0, 'lib')
import f2, enc

def preds(y):
    r0, r1 = y
    out = []
    out.append((0, (f2.inv(r0), r1)))
    for i, g in enumerate(f2.CONJ_LETTERS):
        out.append((1 + i, (f2.conj(r0, (-g,)), r1)))
    out.append((5, (r0, f2.inv(r1))))
    for i, g in enumerate(f2.CONJ_LETTERS):
        out.append((6 + i, (r0, f2.conj(r1, (-g,)))))
    out.append((10, (f2.mul(r0, f2.inv(r1)), r1)))
    out.append((11, (r0, f2.mul(r1, f2.inv(r0)))))
    # drop the ones that are not genuine predecessors
    keep = []
    for m, x in out:
        if f2.step(x, m) == y:
            keep.append((m, x))
    return keep

class Layer:
    def __init__(self, path):
        self.f = open(path, 'rb')
        self.n = os.path.getsize(path) // 8
        self.mm = mmap.mmap(self.f.fileno(), 0, access=mmap.ACCESS_READ) if self.n else None
    def get(self, i):
        return struct.unpack_from('<Q', self.mm, 8 * i)[0]
    def has(self, k):
        lo, hi = 0, self.n - 1
        while lo <= hi:
            mid = (lo + hi) // 2
            v = self.get(mid)
            if v == k: return True
            if v < k: lo = mid + 1
            else: hi = mid - 1
        return False

def find_layer(wd, key, maxlayer):
    for d in range(maxlayer + 1):
        p = os.path.join(wd, 'layer_%05d.bin' % d)
        if not os.path.exists(p):
            return None
        L = Layer(p)
        if L.has(key):
            return d
    return None
