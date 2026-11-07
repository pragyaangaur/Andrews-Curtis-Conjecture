"""enc.py -- acx.c state encoding, so python can produce target files."""
import struct, sys
sys.path.insert(0, 'lib')
import f2

CODE = {1: 0, -1: 1, 2: 2, -2: 3}
UNCODE = {0: 1, 1: -1, 2: 2, 3: -2}


def enc(pair):
    r0, r1 = pair
    k = len(r0) | (len(r1) << 6)
    sh = 12
    for x in list(r0) + list(r1):
        k |= CODE[x] << sh
        sh += 2
    return k


def dec(k):
    n0 = k & 63
    n1 = (k >> 6) & 63
    sh = 12
    r0 = []
    for _ in range(n0):
        r0.append(UNCODE[(k >> sh) & 3]); sh += 2
    r1 = []
    for _ in range(n1):
        r1.append(UNCODE[(k >> sh) & 3]); sh += 2
    return (tuple(r0), tuple(r1))


def write_targets(path, pairs):
    with open(path, 'wb') as f:
        for p in pairs:
            f.write(struct.pack('<Q', enc(p)))


def read_states(path):
    out = []
    with open(path, 'rb') as f:
        while True:
            b = f.read(8)
            if len(b) < 8:
                break
            out.append(struct.unpack('<Q', b)[0])
    return out
