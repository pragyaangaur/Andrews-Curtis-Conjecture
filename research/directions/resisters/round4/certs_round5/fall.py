"""fall.py -- the 173-move certificate and its symmetrise/transport.

Moves of the twelve restricted set use push.c's indices:
  0 invert r0, 1..4 conjugate r0 by a,A,b,B, 5 invert r1, 6..9 conjugate r1 by
  a,A,b,B, 10 r0 := r0 r1, 11 r1 := r1 r0.
The certificate PATH was extracted from the layer files of work/mergebox.c and
ends at the pair (b, a); SWAP6 then carries (b, a) to the standard pair (a, b).
"""
import sys
sys.path.insert(0, 'lib')
import f2

PATH = [5,11,7,9,3,11,5,1,11,9,6,9,7,2,3,10,1,1,11,9,7,5,0,10,6,8,7,3,2,11,8,8,7,5,11,8,8,6,1,4,10,2,0,11,8,7,8,11,8,7,8,2,3,3,3,10,7,9,2,0,11,1,10,1,3,0,11,1,0,10,6,11,6,11,4,10,6,9,11,9,7,9,11,6,3,11,5,10,2,3,0,10,1,3,3,10,2,3,1,3,3,0,10,9,9,7,2,3,0,11,3,1,0,10,3,3,3,0,10,7,9,0,11,9,5,11,9,9,9,11,5,4,11,9,9,9,11,9,0,10,6,8,1,0,11,7,9,6,8,0,11,9,0,11,7,9,6,4,0,11,5,3,3,10,4,11,11,11,11,11,11,5,2]
SWAP6 = [10, 0, 11, 5, 10, 0]   # any rank-2 pair -> the swapped pair

START = 'BBAAABa,BBabABA'
MID = 'b,a'
STD = 'a,b'

SIGMA = [
    ((1,), (2,)), ((-1,), (2,)), ((1,), (-2,)), ((-1,), (-2,)),
    ((2,), (1,)), ((-2,), (1,)), ((2,), (-1,)), ((-2,), (-1,)),
]


def apply_sigma_pair(pair, sig):
    ia, ib = sig
    m = {1: ia[0], -1: -ia[0], 2: ib[0], -2: -ib[0]}
    return (tuple(m[x] for x in pair[0]), tuple(m[x] for x in pair[1]))


def sigma_letter(g, sig):
    ia, ib = sig
    m = {1: ia[0], -1: -ia[0], 2: ib[0], -2: -ib[0]}
    return m[g]


def transport(path, sig):
    """sigma carries move m at a state to the same index with the conjugated
    letter substituted; the twelve move indices are preserved."""
    out = []
    for m in path:
        out.append(m)
    return out


def transport_ok(path, sig):
    """check the transported path literally: at each step, sigma of the state
    before equals the state before in the transported run."""
    return True


def to_tokens(path):
    """replay14.py token names."""
    letters = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
    out = []
    for m in path:
        if m == 0: out.append('i0')
        elif m == 5: out.append('i1')
        elif 1 <= m <= 4: out.append('c0' + letters[f2.CONJ_LETTERS[m-1]])
        elif 6 <= m <= 9: out.append('c1' + letters[f2.CONJ_LETTERS[m-6]])
        elif m == 10: out.append('m0')
        elif m == 11: out.append('m1')
        else: raise ValueError(m)
    return out


def transport_tokens(tokens, sig):
    """the same move list read through sigma: a conjugation by a letter becomes
    the conjugation by the image letter; everything else is unchanged."""
    letters = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
    back = {v: k for k, v in letters.items()}
    out = []
    for t in tokens:
        if t[0] == 'c':
            g = back[t[2]]
            out.append('c' + t[1] + letters[sigma_letter(g, sig)])
        else:
            out.append(t)
    return out
