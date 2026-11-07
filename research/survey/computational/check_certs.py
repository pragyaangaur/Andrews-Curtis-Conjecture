#!/usr/bin/env python3
"""check_certs.py -- independent verifier for the certificate files written by
census.py.  This file shares no code with census.py: word arithmetic, the move
set and the parser are rewritten here, so agreement is a genuine cross-check.

    python3 check_certs.py certs_r8_c11.txt

Certificate format, one line per presentation:

    r1 r2 | i j | move ; move ; ...
    move := inv i | mul i j | conj i g      with g in {1,-1,2,-2} = +-a, +-b

The two relators r1 r2 are words over a, A, b, B.  The moves are applied, in
order, to the presentation whose relators are (r1, r2) reordered by the
permutation i j (a presentation is a set of relators, so reordering the two
relators is notational).  A line passes when the result is exactly (a, b).
"""

import sys

LET = {'a': 1, 'A': -1, 'b': 2, 'B': -2}
SYM = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}


def parse_word(s):
    if s == 'e':
        return ()
    return tuple(LET[c] for c in s)


def reduce_word(w):
    stack = []
    for x in w:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    return tuple(stack)


def multiply(u, v):
    return reduce_word(u + v)


def invert(u):
    return tuple(-x for x in reversed(u))


def conjugate(by, r):
    return multiply(multiply(by, r), invert(by))


def apply(t, move):
    kind, i, arg = move
    t = list(t)
    if kind == 'inv':
        t[i] = invert(t[i])
    elif kind == 'mul':
        t[i] = multiply(t[i], t[arg])
    elif kind == 'conj':
        t[i] = conjugate((arg,), t[i])
    else:
        raise ValueError('unknown move %r' % (move,))
    return tuple(t)


def main():
    path = sys.argv[1]
    n = 0
    bad = 0
    longest = 0
    for raw in open(path):
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        left, perm, moves = [x.strip() for x in line.split('|')]
        w1, w2 = left.split()
        i, j = [int(x) for x in perm.split()]
        t = (parse_word(w1), parse_word(w2))
        t = tuple(t[k] for k in (i, j))
        seq = []
        for part in moves.split(';'):
            part = part.strip()
            if not part:
                continue
            bits = part.split()
            kind = bits[0]
            if kind == 'inv':
                seq.append(('inv', int(bits[1]), None))
            elif kind == 'mul':
                seq.append(('mul', int(bits[1]), int(bits[2])))
            elif kind == 'conj':
                seq.append(('conj', int(bits[1]), int(bits[2])))
            else:
                raise ValueError('unknown move %r in %r' % (part, path))
        for m in seq:
            t = apply(t, m)
        n += 1
        longest = max(longest, len(seq))
        if t != ((1,), (2,)):
            bad += 1
            if bad <= 5:
                print('FAIL line %d: %s ends at %s' % (n, left, t))
    print('checked %d certificates from %s: %d failed, longest %d moves'
          % (n, path, bad, longest))
    print('RESULT', 'PASS' if bad == 0 and n > 0 else 'FAIL')
    return 0 if bad == 0 and n > 0 else 1


if __name__ == '__main__':
    sys.exit(main())
