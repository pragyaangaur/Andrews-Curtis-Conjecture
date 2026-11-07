#!/usr/bin/env python3
"""replay14.py -- independent checker for the length-14 certificates.

Shares no code with c14lib / c14search / c14enum / tc.  Its own word model:
a word is a Python list of letters from 'aA bB', freely reduced by cancelling
adjacent inverse pairs; products and conjugations are implemented directly.

Certificate line format:   start|moves|end
    start, end:  words separated by a comma, letters a A b B, 'e' for empty
    moves:       space separated tokens
                   iN     invert relator N
                   cNL    conjugate relator N by letter L
                   mN     multiply relator N by the other relator
    end:         'std' (a,b) or a literal pair of words
"""
import sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def reduce_word(letters):
    out = []
    for x in letters:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return out


def product(u, v):
    return reduce_word(u + v)


def inverse(u):
    return [INV[x] for x in reversed(u)]


def conjugate(c, u):
    return product(product(list(c), u), inverse(c))


def parse_word(s):
    if s == 'e' or s == '':
        return []
    for x in s:
        if x not in 'aAbB':
            raise ValueError('bad word ' + s)
    w = reduce_word(list(s))
    if ''.join(w) != s:
        raise ValueError('word not freely reduced: ' + s)
    return w


def parse_pres(s):
    a, b = s.split(',')
    return [parse_word(a), parse_word(b)]


def show(t):
    return ','.join(''.join(w) if w else 'e' for w in t)


def apply_token(t, tok):
    kind = tok[0]
    i = int(tok[1])
    if i not in (0, 1):
        raise ValueError('bad relator index in ' + tok)
    if kind == 'i':
        t[i] = inverse(t[i])
    elif kind == 'c':
        c = tok[2]
        if c not in INV:
            raise ValueError('bad conjugator in ' + tok)
        t[i] = conjugate([c], t[i])
    elif kind == 'm':
        t[i] = product(t[i], t[1 - i])
    else:
        raise ValueError('bad move ' + tok)
    return t


def replay(start, moves, end):
    t = [list(start[0]), list(start[1])]
    for tok in moves:
        t = apply_token(t, tok)
    return t, (t[0] == end[0] and t[1] == end[1])


def main(path, verbose=False):
    n = 0
    bad = 0
    longest = 0
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        start_s, moves_s, end_s = line.split('|')
        start = parse_pres(start_s)
        end = parse_pres(end_s) if end_s not in ('std',) else (['a'], ['b'])
        moves = moves_s.split()
        n += 1
        longest = max(longest, len(moves))
        t, ok = replay(start, moves, end)
        if not ok:
            bad += 1
            print('FAIL %s -> %s (got %s) after %d moves'
                  % (start_s, end_s, show(t), len(moves)))
            if verbose:
                print('   ', moves_s)
    print('replayed %d certificates, %d failed, longest %d moves'
          % (n, bad, longest))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1], len(sys.argv) > 2))
