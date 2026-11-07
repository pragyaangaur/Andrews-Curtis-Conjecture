"""transport.py -- a certificate for every Sigma-partner of a falling pair.

If sigma is a signed letter permutation and PATH carries P to Q, the same move
list with each conjugating letter replaced by its sigma-image carries sigma(P)
to sigma(Q); check_transport verifies that step by step.

For a partner R that is only a conjugate/inverse/swap of some sigma(P), a short
explicit path R -> sigma(P) is searched with a length bound: inside a class the
only moves needed are inversions and conjugation by the last letter of a
relator (which rotates the cyclic reduction), and these stay within the total
length of the endpoints.  The relator swap is the six-move SWAP6.
"""
import sys
sys.path.insert(0, 'lib')
import f2, fall

SWAP6 = fall.SWAP6


def last_letter_moves(pair):
    """inversions and conjugation by the last letter of each relator."""
    r0, r1 = pair
    yield 0, (f2.inv(r0), r1)
    yield 5, (r0, f2.inv(r1))
    if r0:
        g = r0[-1]
        yield 1 + f2.CONJ_LETTERS.index(g), (f2.conj(r0, (g,)), r1)
    if r1:
        g = r1[-1]
        yield 6 + f2.CONJ_LETTERS.index(g), (r0, f2.conj(r1, (g,)))


def class_path(P, Q, maxstates=200000):
    """explicit path from P to Q if Q is in the class of P and the walk stays
    within total length max(|P|,|Q|); None otherwise."""
    if P == Q:
        return []
    lim = max(f2.total_len(P), f2.total_len(Q))
    seen = {P: None}
    frontier = [P]
    while frontier:
        nxt = []
        for u in frontier:
            for m, v in last_letter_moves(u):
                if v in seen or f2.total_len(v) > lim:
                    continue
                seen[v] = (u, m)
                if v == Q:
                    path = []
                    cur = v
                    while seen[cur] is not None:
                        prev, mm = seen[cur]
                        path.append(mm)
                        cur = prev
                    return list(reversed(path))
                nxt.append(v)
                if len(seen) > maxstates:
                    return None
        frontier = nxt
    return None


def std_path(P, lim=6, maxstates=100000):
    """short explicit path from P to the standard pair (a,b), or None."""
    STD = f2.parse_pair('a,b')
    if P == STD:
        return []
    seen = {P: None}
    frontier = [P]
    while frontier:
        nxt = []
        for u in frontier:
            for m, v in f2.moves(u):
                if v in seen or f2.total_len(v) > lim:
                    continue
                seen[v] = (u, m)
                if v == STD:
                    path = []
                    cur = v
                    while seen[cur] is not None:
                        prev, mm = seen[cur]
                        path.append(mm)
                        cur = prev
                    return list(reversed(path))
                nxt.append(v)
                if len(seen) > maxstates:
                    return None
        frontier = nxt
    return None


def sigma_pair(pair, sig):
    return fall.apply_sigma_pair(pair, sig)


def transported_path(sig):
    """the PATH move indices read through sigma."""
    tp = []
    for m in fall.PATH:
        if 1 <= m <= 4:
            tp.append(1 + f2.CONJ_LETTERS.index(fall.sigma_letter(f2.CONJ_LETTERS[m - 1], sig)))
        elif 6 <= m <= 9:
            tp.append(6 + f2.CONJ_LETTERS.index(fall.sigma_letter(f2.CONJ_LETTERS[m - 6], sig)))
        else:
            tp.append(m)
    return tp


def check_transport(path, sig, start):
    """walk the path and the sigma-image of the walk together."""
    a = start
    b = sigma_pair(start, sig)
    for m in path:
        a = f2.step(a, m)
        mm = m
        if 1 <= m <= 4:
            mm = 1 + f2.CONJ_LETTERS.index(fall.sigma_letter(f2.CONJ_LETTERS[m - 1], sig))
        elif 6 <= m <= 9:
            mm = 6 + f2.CONJ_LETTERS.index(fall.sigma_letter(f2.CONJ_LETTERS[m - 6], sig))
        b = f2.step(b, mm)
        if sigma_pair(a, sig) != b:
            raise SystemExit('transport fails at move %d' % m)
    return b
