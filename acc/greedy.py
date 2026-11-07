"""Greedy trivialisation with cyclic alignment, in real ac-r2 move currency.

The idea, taken from the structure of the Math-AI-Caltech solver's
`_concatenate` move (github.com/Math-AI-Caltech/ACSolverX at commit
6a12515fe1d95178a483b76d5553266e61122417, envs/ac_moves.py): a bare
multiplication rarely cancels much, but rotating the other relator first lines
up a long common subword.  Their environment treats that rotation as free;
in the competition's metric it costs one move per rotation step, so this
implementation charges min(k, n-k) + 1 for a rotation by k followed by a
multiplication, and keeps only moves whose gain beats their cost.
"""
import sys

sys.path.insert(0, "acc")
import engine as E


def rot_left(w, k):
    n = len(w)
    if n == 0:
        return ()
    k %= n
    return tuple(w[k:] + w[:k])


def invert(w):
    return tuple(-c for c in reversed(w))


def cyc_reduce_moves(w):
    """If w = a s a^-1 for a letter a, conjugation by a shortens it by 2."""
    if len(w) >= 2 and w[0] == -w[-1]:
        return 1
    return 0


def best_move(s):
    r0, r1 = s
    n0, n1 = len(r0), len(r1)
    best = None   # (gain, newstate, moves)
    for i in (0, 1):
        j = 1 - i
        ri, rj = s[i], s[j]
        ni, nj = len(ri), len(rj)
        for sign in (1, -1):
            wj = rj if sign == 1 else invert(rj)
            for k in range(nj):
                cost = min(k, nj - k) + 1
                if cost > 6:
                    continue
                rot = rot_left(wj, k)
                newi = E.free_reduce(ri + rot)
                gain = ni - len(newi) - cost
                if gain <= 0:
                    continue
                # the other relator is rotated in the real state too
                rot_actual = rot_left(rj, k)
                if sign == 1:
                    ns = (newi, rot_actual) if i == 0 else (rot_actual, newi)
                else:
                    # multiplying by rot^{-1}: rotate rj by k then invert, or
                    # equivalently rotate the inverse.  We realise it as
                    # rotate rj by k, invert it, then multiply and untwist.
                    inv_rot = E.free_reduce(ri + rot)
                    ns = (inv_rot, rot_actual) if i == 0 else (rot_actual, inv_rot)
                cand = (gain, ns, (i, j, k, sign))
                if best is None or cand[0] > best[0]:
                    best = cand
    # pure cyclic reduction
    for i in (0, 1):
        if cyc_reduce_moves(s[i]):
            w = s[i]
            a = w[0]
            red = w[1:-1]
            ns = (red, s[1]) if i == 0 else (s[0], red)
            cand = (1, ns, ("cyc", i))
            if best is None or cand[0] > best[0]:
                best = cand
    return best


def expand(spec, s):
    """Turn the chosen macro into real ac-r2 move ids."""
    if spec[0] == "cyc":
        i = spec[1]
        a = s[i][0]
        # conjugate relator i by a^-1 (move id depends on i and letter)
        gid = {1: 6, -1: 7, 2: 8, -2: 9}[a]
        return [gid + 4 * i]
    i, j, k, sign = spec
    moves = []
    # rotate relator j left by k: conjugate by its first letter k times
    for _ in range(k):
        a = s[j][0]
        gid = {1: 6, -1: 7, 2: 8, -2: 9}[a]
        moves.append(gid + 4 * j)
        s = (E.apply_move(s, moves[-1]))
    # now multiply relator i by relator j (or its inverse)
    mul = {(0, 1): 2, (0, -1): 3, (1, 1): 4, (1, -1): 5}[(i, sign)]
    moves.append(mul)
    return moves


def trivialise(state, max_steps=400, verbose=False):
    s = (tuple(state[0]), tuple(state[1]))
    path = []
    for _ in range(max_steps):
        if s == ((1,), (2,)):
            return path
        if E.canonical_suffix(s) is not None:
            return path + list(E.canonical_suffix(s))
        bm = best_move(s)
        if bm is None:
            return None
        gain, ns, spec = bm
        ms = expand(spec, s)
        for m in ms:
            s = E.apply_move(s, m)
        path.extend(ms)
    return None


if __name__ == "__main__":
    import json
    import time
    rows = []
    for line in open(sys.argv[1] if len(sys.argv) > 1 else "data/scored.in"):
        p = line.rstrip("\n").split("\t")
        if len(p) < 3:
            continue
        rows.append((p[0], [int(x) for x in p[1].split(",")] if p[1] else [],
                     [int(x) for x in p[2].split(",")] if p[2] else []))
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    t0 = time.time()
    ok = 0
    lens = []
    for cid, r0, r1 in rows[:n]:
        path = trivialise((r0, r1))
        if path is not None:
            good, fin = E.check_path((r0, r1), path)
            if good:
                ok += 1
                lens.append(len(path))
            else:
                print("BAD", cid, fin)
    print("greedy solved %d/%d, time %.1fs, lengths %s" % (ok, min(n, len(rows)), time.time() - t0, sorted(lens)[:10]))
