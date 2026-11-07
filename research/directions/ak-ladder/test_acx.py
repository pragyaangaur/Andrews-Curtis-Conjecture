"""Sanity checks for acx.py on published and Round 1 certificates."""

import sys
sys.path.insert(0, ".")
import acx

X, Y = (1,), (2,)


def ak1_round1():
    """Replay directions/ak-status/ak1_certificate.py MOVES (19 moves)."""
    B1 = acx.reduce_word((2, 1, -2, -1, -2))
    B1i = acx.inverse(B1)
    B2 = acx.reduce_word((-2, -1, -2))
    B2i = acx.inverse(B2)
    M = [
        (0, "inv", None), (0, "conj", (-1,)), (0, "conj", B1i),
        (1, "mul", 0), (0, "conj", B1), (0, "conj", (1,)),
        (0, "inv", None), (0, "inv", None), (0, "conj", (-1,)),
        (0, "conj", B2i), (1, "mul", 0), (0, "conj", B2),
        (0, "conj", (1,)), (0, "inv", None), (0, "conj", (2,)),
        (1, "mul", 0), (0, "conj", (-2,)), (0, "mul", 1), (0, "mul", 1),
    ]
    start = (acx.reduce_word((1, -2, -2)), acx.XYX)
    moves = []
    for i, kind, data in M:
        if kind == "inv":
            moves.append(("inv", i + 1))
        elif kind == "mul":
            moves.append(("mul", i + 1, data + 1))
        else:
            moves.append(("conj", i + 1, data))
    ok = acx.verify(start, moves, (X, Y))
    print("AK(1) 19-move Round 1 certificate replayed independently:", ok)
    return ok


def local_minimum():
    """No single AC move reduces the total length of AK(n), for many n."""
    conjs = acx.words_up_to(2, 4)
    bad = []
    for n in range(1, 41):
        rs = acx.ak(n)
        L = acx.total_length(rs)
        for m, nrs in acx.successors(rs, 2, conjs):
            if acx.total_length(nrs) < L:
                bad.append((n, m, acx.total_length(nrs)))
                break
    print("AK(n) strict local minima for n=1..40, conjugators up to length 4:",
          "PASS" if not bad else ("FAIL %r" % bad[:3]))
    return not bad


def family_shapes():
    for n in (1, 2, 3, 4, 5, 6, 8, 12):
        a, t = acx.ak(n), acx.n11(n)
        print("n=%2d  AK(n) total=%2d   n+11 tuple total=%2d"
              % (n, acx.total_length(a), acx.total_length(t)))
    # check the two families' exponent-sum matrices
    for n in (3, 5):
        for name, t in (("AK", acx.ak(n)), ("n11", acx.n11(n))):
            print("n=%d %s exp sums %r" % (n, name, [acx.exp_sum(r, 2) for r in t]))
    print("ms(3,w_1) =", acx.ms(3, acx.w_word(1)),
          "len", acx.total_length(acx.ms(3, acx.w_word(1))))
    print("ms(3,w_2) =", acx.ms(3, acx.w_word(2)),
          "len", acx.total_length(acx.ms(3, acx.w_word(2))))


if __name__ == "__main__":
    ok = ak1_round1()
    ok = local_minimum() and ok
    family_shapes()
    print("ALL OK" if ok else "SOME CHECK FAILED")
