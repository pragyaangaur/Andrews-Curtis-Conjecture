"""Two move templates that do not depend on any search, with their checks.

Template A (Myasnikov, Myasnikov, Shpilrain step): AK(n) -> MS(n, w_1), 2n+9
moves.  After a fixed prefix of nine moves the first relator contains a run of
n-1 letters x^-1, and each of the n-1 repetitions of the block
[('mul',1,2), ('conj',1,(1,))] removes one x^-1 from that run and lengthens the
second relator by one y, which is exactly the difference between w_1 and the
relator of AK(n).  The last three moves restore the shape.  The template is
therefore uniform in n, and it is machine-checked below for n = 4, ..., 30.

Template B (the last step, MS(n, w_(n-1)) -> P(n)): nine moves, with no n in
the move list at all.  Checked for n = 3, ..., 30.

Usage: python3 patterns.py
"""

import sys
import acx


def mms_pattern(n):
    mv = [("inv", 1), ("conj", 1, (-2, -1)), ("conj", 2, tuple([-1] * (n - 1))),
          ("mul", 1, 2), ("inv", 1), ("mul", 2, 1), ("inv", 1),
          ("conj", 2, (-1,)), ("inv", 1)]
    for _ in range(n - 1):
        mv += [("mul", 1, 2), ("conj", 1, (1,))]
    return mv[:-1] + [("conj", 1, (2, 1)), ("inv", 2), ("inv", 1)]


def lemma5_pattern():
    return [("inv", 2), ("conj", 1, (-2, 1)), ("conj", 2, (1, 2)), ("mul", 1, 2),
            ("inv", 1), ("conj", 2, (-1, 2)), ("mul", 1, 2), ("inv", 1),
            ("conj", 2, (1,))]


def run():
    bad = []
    for n in range(4, 31):
        if not acx.verify(acx.ak(n), mms_pattern(n), acx.ms(n, acx.w_word(1)), 2):
            bad.append(("template A", n))
    for n in range(3, 31):
        if not acx.verify(acx.ms(n, acx.w_word(n - 1)), lemma5_pattern(),
                          acx.p_form(n), 2):
            bad.append(("template B", n))
    print("template A  AK(n) -> MS(n,w_1)      2n+9 moves   n = 4..30:  %s"
          % ("PASS" if not [b for b in bad if b[0] == "template A"] else "FAIL"))
    print("template B  MS(n,w_(n-1)) -> P(n)       9 moves   n = 3..30:  %s"
          % ("PASS" if not [b for b in bad if b[0] == "template B"] else "FAIL"))
    print("total: %s" % ("PASS" if not bad else "FAIL %r" % bad))
    return not bad


if __name__ == "__main__":
    sys.exit(0 if run() else 1)
