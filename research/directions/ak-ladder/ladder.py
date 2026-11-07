"""The ladder table: one line per rung n = 1, ..., 12.

Columns: total relator length of AK(n); total length of the length-(n+11)
presentation P(n) of Theorem t:n+11; the difference (negative = certified
length reduction available); the determinant of the exponent-sum matrix (an
AC invariant up to sign, unimodular for the whole ladder); the Todd-Coxeter
index of AK(n) and of P(n) with the trivial subgroup (index 1 = the
presentation presents the trivial group); whether AK(n) and P(n) are strict
local minima of total length under every single AC move with conjugators of
length at most 4; and the certified chain, when one is stored.
"""

import glob
import json
import os
import sys
import acx

def _find_checks():
    """Locate the repository's checks/ directory from wherever this file sits."""
    d = os.path.abspath(os.path.dirname(__file__))
    for up in range(0, 6):
        cand = os.path.join(d, *([".."] * up), "checks")
        if os.path.isdir(cand):
            return os.path.abspath(cand)
    return None


_checks = _find_checks()
if _checks is None:
    raise SystemExit("cannot find checks/ (Todd-Coxeter) above this file")
sys.path.insert(0, _checks)
import todd_coxeter as TC


def local_min(rs, conjs):
    L = acx.total_length(rs)
    worst = L
    for m, nrs in acx.successors(rs, len(rs), conjs):
        worst = min(worst, acx.total_length(nrs))
    return L, worst


def chain_for(n):
    path = "certs/chain_ak%d_to_P%d.json" % (n, n)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def main():
    conjs = [w for w in acx.words_up_to(2, 4) if w]
    print("n  |AK(n)|  |P(n)|  diff  det  TC(AK)  TC(P)  AK-min  P-min  chain")
    for n in range(1, 13):
        a, p = acx.ak(n), acx.p_form(n)
        rows = [acx.exp_sum(r, 2) for r in a]
        det = rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0]
        La, wa = local_min(a, conjs)
        Lp, wp = local_min(p, conjs)
        try:
            ia = TC.index_of_subgroup(2, a, (), 100000)
        except Exception as exc:
            ia = "inf?"
        try:
            ip = TC.index_of_subgroup(2, p, (), 100000)
        except Exception as exc:
            ip = "inf?"
        c = chain_for(n)
        if c:
            cs = "%d moves, max %d, replay %s" % (len(c["moves"]),
                                                  c["max_length_on_path"],
                                                  c["replay_ok"])
        else:
            cs = "-"
        print("%2d %7d %8d %5d %4d %7s %6s %7s %6s  %s"
              % (n, La, Lp, Lp - La, det, ia, ip,
                 "yes" if wa == La else "NO", "yes" if wp == Lp else "NO", cs))
    print()
    bad = []
    for n in range(2, 13):
        for k in range(1, n):
            st = acx.ms(n, acx.w_word(k))
            try:
                idx = TC.index_of_subgroup(2, st, (), 100000)
            except Exception:
                idx = "ERR"
            if idx != 1:
                bad.append((n, k, idx))
    print("MS(n,w_k) presents the trivial group for n = 2..12, k = 1..n-1:",
          "PASS" if not bad else bad,
          "(%d tuples)" % sum(n - 1 for n in range(2, 13)))


if __name__ == "__main__":
    main()
