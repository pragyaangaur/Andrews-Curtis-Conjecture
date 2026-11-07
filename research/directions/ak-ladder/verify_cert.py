"""Independent replay of every stored certificate, with two arithmetics.

Arithmetic A: the tuple-of-int representation of acx.py, which the search used.
Arithmetic B: sympy's free groups, written independently here, which the search
never touched.  A certificate passes only if the move sequence is legal move by
move in arithmetic A and the final tuple agrees with the recorded target in
both arithmetics (as reduced words, and as elements of the free group).

Usage: python3 verify_cert.py [certs/*.json ...]
"""

import glob
import json
import sys
import acx
from sympy.combinatorics.free_groups import free_group

F2, sx, sy = free_group("x, y")
SGEN = {1: sx, 2: sy, -1: sx ** -1, -2: sy ** -1}


def to_sympy(word):
    e = F2.identity
    for a in word:
        e = e * SGEN[a]
    return e


def replay_acx(start, moves, n):
    rs = tuple(tuple(r) for r in start)
    for m in moves:
        if m[0] == "inv":
            rs = acx.apply_move(rs, ("inv", m[1]), n)
        elif m[0] == "mul":
            rs = acx.apply_move(rs, ("mul", m[1], m[2]), n)
        elif m[0] == "conj":
            rs = acx.apply_move(rs, ("conj", m[1], tuple(m[2])), n)
        else:
            raise ValueError("illegal move tag %r" % (m,))
    return rs


def replay_sympy(start, moves, n):
    rs = [to_sympy(r) for r in start]
    for m in moves:
        if m[0] == "inv":
            i = m[1] - 1
            rs[i] = rs[i] ** -1
        elif m[0] == "mul":
            i, j = m[1] - 1, m[2] - 1
            rs[i] = rs[i] * rs[j]
        elif m[0] == "conj":
            i = m[1] - 1
            w = to_sympy(tuple(m[2]))
            rs[i] = w * rs[i] * w ** -1
        else:
            raise ValueError("illegal move tag %r" % (m,))
    return rs


def check_file(path):
    with open(path) as f:
        d = json.load(f)
    start = [tuple(r) for r in d["start"]]
    target = [tuple(r) for r in d["target"]]
    moves = [tuple(m) for m in d["moves"]]
    n = len(start)
    out_a = replay_acx(start, moves, n)
    out_b = replay_sympy(start, moves, n)
    tgt_b = [to_sympy(r) for r in target]
    words_ok = out_a == tuple(target)
    group_ok = out_b == tgt_b
    # legality of each move is enforced by replay_acx (it raises otherwise)
    lens = [sum(len(r) for r in replay_acx(start, moves[:k], n))
            for k in range(len(moves) + 1)]
    return {"job": d.get("job", path), "moves": len(moves),
            "words_equal_target": words_ok, "sympy_equal_target": group_ok,
            "start_length": sum(len(r) for r in start),
            "final_length": sum(len(r) for r in out_a),
            "max_length_on_path": max(lens), "min_length_on_path": min(lens),
            "target_length": sum(len(r) for r in target),
            "ok": bool(words_ok and group_ok)}


def main():
    paths = sys.argv[1:] or sorted(glob.glob("certs/*.json"))
    if not paths:
        print("no certificate files found")
        return 1
    bad = 0
    print("%-24s %5s %6s %6s %6s %5s %s"
          % ("job", "moves", "start", "final", "max", "sympy", "verdict"))
    for p in paths:
        r = check_file(p)
        verdict = "PASS" if r["ok"] else "FAIL"
        bad += 0 if r["ok"] else 1
        print("%-24s %5d %6d %6d %6d %5s %s"
              % (r["job"], r["moves"], r["start_length"], r["final_length"],
                 r["max_length_on_path"], r["sympy_equal_target"], verdict))
    print("%d certificate files, %d failed" % (len(paths), bad))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
