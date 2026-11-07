#!/usr/bin/env python3
"""replay4.py -- round-4 (G6) independent replayer for the three certificate families
that AC4.lean has to check in the Lean kernel.

Written from the file formats and from the documented move tables only.  Nothing is
imported from the generators of the certificates.  A word is a tuple of letters from
{1,-1,2,-2} (1 = a = generator 0, 2 = b = generator 1), freely reduced.

Move language (the one AC4.lean uses, after expansion):
    ("invert", i)            r_i -> r_i^{-1}
    ("conj", i, c)           r_i -> c r_i c^{-1}          c a freely reduced word
    ("mul", i, j)            r_i -> r_i r_j               i != j

Input formats
  res   one line of directions/resisters/std_certs.txt or ak3_hits_certs.txt:
        START|MOVES|END, letters a A b B, "e" the empty word, END == "std" for (a,b);
        move tokens iN (invert relator N), cNL (conjugate relator N by letter L),
        mN (multiply relator N by the other relator, on the right).  Indices 0-based.
  path  one line of spot22_paths.txt:  PAIR | path n,n,n,...   with integer indices into
        the twelve-move table documented in directions/resisters/push.c:
          0 inv0, 1 c0a, 2 c0A, 3 c0b, 4 c0B, 5 inv1, 6 c1a, 7 c1A, 8 c1b, 9 c1B,
          10 m0 (r0 -> r0 r1), 11 m1 (r1 -> r1 r0);
        the start is the fixed tuple named on the command line.
  carr  one JSON file of directions/c14/carreras/: words are signed-integer lists,
        moves are ["invert", i], ["conj", i, g] (single signed generator),
        ["mul", i, j, s] (s = +-1, r_i -> r_i r_j^s) and ["cycle", i, k] (left rotation).

The Carreras files end at a tuple "reached" that lies in the orbit of "target" under
relator inversion, relator rotation and relator swap; all three are AC moves, and this
script appends the explicit moves that carry "reached" to "target" itself, so that the
Lean certificate ends at the declared target.
"""
import argparse
import json
import os
import sys

def find_repo():
    """Walk up from this file until a directory with directions/resisters is found."""
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(8):
        if os.path.isdir(os.path.join(d, 'directions', 'resisters')):
            return d
        d = os.path.dirname(d)
    sys.exit('cannot locate the repository root from %s' % os.path.dirname(os.path.abspath(__file__)))


REPO = find_repo()


# ------------------------------------------------------------------ words
def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(-x for x in reversed(w))


def mulw(u, v):
    return red(tuple(u) + tuple(v))


def conjw(c, u):
    return mulw(mulw(c, u), inv(c))


def rot(w, k):
    if not w:
        return w
    k %= len(w)
    return red(tuple(w[k:]) + tuple(w[:k]))


def show(w):
    if not w:
        return "e"
    d = {1: "a", -1: "A", 2: "b", -2: "B"}
    return "".join(d[x] for x in w)


def parse(s):
    d = {"a": 1, "A": -1, "b": 2, "B": -2}
    if s in ("e", ""):
        return ()
    return red(tuple(d[c] for c in s))


# ------------------------------------------------------------------ moves
def apply_move(R, mv):
    kind = mv[0]
    out = list(R)
    if kind == "invert":
        i = mv[1]
        out[i] = inv(out[i])
    elif kind == "conj":
        i, c = mv[1], mv[2]
        out[i] = conjw(c, out[i])
    elif kind == "mul":
        i, j = mv[1], mv[2]
        if i == j:
            raise ValueError("degenerate multiplication move")
        out[i] = mulw(out[i], out[j])
    else:
        raise ValueError("unknown move %r" % (mv,))
    return out


def replay(R, moves):
    R = [red(tuple(w)) for w in R]
    for mv in moves:
        R = apply_move(R, mv)
    return tuple(R)


def replay_states(R, moves):
    """Every intermediate tuple, the start first."""
    R = [red(tuple(w)) for w in R]
    out = [tuple(R)]
    for mv in moves:
        R = apply_move(R, mv)
        out.append(tuple(R))
    return out


# ------------------------------------------------------------------ resister text format
def parse_res_line(line):
    parts = line.rstrip("\n").split("|")
    assert len(parts) == 3, line
    start = [parse(w) for w in parts[0].split(",")]
    end = parts[2]
    if end == "std":
        endw = [(1,), (2,)]
    else:
        endw = [parse(w) for w in end.split(",")]
    moves = []
    for tok in parts[1].split():
        if tok[0] == "i":
            moves.append(("invert", int(tok[1:])))
        elif tok[0] == "c":
            i, letter = int(tok[1:-1]), tok[-1]
            moves.append(("conj", i, parse(letter)))
        elif tok[0] == "m":
            i = int(tok[1:])
            moves.append(("mul", i, 1 - i))
        else:
            raise ValueError(tok)
    return start, moves, endw


# ------------------------------------------------------------------ push.c path format
PATH_MOVES = [
    ("invert", 0),
    ("conj", 0, (1,)), ("conj", 0, (-1,)), ("conj", 0, (2,)), ("conj", 0, (-2,)),
    ("invert", 1),
    ("conj", 1, (1,)), ("conj", 1, (-1,)), ("conj", 1, (2,)), ("conj", 1, (-2,)),
    ("mul", 0, 1),
    ("mul", 1, 0),
]

# ------------------------------------------------------------------ Carreras JSON
def carr_move_to_moves(R, mv):
    """Expand one Carreras move into the normalized language, using the current tuple."""
    op = mv[0]
    if op == "invert":
        return [("invert", mv[1])], None
    if op == "conj":
        return [("conj", mv[1], (mv[2],))], None
    if op == "mul":
        i, j, s = mv[1], mv[2], mv[3]
        if s == 1:
            return [("mul", i, j)], None
        return [("invert", j), ("mul", i, j), ("invert", j)], None
    if op == "cycle":
        i, k = mv[1], mv[2]
        w = R[i]
        k %= len(w)
        if k == 0:
            return [], None
        return [("conj", i, inv(w[:k]))], None
    raise ValueError("unknown move %r" % (mv,))


def carr_apply(R, mv):
    op = mv[0]
    if op == "invert":
        R[mv[1]] = inv(R[mv[1]])
    elif op == "conj":
        R[mv[1]] = conjw((mv[2],), R[mv[1]])
    elif op == "mul":
        i, j, s = mv[1], mv[2], mv[3]
        R[i] = mulw(R[i], R[j] if s == 1 else inv(R[j]))
    elif op == "cycle":
        R[mv[1]] = rot(R[mv[1]], mv[2])
    else:
        raise ValueError(mv)


def orbit_transition(reached, target):
    """Moves carrying `reached` to `target` exactly, using inversion, rotation and swap.

    Returns None when no such triple exists."""
    def options(w):
        """(invert_first, k) such that rot(w after optional inversion, k) == wanted."""
        out = []
        for s in (0, 1):
            base = inv(w) if s else w
            for k in range(max(len(base), 1)):
                out.append((s, k, rot(base, k)))
        return out

    t0, t1 = target
    r0, r1 = reached
    opt0 = options(r0)
    opt1 = options(r1)
    for swap in (False, True):
        a, b = (r1, r0) if swap else (r0, r1)
        o0 = options(a)
        o1 = options(b)
        for (s0, k0, w0) in o0:
            if w0 != t0:
                continue
            for (s1, k1, w1) in o1:
                if w1 != t1:
                    continue
                moves = []
                if swap:
                    moves += [("mul", 0, 1), ("invert", 0), ("mul", 1, 0),
                              ("invert", 1), ("mul", 0, 1), ("invert", 0)]
                    a, b = r1, r0
                else:
                    a, b = r0, r1
                for (i, s, k) in ((0, s0, k0), (1, s1, k1)):
                    w = a if i == 0 else b
                    if s:
                        moves.append(("invert", i))
                        w = inv(w)
                    # note: "a"/"b" is the tuple *after* the optional swap
                    if k:
                        moves.append(("conj", i, inv(w[:k])))
                return moves
    return None


def check_swap(reached):
    """Control: the six-move swap really swaps a rank-2 tuple."""
    seq = [("mul", 0, 1), ("invert", 0), ("mul", 1, 0),
           ("invert", 1), ("mul", 0, 1), ("invert", 0)]
    return replay(reached, seq) == (reached[1], reached[0])


# ------------------------------------------------------------------ the three families
def certs_std():
    out = []
    lines = [l for l in open(os.path.join(REPO, "directions/resisters/std_certs.txt")) if l.strip()]
    for n, line in enumerate(lines):
        start, moves, end = parse_res_line(line)
        out.append(dict(name="std_%02d" % n, group="std", start=start,
                        moves=moves, end=end, source="std_certs.txt line %d" % (n + 1)))
    return out


AK3 = ((1, 2, 1, -2, -1, -2), (1, 1, 1, -2, -2, -2, -2))   # (x y x y^-1 x^-1 y^-1, x^3 y^-4)


def certs_ak3():
    out = []
    lines = [l for l in open(os.path.join(REPO, "directions/resisters/ak3_hits_certs.txt")) if l.strip()]
    swap = [("mul", 0, 1), ("invert", 0), ("mul", 1, 0),
            ("invert", 1), ("mul", 0, 1), ("invert", 0)]
    for n, line in enumerate(lines):
        start, moves, end = parse_res_line(line)
        extra = []
        if tuple(end) != AK3:
            if tuple(end) == (AK3[1], AK3[0]):
                extra = list(swap)
            else:
                raise SystemExit("ak3 line %d has an unexpected end tuple %r" % (n + 1, end))
        out.append(dict(name="ak3_%02d" % n, group="ak3", start=start,
                        moves=moves + extra, end=list(AK3),
                        source="directions/resisters/ak3_hits_certs.txt line %d" % (n + 1)))
    return out


G22START = ("BBABaba,BAbABaa")


def certs_merge():
    src = os.path.join(REPO, ".ultramath/smw2woueq/m4/certs/spot22_paths.txt")
    if not os.path.exists(src):
        src = os.path.join(REPO, ".ultramath/smw2opo0o/m7/work/spot22_paths.txt")
    start = [parse(w) for w in G22START.split(",")]
    out = []
    for n, line in enumerate(l for l in open(src) if l.strip()):
        left, right = line.split("|")
        pair = left.strip()
        idx = [int(x) for x in right.split()[1].split(",")]
        end = [parse(w) for w in pair.split(",")]
        moves = [list(PATH_MOVES[k]) for k in idx]
        moves = [tuple(m) for m in moves]
        out.append(dict(name="merge_%02d" % n, group="merge", start=start,
                        moves=moves, end=end,
                        source="certs/spot22_paths.txt line %d (start %s)" % (n + 1, G22START)))
    return out


CARR = ["cert_ms3_yinvx2yinv_equiv_ak3.json", "cert_ms3_yx2y_equiv_ak3.json",
        "bottleneck_ak_f3_cert.json", "cert_sym_equiv_orphan1.json",
        "cert_idx0_equiv_mirror.json"]


def certs_carr():
    out = []
    for n, fn in enumerate(CARR):
        d = json.load(open(os.path.join(REPO, "directions/c14/carreras", fn)))
        R = [red(tuple(r)) for r in d["initial"]]
        reached_check = [list(r) for r in R]
        moves = []
        for mv in d["moves"]:
            add, _ = carr_move_to_moves(R, mv)
            moves += add
            carr_apply(R, mv)
        reached = tuple(R)
        assert [list(r) for r in reached] == d["reached"], (fn, "reached mismatch")
        target = [red(tuple(r)) for r in d["target"]]
        extra = orbit_transition(reached, tuple(target))
        if extra is None:
            raise SystemExit("no orbit transition for %s" % fn)
        out.append(dict(name="carr_%d" % n, group="carr", start=[red(tuple(r)) for r in d["initial"]],
                        moves=moves + extra, end=target,
                        source="directions/c14/carreras/" + fn,
                        reached=[list(r) for r in reached],
                        extra_moves=len(extra)))
    return out


FAMILIES = {"std": certs_std, "ak3": certs_ak3, "merge": certs_merge, "carr": certs_carr}


def run(fam, json_out=None, verbose=True):
    certs = FAMILIES[fam]()
    bad = 0
    for c in certs:
        got = replay(c["start"], c["moves"])
        ok = tuple(got) == tuple(tuple(w) for w in c["end"])
        c["ok"] = ok
        c["replayed"] = [list(w) for w in got]
        c["path"] = [[list(w) for w in st] for st in replay_states(c["start"], c["moves"])]
        if verbose:
            print("%-4s %-9s %3d moves  %-16s -> %-16s %s" % (
                "PASS" if ok else "FAIL", c["name"], len(c["moves"]),
                ",".join(show(w) for w in c["start"]), ",".join(show(w) for w in got),
                "" if ok else "recorded end " + ",".join(show(tuple(w)) for w in c["end"])))
        bad += 0 if ok else 1
    print("%s: %d certificates, %d failed, %d moves total" %
          (fam, len(certs), bad, sum(len(c["moves"]) for c in certs)))
    if json_out:
        os.makedirs(json_out, exist_ok=True)
        json.dump(certs, open(os.path.join(json_out, "certs_%s.json" % fam), "w"))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("family", choices=list(FAMILIES) + ["all"])
    ap.add_argument("--json-out", default=None)
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    fams = list(FAMILIES) if a.family == "all" else [a.family]
    bad = sum(run(f, a.json_out, verbose=not a.quiet) for f in fams)
    if a.family == "all":
        print("ALL: %d failed certificates" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
