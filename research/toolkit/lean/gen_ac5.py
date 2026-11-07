#!/usr/bin/env python3
"""Generate the Lean 5 certificate section for the 33 Q**-certificates of round 4.

Input:  directions/qdouble-star/m9/certs/*.cert  (member m9's Q**-certificates)
Output: a Lean source fragment in the `QMove` format of AC5.lean, one definition
        block per certificate: the start tuple, the intermediate tuples of the
        blocks, the block move lists, one `decide` theorem per block, the chain
        of `checkCert_append` lemmas, the certificate theorem and `#print axioms`.

The move lists are replayed here first by the independent checker
`directions/qdouble-star/m9/qverify.py` (imported, not reimplemented), so a
certificate that Lean rejects is a Lean-side defect and not a data defect.

Usage: python3 gen_ac5.py OUT.lean [cert files...]
"""
import glob
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def _find_repo(d):
    while d != "/":
        if os.path.isdir(os.path.join(d, "directions", "qdouble-star")):
            return d
        d = os.path.dirname(d)
    raise SystemExit("repository root not found")


REPO = os.environ.get("REPO") or _find_repo(HERE)
M9 = os.path.join(REPO, "directions", "qdouble-star", "m9")
sys.path.insert(0, M9)

import qverify as Q  # noqa: E402

GENS = Q.GENS
BLOCK = int(os.environ.get("BLOCK", "2"))


def letters(w):
    """qverify word (1-based signed ints) -> Lean letter list of (index, Bool)."""
    out = []
    for a in w:
        out.append("(%d, %s)" % (abs(a) - 1, "true" if a > 0 else "false"))
    return "[" + ", ".join(out) + "]"


def pres(p):
    """qverify Pres -> mkQPres call."""
    rels = ", ".join(letters(r) for r in p.rels)
    return "mkQPres %d %d [%s]" % (p.n, len(p.rels), rels)


def lean_move(mv, state):
    k = mv[0]
    if k == "prolong":
        return ".prolong"
    if k in ("inv", "neg", "delete"):
        if k == "delete":
            i = mv[1]
            hits = [j for j, r in enumerate(state.rels) if any(abs(a) == i for a in r)]
            if len(hits) != 1:
                raise SystemExit("delete: generator %d in %d relators" % (i, len(hits)))
            j = hits[0]
            r = state.rels[j]
            pos = [t for t, a in enumerate(r) if abs(a) == i]
            if len(pos) != 1:
                raise SystemExit("delete: letter %d occurs %d times in its relator" % (i, len(pos)))
            t = pos[0]
            pre, suf = r[:t], r[t + 1:]
            if Q.red(list(suf) + list(pre)) != ():
                raise SystemExit("delete: relator is not a conjugate of generator %d" % i)
            return ".delete %d %d %s" % (i - 1, j, letters(pre))
        return ".%s %d" % (k, mv[1] - 1)
    if k in ("mul", "lmul"):
        return ".%s %d %d" % (k, mv[1] - 1, mv[2] - 1)
    if k == "conj":
        return ".conj %d %s" % (mv[1] - 1, letters(mv[2]))
    if k in ("nij", "nji", "nijinv", "njiinv", "swap"):
        return ".%s %d %d" % (k, mv[1] - 1, mv[2] - 1)
    raise SystemExit("unknown move kind %r" % (k,))


def gen(path):
    name = os.path.basename(path)[:-len(".cert")]
    ident = name.replace(".", "_")
    start, end, mvs = Q.read_cert(path)
    st = Q.Pres(start[0], start[1])
    states = [Q.Pres(st.n, [list(r) for r in st.rels])]
    lean_mvs = []
    for mv in mvs:
        lean_mvs.append(lean_move(mv, st))
        Q.apply(st, mv)
        states.append(Q.Pres(st.n, [list(r) for r in st.rels]))
    if end is not None:
        got = (st.n, [tuple(r) for r in st.rels])
        want = (end[0], [tuple(r) for r in end[1]])
        if got != want:
            raise SystemExit("%s: endpoint mismatch" % path)
    blocks = [lean_mvs[i:i + BLOCK] for i in range(0, len(lean_mvs), BLOCK)]
    out = []
    titles = {
        "zieschang": "Zieschang's pair  <x,y | x^3y^3x^3y^2>  ->  <x,y | x^3y^5>",
    }
    title = titles.get(name, "McCool-Pietrowski  <x,y | (x^ky^t)^p y>  ->  <x,y | x^k y^(pt+1)>")
    out.append("/-- `%s.cert`: %s, %d Q**-moves in %d block(s) of at most %d. -/"
               % (name, title, len(lean_mvs), len(blocks), BLOCK))
    out.append("def %s_s : QPres := %s" % (ident, pres(states[0])))
    for bi in range(len(blocks)):
        out.append("def %s_i%d : QPres := %s" % (ident, bi + 1, pres(states[min((bi + 1) * BLOCK, len(states) - 1)])))
    out.append("def %s_e : QPres := %s" % (ident, pres(states[-1])))
    for bi, blk in enumerate(blocks):
        out.append("def %s_c%d : List QMove :=\n  [ %s ]" % (ident, bi + 1, ",\n    ".join(blk)))
    for bi in range(len(blocks)):
        src = "%s_s" % ident if bi == 0 else "%s_i%d" % (ident, bi)
        out.append("set_option maxRecDepth 100000 in\ntheorem %s_b%d :\n    replay %s_c%d %s = some %s_i%d := by decide"
                   % (ident, bi + 1, ident, bi + 1, src, ident, bi + 1))
    # chain: a balanced binary tree of `replay_append` applications, so that no term is deep
    st = ["%s_s" % ident] + ["%s_i%d" % (ident, bi + 1) for bi in range(len(blocks))]
    names = ["%s_c%d" % (ident, bi + 1) for bi in range(len(blocks))]
    leaves = ["%s_b%d" % (ident, bi + 1) for bi in range(len(blocks))]
    lemmas = []

    def chain(i, j):
        """replay of blocks i..j-1 from state i to state j; returns (lemma name, list term)."""
        if j - i == 1:
            return leaves[i], names[i], st[i], st[j]
        mid = (i + j) // 2
        ln, ll, ls, lm = chain(i, mid)
        rn, rl, rs, rm = chain(mid, j)
        name = "%s_k%d_%d" % (ident, i, j)
        lemmas.append("theorem %s : replay (%s ++ %s) %s = some %s :=\n  replay_concat (ms₁ := %s) (ms₂ := %s) (P := %s) (R := %s) (S := %s) %s %s"
                      % (name, ll, rl, ls, rm, ll, rl, ls, lm, rm, ln, rn))
        return name, "(%s ++ %s)" % (ll, rl), ls, rm

    top, topl, tops, tope = chain(0, len(blocks))
    out.extend(lemmas)
    out.append("/-- The certificate checked: %d Q**-moves from the printed start tuple to the printed end\n    tuple. -/\ntheorem %s_replay : replay %s %s_s = some %s_e := %s"
               % (len(lean_mvs), ident, topl, ident, ident, top))
    out.append("/-- The same, in the form of the checker: `checkCert` returns `true` on the recorded\n    start and finish tuples. -/\ntheorem %s_checked : checkCert %s %s_s %s_e = true := by\n  rw [checkCert]\n  exact decide_eq_true_eq.mpr %s_replay"
               % (ident, topl, ident, ident, ident))
    return "\n".join(out) + "\n", ident


def main(argv):
    outpath = argv[1]
    files = argv[2:] or sorted(glob.glob(os.path.join(M9, "certs", "*.cert")))
    chunks = []
    idents = []
    for f in files:
        text, ident = gen(f)
        chunks.append(text)
        idents.append(ident)
    with open(outpath, "w", encoding="utf-8") as fh:
        fh.write("\n\n".join(chunks))
        fh.write("\n")
    print("wrote %s: %d certificates (%s)" % (outpath, len(idents), ", ".join(idents[:3]) + ", ..."))
    with open(outpath + ".axioms", "w", encoding="utf-8") as fh:
        for ident in idents:
            fh.write("#print axioms %s_checked\n" % ident)


if __name__ == "__main__":
    main(sys.argv)
