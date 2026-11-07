"""Deterministic breadth-first search of the AC graph from the standard
presentation.

Vertices are tuples of n reduced relators in F_n with every relator of length at
most ``max_relator_len``.  Edges are the three AC moves of ac.py, with
conjugators taken from the reduced words of length at most ``max_conj_len``.
The vertex set is finite, so the search terminates.

What a run proves.  The search explores exactly those presentations that are
AC-equivalent to the standard presentation by a path that stays inside the
bounded vertex set.  A presentation found by the search comes with a path, and
that path is a certificate which ``ac.verify_path`` replays move by move, so
"found" means proved.  A presentation that is absent was not reached inside the
bounds.  That is a statement about the bounded graph only, and it is not a
statement that the presentation is not AC-equivalent to the standard one.

Two soundness points for the pruning.  The moves never change the Smith normal
form of the exponent-sum matrix (see ``ac.abelianization_invariant``), so
dropping vertices whose abelianisation is nontrivial removes no vertex that the
standard presentation can reach.  The relator length bound is a restriction of
the edge set only, and it is applied to the target of each edge.

Command line, with the defaults:

    python3 toolkit/bfs.py
    python3 toolkit/bfs.py --rank 2 --relator-len 5 --conj-len 2
    python3 toolkit/bfs.py --rank 3 --relator-len 2 --conj-len 1 --verify
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

import words as W
import ac as A


# --------------------------------------------------------------------------
# the search
# --------------------------------------------------------------------------

def bfs_from_standard(n=2, max_relator_len=4, max_conj_len=2, max_radius=None,
                      use_abelianization_filter=True):
    """Breadth-first search from the standard presentation of rank n.

    Returns a dict with keys start, n, params, dist, parent, layer_sizes,
    layer_max_length, edges, accepted.
    """
    start = A.standard(n)
    A.check_presentation(start, n)
    conj = A.conjugators(n, max_conj_len)

    dist = {start: 0}
    parent = {start: None}
    layer_sizes = []
    layer_max_length = []
    abl_cache = {start: A.has_trivial_abelianization(start, n)}
    edges = 0
    accepted = 0
    radius = 0
    frontier = [start]

    while frontier:
        layer_sizes.append(len(frontier))
        layer_max_length.append(max(W.total_length(v) for v in frontier))
        if max_radius is not None and radius >= max_radius:
            break
        nxt = []
        for v in sorted(frontier):
            for mv, s in A.successors(v, n, conj):
                edges += 1
                if max(len(r) for r in s) > max_relator_len:
                    continue
                if use_abelianization_filter:
                    ok = abl_cache.get(s)
                    if ok is None:
                        ok = A.has_trivial_abelianization(s, n)
                        abl_cache[s] = ok
                    if not ok:
                        continue
                if s in dist:
                    continue
                dist[s] = radius + 1
                parent[s] = (v, mv)
                nxt.append(s)
                accepted += 1
        frontier = nxt
        radius += 1

    return {
        "start": start,
        "n": n,
        "params": {
            "max_relator_len": max_relator_len,
            "max_conj_len": max_conj_len,
            "max_radius": max_radius,
            "use_abelianization_filter": use_abelianization_filter,
            "conjugators": len(conj),
        },
        "dist": dist,
        "parent": parent,
        "layer_sizes": layer_sizes,
        "layer_max_length": layer_max_length,
        "edges": edges,
        "accepted": accepted,
    }


def path_to(res, target):
    """The list of move tags from the standard presentation to target, or None."""
    if target not in res["dist"]:
        return None
    out = []
    v = target
    while res["parent"][v] is not None:
        prev, mv = res["parent"][v]
        out.append(mv)
        v = prev
    out.reverse()
    return out


def verify_all_paths(res, n, limit=None):
    """Replay every stored path and check that it ends at its vertex.

    Returns (True, number checked) or (False, first vertex that failed).
    """
    checked = 0
    for v in sorted(res["dist"]):
        if limit is not None and checked >= limit:
            break
        p = path_to(res, v)
        if A.verify_path(A.standard(n), p, n) != v:
            return False, v
        checked += 1
    return True, checked


def box_count(n, max_relator_len, use_abelianization_filter=True, cap=3_000_000):
    """Number of presentations in the bounded box, and how many pass the filter.

    Returns (total, passing) or None when the box is larger than cap.
    """
    box = len(W.all_words(n, max_relator_len)) ** n
    if box > cap:
        return None
    total = 0
    passing = 0
    for tup in itertools.product(W.all_words(n, max_relator_len), repeat=n):
        total += 1
        if not use_abelianization_filter or A.has_trivial_abelianization(tup, n):
            passing += 1
    return total, passing


def box_gap(res, n, max_relator_len, use_abelianization_filter=True):
    """Compare the component with the whole filtered box.

    Returns a dict with the total number of presentations in the box, the
    number that pass the filter, the list of those the search did not reach,
    and a histogram of their relator length profiles.
    """
    reached = res["dist"]
    total = 0
    passing = 0
    missing = []
    for tup in itertools.product(W.all_words(n, max_relator_len), repeat=n):
        total += 1
        if use_abelianization_filter and not A.has_trivial_abelianization(tup, n):
            continue
        passing += 1
        if tup not in reached:
            missing.append(tup)
    hist = {}
    for v in missing:
        key = tuple(sorted(len(r) for r in v))
        hist[key] = hist.get(key, 0) + 1
    return {
        "total": total,
        "passing": passing,
        "missing": missing,
        "histogram": sorted(hist.items()),
    }


# --------------------------------------------------------------------------
# certificate files
# --------------------------------------------------------------------------
#
# One line per presentation:
#
#     relator;relator;...    TAB    inv 1, mul 2 1, conj 1 xY
#
# The relators are written with words.format_word, so generators are x, y, z
# and inverses are X, Y, Z.  Moves are separated by commas because a single
# move contains spaces.  The moves are written with format_move below.  A file
# of such lines is verified with replay_lines, which uses only words.py and
# ac.py and never runs a search.

def format_move(mv):
    """Printable form of a move tag, the inverse of parse_move."""
    if mv[0] == "inv":
        return "inv %d" % mv[1]
    if mv[0] == "mul":
        return "mul %d %d" % (mv[1], mv[2])
    if mv[0] == "conj":
        return "conj %d %s" % (mv[1], W.format_word(mv[2]))
    raise ValueError("unknown move kind %r" % (mv[0],))


def parse_move(text):
    """Read a move tag written by format_move."""
    parts = text.split()
    if not parts:
        raise ValueError("empty move")
    kind = parts[0]
    if kind == "inv" and len(parts) == 2:
        return ("inv", int(parts[1]))
    if kind == "mul" and len(parts) == 3:
        return ("mul", int(parts[1]), int(parts[2]))
    if kind == "conj" and len(parts) == 3:
        return ("conj", int(parts[1]), W.parse_word(parts[2]))
    raise ValueError("cannot read a move from %r" % (text,))


def certificate_lines(res, n):
    """Yield one certificate line per vertex of a search, in sorted order."""
    for v in sorted(res["dist"]):
        moves = path_to(res, v)
        yield (";".join(W.format_word(r) for r in v)
               + "\t"
               + ", ".join(format_move(mv) for mv in moves))


def replay_lines(lines, n):
    """Verify certificate lines from the standard presentation of rank n.

    Returns (number that replay, number that fail, first failing line or None).
    """
    ok = 0
    bad = 0
    first_bad = None
    for line in lines:
        line = line.rstrip("\n")
        if not line.strip():
            continue
        head, _, tail = line.partition("\t")
        target = tuple(W.parse_word(part) for part in head.split(";"))
        moves = [parse_move(tok) for tok in tail.split(",")] if tail.strip() else []
        final = A.verify_path(A.standard(n), moves, n)
        if final == target:
            ok += 1
        else:
            bad += 1
            if first_bad is None:
                first_bad = line
    return ok, bad, first_bad


def replay_file(path, n):
    """replay_lines on a file."""
    with open(path, "r", encoding="utf-8") as handle:
        return replay_lines(handle, n)


# --------------------------------------------------------------------------
# command line
# --------------------------------------------------------------------------

def parse_tuple_arg(text, n):
    """Parse 'x,xxY' into a tuple of relators; each part is parsed greedily."""
    parts = [p.strip() for p in text.split(",")]
    return tuple(W.parse_word(p) for p in parts)


def main(argv=None):
    ap = argparse.ArgumentParser(description="BFS of the AC graph from the standard presentation")
    ap.add_argument("--rank", type=int, default=2)
    ap.add_argument("--relator-len", type=int, default=4)
    ap.add_argument("--conj-len", type=int, default=2)
    ap.add_argument("--max-radius", type=int, default=None)
    ap.add_argument("--no-filter", action="store_true",
                    help="do not prune vertices with nontrivial abelianisation")
    ap.add_argument("--verify", action="store_true",
                    help="replay every stored path (slow on large searches)")
    ap.add_argument("--find", default=None,
                    help="comma separated relators; print a path to this tuple if found")
    ap.add_argument("--count-box", action="store_true",
                    help="count the presentations in the bounded box that pass the filter")
    ap.add_argument("--box-gap", action="store_true",
                    help="list the presentations in the filtered box that the search did not reach")
    ap.add_argument("--gap-examples", type=int, default=5,
                    help="how many missed presentations to print with --box-gap")
    ap.add_argument("--export", default=None,
                    help="write the certificate of every vertex to this file")
    ap.add_argument("--replay", default=None,
                    help="verify a certificate file and stop, without searching")
    ap.add_argument("--tag", default="", help="label printed at the top of the report")
    args = ap.parse_args(argv)

    n = args.rank
    L = args.relator_len
    C = args.conj_len
    use_filter = not args.no_filter

    if args.replay is not None:
        ok, bad, first_bad = replay_file(args.replay, n)
        print("certificate file %s at rank %d" % (args.replay, n))
        print("lines that replay from the standard presentation = %d" % ok)
        print("lines that fail = %d" % bad)
        if first_bad is not None:
            print("first failing line: " + first_bad)
        return 0 if bad == 0 else 1

    t0 = time.time()
    res = bfs_from_standard(n, L, C, args.max_radius, use_filter)
    elapsed = time.time() - t0

    out = []
    if args.tag:
        out.append(args.tag)
        out.append("")
    out.append("rank n = %d" % n)
    out.append("max relator length L = %d" % L)
    out.append("max conjugator length C = %d (number of conjugators %d)"
               % (C, res["params"]["conjugators"]))
    out.append("abelianisation filter = %s" % ("on" if use_filter else "off"))
    if args.max_radius is not None:
        out.append("radius limit = %d" % args.max_radius)
    out.append("")
    out.append("radius   vertices   max total relator length")
    for r in range(len(res["layer_sizes"])):
        out.append("%6d %10d                %d"
                   % (r, res["layer_sizes"][r], res["layer_max_length"][r]))
    total_v = len(res["dist"])
    out.append("")
    out.append("total vertices (component) = %d" % total_v)
    out.append("edges examined = %d, edges accepted = %d" % (res["edges"], res["accepted"]))
    out.append("largest radius reached = %d" % (len(res["layer_sizes"]) - 1))
    all_ok = all(A.has_trivial_abelianization(v, n) for v in res["dist"])
    out.append("every vertex has trivial abelianisation = %s" % all_ok)
    if args.count_box:
        bc = box_count(n, L, use_filter)
        if bc is None:
            out.append("box count skipped (box larger than the cap)")
        else:
            out.append("bounded box: %d presentations, %d pass the filter, component covers %d"
                       % (bc[0], bc[1], total_v))
    if args.box_gap:
        gap = box_gap(res, n, L, use_filter)
        reached = gap["passing"] - len(gap["missing"])
        out.append("bounded box: %d presentations, %d pass the filter, %d reached, %d missed"
                   % (gap["total"], gap["passing"], reached, len(gap["missing"])))
        if gap["histogram"]:
            out.append("relator length profiles of the missed presentations: "
                       + ", ".join("%s: %d" % (list(k), c) for k, c in gap["histogram"]))
            out.append("first missed presentations, in the enumeration order of words.all_words:")
            for v in gap["missing"][:args.gap_examples]:
                out.append("    " + W.format_tuple(v)
                           + "   exponent sums " + str(A.abelianization(v, n)))
    if args.find is not None:
        target = parse_tuple_arg(args.find, n)
        p = path_to(res, target)
        if p is None:
            out.append("target %s NOT found in the component" % W.format_tuple(target))
        else:
            out.append("target %s found at distance %d" % (W.format_tuple(target), len(p)))
            out.append("moves: " + " ".join(str(mv) for mv in p))
            final = A.verify_path(A.standard(n), p, n)
            out.append("replay of the path gives %s = %s"
                       % (W.format_tuple(final), "target" if final == target else "MISMATCH"))
    if args.export is not None:
        with open(args.export, "w", encoding="utf-8") as handle:
            count = 0
            for line in certificate_lines(res, n):
                handle.write(line + "\n")
                count += 1
        out.append("wrote %d certificates to %s" % (count, args.export))
        ok_e, bad_e, first_bad_e = replay_file(args.export, n)
        out.append("replayed the file just written: %d replay, %d fail" % (ok_e, bad_e))
    if args.verify:
        ok, info = verify_all_paths(res, n)
        out.append("all stored paths replay correctly = %s (%s)" % (ok, info))

    print("\n".join(out))
    print("[bfs] %.2f s" % elapsed, file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
