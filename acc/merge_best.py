"""Maintain runs/best.tsv: the single source of truth for solved ids.

Columns: id, length, method, proven_optimal (yes/no), path.
Every candidate is replayed against the independent Python engine before it is
kept, so a corrupt line can never enter the table.  The table is rewritten
atomically and is safe to resume from at any time.
"""
import glob
import os
import sys

sys.path.insert(0, "acc")
import engine as E

BEST = "runs/best.tsv"


def load_init(path="data/scored.in"):
    init = {}
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if len(p) == 3:
            init[p[0]] = ([int(x) for x in p[1].split(",")] if p[1] else [],
                          [int(x) for x in p[2].split(",")] if p[2] else [])
    return init


def parse_moves(mv):
    mv = mv.strip()
    assert mv.startswith("[") and mv.endswith("]"), mv
    body = mv[1:-1]
    return [int(x) for x in body.split(",")] if body else []


def main():
    init = load_init()
    best = {}

    # seed from the existing table
    if os.path.exists(BEST):
        for line in open(BEST):
            p = line.rstrip("\n").split("\t")
            if len(p) == 5 and p[0] != "id":
                best[p[0]] = (int(p[1]), p[2], p[3], p[4])

    files = glob.glob("results/*.out") + glob.glob("runs/*.out")
    added = improved = rejected = 0
    for path in sorted(files):
        method = os.path.basename(path).replace(".out", "")
        for line in open(path):
            p = line.rstrip("\n").split("\t")
            if len(p) < 4 or p[1] == "-1":
                continue
            cid, ln = p[0], int(p[1])
            if cid not in init:
                continue
            incoming_proved = "yes" if (len(p) > 4 and p[4] == "P") else "no"
            if cid in best:
                cur_len, _, cur_proved, _ = best[cid]
                # equal length: allow an optimality upgrade, nothing else
                if cur_len < ln or (cur_len == ln and not (incoming_proved == "yes" and cur_proved == "no")):
                    continue
            mv = p[3]
            try:
                moves = parse_moves(mv)
            except Exception:
                rejected += 1
                continue
            ok, _ = E.check_path(init[cid], moves)
            if not ok:
                rejected += 1
                continue
            proved = "yes" if (len(p) > 4 and p[4] == "P") else "no"
            if cid in best and best[cid][0] == ln and best[cid][2] == "yes":
                proved = "yes"
            was = cid in best
            best[cid] = (ln, method, proved, mv)
            if was:
                improved += 1
            else:
                added += 1

    tmp = BEST + ".tmp"
    with open(tmp, "w") as f:
        f.write("id\tlength\tmethod\tproven_optimal\tpath\n")
        for cid in sorted(best):
            ln, method, proved, mv = best[cid]
            f.write("%s\t%d\t%s\t%s\t%s\n" % (cid, ln, method, proved, mv))
    os.replace(tmp, BEST)
    print("best.tsv: %d ids (%d new, %d improved, %d rejected)" % (len(best), added, improved, rejected))
    prov = sum(1 for v in best.values() if v[2] == "yes")
    print("  proven optimal: %d" % prov)
    return 0


if __name__ == "__main__":
    sys.exit(main())
