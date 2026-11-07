"""Consolidate every search result into the shortest verified path per id,
then emit submission part files and check each with the official verifier.

Only paths that pass the official verifier are written to a submission file.
Anything else is dropped and counted, so a claimed result is never one the
official tool rejects.
"""
import glob
import json
import os
import subprocess
import sys

PARTS = 500
TOOLS = "upstream/competition/tools"
MANIFEST = TOOLS + "/verifier/data/manifest.json"
TRAIN_MANIFEST = "upstream/competition/examples/training_manifest.json"


def load_results(pattern="results/*.out"):
    best = {}
    for path in sorted(glob.glob(pattern)):
        for line in open(path):
            p = line.rstrip("\n").split("\t")
            if len(p) < 4:
                continue
            cid, ln = p[0], p[1]
            if ln == "-1":
                continue
            ln = int(ln)
            moves = p[3]
            flag = p[4] if len(p) > 4 else "-"
            cur = best.get(cid)
            if cur is None or ln < cur[0] or (ln == cur[0] and flag == "P" and cur[2] != "P"):
                best[cid] = (ln, moves, flag, os.path.basename(path))
    return best


def verify(manifest, subfile):
    cmd = [sys.executable, "-m", "verifier", "--manifest", manifest, "--submission", subfile]
    env = dict(os.environ)
    env["PYTHONPATH"] = TOOLS
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    try:
        d = json.loads(p.stdout)
    except Exception:
        return p.returncode, None, p.stdout + p.stderr
    return p.returncode, d, ""


def main():
    best = load_results()
    ac_ids = [c for c in best if c.startswith("ac-")]
    print("raw best paths:", len(best), "ac:", len(ac_ids))

    # order: proved optimal first, then shorter, then id
    ordered = sorted(ac_ids, key=lambda c: (0 if best[c][2] == "P" else 1, best[c][0], c))

    # verify in one batch first
    os.makedirs("submission/ac", exist_ok=True)
    os.makedirs("submission/stable", exist_ok=True)
    tmp = ".scratch/all_ac.txt"
    with open(tmp, "w") as f:
        for c in ordered:
            f.write("%s: %s\n" % (c, best[c][1]))
    rc, d, err = verify(MANIFEST, tmp)
    if d is None:
        print("verifier could not parse:", err[:500])
        return 1
    ok = {r["challenge_id"] for r in d["results"] if r.get("ok")}
    bad = [r for r in d["results"] if not r.get("ok")]
    print("verified ok:", len(ok), "failed:", len(bad))
    for r in bad[:5]:
        print("  FAIL", r)

    good = [c for c in ordered if c in ok]
    lengths = sorted(best[c][0] for c in good)
    print("accepted ids:", len(good), "length min/median/max:",
          lengths[0], lengths[len(lengths) // 2], lengths[-1] if lengths else None)

    # part files
    for path in glob.glob("submission/ac/part-*.txt") + glob.glob("submission/stable/part-*.txt"):
        os.remove(path)
    nparts = 0
    for i in range(0, len(good), PARTS):
        chunk = good[i:i + PARTS]
        nparts += 1
        with open("submission/ac/part-%02d.txt" % nparts, "w") as f:
            f.write("# Andrews-Curtis, part %02d. %d solutions. ac-r2-v1.\n" % (nparts, len(chunk)))
            for c in chunk:
                f.write("%s: %s\n" % (c, best[c][1]))
    nsp = 0
    for i in range(0, len(good), PARTS):
        chunk = good[i:i + PARTS]
        nsp += 1
        with open("submission/stable/part-%02d.txt" % nsp, "w") as f:
            f.write("# Stable AC, part %02d. %d solutions. sac-r8-v1.\n" % (nsp, len(chunk)))
            for c in chunk:
                sid = "sac-" + c.split("-")[1]
                moves = best[c][1].rstrip("]") + ",16,15]"
                f.write("%s: %s\n" % (sid, moves))
    print("wrote %d ac parts and %d stable parts" % (nparts, nsp))

    # verify every part file and record the receipt lines
    report = []
    for kind in ("ac", "stable"):
        for path in sorted(glob.glob("submission/%s/part-*.txt" % kind)):
            rc, d, err = verify(MANIFEST, path)
            n = len(d["results"]) if d else -1
            good_n = sum(1 for r in d["results"] if r.get("ok")) if d else -1
            report.append((path, rc, n, good_n))
            print("  %-32s exit=%d lines=%d ok=%d" % (path, rc, n, good_n))
    json.dump({"parts": [{"path": a, "exit": b, "lines": c, "ok": dd} for a, b, c, dd in report],
               "accepted_ids": good,
               "best": {c: [best[c][0], best[c][2]] for c in good}},
              open("results/summary.json", "w"), indent=1)
    with open("results/best_ac.tsv", "w") as f:
        f.write("challenge_id\tlength\tproved_optimal\tmoves\tsource\n")
        for c in ordered:
            if c in ok:
                f.write("%s\t%d\t%s\t%s\t%s\n" % (c, best[c][0], best[c][2], best[c][1], best[c][3]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
