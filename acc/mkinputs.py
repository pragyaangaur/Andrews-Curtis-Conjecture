"""Build engine input files: id<TAB>r0<TAB>r1."""
import json
import sys

ROOT = "upstream/competition"


def write(path, rows):
    with open(path, "w") as f:
        for cid, r0, r1 in rows:
            f.write("%s\t%s\t%s\n" % (cid, ",".join(map(str, r0)), ",".join(map(str, r1))))


def main():
    tr = json.load(open(ROOT + "/examples/training_424.json"))["instances"]
    write("data/train.in", [(i["training_id"], i["initial_relators"][0], i["initial_relators"][1]) for i in tr])

    m = json.load(open(ROOT + "/tools/verifier/data/manifest.json"))["challenges"]
    ac = [(c["challenge_id"], c["initial_relators"][0], c["initial_relators"][1])
          for c in m if c["challenge_id"].startswith("ac-")]
    ac.sort()
    write("data/scored.in", ac)
    print("train", len(tr), "scored", len(ac))


if __name__ == "__main__":
    main()
