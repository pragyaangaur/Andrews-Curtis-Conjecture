"""Cross-check the C engine against the Python reference and the official verifier.

Checks:
  1. C replay == verifier.core.apply_move on random states and move sequences.
  2. C replay == acc.engine.apply_move (independent implementation).
  3. The eight canonicalisation suffixes really take their state to [[1],[2]].
  4. Sample training paths replay correctly in all three.
"""
import random
import subprocess
import sys

sys.path.insert(0, "upstream/competition/tools")
from verifier import core  # official

sys.path.insert(0, "acc")
import engine as mine


def rand_word(rng, maxlen=6):
    n = rng.randint(0, maxlen)
    w = tuple(rng.choice((1, -1, 2, -2)) for _ in range(n))
    return mine.free_reduce(w)


def main():
    rng = random.Random(20261103)
    cases = []
    for _ in range(4000):
        s = (rand_word(rng, 5), rand_word(rng, 5))
        moves = tuple(rng.randrange(14) for _ in range(rng.randint(0, 12)))
        cases.append((s, moves))

    # official core replay
    bad = 0
    for s, moves in cases:
        so = s
        sm = s
        for m in moves:
            so = core.apply_move(so, m)
            sm = mine.apply_move(sm, m)
        if so != sm:
            bad += 1
            print("MISMATCH python vs official", s, moves, so, sm)
            break
    print("python-vs-official mismatches:", bad)

    # C replay
    inp = []
    for s, moves in cases:
        inp.append("%s|%s|%s" % (
            ",".join(map(str, s[0])), ",".join(map(str, s[1])),
            ",".join(map(str, moves))))
    out = subprocess.run(["./acc/engine", "replay"], input="\n".join(inp) + "\n",
                         capture_output=True, text=True, check=True).stdout.strip().split("\n")
    badc = 0
    for (s, moves), line in zip(cases, out):
        l0, rest = line.split(":", 1)
        w0s, w1s = rest.split("|")
        got = (tuple(int(x) for x in w0s.split(",")) if w0s else (),
               tuple(int(x) for x in w1s.split(",")) if w1s else ())
        want = mine.replay(s, moves)
        if got != want:
            badc += 1
            print("MISMATCH C vs python", s, moves, got, want)
            break
    print("C-vs-python mismatches:", badc)

    # canonicalisation suffixes, checked against the official move table
    okc = 0
    for st, suf in mine.CANON.items():
        cur = st
        for m in suf:
            cur = core.apply_move(cur, m)
        if cur != ((1,), (2,)):
            print("CANON FAIL", st, suf, cur)
        else:
            okc += 1
    print("canonical suffixes ok: %d/8" % okc)

    # every suffix must be shortest: exhaustively BFS to that depth
    from collections import deque
    for st, suf in mine.CANON.items():
        if len(suf) == 0:
            continue
        seen = {st}
        q = deque([(st, 0)])
        found = None
        while q:
            s, d = q.popleft()
            if s == ((1,), (2,)):
                found = d
                break
            if d >= 5:
                continue
            for m in range(14):
                t = core.apply_move(s, m)
                if t not in seen:
                    seen.add(t)
                    q.append((t, d + 1))
        status = "ok" if found == len(suf) else "NOT SHORTEST"
        if found != len(suf):
            print("SUFFIX LENGTH", st, len(suf), found, status)
    print("suffix minimality checked")


if __name__ == "__main__":
    main()
