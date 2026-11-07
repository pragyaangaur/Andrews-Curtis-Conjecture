# The resisters push: 98 of the 164 undecided presentations decided

Round 3 direction F4, member m7. This file covers the 164 presentations that
`directions/c14` recorded as resisting classification at total relator length 13
and 14. Every substantive claim is labelled **Verified**, **Computed**,
**Argument** or **Reported**. Nothing here is a claim about the truth or
falsehood of the Andrews-Curtis conjecture.

## 0. Summary

Every one of the 164 now carries a definite statement: 98 are decided by an
explicit certificate and 66 carry an exact bound. **Computed.**

| status | count | certificate or bound |
| --- | --- | --- |
| AC-equivalent to AK(3) | 26 | explicit moves from the presentation to the relator pair of AK(3) |
| AC-trivial | 72 | explicit moves from the presentation to the standard pair `(a,b)` |
| undecided, bound 20 | 22 | no trivialisation and no AK(3)-equivalence whose intermediate tuples all have total relator length at most 20 |
| undecided, bound 22 | 38 | the same statement at 22 |
| undecided, bound 23 | 6 | the same statement at 23 |

All 14 of the resisting presentations of total relator length 13 are decided: 8
are AC-trivial and 6 are AC-equivalent to AK(3). The 66 presentations that remain
undecided all have total relator length 14.

The certificates come from two meet-in-the-middle computations. The first target
is the ball of the standard pair `(a,b)` at total relator length 15, which has
58,487,624 tuples. The second target is the cap-20 census of the AK(3) class in
`directions/pu-enumeration`, 79,680 classes under conjugation and inversion, or
39,840 distinct class keys once the swap of the two relators is also identified.
A component exploration from the resister at a chosen cap either meets one of
the two targets, which yields a certificate, or exhausts, which yields a bound.

## 1. What the previous round left and what this direction adds

`directions/c14` classified every canonical presentation of total relator length
12, 13 and 14 with unimodular abelianisation. Its 164 resisters carried the
bounds of Section 6 of `directions/c14/c14.md`: 34 exhaustive at cap 17, 40 at
cap 18, 68 at cap 19 and 22 stopped by a budget of 400,000 pairs at cap 19.
Those bounds refer to a meet-in-the-middle whose target on the AK(3) side was
the cap-17 ball of AK(3), with 857,808 tuples. **Reported** from that file.

This direction changes three things. The AK(3) target is enlarged to the whole
cap-20 component of AK(3), which has 51,411,456 tuples and 79,680 classes in
`directions/pu-enumeration`. The standard target is enlarged from the cap-14
ball to the cap-15 ball. The pair budgets are raised, and the cap itself is
raised for the presentations whose components stay small. The rounds are
documented in Section 6.

## 2. The engine

`push.c` is a from-scratch breadth-first explorer of the AC graph of a rank-2
presentation. It shares no code with `directions/c14` or
`directions/pu-enumeration`. A state is a pair of freely reduced words stored as
the byte record `[n1][n2][r1][r2]`. The move list at a state is fixed, with
twelve moves in a fixed order: invert relator 0, conjugate relator 0 by a, A, b
and B, invert relator 1, conjugate relator 1 by a, A, b and B, multiply relator
0 on the right by relator 1, and multiply relator 1 on the right by relator 0.
Each of these twelve moves is an Andrews-Curtis move of the standard move set.
**Computed** by reading `push.c`.

The program has three modes used here.

* `push build CAP OUT START NSTATES` walks the whole ball of `START` inside the
  box of total relator length at most `CAP` and writes every state to `OUT`.
* `push search CAP BUDGET RES TARGETS CLASSKEYS STARTLIST [K]` explores the
  component of each start inside the same box, breadth first, and stops at the
  first state that lies in `TARGETS` (an exact state set) or in `CLASSKEYS` (a
  set of class keys under conjugation, inversion and swap of the relators), or
  when `BUDGET` distinct states are stored, or when the component is exhausted.
  The optional last argument is the conjugator bound: 1 gives the twelve
  restricted moves, and 2 also allows conjugation by any freely reduced word of
  length two, which gives 36 moves at each state.
* `push paths CAP BUDGET OUT START TARGETLIST` records a shortest move sequence
  from `START` to each target state inside the ball.

Every exploration is deterministic: the state set is finite, the move order is
fixed, and no randomness or clock is used in any decision. The only wall-clock
limits in the whole direction are the ones a shell imposed on a command.

## 3. Validation of the engine against round-2 numbers

The engine reproduces ten ball sizes computed independently by two round-2
directions. **Verified** by rerunning the commands of Section 8.

| ball | my count | round-2 count | source |
| --- | --- | --- | --- |
| standard, cap 11 | 700,712 | 700,712 | c14.md Section 3 |
| standard, cap 12 | 1,582,280 | 1,582,280 | c14.md Section 3 |
| standard, cap 13 | 6,476,104 | 6,476,104 | c14.md Section 3 |
| standard, cap 14 | 14,399,816 | 14,399,816 | c14.md Section 3 |
| standard, cap 15 | 58,487,624 | 58,487,624 | c14.md Section 3 |
| AK(3), cap 15 | 6,864 | 6,864 | pu.md Section 4 |
| AK(3), cap 16 | 20,560 | 20,560 | pu.md Section 4 |
| AK(3), cap 17 | 857,808 | 857,808 | pu.md Section 4 |
| AK(3), cap 18 | 2,014,992 | 2,014,992 | pu.md Section 4 |
| AK(3), cap 19 | 23,609,984 | 23,609,984 | pu.md Section 4 |

Four component sizes of `directions/c14/mitm19_results.txt` are reproduced
exactly as well, with no target set and the whole component explored at cap 19.
`BBBAAbA,BABabAA` gives 89,856 states, `BBBAAbA,BBabAAA` gives 124,568,
`BBBAbba,BAAABaa` gives 265,392 and `BBBAbbA,BAAAABa` gives 131,408.
**Verified** with `results/validate19.txt` and `results/validate19_res.txt`.

Two further cross-checks concern the certificates. My own replayer
`replay_own.py`, which has its own word arithmetic, replays all 53,866
certificates of `directions/c14/certs_all.txt` with zero failures, and replays
all 79,680 certificates of `directions/pu-enumeration/cert20k1.txt.gz` from
AK(3) with zero failures. So the two certificate families of round 2 are
reproduced by a third implementation. **Verified.**

## 4. Results

The table gives the class of every resister. **Computed.** The full
per-presentation table is `final_status.tsv`.

| total length | round-2 resisters | AC-trivial now | AK(3)-equivalent now | undecided, with bound |
| --- | --- | --- | --- | --- |
| 13 | 14 | 8 | 6 | 0 |
| 14 | 150 | 64 | 20 | 66 |
| total | 164 | 72 | 26 | 66 |

The 14 length-13 presentations are the following. The second column is the
round-2 label, and the third is the new status. **Computed.**

| presentation | round-2 label | new status |
| --- | --- | --- |
| `BABaba,BBBaBaa` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BABaba,BBBaaBa` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BABaba,BBaBaaa` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BABaba,BBaaaBa` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BAbABa,BBAAABA` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BAbABa,BBABAAA` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BAbABa,BBBAABA` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BAbABa,BBBABAA` | resisting-exhausted-cap17 | AC-trivial, cap 20 |
| `BAbABa,BBBAAAA` | resisting-budget-cap19 | AK(3)-equivalent |
| `BAbABa,BBBBAAA` | resisting-budget-cap19 | AK(3)-equivalent |
| `BBAbaa,BBBaabA` | resisting-budget-cap19 | AK(3)-equivalent |
| `BBAbaa,BBaaabA` | resisting-budget-cap19 | AK(3)-equivalent |
| `BBaabA,BBAbaaa` | resisting-budget-cap19 | AK(3)-equivalent |
| `BBaabA,BBBAbaa` | resisting-budget-cap19 | AK(3)-equivalent |

Letters follow `directions/c14`: a and A are x and x^-1, b and B are y and y^-1,
and `e` is the empty word. The eight rows that round 2 had exhausted and the six
that round 2 had stopped by a budget split into eight AC-trivial and six
AK(3)-equivalent, so the nine length-13 presentations that carried a bound
weaker than the published record are all decided now.

## 5. The 26 AK(3)-equivalences

A resister is AK(3)-equivalent when its pair lies in the class of one of the
79,680 cap-20 census classes of `directions/pu-enumeration`. The certificate is
built in three pieces, all checked by replay. **Verified.**

1. A short move list from the resister onto the census class representative.
   It cyclically reduces each relator, inverts it if the representative is the
   inverse, and rotates it to the representative. When the representative has
   the two relators in the other order, the certificate instead lands on that
   swapped representative and the next piece is reindexed. The start of every
   certificate in this direction is the resister exactly as `final_status.tsv`
   lists it, and no certificate starts from a swapped pair.
2. The reversed certificate of `cert20k1.txt.gz`, which runs from AK(3) to that
   representative. Reversing a restricted move list is exact: an inversion is
   its own inverse, a conjugation by a letter is undone by the opposite letter,
   and the inverse of `r_i -> r_i r_j` is `r_j -> r_j^-1`, `r_i -> r_i r_j`,
   `r_j -> r_j^-1`.
3. The pieces are concatenated and replayed from the resister to the relator
   pair of AK(3), with that pair read in the relator order of the census. The
   end pair must match exactly, and a swap of the relator order is notational.

The 26 certificates are in `ak3_hits_certs.txt`, one line per presentation in
the format `start|moves|end` of `directions/c14`. Their move counts run from 67
to 138. Every intermediate tuple has total relator length at most 20, which
`check_caps.py 20 ak3_hits_certs.txt` reports as the largest intermediate total
length. **Verified** by `replay_own.py` and by `directions/c14/replay14.py`,
with zero failures in both.

## 6. The 72 trivialisations

A resister is AC-trivial when its component at the chosen cap meets the ball of
the standard pair. The certificate is the frontier path from the resister to a
ball state followed by the reverse of a ball path from `(a,b)` to that state.
**Verified** by replay.

The exploration ran in seven rounds. The first two used the AK(3) class keys
alone, which decides the AK(3) side and is cheap in memory. Rounds three to
seven used both targets. Each round took the presentations that the round
before had left open. **Computed.**

| round | cap | pair budget | presentations | targets | decided | exhausted | budget stopped |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 20 | 6,000,000 | 164 | AK(3) keys | 26 AK(3) | 72 | 66 |
| 2 | 20 | 30,000,000 | 66 | AK(3) keys | 0 | 22 | 44 |
| 3 | 20 | 6,000,000 | 138 | both | 44 trivial | 72 | 22 |
| 4 | 20 | 30,000,000 | 22 | both | 0 | 22 | 0 |
| 5 | 21 | 30,000,000 | 72 | both | 20 trivial | 52 | 0 |
| 6 | 22 | 60,000,000 | 52 | both | 8 trivial | 44 | 0 |
| 7 | 23 | 100,000,000 | 11 of 52 | both | 0 | 6 | 4 |

Round 7 was stopped after 11 presentations because the process was killed by the
kernel while four other jobs on the same machine held about 10 GB. It also
re-ran the start list of round 6 instead of the list of the 44 that round 6 had
exhausted, so one presentation that round 6 had already decided was explored
again and decided again. That mistake changes no status: the four budget stops
of round 7 keep the cap-22 bound of round 6, and its six exhaustions carry the
cap-23 bound.

The 72 certificates are in `std_certs.txt` in the same format, with `std` as the
end field. Their move counts run from 73 to 184. The largest intermediate total
length is 19 for 5 of them, 20 for 39, 21 for 20 and 22 for 8, which
`check_caps.py 22 std_certs.txt` reports. **Verified** by `replay_own.py` and by
`directions/c14/replay14.py`, zero failures in both.

## 7. The 66 bounds

For a presentation whose component at cap `C` is explored to exhaustion and
contains neither `(a,b)` nor any tuple of the AK(3) cap-20 component, two
statements hold. **Argument**, from the exhaustion and the two target sets.

1. There is no AC-trivialisation in which every intermediate tuple has total
   relator length at most `C`. The pair `(a,b)` itself is a state of the target
   ball, so a path to it stays inside the component that was explored.
2. There is no AC-equivalence to AK(3) in which every intermediate tuple has
   total relator length at most `C`. AK(3) itself is a state of its cap-20
   component and so lies in the class key set.

Both statements are about the twelve restricted moves, in which a conjugation is
by one generator or its inverse. A certificate in the full move set is not
excluded by them.

The component sizes at the last cap explored are these. **Computed.**

| bound | presentations | component size, in states |
| --- | --- | --- |
| 20 | 22 | 21,349,360, one component for all 22 |
| 22 | 38 | 1,461,200 to 37,464,032 |
| 23 | 6 | 4,049,040 to 33,815,688 |

The 22 presentations of the cap-20 group lie in one component at cap 20, which
is disjoint from both targets at that cap.

### 7.1 The bounds do not depend on the conjugator bound

The twelve restricted moves conjugate a relator by one letter. A larger move set
was also run for every one of the 66, in which a conjugation may be by any
freely reduced word of length one or two, which makes 36 moves at each state.
For all 66 the component has exactly the same number of states as in the twelve
move runs, at the same cap, and contains no target. **Computed.**

| bound | presentations | component sizes with conjugators of length 1 | the same with length 2 |
| --- | --- | --- | --- |
| 20 | 22 | 21,349,360 | 21,349,360 |
| 22 | 38 | 1,461,200 to 37,464,032 | identical for every one |
| 23 | 6 | 4,049,040 to 33,815,688 | identical for every one |

The command is `./push search 20 30000000 work/k2_b20.txt work/ballstd_15.bin
work/ak3keys.bin results/b20.txt 2`, with `22` and `23` and the matching start
lists for the other two groups. The last argument selects the conjugator bound.
The raw outputs are `results/k2_b20.txt`, `results/k2_b22.txt`,
`results/k2_b22b.txt` and `results/k2_b23.txt`.

As a check on the extended engine, the AK(3) ball at cap 18 has 2,014,992 states
with conjugators of length 1 and with conjugators of length 2, which is the
K-invariance that `directions/pu-enumeration` reports at that cap. **Verified**
with `results/k2test_res.txt` and `results/k2test_res1.txt`.

## 8. Files and exact commands

Code in this directory, all deterministic.

| file | what it is |
| --- | --- |
| `reslib.py` | words, the twelve restricted moves, canonical class keys, move lists onto a representative, a certificate replay at the level of a module |
| `push.c` | the C engine, modes `build`, `search` and `paths` |
| `stageA.py` | the direct test of the 164 against the cap-20 AK(3) census, and self-tests of `reslib.py` |
| `mkkeys.py` | the class-key file of the census in the byte convention shared with `push.c` |
| `buildcerts.py` | the three-piece AK(3) certificates of Section 5, replayed before being written |
| `buildstd.py` | the trivialisation certificates of Section 6, replayed before being written |
| `replay_own.py` | a standalone certificate replayer with its own word arithmetic |
| `check_caps.py` | replays certificates and reports the largest intermediate total length |
| `drive.sh`, `mkrem.py` | the resumable driver of the rounds of Section 6 |
| `std_certs.txt` | 72 trivialisation certificates |
| `ak3_hits_certs.txt` | 26 AK(3)-equivalence certificates |
| `final_status.tsv` | one line per resister: length, pair, round-2 label, new status, cap |
| `results/` | the raw result files of every round, the start lists, the conjugator-bound runs of Section 7.1 and the validation transcripts |

Exact commands, from this directory, with `REPO` the repository root and a
scratch subdirectory `work/` created by `mkdir -p work`. The archived outputs of
my runs are in `results/`. **Verified** by running them.

```
mkdir -p work
gcc -O2 -o push push.c
python3 stageA.py REPO                       # 164 resisters against the census
python3 mkkeys.py REPO                       # work/ak3keys.bin, 39,840 keys
./push build 15 work/ballstd_15.bin a,b 59000000
                                             # 58,487,624 states, 2.4 GB peak
./push build 17 work/ballak3_17.bin abaBAB,aaaBBBB 900000
                                             # 857,808 states, reproduces pu.md
./push search 19 3000000 work/validate19_res.txt none none results/validate19.txt
STARTS=results/resisters.txt ./drive.sh 20 6000000 20
STARTS=results/resisters_budget.txt RESFILE=work/res20b30000000.txt \
  ./drive.sh 20 30000000 6
STARTS=results/resisters_left.txt TARGETS=work/ballstd_15.bin \
  RESFILE=work/resboth20.txt ./drive.sh 20 6000000 6
STARTS=results/resisters_budget22.txt TARGETS=work/ballstd_15.bin \
  RESFILE=work/resboth20b30M.txt ./drive.sh 20 30000000 6
STARTS=results/resisters_72.txt TARGETS=work/ballstd_15.bin \
  RESFILE=work/resboth21.txt ./drive.sh 21 30000000 6
STARTS=results/resisters_52.txt TARGETS=work/ballstd_15.bin \
  RESFILE=work/resboth22.txt ./drive.sh 22 60000000 6
STARTS=results/resisters_52.txt TARGETS=work/ballstd_15.bin \
  RESFILE=work/resboth23.txt ./drive.sh 23 100000000 3
./push paths 15 59000000 work/allhit_paths.txt a,b results/allhit_targets.txt
python3 buildstd.py work/resboth20.txt,work/resboth21.txt,work/resboth22.txt,work/resboth23.txt \
  work/allhit_paths.txt work/std_certs.txt
python3 buildcerts.py REPO                   # reads work/res20b6000000.txt
python3 replay_own.py work/std_certs.txt work/ak3_hits_certs.txt
python3 check_caps.py 22 work/std_certs.txt work/ak3_hits_certs.txt
python3 directions/c14/replay14.py work/std_certs.txt
python3 directions/c14/replay14.py work/ak3_hits_certs.txt
```

The start lists in `results/` are `name<TAB>pair` lines derived from
`directions/c14/final_classes.txt` by the following filter, which is the one I
ran.

```
python3 - <<'F'
REPO = '/path/to/repo'
out = open('results/resisters.txt', 'w')
for line in open(REPO + '/directions/c14/final_classes.txt'):
    lv, kind, t = [x.strip() for x in line.split('|')]
    if kind.startswith('resisting'):
        out.write('L%d_%s_%s\t%s\n' % (int(lv), kind.replace('resisting-', ''), t, t))
F
```

The subsets of that list used by each round are in the same directory.

## 9. What is not claimed

1. No claim is made that any of the 66 undecided presentations is nontrivial, or
   that it is not AC-trivial. Each carries a bound, and a larger cap could
   decide it.
2. The bounds are bounds for a cap on the total relator length of an
   intermediate tuple, and they hold for conjugators of length at most two by
   Section 7.1. A trivialisation that needs a longer conjugator, or a longer
   intermediate tuple, is outside them.
3. The AK(3) side of the target is the cap-20 component of AK(3). A path from a
   resister to AK(3) that leaves the cap-20 box on the AK(3) side is outside the
   test, and the AK(3) half of the bounds is therefore a bound for paths that
   meet that component.
4. Nothing here bears on the Andrews-Curtis conjecture. The presentations are
   presentations of the trivial group by the Todd-Coxeter runs of
   `directions/c14`, and the question for each of them is whether an AC path to
   `(a,b)` exists.
5. Round 7 was stopped by the kernel after 11 starts. Its six exhaustions and
   four budget stops are reported as they stand, and the other 33 presentations
   of the round-6 list keep the cap-22 bound.

## 10. Sources and credit

The 164 presentations, their round-2 labels and the certificate format are from
`directions/c14/c14.md` and `directions/c14/final_classes.txt` (round 2, member
m4). The AK(3) cap-20 census and its 79,680 certificates are from
`directions/pu-enumeration` (round 2, member m5). The classification of the
length-13 and length-14 lists is from the same two directions. The length-13
statement about the published record is in `directions/c14/c14.md` Section 6 and
comes from G. Havas and C. Ramsay, "Breadth-first search and the
Andrews-Curtis conjecture", International Journal of Algebra and Computation 13
(2003), 61-68, DOI 10.1142/S0218196703001365. I did not re-read that paper in
this round, and no bound above depends on it. **Reported.**
