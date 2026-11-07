# The resisters at caps 23 and 24, a class-key target, and no new falls

Round 4 direction G1, member m1. This file continues `resisters.md` (round 3,
member m7) and covers the 66 presentations that round 3 left undecided at total
relator length 14. Every substantive claim is labelled **Verified**,
**Computed**, **Argument** or **Reported**. Nothing here is a claim about the
truth or the falsehood of the Andrews-Curtis conjecture.

## 0. Summary

All 66 undecided presentations were pushed to a larger cap, and the negative
side of the ledger improved. **Computed**, with the exact commands of Section 9.

| round-3 bound | presentations | round-4 bound | component states at that bound | deeper exploration |
| --- | --- | --- | --- | --- |
| 20 | 22 | 22 | 176,714,288 (one component, all 22 in it) | cap 23 stopped at 420,000,001 states |
| 22 or 23 | 24 | 25 | 24,781,832, 38,286,952, 43,383,880 or 50,227,344, one component each | none |
| 22 or 23 | 20 | 24 | 67,181,488, 300,941,152 or 375,482,496, one component each | one cap-25 stop at 250,000,001 states |

No presentation fell: no component met the standard class or the AK(3) class.
The target against which every run was made is stronger than the round-3 target:
it is the 452,593 conjugacy-class keys of two standard balls and of the cap-20
AK(3) census, and it contains the round-3 target of 58,487,624 exact states as a
special case (Section 3).
Twenty-four presentations carry a bound of 25, twenty carry 24, and twenty-two
carry 22. One cap-25 run and one cap-23 run were stopped by their own budgets.
The per-presentation table is `final_status_round4.tsv`.

## 1. What round 3 left

Round 3 decided 98 of the 164 resisters and left 66 undecided, all at total
relator length 14. **Reported** from `resisters.md` and checked against
`final_status.tsv`: 22 had no trivialisation and no AK(3)-equivalence with
intermediates of total length at most 20, 38 at most 22, and 6 at most 23. The
targets of those runs were the exact ball of the standard pair at cap 15
(58,487,624 states) and the class keys of the cap-20 AK(3) census
(39,840 keys). Every bound is for the twelve restricted moves, in which a
conjugation is by one letter.

## 2. The engine and what validates it

`acx.c` is a new explorer written from the same twelve-move definitions as
`push.c`. A state is a single 64-bit word (two 6-bit lengths, then two bits per
letter) instead of a variable-length byte record, so a state costs about 16
bytes instead of 54 and the cap-23 run that the kernel killed at 4.7 GB fits in
about 2 GB. The engine was written first, and the class key was then made to
agree with `push.c` exactly.

Agreement with numbers computed by other implementations. **Verified**, by
rerunning each command of Section 9.

| quantity | `acx` | reference |
| --- | --- | --- |
| standard ball, cap 11 | 700,712 | `directions/c14/c14.md` |
| standard ball, cap 13 | 6,476,104 | `directions/c14/c14.md` |
| standard ball, cap 15 | 58,487,624 | `resisters.md` Section 3 |
| AK(3) ball, cap 17 | 857,808 | `directions/pu-enumeration/pu.md` |
| AK(3) component, cap 20 | 51,411,456 | `directions/pu-enumeration/pu.md` |
| AK(3) component, cap 20, distinct class keys | 39,840, all in `ak3keys.bin`, which has 39,840 | `directions/pu-enumeration`, `mkkeys.py` |
| the 22-group, cap 20 | 21,349,360 | `resisters.md` Section 7 |
| `BBBAAbA,BABabAA`, cap 23 | 4,049,040 | round-3 `resboth23.txt` |
| `BBAAbba,BABAbaa`, cap 23 | 33,815,688 | round-3 `resboth23.txt` |

The class-key agreement is the strongest of these: it matches all 39,840 keys
of the cap-20 census as a set, with zero keys outside it and zero census keys
missed, so the move set and the canonical form of `acx` agree with the round-2
`pu-enumeration` conventions. `push.c` was then compiled unchanged and made to
reproduce four of the new state counts (4,049,040 at cap 23, and 9,432,136,
15,886,528 and 67,181,488 at cap 24). **Verified** with
`crosscheck_push.txt`.

The negatives themselves were also confirmed by the second implementation. The
452,593 keys were re-encoded in the byte format that `push.c` reads, and
`push.c search 24 ... none target_push.bin ...` reports
`EXHAUSTED | 24 | BBAABBa,BAbABaa | 17638096` and
`EXHAUSTED | 24 | BBAAbaa,BBabAbA | 67181488`, the same two counts and the same
absence of a hit as `acx` reports with the same target. **Verified** with
`crosscheck_push.txt` and the command of Section 9. This matters because a
negative is a statement about a whole component, and two independent engines now
agree on two of the largest of them with the full target loaded.

## 3. The target: conjugacy-class keys instead of exact states

A class key of a pair of relators is computed as follows. Reduce each relator
cyclically, take the least rotation of the word or of its inverse in the
alphabet order B < A < a < b, then sort the two words by length and bytes. This
is the key of `directions/resisters/push.c` and of `directions/pu-enumeration`.
Two pairs with the same key are related by conjugation of each relator, by
inversion, and by a swap of the two relators.

Lemma. From any state there is a path in the twelve restricted moves to its
canonical representative whose total relator length never increases.
**Argument**, with a machine check of the move sequence.

1. If a relator begins with the inverse of its last letter, conjugating it by
   its last letter deletes both letters. The conjugated word is freely reduced
   inside the move, so the state after the move is shorter.
2. A rotation of a cyclically reduced word by one place is the conjugation by
   its last letter, and it preserves the length.
3. Inversion is a move and preserves the length.
4. `classbfs.c` builds this move sequence, and its `canontest` mode checks on a
   list of pairs that the class key is preserved and that the procedure is
   idempotent. **Verified** by rerunning the command of Section 9.

Consequence. If a bounded exploration reaches a state whose class key is one of
the keys of a ball B, then the state can be carried to its representative
without leaving the box, and that representative is itself a state of B. So a
key hit is exactly as good as an exact-state hit, and the key set of a ball is
strictly stronger than the ball: it also catches conjugates of ball states that
lie at a larger total length. It also costs almost nothing in memory.

The target used for every run of this report is the class keys of the standard
ball at cap 16 joined with the AK(3) census keys, 452,593 keys and 3.6 MB.
**Computed**: the class keys of the standard ball at cap 15 number 185,713 and
are a subset of the 412,753 keys of the standard ball at cap 16, which adds
227,040 keys; the 39,840 AK(3) keys are disjoint from both.

## 4. The runs

The standard ball at cap 16 was built once and turned into keys. **Computed**:
129,247,304 states, twelve moves, no conjugator enlargement, 4 min 14 s and
2.3 GB peak; the key extraction took 63 s and 1.0 GB.

Each run is `acx search CAP BUDGET RESFILE TARGETS CLASSKEYS STARTLIST -1
MEMBERS` with `TARGETS` empty (the key set subsumes it) and `CLASSKEYS` the
452,593-key file. The argument `-1` selects the twelve restricted moves with no
parent array, and the trailing file lists all 66 pairs so that every run also
reports which of the 66 lie in the component it explored. A run with no hit and
no budget stop is an exhaustion, and its state count is the size of the whole
component inside the box.

| group | presentations | cap | verdict | component states |
| --- | --- | --- | --- | --- |
| the 22-group | 22 | 21 | exhausted | 87,981,744 |
| the 22-group | 22 | 22 | exhausted | 176,714,288 |
| the 22-group | 22 | 23 | budget stop | 420,000,001 reached |
| `BBBAbba,BAAAbaa` group | 4 | 23 | exhausted | 125,539,616 |
| same group | 4 | 24 | exhausted | 300,941,152 |
| `BBBAbbA,BAAAbaa` group | 8 | 23 | exhausted | 158,016,512 |
| same group | 8 | 24 | exhausted | 375,482,496 |
| 32 single components | 32 | 23 | exhausted | 4,049,040 to 33,815,688 |
| the same 32 | 32 | 24 | exhausted | 9,432,136 to 67,181,488 |
| 24 of the same 32 | 24 | 25 | exhausted | 24,781,832 to 50,227,344 |
| 8 of the same 32 | 8 | 25 | budget stop | 250,000,001 reached |

The 66 split into 35 components inside the boxes used here. The 22-group is one
component at cap 22 with all 22 members. Twelve presentations, the ones whose
cap-23 components have 125,539,616 and 158,016,512 states, form two components
of 4 and 8. The other 32 each lie in a component of their own, and the sizes of
those components fall into five values that repeat, and the membership test
reports one member for each, so the repeated sizes belong to isomorphic copies
of one component shape. **Computed**, from the `MEMBER` lines of the runs.

The 24 presentations that reach cap 25 split into 8 with component 24,781,832
states at cap 25, 8 with 38,286,952, 4 with 43,383,880 and 4 with 50,227,344,
and each of the 24 is again in a component of its own. The remaining 8 of the
32, whose cap-24 components have 67,181,488 states, were probed once at cap 25:
the probe was stopped by a budget of 250,000,000 states, so those 8 keep the
cap-24 bound. A component of 67,181,488 states at cap 24 growing past
250,000,001 states at cap 25 is consistent with the factor of about 2.6 that the
other components show between those two caps.

## 5. The conjugator bound: the in-box reachable set is the same for every K

Let the K-family of moves be the following three kinds: invert a relator,
multiply relator 0 by relator 1 on the right and relator 1 by relator 0 on the
right, and conjugate a relator by a freely reduced word of length at most K.
This is the family that `acx.c` implements through its K argument, and K = 1 is
the twelve restricted moves of `resisters.md`. The claim is that inside a box of
total relator length at most C the reachable set is the same for every K, so the
hit outcome is the same for every K and for every target, exact states or class
keys alike.

**Argument.** It is enough to show that a conjugation of a relator r by a word w
of length at least two can be replaced by steps of the K = 1 family that stay in
the box. Let s = (r, q) and t = (w r w^{-1}, q) both have total length at most C.
Section 3 gives a twelve-move path from any state to its canonical
representative whose total length never increases, so s reaches c(s) inside the
box of s and t reaches c(t) inside the box of t. The cyclic reduction of the freely reduced
word w r w^{-1} is a rotation of the cyclic reduction of r, and the canonical form of
a relator is the least rotation of that cyclic reduction over the word and over
its inverse, so the two canonical forms agree as ordered pairs: c(t) = c(s).
Running the path from t to c(t) backwards gives a twelve-move path from c(s) to
t, and its states are the states of that path in the reverse order, so their
total lengths are at most |t|. The composite path from s to c(s) to t therefore
carries s to t by twelve-move steps with every intermediate of total length at
most the larger of |s| and |t|, hence at most C. Replacing each such step of a
K-path in turn gives a twelve-move path in the same box, so the two reachable
sets are equal. In particular no conjugation by a longer word can produce a
state, or a class, that the twelve-move search inside the same box does not
already have.

**Computed, as a check of the theorem.** The engine was extended to conjugators
of length up to three, so 108 moves at each state, and six components were
re-explored at their bound caps. Every count is identical to the count with
letter conjugators only, as the theorem requires.

| component | cap | states with K = 1 | states with K = 3 |
| --- | --- | --- | --- |
| the 22-group | 20 | 21,349,360 | 21,349,360 |
| `BBBAAbA,BABabAA` | 23 | 4,049,040 | 4,049,040 |
| `BBBAAbA,BABabAA` | 24 | 9,432,136 | 9,432,136 |
| `BBAAbaa,BBaBabA` | 24 | 13,027,552 | 13,027,552 |
| `BBBAbbA,BAAAABa` | 24 | 15,886,528 | 15,886,528 |
| `BBAABBa,BAbABaa` | 24 | 17,638,096 | 17,638,096 |

Round 3 found the same identity for K = 2 at all 66 presentations. The theorem
above covers every K at once, so those two computations are a check on the
engine and on the theorem, and they are no longer the only support for the
conclusion.

One instance of the replacement, checked by an independent replayer with its own
parser and its own free reduction. Start from the pair `abab,ab` and conjugate
its first relator by the word `bb`, which gives `bbabaB,ab` at total length 8.
The twelve-move search at cap 8 reaches that state in two moves, `c0A` and then
`c0b`, with the total lengths 6, 6 and 8 along the way, so every intermediate is
inside the cap. The commands are in Section 9 and the transcript is
`theorem_step_check.txt`.

## 6. A recorded dead end: the class-quotient exploration

The obvious way to make a deeper cap cheap is to search on classes instead of
states. `classbfs.c` does this: a node is a class key, and the edges are the
twelve moves applied to the canonical representative followed by
canonicalisation. **Computed and refuted.** From the class of AK(3) at cap 20,
the quotient graph reaches three classes, while the state component at the same
cap has 39,840 classes. The reason is exact: within one class the states that
matter are not only the rotations of the canonical relators, but also every
longer conjugate that still fits in the box, and the products taken from two
different conjugates of the same class land in different classes. A quotient
that keeps only the canonical representative therefore loses almost everything.
The repair is to keep every conjugate inside the box at each class, which is
exactly as many objects as the state graph has, so the quotient buys nothing.
This is recorded so that the next round does not repeat it.

## 7. Memory

The state costs about 16 bytes with parents and about 13 without, against about
54 with `push.c`. The largest run of this report is the 420,000,001-state cap-23
budget stop, which used 5.4 GB and 8 minutes. The two largest exhaustions,
300,941,152 and 375,482,496 states, used 4.0 GB and 5.0 GB and took 5.5 and 7
minutes. The target costs 3.6 MB. No run of this report was killed by the
kernel, and one cap-23 run of the 22-group was stopped by its own budget.

## 8. What is not claimed

1. No presentation of this list is claimed trivial or nontrivial. Each carries a
   bound, and a larger cap could decide it.
2. The bounds are for the twelve-move family, and Section 5 proves that
   enlarging its conjugator bound changes nothing at any cap. The gap that
   remains is the other two multiplication forms of the full Andrews-Curtis move
   set, namely left multiplication and multiplication by an inverse relator. The
   twelve-move family reaches both, but only through intermediate tuples that can
   be longer than the two endpoints, so a path that uses them inside the box is
   not excluded by these bounds.
3. The standard side of the target is the exact ball at cap 16 and the AK(3)
   side is the cap-20 census. A path from a resister to AK(3) that needs a state
   outside the cap-20 AK(3) component is outside the test.
4. The state counts are counts of states, not of classes, and they are computed,
   not derived.
5. Round 3's cap-23 run of eleven presentations was stopped by the kernel. Its
   six exhaustions and four budget stops are unchanged by this report, and the
   four budget stops are now superseded by the cap-24 exhaustions of Section 4.

## 9. Files and exact commands

Files of this direction in `directions/resisters/round4/`.

| file | what it is |
| --- | --- |
| `acx.c` | the engine, modes `conv`, `convkeys`, `keytest`, `filekeys`, `build`, `search`, `paths`, `count` |
| `classbfs.c` | the class-quotient explorer and the canonicalisation with explicit moves, modes `classcount`, `classbfs`, `canontest` |
| `std15keys.u64`, `std16keys.u64` | class keys of the standard balls at caps 15 and 16 |
| `ak3keys.u64` | class keys of the cap-20 AK(3) census in the same encoding |
| `target.u64` | the two joined, 452,593 keys |
| `r4_*.txt`, `log_*.log` | the raw outputs of every run, one line per start, with the membership report |
| `final_status_round4.tsv` | the updated per-presentation table |
| `crosscheck_push.txt` | the `push.c` reruns of four counts, and the two class-key reruns |
| `theorem_step_check.py`, `theorem_step_check.txt` | the independent replay of the replacement step of Section 5, and its transcript |
| `run_all.sh` | every command of this section |

Exact commands, from `directions/resisters/round4/`, with a scratch directory
`w/`. **Verified** by running them.

```
gcc -O2 -o acx acx.c ; gcc -O2 -o push ../push.c ; gcc -O2 -o classbfs classbfs.c
./acx build 16 a,b 260000000 w/ballstd16.u64     # 129,247,304 states, 4m14s, 2.3 GB
./acx filekeys w/ballstd16.u64 std16keys.u64     # 412,753 keys
./acx filekeys w/ballstd15.u64 std15keys.u64     # 185,713 keys, ballstd15.u64 from round 3
./acx convkeys ak3keys.bin ak3keys.u64           # 39,840 keys
cat std16keys.u64 ak3keys.u64 > target.u64
./acx search 22 400000000 w/r22.txt none target.u64 w/one20.txt -1 w/all66.txt
./acx search 23 420000000 w/r23.txt none target.u64 w/one20.txt -1 w/all66.txt
./acx search 23 200000000 w/rc23.txt none target.u64 w/chunk.txt -1 w/all66.txt
./acx search 24 400000000 w/rc24.txt none target.u64 w/chunk.txt -1 w/all66.txt
./acx search 25 250000000 w/rc25.txt none target.u64 w/chunk.txt -1 w/all66.txt
./acx search 23 20000000 w/k3.txt none none w/t1.txt 3      # K = 3
./push search 24 70000000 w/x.txt none none w/t3.txt        # cross-check
./push search 24 80000000 w/x2.txt none target_push.bin w/t3.txt   # class-key cross-check
./classbfs canontest ABAbbab,BBBBaaa ab,ab ba,ab
./classbfs classcount 20 100000 abaBAB,aaaBBBB             # 3 classes, the dead end of Section 7
./acx count 20 abaBAB,aaaBBBB 1                            # 51,411,456 states
printf 't\tbbabaB,ab\n' > w/wt.txt
./acx paths 8 200000 abab,ab w/wt.txt w/wt_out.txt         # the replacement step of Section 5
python3 theorem_step_check.py                              # independent replay, own parser
```

The file `target_push.bin` is `target.u64` re-encoded in the byte format that
`push.c` reads, namely the record `[n1][bytes of relator 1][n2][bytes of
relator 2]` with the letter map a = 3, A = 2, b = 4, B = 1. The converter is ten
lines of Python and is part of `run_all.sh`.

The start lists are the 66 pairs of `final_status.tsv` split by round-3 bound;
they are `all66.txt`, `und20.txt`, `und22.txt` and `und23.txt` in the same
directory. `one20.txt` holds the first line of `und20.txt`, and the membership
report of that single run is what certifies that all 22 lie in the one component
exhausted at cap 22.

## 10. Sources and credit

The 66 presentations, their round-3 bounds and the twelve-move engine are from
`directions/resisters/` (round 3, member m7) and `directions/c14/` (round 2,
member m4). The cap-20 AK(3) census and the class-key convention are from
`directions/pu-enumeration/` (round 2, member m5). No literature claim is made
in this file and no published bound is used.
