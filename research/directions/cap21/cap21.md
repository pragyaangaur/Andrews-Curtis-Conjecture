# The cap-21 census of the AK(3) class: disk-backed enumeration, class C, and the residual deficit

Round 4, direction G3. Every number below comes from a deterministic computation
with the exact command given. Nothing here says anything about the truth or the
falsehood of the Andrews-Curtis conjecture, and no claim of a proof or a disproof
of it is made. Claims are labelled [Computed], [Argument], [Source] or [Open].

## 1. Summary

1. [Computed] The AK(3) class inside the total-length-21 box is complete. It
   holds 219,042,976 tuples, which fall into 144,292 classes under conjugation
   and inversion of the relators and into 10,884 classes under the
   Panteleev-Ushakov relation of their Section 4.2. The traversal ends at depth
   167, peaks at 298 MB of resident memory and takes 1983 s. Round 3 recorded
   the opposite outcome for the same cap: killed at 200,608,294 states and
   4.7 GB.
2. [Computed] Every cap-20 class is a cap-21 class. The class count grows from
   39,840 to 144,292 and the PU class count from 2,967 to 10,884.
3. [Computed] Class C is not in the cap-21 box. The box has exactly two PU
   classes of minimal total length 13, the same two as at cap 20, and they are
   the classes A and B of directions/pu-enumeration/pu.md Section 7. The eight
   class-C presentations are absent at the level of conjugation classes (0 of 8)
   and at the level of PU classes (0 of 8 canonical forms). So every AC path
   from AK(3) to class C has an intermediate pair of total length at least 22.
4. [Computed] Under a reimplemented per-relator normal form the residual PU
   deficit at T = 16 to 20 is 3, 23, 49, 404 and 454 classes at cap 20 and 3,
   20, 38, 253 and 290 classes at cap 21. The part of the deficit at T = 17 to
   20 shrinks when the box grows. The part at T = 16 does not move, so those
   three classes need an intermediate pair of total length at least 22.
5. [Computed] The reimplementation reproduces the reference PU class counts at
   cap 20 exactly (2, 5, 35, 40, 206, 246, 1209, 1224 by minimal length;
   cumulative 2, 7, 42, 82, 288, 534, 1743, 2967) and passes a 300-test
   invariance check with 0 failures.
6. [Computed, correction] The normal form of class C printed in
   directions/pu-gap/pu-gap.md Section 4 is one letter short in its first
   relator. The eight class-C presentations normalise to
   (x^3 y x y^2, x y x^-1 y x y^-1). That is what pu-gap's own log prints
   (`xxxyxyy,xyXyxY`, logs/checks13.log lines 10 to 18) and what both normal
   form implementations return. The printed pair (x^2 y x y^2, x y x^-1 y x y^-1)
   has total length 12 and lies in a different PU class, whose own canonical
   form is (x^3 y x y^2, x y^2 x^-1 y).
7. [Computed] The same enumerator was run at T = 22 as well. Section 11 records
   419,826,272 states, 258,032 conjugation classes and 20,111 PU classes. Class
   C is still absent, so the bound on the intermediates of any path to it rises
   to 23, and the residual deficit at T = 16 remains exactly 3 classes.
8. [Computed] The enumerator was run at T = 23 as well. Section 12 records
   1,638,542,144 states at depth 326, 891,748 conjugation classes and 71,572 PU
   classes. The deficit at T = 16 closes exactly at cap 23: the box reaches PU
   classes of minimal length 16 in the number 43 that the halved published cell
   gives. The three classes it adds were absent at cap 22, so they need an
   intermediate pair of total length at least 22. Class C is still absent, so
   the bound on the intermediates of any path to it rises to 24.

## 2. The object, the box and the move set

Let F = F(x,y) and let a presentation be a pair (u,v) of freely reduced words.
AK(3) is the pair (x y x y^-1 x^-1 y^-1, x^3 y^-4) of total length 13. The moves
are the three Andrews-Curtis moves: invert one relator, multiply one relator by
the other on the left or the right, and conjugate one relator by a word w. A
tuple is in the box B(T) when |u| + |v| is at most T. The enumerator walks the
finite graph whose vertices are the tuples of B(T) reachable from AK(3) and
whose edges are the moves that stay in the box, with conjugating words of length
at most K. This is the same object as in directions/pu-enumeration/pu.md
Section 2 and directions/pu-gap/pu-gap.md Section 2, so the numbers are directly
comparable with the round-2 and round-3 tables.

The run reported here uses T = 21 and K = 1. The conjugator bound is not the
binding constraint in this range: round 2 and round 3 verified that K = 1, K = 2
and K = 3 give the same vertex set and the same class set at caps 13 to 20, and
round 3 verified that the K = 2 rerun leaves every resister component unchanged.
That was not re-verified at cap 21, which Section 9 records as a gap.

## 3. The memory plan

The round-3 failure was a memory failure, so the design here removes the visited
set from memory. Nothing in the run is proportional to the number of states
except the 8-byte state key of the current frontier. [Computed, by the peak RSS
of the run: 298,208 KB]

1. The visited set lives in a sorted file of 8-byte keys on disk.
2. The search is breadth first by layer. Layer d is a sorted, deduplicated file
   of the states at distance exactly d from AK(3).
3. Expanding a layer goes into one fixed 128 MB buffer. When the buffer fills,
   it is radix sorted in place, deduplicated, and written as one sorted chunk
   file. Peak memory is the buffer, its sort scratch space and the frontier
   array, which is at most a few hundred MB.
4. The chunk files are merged with a k-way merge, and the result is anti-joined
   against the visited file. Both files are sorted, so the anti-join is one
   streaming pass that writes the new layer and the new visited file. Each level
   also checks the invariant |visited| = 1 + sum of the layer sizes and prints a
   warning when it fails; the cap-21 run printed no warning at any of the 167
   levels.
5. The class pass reads the visited file once and canonicalises each state. It
   uses a hash table whose size depends on the number of classes (144,292), not
   on the number of states.

The disk holds 1.75 GB of visited states and 6.6 MB of class list for this run.
Disk was not a constraint: 222 GB were free.

## 4. Completeness, soundness and validation

[Computed] Soundness holds by construction: every state is produced from a state
of the previous layer by one of the three moves, and the box test is applied at
every step. Completeness inside the box holds because the search is a breadth
first traversal of the connected component of AK(3) in a finite graph, so it
visits every reachable tuple before the frontier empties. The run prints
`depth 167: empty frontier, BFS finished`.

The enumerator is new code, written from the definitions for this direction, so
it was validated against the two existing implementations:

| cap | states (rawbox4) | states (rawbox2) | classes (rawbox4) | classes (rawbox2) |
|-----|-----------------:|-----------------:|------------------:|------------------:|
| 15  | 6,864            | 6,864            | 26                | 26                |
| 17  | 857,808          | 857,808          | 1,000             | 1,000             |
| 18  | 2,014,992        | 2,014,992        | 2,128             | 2,128             |
| 20  | 51,411,456       | 51,411,456       | 39,840            | 39,840            |

At cap 20 the whole class list is identical to `directions/pu-gap/run/cls2_20.txt`
as a set of canonical pairs: 39,840 lines on both sides, 0 lines only in one of
them. The per-length state histogram also agrees with the round-3
`rawbox2` table line for line (13:4032 14:15424 15:241856 16:336288 17:2520832
18:3280096 19:20185152 20:24827776). Three further checks apply to the cap-21
result itself: every cap-20 class is a cap-21 class (set inclusion of 39,840 in
144,292); every one of the 144,292 classes has an exponent-sum matrix of
determinant plus or minus one, which is the AC invariant; and the twelve
cap-21 classes of total length 13 are exactly the twelve rows that
directions/c14/final_classes.txt labels `ak3-equivalent` (6) and
`resisting-budget-cap19` (6).

## 5. The cap-21 tables

States and classes by total length. "classes" counts unordered pairs of
conjugacy classes of relators, which is the conjugation-and-inversion quotient;
it is the quantity `rawbox2` reports and it is half of the ordered count that
round 2's `rawbox` reported.

| T  | states, cap 20 | states, cap 21 | classes, cap 20 | classes, cap 21 |
|----|---------------:|---------------:|----------------:|----------------:|
| 13 | 4,032          | 4,032          | 12              | 12              |
| 14 | 15,424         | 15,424         | 40              | 40              |
| 15 | 241,856        | 255,808        | 516             | 548             |
| 16 | 336,288        | 344,352        | 556             | 572             |
| 17 | 2,520,832      | 2,720,000      | 2,844           | 3,108           |
| 18 | 3,280,096      | 3,476,096      | 3,228           | 3,488           |
| 19 | 20,185,152     | 22,343,488     | 15,620          | 17,688          |
| 20 | 24,827,776     | 26,951,360     | 17,024          | 18,792          |
| 21 |                | 162,932,416    |                 | 100,044         |
|    | **51,411,456** | **219,042,976**| **39,840**      | **144,292**     |

The cap-21 box is 4.26 times the cap-20 box in states and 3.62 times in classes.
The length-13 and length-14 strata do not grow at all between the two caps,
which is consistent with class C being out of reach at both.

PU classes by minimal total length, from the reimplemented normal form of
Section 7:

| minimal length | 13 | 14 | 15 | 16 | 17  | 18  | 19   | 20   | 21   |
|----------------|---:|---:|---:|---:|---:|----:|-----:|-----:|-----:|
| cap 20         | 2  | 5  | 35 | 40 | 206 | 246 | 1209 | 1224 |      |
| cap 21         | 2  | 5  | 35 | 40 | 209 | 257 | 1360 | 1388 | 7588 |
| cumulative 21  | 2  | 7  | 42 | 82 | 291 | 548 | 1908 | 3296 | 10884|

## 6. Class C is not in the cap-21 box

[Computed] Class C is the third PU class of total length 13. Its eight
presentations are the eight rows that directions/c14/final_classes.txt labels
`resisting-exhausted-cap17` at length 13: BAbABa,BBBABAA; BAbABa,BBBAABA;
BAbABa,BBABAAA; BAbABa,BBAAABA; BABaba,BBaaaBa; BABaba,BBaBaaa;
BABaba,BBBaaBa; BABaba,BBBaBaa. Two tests were run, and both are negative.

1. Conjugation level. The eight rows form two conjugation classes. Neither
   canonical pair occurs in the 144,292-class list of the cap-21 census, and the
   census has exactly 12 classes of total length 13, the same 12 as at cap 20.

   [Coordinator note, 5 November 2026, from the round-5 second-referees-4 audit
   (directions/second-referees-4/), rerun and confirmed: the sentence above is
   wrong on the count. Under this file's own Section 5 definition the eight rows
   form EIGHT distinct conjugation classes (the audit's eight canonical pairs
   are pairwise distinct), which collapse to one class at the PU level, as item
   2 below records. The test itself is unaffected, because checkC.py tests all
   eight keys.]
2. PU level. All eight rows have the single canonical form
   (x^3 y x y^2, x y x^-1 y x y^-1). That form is not in the 10,884-class
   cap-21 PU list. The only PU classes of minimal length 13 in the box are A and
   B, and their canonical forms, identical at caps 20 and 21, are
   (x^4 y^3, x y x^-1 y x y^-1) and (x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y).

[Computed] A third test gives the same answer without using any normal form: the
eight presentations themselves, in both relator orders, are absent from the
1.75 GB visited state file (0 of 16 keys found by binary search over the sorted
file). That test is the weaker one, since a conjugate of a class-C presentation
could in principle be in the box while the presentation itself is not, and the
class-level tests rule that out.

[Computed, bounded negative] Therefore no member of PU class C is reached by
paths whose intermediate pairs all have total length at most 21. Any AC path
from AK(3) to class C needs an intermediate pair of total length at least 22.
This strengthens the round-3 statement, which had the same conclusion with 20 in
place of 21. Nothing here decides whether class C is AK(3)-equivalent, and
directions/pu-gap/pu-gap.md predicts that it is not.

## 7. The residual Panteleev-Ushakov deficit under a reimplemented normal form

[Computed] `punf.py` is an independent implementation of the relation of
Panteleev and Ushakov's Section 4.2 as directions/pu-enumeration/pu.md describes
it: swap the two relators, invert one relator, conjugate one relator, and apply
an automorphism of F(x,y). A state is the unordered pair of cyclic-least forms
of the relators. The search takes every elementary automorphism image whose
total length does not increase, breadth first, and the canonical form is the
lexicographically least state among those of least total length. The automorphism
list has 16 elementary maps, including the Nielsen generators and their
inverses and the swap with and without inversions.

[Computed] On the cap-20 class list the reimplementation returns 2,967 distinct
canonical forms with the minimal-length distribution 2, 5, 35, 40, 206, 246,
1209, 1224 for minimal lengths 13 to 20. That is exactly the round-2 and round-3
reference result, including the cumulative sequence 2, 7, 42, 82, 288, 534,
1743, 2967, so the normal form agrees with the published implementation on all
39,840 inputs. A self-test applies random automorphism products to 60 sampled
cap-21 classes, 5 trials each, and recomputes the canonical form: 300 tests, 0
failures. That test matters because round 3's order-sensitive quotient failed
its own invariance test on 172 of 200 samples.

The comparison with Table 1 of arXiv:1609.00325. The cells of that table count
pairs of total length exactly T under the relator-order convention, as round 3
established from the LaTeX of Section 6.1 and as the non-monotone L = 10 column
confirms. Halving the column L = 17 to 20 gives the class counts that are
comparable with ours. The residual deficit is the difference.

| T  | 13 | 14 | 15 | 16 | 17  | 18  | 19   | 20   |
|----|----|----|----|----|-----|-----|------|------|
| their cells, L = 17 to 20 | 4 | 10 | 70 | 86 | 458 | 590 | 3226 | 3356 |
| halved                    | 2 | 5  | 35 | 43 | 229 | 295 | 1613 | 1678 |
| ours, cap 20              | 2 | 5  | 35 | 40 | 206 | 246 | 1209 | 1224 |
| deficit at cap 20         | 0 | 0  | 0  | 3  | 23  | 49  | 404  | 454  |
| ours, cap 21              | 2 | 5  | 35 | 40 | 209 | 257 | 1360 | 1388 |
| deficit at cap 21         | 0 | 0  | 0  | 3  | 20  | 38  | 253  | 290  |

[Computed] The cap-20 row of deficits is 0, 0, 0, 3, 23, 49, 404, 454, which is
the figure recorded in rounds/round-03.md Section 3 and in
directions/pu-gap/pu-gap.md Section 7, so the reimplementation reproduces the
residual that the earlier rounds could not explain. [Argument] The cap-21 row
shows the deficit shrinking at T = 17, 18, 19 and 20 as the box grows, and it
shows the deficit at T = 16 unchanged. Two readings follow. The shrinking part
is a property of the box: classes of total length T that our cap-20 box could
not reach are reached once intermediates of total length 21 are allowed. The
part that stays at T = 16 needs intermediates of total length at least 22, so it
cannot be closed by any box smaller than 22. [Open] The rest of the deficit is
not attributed: a larger box and the ACM-move set that Panteleev and Ushakov use
are both candidates, and this run separates neither from the other.

[Computed] One consequence for the deficit arithmetic. If the halved cells are a
class count, their cumulative values are 2, 7, 42, 85, 314, 609, 2222 and 3900
for T = 13 to 20, against our cap-21 cumulative values 2, 7, 42, 82, 291, 548,
1908 and 3296. The cumulative deficit is then 0, 0, 0, 3, 23, 61, 314 and 604.
The gap therefore grows with T even after the box has grown, which is expected:
the number of classes needing longer intermediates grows with the length of the
class.

## 8. What is not established

1. No per-class certificates are produced at cap 21. The disk-backed enumerator
   does not store parent pointers, so the cap-21 census is a reachable set
   computed by construction and validated by exact agreement with the two
   existing implementations at caps 15, 17, 18 and 20, not by a replayed walk
   for each class.
2. The conjugator bound was left at K = 1 for the cap-21 run. The K = 2 and
   K = 3 agreement is verified only up to cap 20.
3. The move set is the three plain moves. ACM-moves, which Panteleev and Ushakov
   prove generate the same equivalence, are not used, and the comparison with
   their table inherits that difference.
4. The canonicity of the reimplemented normal form is tested rather than proved.
   The descent explores all non-increasing elementary automorphism steps from
   each state, which is complete for the data tested but not proved complete in
   general. Its agreement with the reference implementation is exact on all
   39,840 cap-20 classes.
5. The journal version of Panteleev and Ushakov's table was not read; the arXiv
   e-print of arXiv:1609.00325 was read directly (Section 13), and its cells
   agree with the ones directions/pu-gap/pu-gap.md recorded.
6. The count 219,042,976 is the size of the reachable set inside the box. It is
   not a count of the tuples of the box.

## 9. Files and exact commands

Build and run in a fresh directory:

    gcc -O2 -march=native -o rawbox4 rawbox4.c
    mkdir -p t21 && cd t21 && ../rawbox4 21 1 .
    cd .. && python3 punf.py t21/classes.txt pu21.txt --procs 3
    python3 checkC.py t21/classes.txt t21/visited.bin
    python3 verify.py

Key output lines from the cap-21 run:

    # rawbox4 T=21 K=1
    states 219042976 classes 144292 bfs_time 941.6 scan_time 1041.5
    states_by_total 13:4032 14:15424 15:255808 16:344352 17:2720000 18:3476096 19:22343488 20:26951360 21:162932416
    classes_by_total 13:12 14:40 15:548 16:572 17:3108 18:3488 19:17688 20:18792 21:100044
    depth 167: empty frontier, BFS finished

and `WALL 1983.35 s RSS 298208 KB` from the `/usr/bin/time -f` wrapper.

The normal form run on the cap-21 class list prints

    distinct canonical forms: 10884
      minlen 13: 2   cumulative 2
      ...
      minlen 21: 7588   cumulative 10884

and the class-C test prints `class-level: class C presentations found in the
census class list: 0 of 8` and `state-level: literal presentations found in the
visited set: 0 of 16 (8 x 2 orders)`.

Files of this directory:

* `rawbox4.c`, the disk-backed layer enumerator. `rawbox2` (directions/pu-gap)
  is the in-memory reference it was validated against.
* `punf.py`, the reimplemented PU normal form.
* `checkC.py`, the class-C test (word algebra and canonical form reimplemented
  again, independently of `punf.py`).
* `verify.py`, `verify22.py`, `verify23.py`, the monotonicity, determinant,
  length-13 identification, class-C and normal-form invariance checks for caps
  21, 22 and 23.
* `run_cap21.sh`, the cap-21 commands in one script.
* `results/`, the run outputs: `cap20.out`, `cap21.out`, `cap21_levels.txt`
  (the 167 layers with their state counts), `classes21.txt` (the 144,292 class
  canonical pairs), `classes22.txt`, `classes23.txt.gz`, `pu20.txt`, `pu21.txt`,
  `pu22.txt`, `pu23.txt.gz`, `states23.out` and the logs of the small caps.
  `rawbox4` also has a `scan workdir lo hi outfile` mode and a `--resume` mode,
  which Sections 11 and 12 use.

The 1.75 GB visited state file of the cap-21 run is not shipped. It stays at
`.ultramath/smw2woueq/m5/cap21/t21/visited.bin` in this VM.

## 10. Status of each claim

| claim | status | where checked |
|-------|--------|---------------|
| cap-21 census complete: 219,042,976 states | computed, two implementations agree at caps 15, 17, 18, 20 | Sections 4, 5 |
| 144,292 conjugation classes, 10,884 PU classes | computed | Sections 5, 7 |
| peak memory 298 MB, 1983 s | measured by `/usr/bin/time -v` | Section 3 |
| every class has determinant plus or minus one | computed on all 144,292 | Section 4 |
| the twelve length-13 classes are the c14 twelve | computed, normalised membership | Section 4 |
| class C is absent at cap 21 | computed, three tests | Section 6 |
| any path to class C needs an intermediate of length at least 22 | computed bounded negative | Section 6 |
| PU counts 2, 5, 35, 40, 206, 246, 1209, 1224 at cap 20 | computed by the reimplementation, matches the reference exactly | Section 7 |
| deficits 3, 23, 49, 404, 454 at cap 20 and 3, 20, 38, 253, 290 at cap 21 | arithmetic on computed counts | Section 7 |
| the class-C normal form printed in pu-gap.md is one letter short | computed by two normal forms and by pu-gap's own log | Sections 1, 6 |

## 11. Addendum: the cap-22 box

[Computed] The same enumerator was also run at T = 22. The breadth first part
finished in one process in 1085 s at a peak of 324,616 KB of resident memory and
reached depth 180 with an empty frontier. The class pass was split into three
contiguous ranges of the visited file, run as three processes, each
deduplicating its own range in memory, and the three lists were merged with
`LC_ALL=C sort -u`. That split path was validated at cap 17 against the single
pass: 1,000 classes both ways, and the two class lists are identical.

| quantity | cap 20 | cap 21 | cap 22 |
|----------|-------:|-------:|-------:|
| states | 51,411,456 | 219,042,976 | 419,826,272 |
| conjugation classes | 39,840 | 144,292 | 258,032 |
| PU classes | 2,967 | 10,884 | 20,111 |
| depth reached | 151 | 167 | 180 |
| peak RSS | 189,644 KB | 298,208 KB | 324,616 KB |
| wall clock | 173 s | 1,983 s | 1,085 s (BFS) + 686 s (class pass) |

The growth from cap 21 to cap 22 is 1.92 in states, against 4.26 from cap 20 to
cap 21, so the box is closing faster than the earlier factor suggested. The
cap-22 states by total length are 13:4032, 14:15424, 15:255808, 16:344352,
17:2733440, 18:3540928, 19:22736896, 20:27711872, 21:167300032 and 22:195183488,
and the classes by total length are 13:12, 14:40, 15:548, 16:572, 17:3132,
18:3592, 19:18176, 20:19472, 21:103432 and 22:109056.

[Computed] The PU classes by minimal total length at cap 22 are 2, 5, 35, 40,
210, 264, 1390, 1407, 7950 and 8808 for minimal lengths 13 to 22, with
cumulative values 2, 7, 42, 82, 292, 556, 1946, 3353, 11303 and 20111. The
deficits against the halved Table 1 cells are then:

| T  | 13 | 14 | 15 | 16 | 17 | 18 | 19  | 20  |
|----|----|----|----|----|----|----|-----|-----|
| cap 20 | 0 | 0 | 0 | 3 | 23 | 49 | 404 | 454 |
| cap 21 | 0 | 0 | 0 | 3 | 20 | 38 | 253 | 290 |
| cap 22 | 0 | 0 | 0 | 3 | 19 | 31 | 223 | 271 |

[Argument] Across three caps the deficit at T = 16 stays at exactly 3 while the
deficits at T = 17 to 20 keep falling. The natural reading is that those three
classes of total length 16 need an intermediate pair of total length at least
23, since they are still outside a box that allows 22, and that the rest of the
deficit is a matter of how much box the search allows. This run does not
separate the box from the ACM move set, and it does not identify the three
classes.

[Computed] Class C is still outside at cap 22. The box has 12 conjugation
classes of total length 13, the same twelve rows of directions/c14/ as before,
and 0 of the 8 class-C rows. It has 2 PU classes of minimal length 13, the same
two canonical forms as at caps 20 and 21, and 0 of the 8 class-C canonical
forms. The eight presentations in both relator orders are also absent from the
visited state file (0 of 16 literal keys). So any AC path from AK(3) to class C
needs an intermediate pair of total length at least 23.

[Computed] Three further checks hold at cap 22. Every cap-21 class is a cap-22
class (144,292 of 258,032). Every one of the 258,032 classes has an exponent-sum
matrix of determinant plus or minus one, with 0 exceptions. And the twelve
length-13 classes are exactly the c14 rows labelled `ak3-equivalent` (6) and
`resisting-budget-cap19` (6).

[Computed] The cap-22 commands, in the order they were run:

    mkdir -p t22 && cd t22 && ../rawbox4 22 1 . --maxsec 3000 --no-classes
    R=$(($(stat -c %s visited.bin)/8))
    ../rawbox4 scan . 0 $((R/3)) p1.txt &
    ../rawbox4 scan . $((R/3)) $((2*R/3)) p2.txt &
    ../rawbox4 scan . $((2*R/3)) $R p3.txt &
    wait
    cat p1.txt p2.txt p3.txt | LC_ALL=C sort -u > classes.txt
    cd .. && python3 punf.py t22/classes.txt pu22.txt --procs 3
    python3 verify22.py

The three range scans print `251212`, `258032` and `132732` distinct class keys
and the merged list has 258,032 lines. `verify22.py` prints

    classes cap21 144292 cap22 258032 ; cap21 subset of cap22: True
    determinant check: 258032 classes, 0 with |det| != 1
    c14 length-13 rows in the cap-22 class list: {'ak3-equivalent': [6, 6], 'resisting-exhausted-cap17': [0, 8], 'resisting-budget-cap19': [6, 6]}
    cap-22 classes of total length 13: 12
    PU classes of minlen 13: cap21 2, cap22 2, identical: True
    class C canonical forms present in the cap-22 PU list: 0 of 8

The cap-22 outputs are in `results/` as `cap22.out`, `classes22.txt`, `pu22.txt`
and the three range logs `s1.err`, `s2.err`, `s3.err`. The 3.36 GB visited state
file stays at `.ultramath/smw2woueq/m5/cap21/t22/visited.bin`.

## 12. Addendum: the cap-23 box

[Computed] The enumerator was also run at T = 23. That box is large enough that
the breadth first pass needs a stop and resume facility: the process stops at a
level boundary when a wall clock limit is reached, the visited file and the
frontier file stay on disk, and `--resume` continues from them. Three calls
completed it, 2,905 s, 2,905 s and 1,045 s, at depths 128, 273 and finally 326
with an empty frontier. The peak resident memory of the first call was 540,808
KB and the visited file is 13.1 GB.

| quantity | cap 21 | cap 22 | cap 23 |
|----------|-------:|-------:|-------:|
| states | 219,042,976 | 419,826,272 | 1,638,542,144 |
| conjugation classes | 144,292 | 258,032 | 891,748 |
| PU classes | 10,884 | 20,111 | 71,572 |
| depth reached | 167 | 180 | 326 |
| class-C reached? | no | no | no |

[Computed] The states by total length are 13:4032, 14:15424, 15:259392,
16:354432, 17:2786560, 18:3640640, 19:23359744, 20:28772704, 21:172911296,
22:204765280 and 23:1201672640. The conjugation classes by key length are
13:12, 14:40, 15:556, 16:592, 17:3200, 18:3688, 19:18768, 20:20356, 21:107264,
22:115212 and 23:622060. The key length is the total length of the canonical
pair, which is at most the total length of the state because the canonical form
applies cyclic reduction, so the two histograms are not the same partition.

[Computed] The PU classes by minimal total length at cap 23 are 2, 5, 35, 43,
217, 272, 1440, 1485, 8447, 10014 and 49612 for minimal lengths 13 to 23, with
cumulative values 2, 7, 42, 85, 302, 574, 2014, 3499, 11946, 21960 and 71572.

[Computed] The deficits against the halved Table 1 cells now run as follows.

| T  | 13 | 14 | 15 | 16 | 17 | 18 | 19  | 20  |
|----|----|----|----|----|----|----|-----|-----|
| cap 20 | 0 | 0 | 0 | 3 | 23 | 49 | 404 | 454 |
| cap 21 | 0 | 0 | 0 | 3 | 20 | 38 | 253 | 290 |
| cap 22 | 0 | 0 | 0 | 3 | 19 | 31 | 223 | 271 |
| cap 23 | 0 | 0 | 0 | 0 | 12 | 23 | 173 | 193 |

[Computed] The deficit at T = 16 closes exactly at cap 23: the box has 43 PU
classes of minimal length 16, and the halved published cell is 43. The three
classes that were missing at cap 20, 21 and 22 are the three that cap 23 adds,
so each of them needs an intermediate pair of total length of at least 22, and
a path through the cap-23 box suffices. Their canonical forms and the key
lengths of the box classes that realise them are

    (x^4 y x y^2, x y^4 x^-1 y^-3)          realised at key lengths 16 and 17
    (x^3 y x^-2 y^3, x^2 y x^-1 y x^-1 y^-1) realised at key length 21
    (x^3 y x^-1 y^2, x^2 y^2 x y x^-2 y^-1)  realised at key length 23

   [Coordinator note, 5 November 2026, from the round-5 second-referees-4 audit,
   verified directly against pu23.txt.gz: the first of the three forms above is
   misprinted. As printed it has total length 17 and does not occur in
   pu23.txt.gz. The form in the data is (x^4 y x y, x y^4 x y^-3), total length
   16, stored as the canonical pair XXXXYXY | XYYYYXyyy: the first relator is
   x^4 y x y, not x^4 y x y^2, and the eighth letter of the second relator is x,
   not x^-1. The audit's own report carries the same y^2 slip in its quote of
   the correction; the form here is taken from the data and from the audit's
   rerun output. The other two printed forms are correct as they stand.]

[Computed, interpretation] The first of the three is represented in the box by a
pair of total length 16, so a length-16 pair is reachable from AK(3), and every
such path passes through a pair of total length 22 or 23. The other two are
represented only by longer pairs. This is the first case in this campaign where
a class of the published table that our box missed is shown to be reachable, and
it identifies exactly what the deficit at T = 16 was counting.

[Argument] The deficits at T = 17 to 20 remain positive at 12, 23, 173 and 193.
Each of those classes therefore still needs an intermediate pair of total length
at least 24, and the run does not say how much more. The deficits fall
monotonically in the cap at every one of those four lengths, which is consistent
with the box being the explanation for the whole residual.

[Computed] Class C is still absent at cap 23. The box has 12 conjugation classes
of total length 13, the same twelve c14 rows, and 0 of the 8 class-C rows. It has
2 PU classes of minimal length 13, the same two canonical forms as at caps 20,
21 and 22, and 0 of the 8 class-C canonical forms. So any AC path from AK(3) to
class C needs an intermediate pair of total length at least 24.

[Computed] The cap-23 checks are: every cap-22 class is a cap-23 class (258,032
of 891,748); every one of the 891,748 classes has an exponent-sum matrix of
determinant plus or minus one, with 0 exceptions; and the twelve length-13
classes are exactly the c14 rows labelled `ak3-equivalent` (6) and
`resisting-budget-cap19` (6). The class count also has two independent
computations: the class pass was run as four contiguous ranges, the first with
an in-memory class set and the other three with chunked sorting, and their union
has 891,748 classes; a single pass over the whole file with chunked sorting and
a streaming merge gives the same 891,748 classes with the same distribution by
key length.

[Computed] The cap-23 commands:

    mkdir -p t23 && cd t23
    ../rawbox4 23 1 . --maxsec 2900 --no-classes      # run three times, the
                                                     # later ones with --resume
    ../rawbox4 scan . 0 1638542144 full.txt          # single pass, 1079.9 s
    cd .. && python3 punf.py t23/full.txt pu23.txt --procs 3
    python3 verify23.py

The single pass prints `scan [0,1638542144) done: 891748 distinct class keys`,
`punf.py` prints `distinct canonical forms: 71572` with the distribution above,
and `verify23.py` prints

    classes cap22 258032 cap23 891748 ; cap22 subset of cap23: True
    determinant check: 891748 classes, 0 with |det| != 1
    c14 length-13 rows in the cap-23 class list: {'ak3-equivalent': [6, 6], 'resisting-exhausted-cap17': [0, 8], 'resisting-budget-cap19': [6, 6]}
    PU classes of minlen 13: cap22 2, cap23 2, identical: True
    class C canonical forms present in the cap-23 PU list: 0 of 8

The cap-23 outputs are in `results/` as `classes23.txt.gz` (53 MB of text,
gzipped), `pu23.txt.gz` and `states23.out`. The 13.1 GB visited file stays at
`.ultramath/smw2woueq/m5/cap21/t23/visited.bin`.

## 13. Primary-source check of Table 1, and the comparison at T = 21 to 23

[Source] I downloaded the arXiv e-print of Panteleev and Ushakov,
arXiv:1609.00325 (file ac15.tex), on 5 November 2026 with the command
`curl -sL -o ep.gz https://arxiv.org/e-print/1609.00325`. The caption of the
table labelled `tab:presentation_num` reads: "Each cell in Table 1 corresponds
to a value L and a value T and presents the number of pairs of the total length
equal to T constructed by the program with the single-word-bound L." That
confirms the per-length convention that Section 7 uses, which round 3
established from the same source. The cells of the columns L = 17 to 20 for
T = 13 to 20 are 4, 10, 70, 86, 458, 590, 3226 and 3356, exactly as recorded in
directions/pu-gap/pu-gap.md, and the L = 10 column falls from 240 at T = 19 to
10 at T = 20, which the caption already implies.

[Source] The same table also gives the cells for T = 21, 22 and 23. In the
L = 20 column they are 19692, 23192 and 128388, and the table runs on to
T = 42. Those rows were never compared in this campaign, because no box larger
than 20 had been computed.

[Computed, comparison] Halving the three cells and comparing them with the
cap-23 counts of Section 12 gives the following.

| T  | their cell, L = 20 | halved | ours at cap 23 | deficit |
|----|-------------------:|-------:|---------------:|--------:|
| 21 | 19,692             | 9,846  | 8,447          | 1,399   |
| 22 | 23,192             | 11,596 | 10,014         | 1,582   |
| 23 | 128,388            | 64,194 | 49,612         | 14,582  |

[Argument] These deficits are one to two orders of magnitude larger than the
ones at T = 16 to 20, and the source says why: their run allows intermediates of
total length up to 2L + 2, which is 42 at L = 20, so its cells at T = 21 to 23
count pairs whose paths need intermediates that our cap-23 box excludes. The
comparison at T = 21 to 23 therefore measures the box, and it says nothing about
the normal form. It does not contradict the comparison at T of 20 or less, where
the two boxes are both far larger than the class length.

[Computed, caveat] The halving is exact only where every PU class contributes
exactly two entries, one per relator order. It was verified to be exact at
T = 13, 14 and 15. At larger T a class can contribute to several cells, one for
each representative of that exact length, so the three deficits above are
indicative of the box difference and are not class counts. The deficits at
T = 16 to 20 in Section 7 are computed in the same way and carry the same
caveat, which is why they are presented as a deficit against a convention
rather than as a count of missing classes.

[Coordinator note, 5 November 2026, from the round-5 second-referees-4 audit,
argument checked by hand: the caveat does not reach T = 16, and the closure
recorded in Sections 7 and 12 at T = 16 is rigorous. A published cell counts
ordered pairs of total length exactly T, so the halved cell counts unordered
pairs of total length exactly T, summed over classes, which is at least the
number of classes that have any pair of total length T. Each of our 43
minimal-length-16 classes has a pair of total length 16, so at least 43
unordered pairs of that length lie in the published cell, whose halved value
is exactly 43. There are therefore exactly 43 such classes and each contributes
exactly one unordered pair, so the halved cell at T = 16 is a class count and
the box's 43 closes it exactly.]
