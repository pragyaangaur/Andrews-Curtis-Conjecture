# The cap-24 census of the AK(3) class: class C, the T = 17 deficit, and the end of the box

Round 5, direction H1. Every number below comes from a deterministic computation
whose exact command is given in Section 9. Nothing here says anything about the
truth or the falsehood of the Andrews-Curtis conjecture, and no claim of a proof
or a disproof of it is made. Claims are labelled [Computed], [Argument],
[Source] or [Open].

## 1. Summary

1. [Computed] The AK(3) class inside the total-length-24 box is complete. It
   holds 3,056,896,064 tuples, which fall into 1,596,072 classes under
   conjugation and inversion of the relators and into 131,620 classes under the
   Panteleev-Ushakov relation of their Section 4.2. The traversal reaches its
   fixed point after 669 rounds, peaks at 7.79 GB of resident memory and writes
   24.5 GB of run files.
2. [Computed] Every cap-23 class is a cap-24 class (891,748 of 1,596,072), the
   class count grows by a factor 1.790 and the state count by 1.866. The
   growth from cap 22 to cap 23 was a factor 3.903, so the box is closing.
3. [Computed] Class C is not in the cap-24 box. The box has exactly two PU
   classes of minimal total length 13, the same two as at caps 20, 21, 22 and
   23, and the eight class-C presentations are absent at the level of
   conjugation classes (0 of 8), at the level of PU canonical forms (0 of 8)
   and at the level of literal states in the 24.5 GB state file (0 of 16). So
   every AC path from AK(3) to class C needs an intermediate pair of total
   length at least 25.
4. [Computed] The residual PU deficit at T = 17 does NOT close at cap 24. It is
   exactly 12 classes at cap 23 and exactly 12 classes at cap 24, against a
   halved published cell of 229. No class counted by that deficit entered at cap
   24, so on the halving convention of Section 7 each of them needs an
   intermediate pair of total length at least 25. This answers the question the
   direction asked, with a negative.
5. [Computed] The deficits at T = 18, 19 and 20 keep falling: 23, 173 and 193 at
   cap 23 against 20, 161 and 166 at cap 24. The deficit at T = 16 stays at 0,
   which is the closure that round 4 reported at cap 23. The deficits at
   T = 21, 22, 23 are 1,286, 1,474 and 11,262, and the new row T = 24 has
   deficit 18,673 against the published cell of 150,276.
6. [Computed, validation] The new engine reproduces every earlier census
   exactly: caps 13, 15, 17, 18, 20, 21 and 22 in state count, class count and
   per-length histogram, and cap 23 in state count, per-length histogram, a
   checksum over all 1,638,542,144 states that agrees with the round-4 visited
   file, and a sorted class list that is byte-identical to the round-4 class
   list. The cap-21 class list and checksum also agree with round 4.
7. [Computed, interpretation] The three stratifications agree with each other:
   the states of total length 13 to 18 have exactly the same counts at caps 23
   and 24, and the classes of key length 13 to 18 are likewise unchanged, so
   the extra room at cap 24 buys almost nothing at the short lengths. The whole
   of the growth is in the strata of total length 23 and 24, which hold
   1,207,646,336 and 1,411,296,448 states.
8. [Computed] The box has added no PU class of minimal length 17 since cap 23,
   and none of minimal length 16 since cap 23 either. Section 12 gives the first
   cap at which each PU class appears: of the 217 classes of minimal length 17,
   206 were already in the cap-20 box, 3 entered at cap 21, 1 at cap 22 and 7 at
   cap 23, and cap 24 added none. The twelve classes of the T = 17 deficit are
   therefore outside every box up to cap 24, and the deficit is not a matter of
   one more unit of cap.
9. [Computed, bounded] The cap-25 census is out of reach for this engine. Two
   attempts were made. The second, with the widened key and with one bug fixed,
   reached 5,222,573,371 states, which is a sound lower bound for the cap-25 box,
   with the frontier at 243,285,727 states and 14.0 GB of resident memory when a
   child process was killed by the memory ceiling. Section 13 records the exact
   stopping point, the engine bug that the first attempt exposed and its fix,
   and why the partial set says nothing about the T = 17 deficit.
10. [Open] Nothing here decides whether class C is AK(3)-equivalent. The
   prediction of directions/pu-gap/pu-gap.md that it is not remains a
   prediction. The census also says nothing about AK(3) beyond total length 24.

## 2. The object, the box and the move set

Let F = F(x,y) and let a presentation be a pair (u,v) of freely reduced words.
AK(3) is the pair (x y x y^-1 x^-1 y^-1, x^3 y^-4) of total length 13. The moves
are the three Andrews-Curtis moves: invert one relator, multiply one relator by
the other on the left or the right, and conjugate one relator by a word w. A
tuple is in the box B(T) when |u| + |v| is at most T. The enumerator walks the
finite graph whose vertices are the tuples of B(T) reachable from AK(3) and
whose edges are the moves that stay in the box, with conjugating words of
length at most K. This is the same object as in
directions/pu-enumeration/pu.md Section 2, directions/pu-gap/pu-gap.md
Section 2 and directions/cap21/cap21.md Section 2, and the move set, the
encoding and the class canonical form are copied from rawbox4.c, so the numbers
are directly comparable with the round-2, round-3 and round-4 tables.

The run reported here uses T = 24 and K = 1. The conjugator bound is not the
binding constraint in this range: rounds 2 and 3 verified that K = 1, K = 2 and
K = 3 give the same vertex set and the same class set at caps 13 to 20, round 3
verified that the K = 2 rerun leaves every resister component unchanged, and
round 4's conjugator-independence theorem covers the class-key level for every
K. That theorem applies to the class-key target of the resisters engine, and it
is not re-verified here at cap 24, which Section 8 records as a gap.

## 3. The engine, and why round 4's design does not reach cap 24

rawbox4.c is level by level against a single visited file, and it reads and
rewrites the whole visited file at every level. The cap-23 run's own level
summary gives the size of that traffic: the frontier sizes sum to exactly the
1,638,542,144 states, but the cumulative sizes sum to 4.2879e11 records, which
is 6.9 TB of reading and writing for a 13.1 GB answer. Extrapolating that design
to cap 24 gives roughly 400 levels over a 24.5 GB visited file, about 20 TB of
traffic, and a wall clock of many hours with no useful intermediate result.

rawbox6.c, written for this direction, keeps the same move set and the same
encoding, and changes the traversal. The visited set is written once as a short
list of disjoint sorted run files, and it is consulted once per batch instead of
once per level:

    a batch, with F the frontier (sorted array) and H every state discovered so
    far in this batch (sorted array containing F):
      repeat  C = neighbours of F inside the box (parallel expansion)
              F' = C \ H ;  H <- H union F' ;  F <- F'
      until |H| >= hmax, or the batch is older than batchsec, or F is empty
      flush   Hnew = H \ (union of runs), written as a new run
              F2 = F intersect Hnew

The fixed point is reached exactly when F2 is empty. Every state in Hnew is new,
and every state of H outside Hnew is in an old run and was expanded in an
earlier batch, so at that moment the visited set is closed under the moves
inside the box. A state that is already in an old run but rediscovered in the
current batch is expanded again, which costs time and nothing else. The
expansion of the frontier is split over four child processes, each expanding
every fourth frontier entry into its own sorted and deduplicated chunks, which
the child then merges into one stream so that the parent merges four streams.
Runs are merged into one file whenever there are more than four of them (six in rawbox7).

The parameters of the cap-24 run are hmax = 300,000,000, batchsec = 1200, four
processes. It ran in four stage calls of 186, 414, 2197 and 1063 seconds, giving
3860 seconds of wall clock for the breadth first part. The first stage ended on
the engine's own allocation check (exit 2) at 6.0 GB of resident memory and the
second on a broken pipe from a display filter; each lost at most one batch of
work, and both are included in that total. The checkpoint written at the last
flush before each stop was resumed, and the final state file records batch 20
with 3,056,896,064 states. The class pass was split into four processes that
each read all runs and keep one quarter of the states, chosen by a hash of the
state key, and it took 1086 seconds. The PU normal form took 1424 seconds on
four processes. Peak memory was 7,794,640 KB of resident memory, which is the
two H arrays of 2.4 GB each at hmax = 3e8 plus the frontier arrays; the machine
has 16 GB.

Disk: the four run files are 23,952,335,784, 284,284,504, 218,545,760 and 2,464
bytes, that is 24.5 GB. The key uses 16 bits for the two relator lengths and 48
bits for letters, which is exactly 24 letters, so the cap-24 box is the last one
this key can hold. Section 13 has a wider key that covers T = 27, and the
reason the cap-25 run still fails.

## 4. Validation

The engine is new code, so it was checked against every count the campaign has
recorded. All of the following are exact reproductions, not approximations:

| cap | states, this engine | states, recorded | classes, this engine | classes, recorded |
|-----|--------------------:|-----------------:|---------------------:|------------------:|
| 13  | 168                 | 168              | 1                    | 1                 |
| 15  | 6,864               | 6,864            | 26                   | 26                |
| 17  | 857,808             | 857,808          | 1,000                | 1,000             |
| 18  | 2,014,992           | 2,014,992        | 2,128                | 2,128             |
| 20  | 51,411,456          | 51,411,456       | 39,840               | 39,840            |
| 21  | 219,042,976         | 219,042,976      | 144,292              | 144,292           |
| 22  | 419,826,272         | 419,826,272      | 258,032              | 258,032           |
| 23  | 1,638,542,144       | 1,638,542,144    | 891,748              | 891,748           |

The per-total-length histograms also agree in every case, for instance
13:4032 14:15424 15:241856 16:336288 17:2520832 18:3280096 19:20185152
20:24827776 at cap 20, and the cap-23 row
13:4032 14:15424 15:259392 16:354432 17:2786560 18:3640640 19:23359744
20:28772704 21:172911296 22:204765280 23:1201672640.

Three stronger checks were made against files that round 4 left on disk. First,
the cap-21 class list produced here is identical as a set to
directions/cap21/results/classes21.txt (144,292 lines, zero differences after
sorting), and the cap-22 class list is byte-identical to
directions/cap21/results/classes22.txt (258,032 lines, `cmp` reports no
difference). Second, at cap 23 the sorted class list produced here is
byte-identical to directions/cap21/results/classes23.txt.gz (891,748 lines,
`cmp` reports no difference), and the order-independent checksum
XOR over all keys of key times 0x9e3779b97f4a7c15 gives 91386f4d10000000 both
for the run files here and for the round-4 visited file at
.ultramath/smw2woueq/m5/cap21/t23/visited.bin, over 1,638,542,144 states on
both sides. Since rawbox4 and rawbox6 share no traversal code, agreement at
that scale is evidence that the batched traversal loses no state and invents
none.

Three further checks apply to the cap-24 result itself: every cap-23 class is a
cap-24 class (891,748 of 1,596,072); every one of the 1,596,072 classes has an
exponent-sum matrix of determinant plus or minus one, which is the AC invariant
(0 exceptions); and the twelve classes of total length 13 are exactly the twelve
rows of directions/c14/final_classes.txt labelled ak3-equivalent (6 of 6) and
resisting-budget-cap19 (6 of 6), with 0 of the 8 rows labelled
resisting-exhausted-cap17, which are class C.

## 5. The cap-24 tables

States by total length, from the class pass:

| T  | states, cap 22 | states, cap 23 | states, cap 24 |
|----|---------------:|---------------:|---------------:|
| 13 | 4,032          | 4,032          | 4,032          |
| 14 | 15,424         | 15,424         | 15,424         |
| 15 | 255,808        | 259,392        | 259,392        |
| 16 | 344,352        | 354,432        | 354,432        |
| 17 | 2,733,440      | 2,786,560      | 2,786,560      |
| 18 | 3,540,928      | 3,640,640      | 3,640,640      |
| 19 | 22,736,896     | 23,359,744     | 23,365,504     |
| 20 | 27,711,872     | 28,772,704     | 28,791,200     |
| 21 | 167,300,032    | 172,911,296    | 173,170,752    |
| 22 | 195,183,488    | 204,765,280    | 205,565,344    |
| 23 |                | 1,201,672,640  | 1,207,646,336  |
| 24 |                |                | 1,411,296,448  |
|    | **419,826,272**| **1,638,542,144** | **3,056,896,064** |

Classes by canonical key length. The key length is the total length of the
canonical pair, which is at most the total length of the state because the
canonical form applies cyclic reduction, so this is not the same partition as
the table above.

| key length | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|------------|---:|---:|---:|---:|---:|---:|---:|----:|----:|----:|----:|----:|
| cap 23     | 12 | 40 | 556| 592| 3200| 3688| 18768| 20356| 107264| 115212| 622060| |
| cap 24     | 12 | 40 | 556| 592| 3200| 3688| 18776| 20380| 107544| 116052| 627320| 697912 |

PU classes by minimal total length:

| minimal length | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|----------------|---:|---:|---:|---:|---:|---:|---:|----:|----:|----:|----:|----:|
| cap 22         | 2 | 5 | 35 | 40 | 210 | 264 | 1390 | 1407 | 7950 | 8808 | | |
| cap 23         | 2 | 5 | 35 | 43 | 217 | 272 | 1440 | 1485 | 8447 | 10014 | 49612 | |
| cap 24         | 2 | 5 | 35 | 43 | 217 | 275 | 1452 | 1512 | 8560 | 10122 | 52932 | 56465 |

Cumulative from 13: cap 23 gives 2, 7, 42, 85, 302, 574, 2014, 3499, 11946,
21960 and 71572; cap 24 gives 2, 7, 42, 85, 302, 577, 2029, 3541, 12101, 22223,
75155 and 131620.

## 6. Class C is not in the cap-24 box

[Computed] Class C is the third PU class of total length 13. Its eight
presentations are the eight rows that directions/c14/final_classes.txt labels
resisting-exhausted-cap17 at length 13: BAbABa,BBBABAA; BAbABa,BBBAABA;
BAbABa,BBABAAA; BAbABa,BBAAABA; BABaba,BBaaaBa; BABaba,BBaBaaa;
BABaba,BBBaaBa; BABaba,BBBaBaa. Three tests were run, and all three are
negative.

1. Conjugation level. The eight rows form two conjugation classes. Neither
   canonical pair occurs in the 1,596,072-class list of the cap-24 census, and
   the census has exactly 12 classes of total length 13, the same 12 as at caps
   20, 21, 22 and 23.
2. PU level. All eight rows have the single canonical form
   (x^3 y x y^2, x y x^-1 y x y^-1). That form is not in the 131,620-class
   cap-24 PU list. The only PU classes of minimal length 13 in the box are A
   and B, with the canonical forms (x^4 y^3, x y x^-1 y x y^-1) and
   (x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y), identical at caps 20 to 24.
3. State level. The eight presentations themselves, in both relator orders,
   are absent from the 3,056,896,064-state run files (0 of 16 keys found by
   streaming all four runs).

[Computed, bounded negative] Therefore no member of PU class C is reached by
paths whose intermediate pairs all have total length at most 24. Any AC path
from AK(3) to class C needs an intermediate pair of total length at least 25.
This continues the sequence 21, 22, 23 and 24 of caps 20 to 23, one step per
unit of cap. Nothing here decides whether class C is AK(3)-equivalent, and
directions/pu-gap/pu-gap.md predicts that it is not.

## 7. The residual deficit, and the answer at T = 17

[Computed] punf.py, the reimplementation of the Panteleev-Ushakov normal form
that round 4 wrote, is used unchanged. On the cap-23 PU file that round 4
shipped it returns 71,572 distinct canonical forms with the distribution
2, 5, 35, 43, 217, 272, 1440, 1485, 8447, 10014, 49612 for minimal lengths 13
to 23, which is exactly the round-4 figure, so the two computations are
comparable. On the cap-24 class list it returns 131,620 distinct forms with the
distribution in Section 5.

[Source] The comparison uses the L = 20 column of Table 1 of
arXiv:1609.00325. I extracted the table from the e-print again for this report.
The caption reads "Each cell in Table 1 corresponds to a value L and a value T
and presents the number of pairs of the total length equal to T constructed by
the program with the single-word-bound L", which is the per-length convention
that rounds 3 and 4 established. The cells of the L = 20 column for T = 13 to 24
are 4, 10, 70, 86, 458, 590, 3226, 3356, 19692, 23192, 128388 and 150276.

| T  | published L=20 | halved | ours cap 23 | ours cap 24 | deficit cap 23 | deficit cap 24 |
|----|---------------:|-------:|------------:|------------:|---------------:|---------------:|
| 13 | 4              | 2      | 2           | 2           | 0              | 0              |
| 14 | 10             | 5      | 5           | 5           | 0              | 0              |
| 15 | 70             | 35     | 35          | 35          | 0              | 0              |
| 16 | 86             | 43     | 43          | 43          | 0              | 0              |
| 17 | 458            | 229    | 217         | 217         | 12             | 12             |
| 18 | 590            | 295    | 272         | 275         | 23             | 20             |
| 19 | 3226           | 1613   | 1440        | 1452        | 173            | 161            |
| 20 | 3356           | 1678   | 1485        | 1512        | 193            | 166            |
| 21 | 19692          | 9846   | 8447        | 8560        | 1399           | 1286           |
| 22 | 23192          | 11596  | 10014       | 10122       | 1582           | 1474           |
| 23 | 128388         | 64194  | 49612       | 52932       | 14582          | 11262          |
| 24 | 150276         | 75138  |             | 56465       |                | 18673          |

[Computed] The answer to the direction's second question. The deficit at T = 17
is 12 at cap 23 and 12 at cap 24. No class counted in that deficit is inside the
cap-24 box, so each of the twelve needs an intermediate pair of total length at
least 25. The deficit at T = 16 was 3 at caps 20, 21 and 22 and closed to 0 at
cap 23, where the box first reached the published count; it stays 0 at cap 24.
So the closure at T = 16 is stable, and the deficit at T = 17 is not closed by
one more unit of cap.

[Computed, interpretation] The deficits at T = 18, 19 and 20 fall by 3, 12 and
27 when the cap grows from 23 to 24, and the deficits at T = 21, 22 and 23 fall
by 113, 108 and 3320. Every one of those is positive at cap 24, so each of those
classes still needs an intermediate pair of total length at least 25 as well,
and this run does not say how much more.

[Caveat, carried from round 4] The halving is exact only where every PU class
contributes exactly two entries to the published cell, one per relator order.
Round 4 verified that at T = 13, 14 and 15. At larger T a single class can
contribute to several cells, one for each representative of that exact length,
so the deficits are a deficit against a stated convention rather than a count of
missing classes. This is why Section 1 item 4 says "against a halved published
cell of 229" instead of "twelve classes are missing from a list".

## 8. What is not established

1. No per-class certificates are produced at cap 24. The enumerator does not
   store parent pointers, so the census is a reachable set computed by
   construction and validated by exact agreement with rawbox4's counts at eight
   caps and with three of its class lists at caps 21, 22 and 23 and its cap-23
   state file, not by a replayed walk for each class.
2. The conjugator bound was left at K = 1. The K = 2 and K = 3 agreement is
   verified up to cap 20, and round 4's conjugator-independence theorem covers
   the class-key level for every K; neither is re-verified here at cap 24.
3. The move set is the three plain moves. ACM moves, which Panteleev and
   Ushakov prove generate the same equivalence, are not used, and the
   comparison with their table inherits that difference.
4. The canonicity of the PU normal form is tested rather than proved, as in
   round 4. Its exact agreement with the round-4 PU file on 891,748 inputs is
   the check that was made.
5. The round counter in Section 1 is not the breadth first depth. Because
   batches overlap in the states they rediscover, the engine counts rounds of
   expansion, and the cap-23 run took 464 rounds where rawbox4 took 326 levels.
   Nothing in the results depends on the round count.
6. The T = 17 deficit is not identified class by class, because the published
   table gives counts and not the classes.
7. The growth factor of the state count from cap 23 to cap 24 is 1.866, and it
   is not evidence that the box closes at cap 25. It only says that this unit of
   cap bought less than the previous one did.
8. The source of rawbox6.c that ships here is not byte-identical to the binary
   that produced Sections 4 to 7. Two repairs were made afterwards, and neither
   can change any number reported for caps 13 to 24. The first is the guard on
   the single-partition path of `rawbox6 scan`, which shifted by 64 for one
   part; every scan reported here used four partitions, which is the path that
   ran. The second is the order of the run compaction and the state file write,
   which Section 13 explains; it can only matter across a `--resume` that
   follows a compacting flush, and none of the cap-24 stages did. The repaired
   engine reproduces the cap-20 and cap-22 counts exactly and the cap-20 and
   cap-23 class lists byte-identically, so the repairs are inert on the path
   that produced the census.

## 9. Files and exact commands

    gcc -O3 -march=native -o rawbox6 rawbox6.c
    mkdir -p w24 && ./rawbox6 bfs 24 1 w24 --procs 4 --hmax 300000000 \
        --batchsec 1200 --maxsec 2100
    # repeated with --resume until it prints "fixed point reached"
    ./rawbox6 count 24 1 w24
    for i in 0 1 2 3; do ./rawbox6 scan 24 1 w24 w24/p$i.txt $i 4 2>w24/s$i.err & done; wait
    cat w24/p0.txt w24/p1.txt w24/p2.txt w24/p3.txt | LC_ALL=C sort -u > w24/classes.txt
    python3 punf.py w24/classes.txt w24/pu24.txt --procs 4
    python3 verify24.py
    python3 checkC24.py
    ./rawbox6 sum 24 1 w24

From the shipped files the two checkers run as

    zcat results/classes24.txt.gz > c24.txt
    zcat results/pu24.txt.gz > pu24.txt
    zcat ../../cap21/results/classes23.txt.gz > ref23.txt
    python3 verify24.py c24.txt ref23.txt pu24.txt
    python3 checkC24.py w24            # needs the run files of Section 13

Key output lines:

    fixed point reached, 1062.6s
    states 3056896064 batches 20 rounds 669
    states_by_total 13:4032 14:15424 15:259392 16:354432 17:2786560 18:3640640
      19:23365504 20:28791200 21:173170752 22:205565344 23:1207646336 24:1411296448
    runs 4 states 3056896064
    checksum 5b9465cbb0000000 states 3056896064 runs 4
    distinct canonical forms: 131620
    classes cap23 891748 cap24 1596072 ; cap23 subset of cap24: True
    determinant check: 1596072 classes, 0 with |det| != 1
    c14 length-13 rows in the cap-24 class list: {'ak3-equivalent': [6, 6],
      'resisting-exhausted-cap17': [0, 8], 'resisting-budget-cap19': [6, 6]}
    class C canonical forms present in the cap-24 PU list: 0 of 8
    class-level: class C presentations found in the cap-24 census class list: 0 of 8
    streamed 3056896064 states over 4 runs; literal class-C keys found: 0 of 16

The cap-23 recheck, which is the engine's validation against round-4 files:

    mkdir -p w23 && ./rawbox6 bfs 23 1 w23 --procs 4 --hmax 300000000 --batchsec 1200 --maxsec 2000
    ./rawbox6 sum 23 1 w23
    # yields  checksum 91386f4d10000000 states 1638542144 runs 3
    # and the same checksum over .ultramath/smw2woueq/m5/cap21/t23/visited.bin
    for i in 0 1 2 3; do ./rawbox6 scan 23 1 w23 w23/p$i.txt $i 4 2>w23/s$i.err & done; wait
    cat w23/p?.txt | LC_ALL=C sort -u > w23/classes.txt
    zcat ../../../../directions/cap21/results/classes23.txt.gz | LC_ALL=C sort -u > ref23s.txt
    cmp ref23s.txt w23/classes.txt      # no output: the lists are identical

Files of this directory:

* `rawbox6.c`, the batched parallel enumerator, with the design in the comment
  at its head.
* `punf.py` and `checkC.py`, copied unchanged from directions/cap21/, used as
  they are so that the comparison with round 4 is like for like.
* `verify24.py`, the monotonicity, determinant, c14-row, PU-distribution,
  deficit and class-C checks.
* `checkC24.py`, the state-level class-C test over the run files.
* `rawbox7.c`, the same engine with 5 bits per relator length, which covers
  T = 27; it is the engine of the cap-25 attempt of Section 13.
* `results/` holding `state24.txt` (the final state file of the run),
  `runs24.txt` (the run manifest), `scan24.log` (the four class-pass ranges
  with their per-length histograms), `classes24.txt.gz` (1,596,072 lines),
  `pu24.txt.gz` (1,596,072 lines, one per class), `states24.txt` (the summed
  per-length table), `classes23_recomputed.txt.gz` (the cap-23 recheck) and
  `cap23_recheck_bfs.log` (the full flush log of the cap-23 run),
  `verify24.log` and `checkC24.log` (the two checkers' output),
  `cap25_attempt.log`, `state25_partial.txt` (5,222,573,371 states at batch 34)
  and `classes25_partial.txt.gz` (3,068,859 lines) for Section 13.

The 24.5 GB of run files and the 13.8 GB of the cap-23 recheck stay at
.ultramath/smw38010i/m1/cap24/w24/ and .ultramath/smw38010i/m1/cap24/w23/ in
this VM.

## 10. Status of each claim

| claim | status | where checked |
|-------|--------|---------------|
| cap-24 census complete: 3,056,896,064 states | computed, engine reproduces eight earlier caps exactly | Sections 4, 5 |
| 1,596,072 classes, 131,620 PU classes | computed | Sections 5, 7 |
| class C absent at cap 24 at three levels | computed, three tests | Section 6 |
| any path to class C needs an intermediate of length at least 25 | computed bounded negative | Section 6 |
| the T = 17 deficit is 12 at caps 23 and 24 | computed, both PU files with the same normal form | Section 7 |
| the T = 16 deficit is 0 at caps 23 and 24 | computed | Section 7 |
| deficits at T = 18 to 24 | arithmetic on computed counts | Section 7 |
| the engine agrees with round 4 at cap 23 | computed, checksum over 1.64e9 states and a byte-identical class list | Section 4 |
| peak memory 7.79 GB, 3860 s of breadth first time | measured by `/usr/bin/time -f` | Section 3 |

## 11. What the growth says, and the next test

[Argument] The state count went 219,042,976, 419,826,272, 1,638,542,144 and
3,056,896,064 for caps 21 to 24, so the factors are 1.917, 3.903 and 1.866. The
classes went 144,292, 258,032, 891,748 and 1,596,072, factors 1.788, 3.456 and
1.790. A single factor 3.903 followed by 1.866 is not a trend, so this run does
not predict cap 25, and the fact that the strata at total length 13 to 18 did
not move at all between caps 23 and 24 says that the growth is a boundary
effect at the top two strata. [Open] The obvious next test is the cap-25 census,
which needs a wider state key than 64 bits, and the question it would settle is
whether the T = 17 deficit of 12 closes at cap 25 or needs more.

## 12. When each PU class enters the box

[Computed] The five PU class lists of caps 20 to 24 are available, so each class
can be given the first cap at which it appears. The output format of `punf.py`
is one line per input class, so the lists are deduplicated by canonical form and
the minimal length is carried along; the deduplication reproduces the round-4
distribution at cap 23 exactly, which is the check that the five files are
comparable.

| PU classes first reached at cap | 20 | 21 | 22 | 23 | 24 | total |
|---------------------------------|---:|---:|---:|---:|---:|------:|
| count                           | 2,967 | 7,917 | 9,227 | 51,461 | 60,048 | 131,620 |

Broken down by minimal length:

| minimal length | cap 20 | cap 21 | cap 22 | cap 23 | cap 24 | total |
|----------------|-------:|-------:|-------:|-------:|-------:|------:|
| 13 | 2 | 0 | 0 | 0 | 0 | 2 |
| 14 | 5 | 0 | 0 | 0 | 0 | 5 |
| 15 | 35 | 0 | 0 | 0 | 0 | 35 |
| 16 | 40 | 0 | 0 | 3 | 0 | 43 |
| 17 | 206 | 3 | 1 | 7 | 0 | 217 |
| 18 | 246 | 11 | 7 | 8 | 3 | 275 |
| 19 | 1,209 | 151 | 30 | 50 | 12 | 1,452 |
| 20 | 1,224 | 164 | 19 | 78 | 27 | 1,512 |
| 21 | 0 | 7,588 | 362 | 497 | 113 | 8,560 |
| 22 | 0 | 0 | 8,808 | 1,206 | 108 | 10,122 |
| 23 | 0 | 0 | 0 | 49,612 | 3,320 | 52,932 |
| 24 | 0 | 0 | 0 | 0 | 56,465 | 56,465 |

[Computed, interpretation] The row for minimal length 16 shows the closure that
round 4 found: three classes entered at cap 23 and none at cap 24. The row for
minimal length 17 shows the stronger statement of Section 7: seven classes
entered at cap 23 and none at cap 24, so the box is saturated at that length and
no class counted by the deficit is reachable with intermediates of total length
at most 24. The rows for 18, 19 and 20 still gain at cap 24, which is why their deficits
fall, and the rows for 21 to 24 gain most of the new classes, which is expected
because a class of minimal length T needs the box to be at least as large as T.

## 13. The cap-25 attempt: the key, the bug, and the exact stopping point

[Computed] The 64-bit state key of rawbox4 and rawbox6 spends 8 bits on each
relator length, which leaves 48 bits for letters and therefore stops at 24
letters. `rawbox7.c` is rawbox6.c with 5 bits per relator length, which leaves 54
bits and covers T = 27. It reproduces the cap-15, cap-17 and cap-20 state counts
exactly and the cap-20 class list byte-identically (39,840 lines, `cmp` reports
no difference), so narrowing the length field is harmless.

[Computed, engine bug, found and fixed] The first cap-25 attempt exposed a defect
in rawbox6.c and rawbox7.c that the cap-24 run did not trigger. The flush wrote
the state file before compacting the run files. The state file records the run id
counter, and the compaction takes one more id, so a checkpoint written at a
compacting flush was stale by one id. A later `--resume` then reused the id of
the merged run file and truncated it. This happened at cap 25 and destroyed
3.3e9 states of that run. It did not happen at cap 24, and the reason is
checkable: the four stage calls of the cap-24 run ended at batches 1, 3, 16 and
20, the compactions fell at batches 13 and 17, and no resume followed a
compacting flush. Three independent counts of the cap-24 box agree exactly
(Section 4), and a truncated run would have broken that agreement. The fix moves
`compact_runs()` before `write_state()`, and it was checked on the exact
scenario: cap 22 with hmax = 2e7, stopped after nine batches (four compactions
already done), resumed, and taken to the fixed point, gives 419,826,272 states
and 419,826,272 in the run files.

[Computed, bounded] The second cap-25 attempt used the fixed engine with hmax =
200,000,000 and compaction at more than six runs. It ran two stages, reached
5,222,573,371 states at batch 34 with a frontier of 243,285,727 states and
14.0 GB of resident memory, and was stopped by the memory ceiling: a child
process was killed, and the engine reports `FATAL child failed`. The checkpoint
is consistent, because `rawbox7 count 25 1 w25` returns exactly the recorded
cumulative 5,222,573,371 over the four run files.

[Computed] The partial cap-25 set, which is a set of states reached from AK(3)
inside B(25) and therefore a sound lower bound:

| quantity | value |
|----------|------:|
| states | 5,222,573,371 |
| conjugation classes | 3,068,859 |
| PU classes | 390,826 |

States by total length: 13:2686, 14:12412, 15:183357, 16:232345, 17:1769946,
18:2229988, 19:13351373, 20:16022115, 21:91323650, 22:106079398, 23:590969070,
24:680076671, 25:3720320360, summing exactly to the state count. PU classes by
minimal length: 2, 5, 35, 40, 203, 254, 1295, 1356, 7457, 9160, 45415, 55760
and 269844 for minimal lengths 13 to 25.

[Computed, and the reason the partial set settles nothing] The partial set is not
a superset of the cap-24 box. Its count of PU classes of minimal length 17 is
203, against 217 in the cap-24 box, because a partial breadth first search stops
at a distance and a state of the cap-24 box can sit further away in the larger
box. So the partial set cannot be used to say that a class is missing, and it
cannot be used to improve the T = 17 deficit of Section 7 in either direction.
What it does say is a set of lower bounds: the cap-25 box holds at least
5,222,573,371 states, at least 3,068,859 conjugation classes, at least 390,826 PU
classes, and at least 269,844 PU classes of minimal length 25.

[Argument] The cap-25 box is much larger than the cap-24 box, and the partial
set shows where the growth is: the stratum of total length 25 already holds
3,720,320,360 states while the strata of length 23 and 24 hold 590,969,070 and
680,076,671 against their cap-24 final values of 1,207,646,336 and 1,411,296,448.
If the length-25 stratum grows as the length-24 stratum did after the same point
of its traversal, the cap-25 box is of the order of 8e9 states, and its run files
would be 64 GB. The memory floor of the present design is two arrays of the size
of the frontier, because the children read the frontier from memory and the
survivors of a round have to be held somewhere; at a frontier of 243M keys that
is 3.9 GB before the batch set H is counted.

[Argument] The repair the next attempt needs is a disk-resident frontier. The
children already read the frontier in a strided order, so each child can read a
frontier file sequentially and take every fourth key, and the parent can stream
the frontier file again at the flush to intersect it with the new part of the
batch set. That removes both frontier arrays and leaves the batch set as the only
large allocation, which at hmax = 2e8 is 1.6 GB plus the merge room. The two
other requirements are a flush triggered by a byte budget rather than a key
count, and enough disk: 64 GB of run files plus the transient compaction copy,
which the binary-counter compaction of Section 3 needs.

Commands and files of the attempt:

    gcc -O3 -march=native -o rawbox7 rawbox7.c
    mkdir -p w25 && ./rawbox7 bfs 25 1 w25 --procs 4 --hmax 200000000 --batchsec 900 --maxsec 1700
    ./rawbox7 bfs 25 1 w25 --procs 4 --hmax 200000000 --batchsec 900 --maxsec 1700 --resume
    ./rawbox7 count 25 1 w25            # 5,222,573,371
    for i in 0 1 2 3; do ./rawbox7 scan 25 1 w25 w25/p$i.txt $i 4 2>w25/s$i.err & done; wait
    cat w25/p?.txt | LC_ALL=C sort -u > w25/classes.txt    # 3,068,859 lines
    python3 punf.py w25/classes.txt w25/pu25.txt --procs 4  # 390,826 distinct

`results/cap25_attempt.log` holds the console transcript of both attempts,
`results/state25_partial.txt` the state file of the second, and
`results/classes25_partial.txt.gz` the class list of the partial set. The 42 GB
of run files of the partial set stay at .ultramath/smw38010i/m1/cap24/w25/.
