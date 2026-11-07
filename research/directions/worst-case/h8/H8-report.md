# H8: the length-5-relator family, the exact multiplication count, and where the invariants stop

Direction H8 of round 5, member m5. Every claim below carries a label.
**VERIFIED** means a command in Section 10 reruns it and the output is quoted
there. **COMPUTED** means a computation of this direction whose code is in
`directions/worst-case/h8/` and whose output is quoted. **ARGUMENT** means a
deduction from stated facts. **CONJECTURE** means nothing more. No claim about
the truth of the Andrews-Curtis conjecture is made anywhere in this file.

## 0. Summary

1. The exact minimum number of relator multiplications is now known for every
   one of the 52,744 solved presentations, as a minimum over **all** twelve-move
   paths that keep the total relator length at most 15 and not only over the
   move-minimal certificates. The maximum is 17 and it is attained by exactly
   the 16 presentations that carry more than 40 moves, which are exactly the
   16 presentations whose round-4 minimal certificate uses 17 multiplications.
   At cap 14 the maximum is also 17, with 24 presentations attaining it.
   **VERIFIED**
2. Adding the left multiplications and the multiplications by an inverse relator
   (the residual gap named in round 4) changes no count at any of the 52,744
   presentations, and the ball keeps exactly the same 58,487,624 states at cap
   15. The 16 hard cases still need 17. **VERIFIED**
3. The cheapest lower bound, the abelian exponent-vector bound, is 3 on all 16
   hard cases and at most 12 anywhere in the sample. The bound is honest and it
   is far below the truth. The exact count is not a function of the abelian data
   at all: 5,900
   of the 8,992 abelian classes present in the cap-15 ball carry presentations
   with different counts, and the hard cases' own abelian class contains
   presentations that need 3 multiplications. **VERIFIED**
4. The mechanism visible in the shortest certificates is one-letter eating. Each
   multiplication inserts the short relator and the cancellation at the seam
   removes one letter of the long relator, and the length change at a
   multiplication is exactly minus one in 179,150 of the sample's multiplication
   steps. **COMPUTED**, and the account is an **ARGUMENT** from the printed
   trace in Section 5.
5. The family is not characterised by the length of the short relator. Inside
   the 3,168 presentations with a relator of length 5 the exact count ranges
   from 2 to 17 with median 5, and 392 presentations share the finer profile of
   the 16 (a length-5 relator of exponent-vector norm 1 next to a length-9
   relator of norm 3) while their counts range from 3 to 17. What length 5 does
   is to supply the largest maximum that fits inside total length 14.
   **VERIFIED**
6. Beyond the total lengths of the solved sample the same growth continues. Over
   the whole cap-15 ball the maximum is 23, attained in the bucket with relator
   lengths 5 and 10 at the presentation `bABaa,BBABabbaaa` and in the bucket
   (10,5) at `BAAbAbaaaa,BBAba`. The buckets with a relator of length 1 grow
   linearly, with the bucket (1,L) reaching L. **VERIFIED**
7. The limits are recorded in Section 9. No general lower bound beyond the
   abelian one is proved here, the exact values hold for paths inside total
   length 15 and never claim anything beyond it, and the conjugacy-class
   quotient was tried as a lower-bound framework and is a dead end with a
   precisely measured failure.

## 1. Conventions

The rank-2 free group is on `a` and `b`. Letters are `1 = a`, `-1 = A`, `2 = b`,
`-2 = B`, and a word is freely reduced. A presentation is an ordered pair of
words, relator 0 and relator 1. Total length is the sum of the two relator
lengths.

The move system is the twelve-move system of `directions/c14` and of
`directions/worst-case/wcase.py`: invert one relator, conjugate one relator by
one generator on the left and its inverse on the right (four conjugators for
each relator), and multiply one relator on the right by the other. A
**multiplication** is one of the two moves `m0` and `m1`. The **cap** is the
largest total length a state of a path may have. The quantity computed in this
file is, for a presentation `s` and a cap `C`, the least number of
multiplications over all paths from `s` to the standard pair `(a,b)` whose
states all have total length at most `C`. Section 8 adds the left
multiplications and the multiplications by an inverse relator to the system.

The sample is the 52,744 presentations of `directions/c14/certs_12.txt`,
`certs_13.txt` and `certs_14.txt`, listed with their round-4 minimal
certificates in `directions/worst-case/min_cap14.txt` and `min_cap15.txt`.

## 2. Engines and the checks that were run on them

### 2.1 The engine

`h8/multmin.c` is a 0-1 BFS from the standard pair in the **reverse** twelve-move
system. A reverse move is the inverse of a forward move. The reverse of a
multiplication is not a multiplication (it is `r0 -> r0 r1^{-1}` and
`r1 -> r1 r0^{-1}`), and that edge costs one, because traversing it corresponds
to one forward multiplication. Every other reverse edge costs zero, because
inversions and conjugations are not multiplications. Cost layers are processed
in increasing order and the zero-cost closure of a layer is exhausted before the
next layer starts, so the first cost assigned to a state is its minimum. A state
that a one-cost edge put in the next layer can still be claimed by a zero-cost
edge of the current layer, and the program handles that by lowering the cost and
pushing the state into the current layer with a stale-entry test at pop time.

`h8/agg.c` is the same engine with a final pass that groups all states of the
ball by relator lengths and exponent vectors and records the least and the
greatest count in each group. `h8/multmin.c` also has a forward mode (`FWD=1`)
that computes the same quantity from the other end, by counting forward
multiplications on forward paths from a stated root, and a root option
(`ROOT=pair`) for that purpose.

### 2.2 The state counts agree with the recorded ones

The number of states in the ball is an independent check on the state encoding,
because it was recorded in rounds 3 and 4 with a different engine. The counts
agree at every cap where a record exists. **VERIFIED**

| cap | this engine | recorded |
| ---: | ---: | ---: |
| 11 | 700,712 | 700,712 |
| 12 | 1,582,280 | 1,582,280 |
| 13 | 6,476,104 | 6,476,104 |
| 14 | 14,399,816 | 14,399,816 |
| 15 | 58,487,624 | 58,487,624 |

### 2.3 The costs agree with a reference Dijkstra

`h8/dijk.py` is a straightforward Dijkstra with a heap over the same reverse
graph, written without cost layers. At caps 8 and 9 the two programs agree on
every state of the ball, which is 18,344 states at cap 8 and 74,856 states at
cap 9, with zero mismatches. **VERIFIED**

### 2.4 The forward and the reverse computations agree

Nine states are tabulated below, and all sixteen extremal presentations of
Section 7 were checked the same way with the counts stated there. In every case
the forward mode with that state as root and the reverse mode from the standard
pair give the same count, and the forward mode explores the same 58,487,624
states. **VERIFIED**

| presentation | forward count | reverse count |
| --- | ---: | ---: |
| `BBabA,BBABAbaaa` | 17 | 17 |
| `bABaa,BBABabbaaa` | 23 | 23 |
| `BAAbAbaaaa,BBAba` | 23 | 23 |
| `bABaba,BBabbAbaa` | 21 | 21 |
| `ABAbbaa,bbAAbaaa` | 16 | 16 |
| `b,bbbbbbbbbbbbba` | 14 | 14 |
| `ba,bbbbbbaaaaaaa` | 8 | 8 |
| `BBBBBBa,Aba` | 6 | 6 |
| `BBBBBa,Aba` | 5 | 5 |

### 2.5 Three defects found in my own code by these checks

The first version of the 0-1 BFS assigned a state's cost at first discovery and
never lowered it, so a state reached by a one-cost edge early in a layer kept
that cost even when a zero-cost chain of the same layer reached it. The
reference Dijkstra exposed this, and the layer rule above is the fix. The second
defect was a four-integer buffer for the root word of the forward mode, which
overflowed for roots of length five or more. It produced a forward count of 3
for `BBBBBa,Aba` where the reverse computation gives 5, and it failed to find
the goal at all from `BBBBBBa,Aba` where the reverse computation gives 6. The third defect was in the class-graph
experiment of Section 9: it rotated a word before cyclic reduction, which
identified words of different conjugacy classes, and a brute-force BFS over the
class graph exposed it. All three were mine, all three were found by a check
that is quoted here, and the numbers in this report come from the corrected
programs.

## 3. The exact minimum multiplication count

### 3.1 The sample

The counts at cap 15 for the 52,744 presentations. **VERIFIED**

| multiplications | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 15 | 17 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| cap 15 | 320 | 5,093 | 5,800 | 18,946 | 7,956 | 9,327 | 1,901 | 2,442 | 380 | 293 | 101 | 25 | 88 | 56 | 16 |
| cap 14 | 320 | 5,077 | 5,776 | 18,953 | 7,969 | 9,318 | 1,892 | 2,459 | 399 | 293 | 94 | 26 | 88 | 56 | 24 |
| round-4 certificates | 214 | 3,402 | 4,902 | 18,225 | 8,544 | 11,060 | 2,177 | 3,008 | 478 | 388 | 135 | 43 | 96 | 56 | 16 |

The last row is the number of multiplications in the move-minimal certificates
of round 4, quoted for comparison. Two facts follow. Move-minimal certificates
do not minimise multiplications: in 6,123 presentations the certificate uses
more multiplications than the cap-15 minimum, by up to 8. And the maximum of 17
survives the passage from "in a shortest path" to "over all capped paths",
which is the strengthening of the round-4 statement. **VERIFIED**

At cap 13 only 22,104 presentations are inside the ball, exactly the 4,376 of
length 12 and the 17,728 of length 13. So every presentation of total length 12
or 13 lies in the cap-13 ball and none of length 14 does, which is what the
round-4 l-increase table says. Their histogram at cap 13 is
`1:320 2:1133 3:5207 4:5331 5:6065 6:1876 7:1500 8:306 9:267 10:55 11:16 12:28`.
**VERIFIED**

### 3.2 The 16 hard cases

All 16 presentations above 40 moves need exactly 17 multiplications at cap 15
and exactly 17 at cap 14, so the 17 of their certificates is optimal and not an
artefact of the move count. **VERIFIED**

| presentation | moves | certificate multiplications | exact at cap 15 | abelian bound |
| --- | ---: | ---: | ---: | ---: |
| `BBabA,BBAAAbaBa` | 45 | 17 | 17 | 3 |
| `BBAba,BAAAABaaa` | 44 | 17 | 17 | 3 |
| `BBAba,BBaBabAAA` | 44 | 17 | 17 | 3 |
| `BBAba,BBaaabABA` | 44 | 17 | 17 | 3 |
| `BBBAbabaa,BAAba` | 44 | 17 | 17 | 3 |
| `BBBabAbAA,BAAba` | 44 | 17 | 17 | 3 |
| `BBabA,BBABAbaaa` | 44 | 17 | 17 | 3 |
| `BBAba,BAAABaaaa` | 43 | 17 | 17 | 3 |
| `BBBBAbbbA,BAbaa` | 43 | 17 | 17 | 3 |
| `BBabA,BAAAABaaa` | 43 | 17 | 17 | 3 |
| `BBBAAbAba,BAbaa` | 42 | 17 | 17 | 3 |
| `BBBBAbbbA,BAAba` | 42 | 17 | 17 | 3 |
| `BBBBabbba,BAAba` | 42 | 17 | 17 | 3 |
| `BBBBabbba,BAbaa` | 42 | 17 | 17 | 3 |
| `BBabA,BAAABaaaa` | 42 | 17 | 17 | 3 |
| `BBBaababA,BAbaa` | 40 | 17 | 17 | 3 |

### 3.3 The whole cap-15 ball

The maximum over all 58,487,624 states of the ball is 23, and only the buckets
with relator lengths 5 and 10 reach it. The ball is larger than the sample, so
these statements are about presentations outside the solved sample and carry no
claim of trivialisability beyond what the count itself says. **VERIFIED**

## 4. The cheap lower bound and the exact point where it fails

### 4.1 The abelian bound

For a presentation with relator exponent vectors `v0` and `v1` in `Z^2`, the
available exponent-vector moves are a sign flip (an inversion, which costs no
multiplication) and the addition of one vector to the other (a multiplication).
Conjugations do not change the vectors. The least number of additions that
brings `(v0,v1)` to `(+-e1,+-e2)`, with `e1=(1,0)` and `e2=(0,1)`, is therefore
a lower bound for the number of multiplications in any twelve-move path, with or
without a cap. **ARGUMENT**

`h8/abelian.py` computes that bound exactly for every presentation of the sample
by a Dijkstra over the exponent-vector pairs, with the sign flips free and the
coordinates bounded far beyond the values that occur. **COMPUTED**

| bound | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| presentations | 5,960 | 4,658 | 13,747 | 7,639 | 10,842 | 3,312 | 4,045 | 853 | 1,344 | 152 | 184 | 4 | 4 |

The bound equals the exact cap-15 count in 22,745 presentations and is strictly
smaller in the other 29,999. The largest gap is 14, and it is attained exactly by
the 16 hard cases, where the bound is 3 and the truth is 17. **VERIFIED**

### 4.2 The bound is the best that an abelian argument can give

The count is not a function of the abelian data, so no argument that reads only
the exponent vectors can reach the truth. `h8/agg.c` groups the whole cap-15 ball
by relator lengths and exponent vectors and records the least and the greatest
count in each group. There are 8,992 groups, 5,900 of them carry at least two
different counts, and 96.3 percent of the 58,487,624 states live in such a
group. The largest spread inside one group is 22. The group of the hard cases,
with relator lengths 5 and 9 and exponent vectors `(0,-1)` and `(1,-2)`, contains
10,704 states whose counts run from 3 to 21, and the hard cases sit at 17.
**VERIFIED**

This is the exact point where the cheap argument stops. A lower bound of 17
would have to read the words and not only their abelian images.

## 5. The mechanism in the shortest certificates

The 44-move certificate of `BBabA,BBABAbaaa` from round 4, replayed by this
direction with a replayer written here, has 17 multiplications. The length
change at each of them is below. **COMPUTED**

| multiplication | relator replaced | relator lengths before | after | total change |
| ---: | ---: | --- | --- | ---: |
| 1 | 1 | 5+9 | 5+8 | -1 |
| 2 | 1 | 5+8 | 5+9 | +1 |
| 3 | 1 | 5+9 | 5+10 | +1 |
| 4 | 1 | 5+10 | 5+9 | -1 |
| 5 | 1 | 5+9 | 5+8 | -1 |
| 6 | 1 | 5+8 | 5+9 | +1 |
| 7 | 1 | 5+9 | 5+10 | +1 |
| 8 | 1 | 5+10 | 5+9 | -1 |
| 9 | 1 | 5+9 | 5+10 | +1 |
| 10 | 0 | 5+8 | 7+8 | +2 |
| 11 | 1 | 7+8 | 7+3 | -5 |
| 12 | 0 | 7+3 | 6+3 | -1 |
| 13 | 0 | 6+3 | 5+3 | -1 |
| 14 | 0 | 5+3 | 4+3 | -1 |
| 15 | 0 | 4+3 | 3+3 | -1 |
| 16 | 0 | 3+3 | 2+3 | -1 |
| 17 | 0 | 2+3 | 1+3 | -1 |

Ten of the seventeen multiplications end with a net loss of exactly one letter,
and the only large change is the multiplication numbered 11, which removes five
letters at once. Over all 52,744
round-4 certificates the length change at a multiplication is distributed as
`-7:346 -6:473 -5:4326 -4:2737 -3:25611 -2:15053 -1:179150 0:6662 +1:18883
+2:1436 +3:592 +4:218 +5:62 +6:1`, so minus one is the single most common
outcome by a factor of seven over the next. **VERIFIED**

The reading is this. A conjugation can only cyclically reduce a relator, at most
two letters at a time, and the only move that brings new material to the seam is
a multiplication. The short relator is the tool that eats the long one, one
letter per bite, because the seam overlap that the product can cancel is one
letter long in these presentations. The count is then the number of bites the
long relator needs, and that number is a property of the two cyclic words and of
the cap. **ARGUMENT** from the trace and the histogram, with the last sentence
qualified by Section 4.2: the bites are not visible in the abelian data.

## 6. The family

Three statements hold about the 16 hard cases, and one statement that round 4
made about them does not survive. **VERIFIED**

First, all 16 have a relator of length 5 and the other relator has length 9,
with the short one in first place in 8 cases and in second place in the other 8.
Second, the exponent-vector norm of the short relator is 1 in all 16 and the norm
of the long relator is 3 in all 16. Third, the 16 are exactly the presentations
above 40 moves and exactly the presentations at the maximum count of 17, so the
three properties coincide on the sample.

What does not survive is the reading that the short relator forces the
multiplications. Inside the 3,168 presentations with a relator of length 5 the
exact count has the distribution
`2:16 3:221 4:749 5:610 6:580 7:399 8:132 9:126 10:57 11:97 12:21 13:88 15:56
17:16`, with median 5. Inside the 2,012 presentations whose relator lengths are
5 and 9 in either order, and which in addition have the hard cases' profile of
the exponent-vector norms 1 and 3, there are 392 presentations whose counts have
the distribution `3:69 4:73 5:79 6:12 7:15 8:7 9:25 10:3 11:37 13:40 15:16
17:16`. The length-5 property and the correct exponent vectors are therefore
necessary on the sample and far from sufficient.

## 7. Beyond length 5

The solved sample stops at total length 14. The buckets of total length 14 are
(1,13), (2,12), (3,11), (4,10), (5,9), (6,8) and (7,7), and the sample contains
the four of them (1,13), (5,9), (7,7) and (9,5). The
bucket maximum is not monotone in the split, and the largest of them is (5,9) at
17, which is why the length-5 family owns every case above 40 moves in the
sample. The question whether the phenomenon is specific to length 5 is therefore
a question about the buckets that do not fit in total length 14, and the cap-15
ball answers it for total length 15. **VERIFIED**

The bucket maxima over the whole cap-15 ball, with one extremal presentation for
each bucket, are below. The count is the minimum number of multiplications for
that presentation.

| lengths | maximum | extremal presentation (least state key) |
| --- | ---: | --- |
| 1, 14 | 14 | `b,bbbbbbbbbbbbba` |
| 1, 13 | 13 | `b,bbbbbbbbbbbba` |
| 1, 12 | 12 | `b,bbbbbbbbbbba` |
| 2, 13 | 8 | `ba,bbbbbbaaaaaaa` |
| 3, 12 | 12 | `Aba,bbbbbbbbbbba` |
| 4, 11 | 12 | `bbba,bAAAAbaaaaa` |
| 5, 10 | 23 | `bABaa,BBABabbaaa` |
| 6, 9 | 21 | `bABaba,BBabbAbaa` |
| 7, 8 | 16 | `ABAbbaa,bbAAbaaa` |
| 8, 7 | 16 | `bbbaBBaa,ABAbaaa` |
| 9, 6 | 21 | `bAAAbaaaa,BAbaba` |
| 10, 5 | 23 | `BAAbAbaaaa,BBAba` |
| 11, 4 | 12 | `BBBBabbbbba,baaa` |
| 12, 3 | 12 | `baaaaaaaaaaa,Bab` |
| 13, 2 | 8 | `bbbbbbbaaaaaa,ba` |
| 14, 1 | 14 | `baaaaaaaaaaaaa,a` |

The presentation of each row is the least state key that attains the maximum of
its bucket, so the table is reproducible, and all sixteen counts are confirmed
by the forward mode of Section 2.4. **VERIFIED**

Three readings follow, and each is a statement about the cap-15 ball only.
**VERIFIED** for the numbers, **ARGUMENT** for the readings.

The growth with the length of the long relator is not confined to length 5. Both
the (5,10) and the (10,5) buckets reach 23 and both the (6,9) and the (9,6)
buckets reach 21, so the pattern continues past the sample's budget. The buckets
with a relator of length 1 grow linearly, and the bucket (1,L) reaches L for
every L from 2 to 14 and reaches 3 at L = 1, which
is the cleanest case of the mechanism of Section 5: a primitive relator can eat
one letter per multiplication and the long relator has no other way to shorten.
The length-5 family of round 4 is not a special length. It is the bucket with
the largest maximum among those that fit inside total length 14.

## 8. The full multiplication set

Round 4 named the residual gap of the move system precisely: the twelve-move
system has no left multiplication `r0 -> r1 r0` and no multiplication by an
inverse relator `r0 -> r0 r1^{-1}`. `multmin.c` with `MULT4=1` adds the reverses
of all eight multiplication types to the reverse system, so the forward system
contains the right multiplications, the left multiplications, and both of them
with an inverse relator. **VERIFIED**

The ball is unchanged. At every cap from 9 to 15 the state count is the same as
in the twelve-move system, namely 74,856 at cap 9, 169,992 at cap 10, 700,712 at
cap 11, 1,582,280 at cap 12, 6,476,104 at cap 13, 14,399,816 at cap 14 and
58,487,624 at cap 15. The counts are
unchanged for all 52,744 presentations at cap 15, and for the 22,104 inside cap
13 at cap 13. The 16 hard cases still need 17. The maximum over the ball is
still 23. **VERIFIED**

So for these presentations and inside these caps the residual gap does not
reduce the number of multiplications. This does not close the gap in general,
because a path that leaves the cap is not covered, and because a conjugation by
a word of two or more letters is not one of the moves computed here.

## 9. What this direction does not settle

1. No general lower bound beyond the abelian one is proved. The exact values are
   computed, and they are not an argument. The abelian bound fails by 14 on the
   hard cases and Section 4.2 shows that no abelian refinement can repair it.
   A lower bound of the true size has to read the cyclic words.
2. The exact values are minima inside a cap. A path that leaves total length 15
   and returns could in principle use fewer multiplications, and nothing here
   excludes it. The values at caps 13, 14 and 15 are given separately so that
   the dependence on the cap is visible, and the value for `BBabA,BBABAbaaa` is
   17 at both cap 14 and cap 15.
3. Conjugation by a word of two or more letters is not in the computed system.
   At total length 14 with a cap of 15 such a move can act only when it shortens
   a relator by at least three letters, so the omissions are restricted, but
   they are not empty and no claim is made about them.
4. The conjugacy-class quotient was tried as a lower-bound framework and it
   fails. The idea is to quotient by conjugation, since conjugations cost no
   multiplication, and to run the same search on pairs of conjugacy classes.
   The quotient is too permissive inside a cap, because a conjugation that leads
   out of the cap is not a legal move there, and the quotient cannot see the
   cap. `h8/cg.py` with a heap search over the class graph gives 16 for all 16
   hard cases against the true 17, and it agrees with the truth on 20 of 20
   randomly chosen control presentations. That agreement on the controls and the
   failure on exactly the hard cases is the recorded dead end. As an upper bound
   in the uncapped system with long conjugations the same path gives an
   **ARGUMENT** that 16 multiplications suffice for each hard case, and no
   certificate for that statement was materialised, so the statement is not
   claimed as verified. **COMPUTED** for the class-graph distances, the rest is
   **ARGUMENT**.
5. The 16 hard cases are a property of the solved sample and not a classification
   theorem. The cap-15 ball contains presentations with a strictly larger count,
   up to 23, and no trivialisation certificate for any of them is known to this
   direction.

## 10. Files, commands and output

Everything is in `directions/worst-case/h8/`. The engines are C with no
dependency beyond libc, and the analysis scripts are Python 3 with no dependency
beyond the standard library. The runner `run_h8.sh` reruns the whole chain.

| file | content |
| --- | --- |
| `multmin.c` | the 0-1 BFS engine, reverse and forward modes, `MULT4` extension, per-target output, bucket maxima with extremal states |
| `agg.c` | the same engine followed by the grouping by relator lengths and exponent vectors |
| `dijk.py`, `py01.py` | the independent Python Dijkstra and its graph, used to check the C engine at caps 8 and 9 |
| `words.py` | the word model, written from the definitions |
| `analyze.py`, `costs.py`, `tables.py`, `abelian.py` | the analyses of Sections 3 to 7 |
| `cg.py`, `materialise.py` | the conjugacy-class experiment of Section 9, including the failed materialisation |
| `cost13.txt`, `cost14.txt`, `cost15.txt`, `cost15m4.txt`, `cost13m4.txt` | the exact minimum multiplication count per presentation, one line per presentation |
| `agg15.txt` | the grouping of the whole cap-15 ball by relator lengths and exponent vectors |
| `argmax15.txt` | the bucket maxima with their extremal presentations |
| `facts.out`, `costs.out`, `abelian.out`, `tables.out` | the printed tables of this report |

The commands, with the key output of each. **VERIFIED**

```
$ gcc -O2 -o multmin multmin.c
$ gcc -O2 -o agg agg.c
$ ./multmin 15 targets.txt cost15.txt
   states 58487624 maxcost 23
   targets: 52744 found, 0 missing
$ MULT4=1 ./multmin 15 targets.txt cost15m4.txt
   states 58487624 maxcost 23
   targets: 52744 found, 0 missing
$ ./multmin 14 targets.txt cost14.txt
   states 14399816 maxcost 18
$ ./multmin 13 targets.txt cost13.txt
   states 6476104 maxcost 12
   targets: 22104 found, 30640 missing
$ ./agg 15 > agg15.txt
   states 58487624 maxcost 23 agg keys 8992
$ python3 check_dijk.py 8
   cap 8 mult4 False: compared 18344 states, mismatches 0
$ python3 check_dijk.py 9
   cap 9 mult4 False: compared 74856 states, mismatches 0
$ ROOT="BBabA,BBABAbaaa" FWD=1 ./multmin 15 goalt.txt fwd_out.txt
   states 58487624 maxcost 39 time 31.31
   BBabA,BBABAbaaa  cost 17
$ python3 costs.py
   min-multiplication histogram, cap 15: {1: 320, 2: 5093, ... 15: 56, 17: 16}
   cases where the minimal-move certificate uses more multiplications than
   the cap-15 minimum: 6123, max excess 8
$ python3 abelian.py
   shear bound histogram {0: 5960, ..., 12: 4}
   gap 14  BBabA,BBABAbaaa  bound 3 exact 17
$ python3 tables.py
   the tables of Sections 5, 6 and 7
```

The `targets.txt` file is a copy of `directions/worst-case/data/all_targets.txt`,
which lists the 52,744 presentations of the sample. `goalt.txt` holds the single
line `goal<TAB>a,b` and is the query used by the forward mode.

## Appendix: the complete bucket table of the cap-15 ball

Rows are the length of relator 0, columns are the length of relator 1, and the
entry is the maximum over the bucket of the minimum multiplication count. The
table is printed by `./multmin 15` and is the source of Section 7. **VERIFIED**

```
len 1: 1:3 2:2 3:3 4:4 5:5 6:6 7:7 8:8 9:9 10:10 11:11 12:12 13:13 14:14
len 2: 1:2 3:3 5:4 7:5 9:6 11:7 13:8
len 3: 1:3 2:3 3:3 4:4 5:5 6:6 7:7 8:8 9:9 10:10 11:11 12:12
len 4: 1:4 3:4 5:6 7:8 9:10 11:12
len 5: 1:5 2:4 3:5 4:6 5:6 6:8 7:11 8:16 9:22 10:23
len 6: 1:6 3:6 5:8 7:15 9:21
len 7: 1:7 2:5 3:7 4:8 5:11 6:15 7:16 8:16
len 8: 1:8 3:8 5:16 7:16
len 9: 1:9 2:6 3:9 4:10 5:22 6:21
len 10: 1:10 3:10 5:23
len 11: 1:11 2:7 3:11 4:12
len 12: 1:12 3:12
len 13: 1:13 2:8
len 14: 1:14
```

Both parities of the length sum occur, and the table has no parity restriction
that this direction can state as a fact. **COMPUTED**
