# Second referees 4: an independent audit of the round-4 artifacts

Round 5, direction H9, member m10. I wrote my own implementations of the
objects first, from the definitions printed in the targets, and read the
targets' code only afterwards. The code of this audit is in `code/` and the
recorded outputs are in `logs/`. Nothing in this file is a claim of a proof or
a disproof of the Andrews-Curtis conjecture.

## 0. Verdicts

| target | verdict | independent reproduction made here | not audited here |
|---|---|---|---|
| (a) `directions/cap21` | **SOUND**, with two documentation defects and one under-argued step | the cap-20 box exactly, the class list as a set, the PU normal form at caps 20 and 21, class C at four caps, the deficit arithmetic, Table 1 of the source | the cap-21, cap-22 and cap-23 breadth-first runs |
| (b) `directions/resisters/round4` | **SOUND** where audited | the 452,593-key target exactly, all 98 certificates, five component negatives at cap 23 | the cap-22, cap-24 and cap-25 runs |
| (c) `directions/psl27-frontier` | **SOUND** for the permutation half | all four permutation certificates, the group order and the stabiliser order | the Reidemeister-Schreier matrix and its integer vector |
| (d) `directions/worst-case` | **SOUND** | the exact distances, the asymmetry, all 105,492 certificate lines, a 15-case minimality sample | the l-increase files, the cap-16 probe |
| (e) `directions/p-trivial` | **SOUND** for the three certificates | all three, with their move counts and peak lengths | the exhaustive negatives, the box counts |
| (e) `directions/ac-graph-diameters` | **SOUND** for one value | the diameter of Delta_2(A5), independently recomputed | the other seven groups, the orbit reduction |
| (f) the two unsubmitted drafts | not audited, except the resister material inside (b) | none | `second-referees-3`, `qdouble-star/m9` |

## 1. Method and the two state conventions

Two conventions occur in the repository and a referee has to keep them apart.
In the ordered convention a state is the ordered pair `(u,v)` of reduced
relators. In the unordered convention `(u,v)` and `(v,u)` are one state. Both
conventions appear in the round-4 artifacts, and at small caps the two counts
can coincide, so a check at one cap alone does not settle which one a target
used.

My own census `code/census.c` has both modes and four multiplication forms,
`u <- uv`, `v <- vu`, `v <- uv` and `u <- vu`, while the target engines use the
two right multiplications of arXiv:1609.00325 and of `reslib.moves`. The four
forms gave exactly the two-form counts in every box I tested, which is
evidence that the extra forms stay inside the closure at these caps.

The ordered convention is the one the round-4 engines use. My cap-13 and cap-15
runs reproduce the target numbers 168 and 6,864 in both conventions, because at
those caps the reachable set is not swap closed. At cap 17 the ordered count is
857,808 and the unordered one is 428,904, and the target's 857,808 is the
ordered figure.

## 2. Target (a), the cap-21 census

### 2.1 The cap-20 box reproduced exactly

`code/census.c` in ordered mode, run from AK(3) = `(x y x y^-1 x^-1 y^-1,
x^3 y^-4)` at cap 20, prints

    states 51411456 depth 145
    states_by_total 13:4032 14:15424 15:241856 16:336288 17:2520832 18:3280096 19:20185152 20:24827776
    classes 39840
    classes_by_keylen 13:12 14:40 15:516 16:556 17:2844 18:3228 19:15620 20:17024
    WALL 118.45 RSS 3175876 KB

Every figure equals the cap-20 row of `directions/cap21/results/cap20.out`. My
class list, sorted, has 39,840 lines, and `diff` against the sorted
`directions/cap21/results/classes20.txt` is empty: 0 differing lines. The
cap-15 class lists also agree as sets, 26 lines on each side, and the cap-17
and cap-18 counts 857,808 and 2,014,992 with 1,000 and 2,128 classes are
reproduced in ordered mode. This is the strongest single check in this audit,
because it fixes the move set, the canonical form and the box discipline of the
target at one cap exactly.

### 2.2 Class C

The eight class-C rows of `directions/c14/final_classes.txt` labelled
`resisting-exhausted-cap17` give eight distinct conjugation classes under the
definition the target itself uses, namely the unordered pair of conjugacy
classes of relators. My computation of their canonical pairs is

    xxyxyyy,xyXyxY   xxyyyxy,xyXyxY   xxxyxyy,xyXyxY   xxxyyxy,xyXyxY
    xxxYxYY,xyxYXY   xxxYYxY,xyxYXY   xxYxYYY,xyxYXY   xxYYYxY,xyxYXY

with all eight in the letter convention of `directions/cap21/punf.py`. None of
the eight occurs in the class list at cap 20, 21, 22 or 23. The box has 12
classes of minimal key length 13 at every cap, and the twelve are exactly the
12 rows of `final_classes.txt` at length 13 labelled `ak3-equivalent` (6) and
`resisting-budget-cap19` (6). At the PU level all eight rows have the single
canonical form `(x^3 y x y^2, x y x^-1 y x y^-1)` under my own normal form of
Section 2.4, and that form is absent from the cap-21 PU list. So the negative
conclusion of the target stands at all four caps. The count of eight classes
is a description error, and the test itself is unaffected because `checkC.py`
tests all eight keys.

### 2.3 Defect 1: the count of conjugation classes of class C

`directions/cap21/cap21.md` line 172 reads "The eight rows form two conjugation
classes." Under the report's own definition in Section 5 of the same file the
number is eight, as the list above shows. The sentence is not used in the
argument, since the test is a membership test of all eight keys, and
`checkC.py` does test all eight. The correction is to replace "two" by "eight",
and to say that the eight collapse to one class at the PU level.

### 2.4 The PU normal form, reproduced at caps 20 and 21

The relation of arXiv:1609.00325 Section 4.2 is the transitive closure of the
swap, the inversion of one relator, the conjugation of one relator, and the
diagonal action of Aut(F_2). The normal form minimises the total length and
then takes the least pair of cyclic least forms. The quoted Whitehead theorem
makes the minimisation reachable by single Whitehead automorphisms with
non-increasing total length, so an implementation that searches over all 20
Whitehead automorphisms of F_2 is correct by that theorem.

`directions/cap21/punf.py` searches over 16 elementary maps. Thirteen of them
are Whitehead automorphisms: seven of the eight length-preserving maps and six
of the twelve non-length-preserving ones. Three entries are automorphisms that
are not Whitehead automorphisms, namely `x -> x, y -> xY`, `x -> x, y -> Yx`
and `x -> y, y -> Xy`. Six of the twelve non-length-preserving Whitehead
automorphisms are missing, for instance `x -> x, y -> Xyx` and
`x -> Yxy, y -> y`. The report's own Section 8.4 records that completeness is
tested and not proved, which it states honestly.

My own normal form `code/punf.c` uses the complete set of 20: eight
length-preserving maps and twelve multiplier maps, enumerated from the
definition and filtered by the determinant test. On the target's own class
lists it returns

| cap | inputs | distinct canonical forms | my list against `punf.py` |
|---|---|---|---|
| 20 | 39,840 | 2,967 | the map form to minimal length is identical |
| 21 | 144,292 | 10,884 | the map form to minimal length is identical |

with the minimal-length distributions 2, 5, 35, 40, 206, 246, 1209, 1224 and
2, 5, 35, 40, 209, 257, 1360, 1388, 7588. So the incomplete generator set of
`punf.py` costs nothing on this data, and the PU class counts used by the
target are confirmed by an implementation whose correctness rests on the
Whitehead theorem, with the invariance test kept as a check. A referee should
still ask for the 20-map set in a future version, because the present
justification of canonicity is a 300-case invariance test.

### 2.5 The deficit arithmetic and the closure at T = 16

The halved published cells at T = 13 to 20 are 2, 5, 35, 43, 229, 295, 1613 and
1678. Subtracting the computed class counts gives the four rows 0,0,0,3,23,49,404,454
(cap 20); 0,0,0,3,20,38,253,290 (cap 21); 0,0,0,3,19,31,223,271 (cap 22);
0,0,0,0,12,23,173,193 (cap 23). I recomputed all four rows from the shipped
`pu20.txt`, `pu21.txt`, `pu22.txt` and `pu23.txt.gz` files, and the counts of
distinct canonical forms and their minimal-length distributions are 2,967;
10,884; 20,111 and 71,572 with the distributions quoted in Sections 7, 11 and
12 of the target. The arithmetic is correct.

The closure at T = 16 needs one sentence the target does not write. Section 13
of `cap21.md` warns that halving is a class count only where each class
contributes exactly two entries, and it says that this is verified only at
T = 13, 14 and 15, which a reader can take as undercutting Section 12. The
repair is short. A published cell counts ordered pairs of total length exactly
T, so halving gives the number of unordered pairs of total length T summed over
classes, and that number is at least the number of classes that have any pair
of total length T. Each of our 43 classes has a pair of total length 16, so all
43 occur among the published classes, whose number is at most 43. There are
therefore exactly 43 such classes, and each of them contributes exactly one
pair. The closure at T = 16 is rigorous, and the report should say so.

### 2.6 Defect 2: a misprinted canonical form

`cap21.md` line 474 prints the first of the three new minimal-length-16 classes
as `(x^4 y x y^2, x y^4 x^-1 y^-3)`. That pair has total length 17, so it
cannot be the canonical form of a class of minimal length 16, and it is not in
`pu23.txt.gz`. The form in the data is `(x^4 y x y^2, x y^4 x y^-3)`, total
length 16. The other two printed forms are correct, and the file's
minimal-length-16 classes are 40 at cap 22 and 43 at cap 23 with exactly the
three new forms

    x^4 y x y^2 , x y^4 x y^-3
    x^3 y x^-2 y^3 , x^2 y x^-1 y x^-1 y^-1
    x^3 y x^-1 y^2 , x^2 y^2 x y x^-2 y^-1

so the correction is one letter in one printed word. This is the second
one-letter defect in this table in two rounds, and a machine check that every
printed canonical form has the printed minimal length would have caught both.

### 2.7 The source

I downloaded the e-print of arXiv:1609.00325 on 5 November 2026 with
`curl -sL -o pu_eprint.gz https://arxiv.org/e-print/1609.00325` and read the
table environment `tab:presentation_num` in `ac15.tex`. The caption reads "Each
cell shows the number of pairs AC-equivalent to AK(3) of total length T obtained
by the program when run with the length bound L. Highlighted cells do not
increase when L is increased." The L = 17 column at T = 13 to 20 is 4, 10, 70,
86, 458, 590, 3226, 3356, and the L = 20 column at T = 21, 22, 23 is 19692,
23192, 128388. Both agree with the target's quotations. The per-length reading
that the halving uses is therefore verified against the live source.

### 2.8 What I did not reproduce

I did not rerun the breadth-first search at caps 21, 22 or 23. My engine would
need about 9 GB at cap 21 and more than 25 GB at cap 23, and the target's
disk-backed method is what makes those caps reachable. The cap-21, cap-22 and
cap-23 state counts, class counts and PU counts therefore rest on the target's
engine, on its agreement with mine at cap 20, and on the internal checks that I
did rerun on the shipped files: the class lists have exactly the stated
numbers of distinct lines at 144,292, 258,032 and 891,748, the subset chains
hold on the files, and the length-13 and class-C claims hold at every cap.

## 3. Target (b), the resisters at caps 24 and 25

### 3.1 The 452,593-key target is verified exactly

The target is the union of the conjugacy-class keys of the standard ball at cap
16 and the keys of the cap-20 AK(3) census. I rebuilt both balls with my own
code and rebuilt the keys with my own implementation of the printed convention,
which is the least rotation in the order B < A < a < b followed by the 64-bit
record of `mkkeys.py` and `acx.c`.

| object | my count | file count | sets equal |
|---|---|---|---|
| standard ball, cap 11, states | 700,712 | 700,712 (reference) | n/a |
| standard ball, cap 13, states | 6,476,104 | 6,476,104 (reference) | n/a |
| standard ball, cap 15, states and keys | 58,487,624 and 185,713 | 185,713 in `std15keys.u64` | yes, 0 differing keys |
| standard ball, cap 16, states and keys | 129,247,304 and 412,753 | 412,753 in `std16keys.u64` | yes, 0 differing keys |
| AK(3) census, cap 20, keys | 39,840 | 39,840 in `ak3keys.u64` | yes, 0 differing keys |

`target.u64` has 452,593 distinct words and equals the union of the two key
sets. The AK(3) keys are disjoint from the standard keys, the cap-15 keys are a
subset of the cap-16 keys, and the cap-16 set adds 227,040 keys. Every number
in Section 3 of the target's README is therefore confirmed by an independent
construction.

### 3.2 The 98 certificates

`code/replay_res.py` is my own replayer of the twelve restricted moves. It
parses `std_certs.txt` and `ak3_hits_certs.txt`, applies the moves and compares
the endpoint with the stated one. The conjugation has to be read as
`r -> g r g^-1` with `g` the named letter. Under that reading

    72 of 72 trivialisations end at (x,y) with final total length 2,
    26 of 26 AK(3)-equivalences end at aaaBBBB,abaBAB with final length 13,
    11,951 moves in total, 0 failures, longest certificates 184 and 138 moves.

Under the other reading of a letter conjugation, `r -> g^-1 r g`, all 98 fail
and the states grow without bound, so the convention is pinned by the data.
Both readings describe legal AC moves, so the choice only fixes how the printed
tokens are read, and under the reading the data pins every certificate is a
valid twelve-move path.

### 3.3 The conjugator-independence theorem

The argument of Section 5 is sound. I checked it step by step. The lemma of
Section 3 gives, for any state, a twelve-move path to the canonical
representative whose total length never increases, by deleting a cancelling
letter pair through a conjugation and then rotating. For two in-box states `s`
and `t` that differ by a conjugation by a long word, the canonical forms agree,
so `s` reaches `c(s) = c(t)` inside the box of `s` and `c(t)` reaches `t`
inside the box of `t`, and the composite stays inside the larger box. One
detail the text compresses is that the reverse of a multiplication step is not
a single move of the twelve, since `r0 -> r0 r1` is undone by inverting the
second relator, multiplying and inverting it back. That is three moves, all
length non-increasing, so the bound on intermediates survives. With that
sentence added the theorem is proved.

### 3.4 Independent negatives at cap 23

I ran my own ordered census from five of the 66 undecided starts at cap 23,
turned each ball into class keys with my own convention, and intersected with
`target.u64`.

| start | my states at cap 23 | recorded count | class keys | hits on the target |
|---|---|---|---|---|
| BBBAAbA,BABabAA | 4,049,040 | 4,049,040 | 1,825 | 0 |
| BBAbaba,BBaabAA | 33,815,688 | 33,815,688 | 16,022 | 0 |
| BBBabba,BABaaaa | 6,696,536 | not recorded | 3,176 | 0 |
| BBAABBa,BAbABaa | 8,200,488 | 17,638,096 at cap 24 | 3,607 | 0 |
| BBAAbba,BAbaaBa | 4,810,680 | not recorded | 2,167 | 0 |

Two of the five counts equal the target's recorded figures exactly, which is a
second engine agreeing on the component size with the full target loaded. The
hit count is zero in all five. What this does not do is check the target's
engine at the caps it quotes, namely 24 and 25, and I did not rerun the
176,714,288-state cap-22 component of the 22-group.

## 4. Target (c), the PSL(2,7) frontier

The four pairs of permutations of 28 points printed in
`directions/psl27-frontier/code/verify.py` were checked by my own code. For each
of the four presentations both relators evaluate to the identity permutation,
the action of the generated group is transitive on 28 points, the image has
order 9,828 and the point stabiliser has order 351. The logical step that turns
this into infinitude, namely that a finite-index subgroup with infinite
abelianisation makes the whole group infinite, is sound. The part I did not
reimplement is the Reidemeister-Schreier matrix and the integer vector `w` with
`M w = 0`, so the claim that the stabiliser's abelianisation is Z^2 + Z/2
rests here on the target's own `verify.py` and on the coordinator's independent
pipeline. No third implementation of that step exists yet.

## 5. Target (d), the 91-move worst case

### 5.1 The exact distances

`code/dirbfs.c` is my own breadth-first search in the ordered twelve-move
directed system. It reproduces every number of Section 4 and Section 6 of the
target.

| question | my answer | target |
|---|---|---|
| BBabA,BBABAbaaa to (x,y), cap 15 | 44 | 44 |
| BBAba,BBaBabAAA to (x,y), cap 15 | 44 | 44 |
| BBabA,BBABAbaaa to (x,y), cap 14 | 50 | 50 |
| BBAba,BBaBabAAA to (x,y), cap 14 | 50 | 50 |
| (x,y) to BBabA,BBABAbaaa, cap 15 | 43 | 43 |

The two directions differ, so the system is directed and the report is right to
distinguish them. My search from the presentation is exhaustive layer by layer
and stops the first time the standard pair appears, so 44 and 50 are exact
inside those caps, and the 43 is exact in the other direction.

A caution for anyone repeating this. A search that stores unordered pairs and
applies the two right multiplications to the sorted order is a different graph,
and it finds 18 instead of 19 for `BBBAAba,BBAABa`. The correct answer 19 is
what the target's file records, and it appears as soon as the state is ordered.
I record this because my first run made exactly that mistake.

### 5.2 The certificates

I replayed all 105,492 certificate lines of the target with my own replayer.
`min_cap15.txt` has 52,744 lines, all 52,744 reach the standard pair, the
largest move count is 45 at `BBabA,BBAAAbaBa`, and the total is 636,293 moves.
`min_cap14.txt` has 52,744 lines, all reach the standard pair, and the largest
count is 50. `new_certs.txt` has the four new certificates, all correct, with
counts 44, 44, 50 and 50.

I then took a deterministic sample of 15 presentations from `min_cap15.txt`,
namely every 4,400th line together with the three named cases, and ran my own
ordered search at cap 15 on each. All 15 distances equal the recorded
certificate lengths, including the 45. So the recorded minima are exact on the
sample and the certificates are valid paths everywhere.

The l-increase claims of Section 5 were not audited, since they need the
definition of the invariant and a rerun of five presence searches.

## 6. Target (e), p-trivial

`code/replay_pt.py` replays the three certificates of `directions/p-trivial`
with my own parser of the one-based move tokens. All three reach their stated
endpoints, with

    P(3) to AK(3): 24 moves, maximum intermediate total length 20
    AK(4) to P(4): 41 moves, maximum intermediate total length 23
    AK(4) to P(4): 43 moves, maximum intermediate total length 22

which are exactly the claims of the direction. The conjugation convention is
again pinned by the data, this time as `r -> g r g^-1`. The exhaustive
negatives at caps 20 to 22 and the box counts were not rerun.

## 6b. Target (e), the AC-graph diameters

I recomputed Delta_2(A5) with my own code. The vertices are the 3,599 ordered
pairs of elements of A5 other than the identity pair, and the edges are the
twelve AC moves, with conjugation by every element of A5. The graph has 3,599
vertices, it is connected, every vertex has degree 126, and the diameter is 8.
I did not recompute the other seven groups, and I did not reproduce the claim
about the orbit reduction or the claim that the diameter is attained at a tuple
with a trivial entry. The round-4 value for A5 is confirmed.

## 7. What this audit did not cover

The ac-graph diameters direction was audited only at A5, and the two
unsubmitted drafts were not audited as wholes. From `directions/second-referees-3` I read
only its conclusions about the resister certificates, which the round-4 report
already records as coordinator-verified, and from `directions/qdouble-star/m9` I
read nothing. The cap-21, cap-22 and cap-23 breadth-first searches, the
resister searches at caps 22, 24 and 25, the Reidemeister-Schreier computation,
and the exhaustive negatives of p-trivial are likewise outside this audit. A
next round should attack the cap-23 census with an independent disk-backed
engine, since that is the one load-bearing computation of round 4 that no
second implementation has reproduced.

## 8. Defect list

1. `directions/cap21/cap21.md` line 172: "The eight rows form two conjugation
   classes" should read "eight conjugation classes", with the note that they
   form one PU class.
2. `directions/cap21/cap21.md` line 474: the first canonical form should read
   `(x^4 y x y^2, x y^4 x y^-3)`.
3. `directions/cap21/cap21.md` Sections 7 and 12: the closure at T = 16 needs
   the inequality sentence of Section 2.5 of this report to survive the caveat
   of Section 13.
4. `directions/cap21/punf.py`: the 16 elementary maps are not the 20 Whitehead
   automorphisms, so the canonicity argument needs the complete set. The
   outputs agree on all 39,840 cap-20 classes and all 144,292 cap-21 classes,
   so this is a justification gap and the numbers are unaffected.
5. `directions/resisters/round4/README.md` Section 5: add that reversing a
   multiplication step costs three moves, all length non-increasing.

## 9. Files, commands and outputs

The scripts are in `code/` and every one of them finds the repository root by
itself. Run the cheap ones with `bash code/rerun.sh` from this directory. The
commands below are the exact ones I ran, with the paths of this directory.

    gcc -O2 -march=native -o code/census code/census.c
    ORDERED=1 code/census 20 1 c20.txt                     # 118 s, 3.2 GB
    LC_ALL=C sort c20.txt > a.txt
    LC_ALL=C sort ../cap21/results/classes20.txt > b.txt
    diff a.txt b.txt                                       # empty
    ORDERED=1 code/census 17 1                            # 857,808 states, 1,000 classes
    ORDERED=1 code/census 18 1                            # 2,014,992 states, 2,128 classes
    START="x,y" ORDERED=1 code/census 15 1 std15.txt       # 58,487,624 states, 185,713 keys
    START="x,y" ORDERED=1 VISCAP=268435456 code/census 16 1 std16.txt   # 129,247,304, 412,753
    START="YYYXXyX,YXYxyXX" ORDERED=1 VISCAP=67108864 code/census 23 1 res1.txt
    python3 code/keysets.py std15.txt std16.txt c20.txt
    gcc -O2 -march=native -o code/punf code/punf.c
    code/punf ../cap21/results/classes20.txt pu20_mine.txt    # 16 s
    code/punf ../cap21/results/classes21.txt pu21_mine.txt    # 86 s
    gcc -O2 -march=native -o code/dirbfs code/dirbfs.c
    ORDERED=1 code/dirbfs 15 YYxyX,YYXYXyxxx x,y 134217728    # distance 44
    ORDERED=1 code/dirbfs 14 YYxyX,YYXYXyxxx x,y 33554432     # distance 50
    ORDERED=1 code/dirbfs 15 x,y YYxyX,YYXYXyxxx 134217728      # distance 43 in the other direction
    python3 code/check_cap21.py c20.txt                        # 79 s
    python3 code/replay_res.py                                 # 98 and 105,492 certificates
    python3 code/replay_pt.py
    python3 code/replay_psl27.py

The heavy runs are the three censuses (118 s, 172 s and 322 s), the PU normal
form at cap 21 (86 s) and `check_cap21.py` (79 s). Everything else finishes in
seconds. The peak memory is 4.9 GB for the cap-16 standard ball, 3.2 GB for the
cap-20 box and 3.0 GB for the cap-23 resister component of 33,815,688 states.
The two C programs take the box, the conjugator bound K and an output class
list as arguments, and `ORDERED`, `START`, `VISCAP` as environment variables.
