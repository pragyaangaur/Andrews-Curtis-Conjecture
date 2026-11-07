# Second referees 3: a fresh-context audit of five round-3 artifacts

Direction G5 of round 4, swarm smw2woueq, member m7. Written 2026-11-05 UTC. The
targets are the five that this direction names: (a) `directions/hardness/`,
(b) `directions/pu-gap/`, (c) the uniform ladder step of
`.ultramath/smw2opo0o/m1/ak-ladder/`, (d) `directions/c14/carreras/`, and (e) the
two unsubmitted drafts `directions/resisters/` and `directions/qdouble-star/`,
which no member submitted and which are audited hardest.

Method. For every target I wrote my own implementation from the written
definitions and from the data formats, in this directory, and ran it before
reading any of the target's code. Where a format was ambiguous I tested all
conventions and kept the one combination that replays every file. The conventions
that replay everything are recorded below, because a certificate is only as strong
as the semantics it is replayed under. I read a target's code in one place only,
`directions/pu-enumeration/rawbox.c`, after my own class count failed to reproduce
its `classes (conj)` column, to find out what its key function does (Section 2).

Verdicts.

| target | verdict |
|---|---|
| (a) hardness | SOUND at caps 13 to 18 and on all 52,744 certificates; caps 19 and 20 were not recomputed |
| (b) pu-gap | SOUND for the source reading, the box counts at caps 13 to 18, the class counts at caps 13 to 17, the PU-class counts at caps 15 and 16, the six certificates and the class-C status at cap 17; the cap-20 figures were not recomputed |
| (c) ak-ladder uniform step | SOUND for every instance with n at most 60 and for the four word identities; the all-n claim rests on the induction that the note itself says is not written out |
| (d) carreras | SOUND; all five files replay and are byte-identical to the upstream repository |
| (e) resisters draft | SOUND where checkable; 98 certificates, the status table, and one cap-22 component size reproduced; the 66 undecided stay bounded negatives |
| (e) qdouble-star draft | SOUND where checkable; 69 certificates, all 164 presentations of order 1 under my own GAP script; the 96 open stay bounded negatives |

Nothing here bears on the truth or the falsehood of the Andrews-Curtis
conjecture, and no verdict above is more than a statement that the computation or
the argument in question survived this audit.

## 0. The engine, and how its conventions were fixed

`ac_engine.py` is my own implementation. A word is a tuple of nonzero integers,
with 1 and -1 for x and x inverse and 2 and -2 for y and y inverse, and a
presentation is a pair of a rank and a tuple of relators, with every relator freely
reduced. The file implements free reduction, inversion, cyclic reduction and
rotation, conjugation of a relator by any word, right and left multiplication of a
relator by another, the elementary Nielsen moves on the generators, and
prolongation. Every replayer in this report is a small parser over that engine, so
a certificate is checked by arithmetic that shares no code with any target.

The conventions that replay every file, each one selected by testing all
combinations and finding that only one works, are these.

1. Resister certificates `start|moves|end`: `i0` and `i1` invert a relator, `m0` and
   `m1` multiply relator i by the other on the right, and `c0a`, `c0A`, `c0b`, `c0B`
   conjugate relator 0 by a letter on the left, so a relator r goes to g r g
   inverse. The wrong multiplication side makes the words grow without bound, which
   is why the replay script abandons a convention at a total relator length of
   20,000.
2. Q* certificates of `directions/qdouble-star/out`: `inv`, `conj` by one letter on
   the left, `mul` and `lmul` on the right and on the left, `nij i j` sending x_i to
   x_i x_j, `nji i j` sending x_i to x_j x_i, `neg`, and `prolong`.
3. `directions/pu-gap/run/certs13_settled.txt`: `c1=w` and `c2=w` conjugate a
   relator by the word w on the left, `i1` and `i2` invert, and `m21` multiplies
   relator 2 by relator 1 on the right.
4. the ak-ladder JSON certificates: 1-based relator indices, `conj` on the left,
   and `mul i j` sending r_i to r_i times r_j.
5. the Carreras JSON certificates: 0-based indices, `conj` on the left,
   `mul i j s` sending r_i to r_i times r_j to the power s, and `cycle i k` the
   cyclic rotation of relator i left by k letters.

## 1. Target (a), the hardness direction

```
python3 directions/second-referees-3/hardness_check.py .
certificates = 52744
replay failures = 0
bound histogram = {0: 4780, 1: 38480, 2: 4607, 3: 3632, 4: 299, 5: 856, 6: 90}
sum = 52744
moves: min 9 max 91 mean 25.68
  bound 0: cases 4780 mean 33.5 median 31 max 91 min 14
  bound 1: cases 38480 mean 24.1 median 24 max 45 min 9
  bound 2: cases 4607 mean 28.7 median 28 max 54 min 13
  bound 3: cases 3632 mean 27.7 median 27 max 48 min 14
  bound 4: cases 299 mean 26.5 median 26 max 42 min 15
  bound 5: cases 856 mean 27.9 median 28 max 43 min 16
  bound 6: cases 90 mean 24.8 median 25 max 31 min 19
Spearman(bound, moves) = 0.0060
bound 0: cases 4780, moves from 14 to 91, mean 33.5
hardest overall: 91 moves at bound 0
```

This reproduces every number of Section 4.2 of `hardness.md`: the histogram, the
seven rows of means, medians and maxima, the rank correlation plus 0.0060, and the
identification of the 91-move worst case as a path with l-increase exactly 0. The
52,744 certificates of `certs_12.txt`, `certs_13.txt` and `certs_14.txt` replay
under my engine with zero failures, so the l-increase values are recomputed from
the paths and not taken from the target.

```
python3 directions/second-referees-3/barcode_forest.py 15
python3 directions/second-referees-3/barcode_forest.py 16
python3 directions/second-referees-3/barcode_forest.py 17
python3 directions/second-referees-3/barcode_forest.py 18
```

give the following, with the reported values of `hardness.md` beside them.

| cap | my states | my finite bars | my bar lengths | their bars | their bar lengths |
|---|---|---|---|---|---|
| 15 | 6,864 | 1 | 2: 1 | 1 | 2: 1 |
| 16 | 20,560 | 11 | 1: 8, 2: 2, 3: 1 | 11 | 1: 8, 2: 2, 3: 1 |
| 17 | 857,808 | 167 | 1: 112, 2: 44, 3: 7, 4: 4 | 167 | 1: 112, 2: 44, 3: 7, 4: 4 |
| 18 | 2,014,992 | 247 | 1: 176, 2: 48, 3: 19, 4: 4 | 247 | 1: 176, 2: 48, 3: 19, 4: 4 |

The state counts at caps 13 and 14 are 168 each with no finite bar, which matches
the table as well. My computation is a merge forest: the components of each level
of the length filtration are recomputed from scratch by breadth first search, and a
component of level k that contains m components of level k minus one contributes
m minus one bars, the youngest dying first. No union find is used.

I record one disagreement that my own work produced, because it is the kind of
thing a fresh referee is for. My first barcode program used a union find with the
elder rule, and at cap 17 it reported 168 finite bars with h_2 equal to 45. The
rank identity of a graph filtration, that the number of components of the level-k
graph equals one plus the number of bars with b at most k and d greater than k, is
a theorem and it does not depend on the implementation. Computing the component
counts of the levels directly showed that my union find was wrong by one bar at
levels 15 and 16, and that 167 is the consistent count. The union-find run is kept
as `barcode_check.py` and `barcode_identity.py` so that the disagreement and its
resolution can be rerun.

I did not recompute the cap-19 and cap-20 barcodes, the within-component
correlations of Section 4.1, which need the 51,411,456-state run, or the printed
values of the source's Table in Section 7.3. The quotations from
arXiv:2408.15332v2 that the structural finding rests on were checked live: I
fetched `https://arxiv.org/html/2408.15332v2` and read "The minimum increase in
length across all possible AC-trivializations serves as an invariant of the
presentation, its l-increase, which is correlated with how hard it is to
trivialize", "For L in {11, ..., 16} we take the induced subgraph containing all
nodes admitting a trivialization path containing only presentation of length at
most L", and "the absence of infinite bars in this barcode is equivalent to the AC
conjecture". The argument that the published approximation is undefined exactly on
the unresolved components follows from the second quotation.

## 2. Target (b), the pu-gap direction

### 2.1 The source reading

I fetched the paper live at `https://ar5iv.labs.arxiv.org/html/1609.00325`, whose
submission history shows a single version, so the rendering is v1. It contains "We
also set a limit on the total length of pairs to be 2L+2", "Each cell in Table 1
corresponds to a value L and a value T and presents the number of pairs of the
total length equal to T constructed by the program with the single-word-bound L",
and the caption "Each cell shows the number of pairs AC-equivalent to AK(3) of
total length T obtained by the program when run with the length bound L". The
L equals 10 column of Table 1 as rendered reads 4, 10, 70, 64, 220, 98, 240, 10,
20, 0 for T from 13 to 22, so the drop from 240 at T equal to 19 to 10 at T equal
to 20 is there, and a cumulative count could not do that. The cells that the report
compares at L from 17 to 20 are 86, 458, 590, 3226 and 3356 for T from 16 to 20,
exactly as quoted, and the arithmetic 86 minus 80, 458 minus 412, 590 minus 492,
3226 minus 2418 and 3356 minus 2448 gives 6, 46, 98, 808 and 908 entries, that is
3, 23, 49, 404 and 454 classes. The per-length reading of Table 1 is therefore
confirmed against the live source, and the withdrawn cumulative deduction is
rightly withdrawn.

### 2.2 Box counts and class counts

```
python3 directions/second-referees-3/puclass_check.py .
cap 13: states 168 ordered classes 1 unordered classes 1 ratio 1.000
cap 15: states 6864 ordered classes 26 unordered classes 26 ratio 1.000
cap 16: states 20560 ordered classes 80 unordered classes 40 ratio 2.000
cap 17: states 857808 ordered classes 2000 unordered classes 1000 ratio 2.000
cap 15 (orbit length bound 22): unordered classes 26, Aut(F_2) orbits 7
cap 16 (orbit length bound 22): unordered classes 40, Aut(F_2) orbits 11
```

The ordered column reproduces `pu.md` exactly at caps 13, 15, 16 and 17, which are
1, 26, 80 and 2000, and the PU-class column exactly at caps 15 and 16, which are 7
and 11. The unordered count is exactly half the ordered one at caps 16 and 17,
which supports the reading that the 79,680 figure of round 2 is the ordered count
and the 39,840 figure of `rawbox2` is the unordered one. At cap 15 the two counts
coincide, so the halving is not a general identity and the fact that it holds at 16
and 17 is content. The PU-class count is my own orbit count of the unordered
classes under the five Nielsen generators of Aut(F_2), with the orbit closure taken
inside total length 22. The bound can only merge too little, so 7 and 11 are upper
bounds, and they equal the reported values.

`counts.py` gives the state counts 168, 168, 6,864, 20,560 and 857,808 at caps 13
to 17 and the length histogram 13: 2,016, 14: 4,704, 15: 76,800, 16: 94,416, 17:
679,872 at cap 17, and 13: 336, 15: 6,528 at cap 15. These are exactly the rows of
the `raw_by_total` column of `pu-gap.md`.

My first class count, in `pugap_check.py`, was 28 at cap 15 and 84 at cap 16,
against the 26 and 80 of the target. I resolved this by reading `rawbox.c` after my
own implementation was complete: its histogram is indexed by the length of the
class key, and a class key can be shorter than the state it comes from because the
key is cyclically reduced. Counting distinct keys, as `puclass_check.py` does,
gives 26 and 80. The discrepancy was mine, and the `classes (conj)` column is
confirmed.

I did not reproduce the cap-20 figures 79,680, 39,840 and 2,967, because my
enumeration stops at cap 18.

### 2.3 The six certificates and class C

```
python3 directions/second-referees-3/replay_settled.py .
lines = 6
conj_left=True mul=ij : reach stated end 6, fail 0, ends ['aaaBBBB,abaBAB', 'abaBAB,aaaBBBB'], max intermediate 20
```

All six reach the stated end, which is AK(3) with the two relators in either order,
and no intermediate pair exceeds total length 20, as the report claims.

The eight length-13 presentations that `final_classes.txt` labels
`resisting-exhausted-cap17` are the eight members of class C. Each of the eight is
in `std_certs.txt`, so each is AC-trivial by a certificate that the Section 5
replay checks. None is in `ak3_hits_certs.txt`, and none lies in my own cap-17
component of AK(3), which has 857,808 states. The cap-17 half of the claim that
class C lies outside the box is therefore confirmed independently, and the cap-20
half rests on the 51,411,456-state enumeration, which I did not reproduce.

I could not reconstruct the "twelve unordered classes of total length 13" of
Section 5, and I did not verify the labels A, B and C or the split of four and
eight between A and B. My bounded orbit normal form, the least image among orbits
of minimal total length with closure inside total length 25, puts four of the six
settled presentations in class B and two in a class whose minimal representative
has total length 13, while the printed normal form of A has minimal total length 9
in my computation. The printed forms are therefore not minimal representatives of
their automorphism orbits, and their labels depend on the Whitehead minimisation
program, which I did not reimplement. This item is left inconclusive rather than
marked sound or unsound.

## 3. Target (c), the uniform ladder step

```
python3 directions/second-referees-3/ladder_check.py
ladder step: 1711 instances, 0 failures
correction identity: 0 failures over n=3..60
Lemma 3 identities: 1160 checks, 0 failures
```

The first line replays the ten-move certificate of Theorem 1 from the definitions
in Section 3 of the note, with A equal to x inverse y to the n x y to the minus n
plus one and B_k equal to x inverse y to the minus k x inverse y x y, for every n
from 3 to 60 and every k from 1 to n minus 2. That is exactly the 1,711 instances
the note claims, and every one ends at the pair with B_(k+1) exactly, as reduced
words. The second line checks that the correction c of Lemma 2 equals A times the
conjugate of A by y to the n x inverse y to the minus n plus one x times the
conjugate of A inverse by y inverse, as an exact word identity, again for every
instance with n from 3 to 60. The third line checks the four identities of Lemma 3
for n from 2 to 30 and q from 1 to 10.

The first two runs of the third check printed 551 and then 261 failures out of
1,160, and both times the reason was a bug in my own transcription of an identity.
The third identity needs the conjugator y to the j n x, and I had written y to the
j x; the fourth needs a negative power of y, and I had written a tuple times a
negative integer, which Python reads as the empty tuple. After both fixes all 1,160
checks pass. I record this because the first output, taken alone, would have looked
like a refutation of Lemma 3, and because the episode shows how easily a referee
transcribes a formula wrongly.

```
python3 directions/second-referees-3/replay_akladder.py '.ultramath/smw2opo0o/m1/ak-ladder/certs/*.json'
files = 62
conj_left=True mul=right : exact target 62, fail 0, blown 0
```

All 62 stored certificates replay exactly, among them the 19 end-to-end chains
`chain_uniform_N` for n from 2 to 20, each with exactly 12n minus 2 moves. The peak
total lengths on those chains are 15, 31, 38, 45, 52, 59, 66, 73 and so on up to
150 at n equal to 20, matching the table of Section 4 of the note.

The exact gap is the one the note states. Lemma 2 is labelled "ARGUMENT plus finite
check" and its text says that the general-n step from the finite instances to all n
is not written out as an induction, and Lemma 4 is labelled "PROVED, conditional on
Lemma 3". My computations establish the ladder step for n up to 60 and the
identities for n up to 30 with q up to 10. A reader who needs the all-n statement
should treat it as conditional on the induction that the note does not write.

## 4. Target (d), the Carreras certificates

```
python3 directions/second-referees-3/replay_carreras.py 'directions/c14/carreras/*.json'
files = 5
conj_left=True mul=right cycle_left=True : target 0 reached 5 both 0 of 5, blown 0, maxlen 33
```

All five files reach their own `reached` field exactly, with a largest intermediate
total length of 33. The column `target 0` needs a word of explanation: that check is
an exact comparison, and the stored `target` differs from the stored `reached` by a
cyclic rotation of each relator and sometimes by the order of the two relators.
Comparing the conjugation classes of the two fields, which is the right comparison,
gives agreement for all five files up to the order of the two relators. A cyclic
rotation of a relator is a conjugation and so an AC move, and a swap of the two
relators is notational, so each file is a valid certificate from its initial pair to
its target pair.

The identifications were checked against `final_classes.txt` with the conjugation
class of the two relators, and they match the table of the README up to that same
notational freedom. The pair of `cert_idx0_equiv_mirror` is `BBBAbba,BAABaaa` to
`BBBAbba,BAAABaa`, that of `cert_sym_equiv_orphan1` is `BBBAbba,BAAbaaa` to
`BBBAbba,BAAAbaa`, that of `cert_ms3_yx2y_equiv_ak3` starts at `BAABa,BBBBAbbba`,
that of `bottleneck_ak_f3_cert` ends there, and that of
`cert_ms3_yinvx2yinv_equiv_ak3` starts at a conjugate of `BABaa,BBBBAbbba`, which
`final_classes.txt` labels ak3-equivalent rather than resisting. The last point is a
label in the round-2 list and it does not affect the claim of the README.

Provenance was verified live. I downloaded the five files from
`https://raw.githubusercontent.com/joe-carr-data/ac-certificates/main/certs/` and
their SHA-256 sums equal those of the local copies byte for byte, for all five
files. The git blob hashes of the local copies also equal the hashes recorded in
`provenance.json`. The round-3 report said that two files had been re-downloaded,
and all five are now confirmed.

## 5. Target (e), the resisters draft

```
python3 directions/second-referees-3/replay_resisters.py directions/resisters/std_certs.txt directions/resisters/ak3_hits_certs.txt
certificates = 98
conj_left=True mul_side=right : reached 98, failed 0, blowups 0, swaps 0, max intermediate total length 22
```

The 72 trivialisation certificates have 73 to 184 moves and a largest intermediate
total length of 22, and the 26 AK(3) certificates have 67 to 138 moves and a largest
intermediate total length of 20. Both ranges are exactly those of the report, and
one certificate of each family altered in a single move is rejected by the same
checker, which shows that the replay is sensitive.

```
python3 directions/second-referees-3/consistency.py .
final_status rows = 164
std certs = 72 ak3 certs = 26
distinct std starts = 72 distinct ak3 starts = 26
starts not in final_status: []
status mismatches = 0
undecided rows = 66 statuses Counter({'undecided': 66})
undecided caps Counter({22: 38, 20: 22, 23: 6})
undecided lengths Counter({14: 66})
```

The status table, the two certificate files and the counts of undecided
presentations by bound agree with each other, and all 14 length-13 rows are decided.

The bound machinery was checked against a component size that I recomputed from the
definitions.

```
python3 directions/second-referees-3/resister_component.py
a,b                cap 11 states 700712  (17.3 s)
a,b                cap 12 states 1582280  (46.7 s)
BBAAABa,BBabABA    cap 22 states 1461200  (36.2 s)
```

The two standard-pair sizes are the ones the report uses to validate the engine,
and the third is the smallest cap-22 component of the 38 presentations that carry a
cap-22 bound, as recorded in `results/resboth22.txt`. My count equals the recorded
1,461,200 exactly, with my own twelve-move explorer, which corroborates the
machinery behind the negative bounds at one instance.

I did not recompute the one-component claim for the 22 cap-20-undecided
presentations, whose component has 21,349,360 states and is too large for my Python
explorer, nor the K equals 2 conjugator rerun, nor the generation of the 72 and 26
certificates. The negative bounds themselves stay what the draft labels them:
statements about a twelve-move exploration inside a total-length cap, and the draft
says so in its Section 7 and its Section 9.

## 6. Target (e), the qdouble-star draft

```
python3 directions/second-referees-3/replay_qstar.py 'directions/qdouble-star/out/*.cert'
certificates = 69
conj_left=True mul=right nij=ij : ok 69 bad 0 blowups 0 endranks [2] maxlen 15
```

All 69 files replay, with a largest intermediate total length of 15. The 68
resister certificates have 26 to 55 moves, mean 38.4, exactly the figures of the
report, and they split eight at length 13 and sixty at length 14. Every one of their
starts is a row of `final_status.tsv`, no path exceeds the starting total length by
more than one, and every path stays at rank 2, so the certificates are Q*
certificates and not Q** certificates. The sixty-ninth file is the one-move
prolongation from the rank-one presentation (x | x) to the rank-two presentation
(x, y | x, y). Since Q* moves never change the rank, that pair is Q**-equivalent
and not Q*-equivalent, so the claim about the smallest such pair is sound.

The claim that all 164 resisters present the trivial group was recomputed by me in
GAP, with a script built from my own reading of `final_status.tsv` and not from the
draft's files.

```
gap -q sizes164.g
count 164
orders [ [ 1, 164 ] ]
```

Every one of the 164 presentations has order 1, in under a second in total.

I did not rerun the bounded negatives for the 96 open resisters, for AK(3), for
Metzler's pair or for Barmak's pair, nor the control run without Nielsen moves, nor
the winding check. Those stay as the draft labels them, bounded negatives with
stated caps and budgets.

## 7. What I could not verify, in one place

1. Hardness: the cap-19 and cap-20 barcodes, the within-component correlations,
   and the numbers of the source's own Table in Section 7.3.
2. pu-gap: the cap-20 class counts 79,680, 39,840 and 2,967, the A, B and C labels
   and the four-eight split, and therefore the cap-20 half of the class-C claim.
3. ak-ladder: the general-n induction, the 66 Todd-Coxeter runs, and the depth
   profile of Section 7. The stored certificates and the 1,711 instances were
   verified.
4. Carreras: nothing in the replay. The identification of
   `cert_ms3_yinvx2yinv_equiv_ak3` with a "resisting" row is a round-2 label, since
   `final_classes.txt` labels that row ak3-equivalent.
5. Resisters: the 21,349,360-state cap-20 component, the K equals 2 rerun, and the
   certificate generation.
6. qdouble-star: the bounded negatives and the two control runs.

## 8. Files of this report

All scripts are deterministic. The whole set takes about fifteen minutes of wall
clock, of which the cap-18 barcode is about four minutes.

| file | what it does |
|---|---|
| `ac_engine.py` | words, free reduction, the AC moves, the Nielsen moves, prolongation |
| `replay_resisters.py` | the 98 resister certificates, with a convention search |
| `consistency.py` | `final_status.tsv` against the two certificate files |
| `resister_component.py` | component sizes: standard at caps 11 and 12, one resister at cap 22 |
| `replay_qstar.py` | the 69 Q* certificates |
| `hardness_check.py` | the 52,744 certificates, the l-increase table and the rank correlation |
| `barcode_check.py`, `barcode_identity.py` | my first union-find barcode and the rank identity that refuted it |
| `barcode_forest.py` | the merge-forest barcode used for the verdict |
| `counts.py` | state counts and length histograms of the AK(3) box |
| `puclass_check.py` | class counts and the Aut(F_2) orbit count |
| `pu_normal_form.py` | the bounded orbit normal form used for the inconclusive label check |
| `pugap_check.py` | my first class count, kept to record the discrepancy and its cause |
| `replay_settled.py` | the six pu-gap certificates |
| `ladder_check.py` | the 1,711 ladder instances, the correction identity, the four identities |
| `replay_akladder.py` | the 62 stored ak-ladder certificates |
| `replay_carreras.py` | the five Carreras certificates |

The target files were read as data only, with the single exception recorded in
Section 2: `directions/pu-enumeration/rawbox.c` was read after my own class count
failed, to find that its histogram is indexed by key length.
