# The Panteleev-Ushakov table gap: conventions, and where the difference comes from

This is Round 3, direction F3. It answers the round-2 question about the gap
between our census of the AK(3) class and Table 1 of Panteleev and Ushakov.
Every claim is labelled [Computed], [Source], [Argument], [Reported] or [Open].
Nothing here bears on the truth of the Andrews-Curtis conjecture, and no claim of
a proof or a disproof of it is made.

## 0. Summary

Round 2 compared its cumulative counts of Panteleev-Ushakov classes,

    2, 7, 42, 82, 288, 534, 1743, 2967   (T = 13, ..., 20)

with the cells of Table 1 of arXiv:1609.00325v1,

    4, 10, 70, 86, 458, 590, 3226, 3356,

read as cumulative counts, and drew the conditional deduction that at least two
of their four length-13 members need an intermediate pair of total length
greater than 20. The comparison behind that deduction used two different
conventions, and the deduction does not survive the correction. The findings
are these.

1. [Source] The cells of Table 1 count pairs of total length **equal** to T, not
   pairs of total length at most T. The paper says so in the text of Section 6.1
   and in the table caption. The cumulative reading is also refuted by the table
   itself: in the column L = 10 the cell for T = 19 is 240 and the cell for
   T = 20 is 10, which is impossible for a cumulative count of one fixed run.
2. [Computed] Our own counts were reproduced with a new enumerator that uses
   less memory per state, and they agree with round 2 exactly. The per-length
   counts of Panteleev-Ushakov classes are 2, 5, 35, 40, 206, 246, 1209, 1224
   for T = 13, ..., 20.
3. [Computed] Compared correctly, their cells are exactly twice ours at
   T = 13, 14 and 15, and exceed twice ours by 6, 46, 98, 808 and 908 at
   T = 16, 17, 18, 19 and 20.
4. [Argument] A count of 4 Panteleev-Ushakov classes of total length 13 is
   impossible unless AK(3) is AC-trivial. At most three such classes exist,
   because the complete length-13 census of directions/c14/ leaves only
   6 presentations certified AK(3)-equivalent and 14 undecided, and those 14
   fall in exactly three classes, two of which are the two certified ones.
5. [Argument] The exact factor two at three consecutive lengths is what counting
   the two relator orders separately gives: one entry for (u,v) and one for
   (v,u) in every class. That convention reproduces 4, 10 and 70 exactly.
   The alternative, that their four length-13 entries are four classes, is
   excluded by finding 4. So the round-2 deduction is withdrawn: the four
   length-13 entries are the two classes of the cap-20 box, each entered twice.
6. [Computed] One thing the round-2 deduction was after does hold: a third
   length-13 candidate class exists, its eight presentations are outside our
   cap-20 box, and if any of them is AK(3)-equivalent then every such path needs
   an intermediate pair of total length at least 21. That class is the set of
   the eight length-13 presentations that directions/c14/ exhausted at cap 17.
7. [Computed] Six of the 164 resisters of directions/c14/ fall. The six
   length-13 presentations that c14 stopped by budget are in the cap-20 census,
   and this file ships explicit certificates from each of them to AK(3) that
   replay under two independent checkers.
8. [Open] The residual deficit at T = 16 to 20 (6, 46, 98, 808, 908 entries
   after doubling, that is 3, 23, 49, 404, 454 classes) is a matter of the
   search box. Their search allows intermediates of total length up to
   2L + 2, which is 22 at L = 10 and 42 at L = 20, and it uses ACM-moves.
   Our box stops at total length 20, and our search uses the three plain moves.
   The cap-21 run did not complete on this shared VM (Section 8).

## 1. The source, and what each cell counts

Panteleev and Ushakov, *Conjugacy search problem and the Andrews-Curtis
conjecture*, arXiv:1609.00325v1 (submitted 1 September 2016); journal version
Groups Complexity Cryptology 11 (2019), no. 1, 43-60, DOI
10.1515/gcc-2019-2005. [Source] The journal identity, volume, pages and DOI were
checked against the Crossref record (api.crossref.org/works/10.1515/gcc-2019-2005,
fetched 4 November 2026), whose abstract says: "The improved technique allows us
to enumerate balanced presentations AC-equivalent to AK(3) with relations of
lengths up to 20 (previous record was 17)." The numbers compared here are the
arXiv v1 numbers, which is the same source round 2 used. The published table was
not accessible to me, because the publisher page redirects to a host that I did
not fetch.

Three quotations fix the meaning of a cell. [Source]

* Section 6, opening: "We also set a limit on the total length of pairs to be
  2L + 2."
* Section 6.1: "Each cell in Table 1 corresponds to a value L and a value T and
  presents the number of pairs of the total length equal to T constructed by the
  program with the single-word-bound L."
* Table 1 caption: "Each cell shows the number of pairs AC-equivalent to AK(3)
  of total length T obtained by the program when run with the length bound L."

So a cell is a count for one exact total length T, over the pairs found by one
run with a per-relator bound L. [Source]

One sentence in the same section reads against this: "we can conjecture that the
number of normal forms of AK(3)-equivalent presentations of total length 20 or
less is 3356". Under the per-length reading the sum of the first eight cells is
4 + 10 + 70 + 86 + 458 + 590 + 3226 + 3356 = 7800, so the sentence and the table
cannot both be right. [Computed, arithmetic] This sentence is presumably what
produced the cumulative reading in round 2. The table itself decides against it,
because under the cumulative reading a fixed run would have to lose pairs when T
grows. The column L = 10 reads 4, 10, 70, 64, 220, 98, 240, 10, 20, 0 for
T = 13, ..., 22 (arXiv v1, Table 1). [Source] The drop from 240 at T = 19 to 10
at T = 20, and the drop from 220 at T = 17 to 98 at T = 18, are impossible for
cumulative counts of one run. [Argument] The column L = 12 shows the same
pattern (454 at T = 17, 398 at T = 18). So the cells are per-length counts.

## 2. Our data, re-verified

Round 2 measured two different quotients of the same reachable set, and the
report quoted both. The first is the number of classes under conjugation and
inversion of the relators. The second is the number of classes under the full
relation of Section 4.2 of the paper (swap of the two relators, inversion of one
relator, conjugation of one relator, automorphism of the free group). Only the
second is comparable with Table 1.

Round 2's enumerator counts *ordered* pairs in its class column: `rawbox.c`
builds the class key from the least cyclic form of u and the least cyclic form
of v without sorting the two words, so (u,v) and (v,u) are two classes. Its
reported 79,680 classes at cap 20 are therefore ordered, and it is the class
list that is fed to the normal-form program, which sorts the two words and so
recovers the correct quotient. [Computed, by reading `rawbox.c` and by
comparison with the new enumerator]

I wrote a second enumerator, `rawbox2.c`, with the same move set and the same
box, states packed into 64 bits, and no per-state arena. It reproduces round 2's
raw state counts at every cap where both were run [Computed]:

| T  | states rawbox2 | states rawbox | raw_by_total (both)                       |
|----|---------------:|--------------:|-------------------------------------------|
| 13 | 168            | 168           | 13:168                                    |
| 15 | 6,864          | 6,864         | 13:336 15:6,528                           |
| 17 | 857,808        | 857,808       | 13:2,016 14:4,704 15:76,800 16:94,416 17:679,872 |
| 18 | 2,014,992      | 2,014,992     | 13:2,016 14:4,704 15:95,872 16:102,480 17:915,520 18:894,400 |
| 20 | 51,411,456     | 51,411,456    | 13:4,032 14:15,424 15:241,856 16:336,288 17:2,520,832 18:3,280,096 19:20,185,152 20:24,827,776 |

At cap 20 the new enumerator reports 39,840 unordered classes under conjugation
and inversion, exactly half of the 79,680 ordered ones, with class counts per
length exactly half of round 2's (12, 40, 516, 556, 2844, 3228, 15620, 17024
against 24, 80, 1032, 1112, 5688, 6456, 31240, 34048). [Computed]

Feeding those 39,840 classes to round 2's own normal-form program
(`directions/pu-enumeration/puclass2.py`, whose self-test reports 0 failures)
reproduces the round-2 class counts exactly [Computed]:

    ~-classes: 2967
      minlen 13 :      2   N(<=13) = 2
      minlen 14 :      5   N(<=14) = 7
      minlen 15 :     35   N(<=15) = 42
      minlen 16 :     40   N(<=16) = 82
      minlen 17 :    206   N(<=17) = 288
      minlen 18 :    246   N(<=18) = 534
      minlen 19 :   1209   N(<=19) = 1743
      minlen 20 :   1224   N(<=20) = 2967

Every certificate of the new enumerator that covers a class of total length at
most 16 replays under round 2's independent checker: "certificates checked:
1124, verified: 1124, failed: 0, total 58,467 moves, max 131". [Computed]

## 3. The comparison, done with one convention

| T  | Table 1, L = 17 to 20 | our PU classes, exact T | 2 x ours | excess of theirs over 2 x ours | ratio |
|----|----------------------:|------------------------:|---------:|-------------------------------:|------:|
| 13 | 4                     | 2                       | 4        | 0                              | 2.00  |
| 14 | 10                    | 5                       | 10       | 0                              | 2.00  |
| 15 | 70                    | 35                      | 70       | 0                              | 2.00  |
| 16 | 86                    | 40                      | 80       | 6                              | 2.15  |
| 17 | 458                   | 206                     | 412      | 46                             | 2.22  |
| 18 | 590                   | 246                     | 492      | 98                             | 2.40  |
| 19 | 3226                  | 1209                    | 2418     | 808                            | 2.67  |
| 20 | 3356                  | 1224                    | 2448     | 908                            | 2.74  |

[Computed] The left column is read from arXiv v1 Table 1, the second column is
Section 2, and the rest is arithmetic.

The old comparison (our cumulative counts against their per-length cells) is
reproduced here only to record what went wrong:

| T  | 13 | 14 | 15  | 16 | 17  | 18  | 19   | 20   |
|----|----|----|-----|----|-----|-----|------|------|
| their cells | 4 | 10 | 70 | 86 | 458 | 590 | 3226 | 3356 |
| our cumulative | 2 | 7 | 42 | 82 | 288 | 534 | 1743 | 2967 |

[Computed] Two cumulative sequences that cross cannot be compared cell by cell,
and the "agreement at 16 and 20" that round 2 noticed is an artefact of mixing
the two conventions.

## 4. Why the first three cells are exactly twice ours

The fit is exact at three consecutive lengths. The explanation that fits is a
counting convention: their set stores the pair (u,v) without storing (v,u) as
the same object, so a class counts twice whenever the two orders are not
themselves equivalent. [Argument]

A competing explanation is that their search reaches two more classes of total
length 13. That explanation fails, on the following argument. [Argument]

* Let (u,v) be AK(3)-equivalent with |u| + |v| = 13. The exponent-sum matrix of
  (u,v) is unimodular, because AC-moves change it by left and right
  multiplication by unimodular integer matrices. [Argument]
* directions/c14/ enumerated every canonical pair of total length exactly 13
  with |det| = 1, one per class under relator order, cyclic rotation and
  inversion: 18,116 pairs. It labels them 18,076 AC-trivial with certificates,
  20 nontrivial with an explicit homomorphism to A5, 6 AC-equivalent to AK(3)
  with certificates, and 14 undecided. [Computed, directions/c14/]
* The 20 nontrivial ones are not AK(3)-equivalent, because AK(3) presents the
  trivial group. I reran the Lean proof of that (directions/ak-status/
  ak_trivial.lean, exit 0, and `#print axioms` reports only propext,
  Classical.choice and Quot.sound), and an independent GAP coset enumeration
  gives order 120 for all 20 of them. [Computed]
* The 6 certified ones form exactly two PU classes, with normal forms
  A = (x^4 y^3, x y x^-1 y x y^-1) and B = (x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y).
  [Computed]
* The 14 undecided ones form exactly three PU classes. Two of them are A and B,
  and the third has normal form C = (x^2 y x y^2, x y x^-1 y x y^-1). The eight

COORDINATOR CORRECTION, 2026-11-05 (round 4, from the cap-21 census of member
m5 of swarm smw2woueq, accepted after fresh refereeing): the normal form of
class C printed here and at line 230 below is ONE LETTER SHORT in its first
relator. The eight class-C presentations normalise to
(x^3 y x y^2, x y x^-1 y x y^-1), as this file's own log prints
(logs/checks13.log, "xxxyxyy,xyXyxY") and as both independent normal-form
implementations of directions/cap21/punf.py and checkC.py return. The printed
pair (x^2 y x y^2, x y x^-1 y x y^-1) has total length 12 and lies in a
different PU class. The class-C exclusion and all other results of this file
are unaffected. Round 4 further established (directions/cap21/cap21.md) that
class C is absent from the cap-21, cap-22 and cap-23 boxes, so any AC path
from AK(3) to class C needs an intermediate pair of total length at least 24.
  presentations of class C are exactly the ones c14 exhausted at cap 17, and the
  six that c14 stopped by budget lie in A and B. [Computed]
* The 18,076 AC-trivial ones can be AK(3)-equivalent only if AK(3) is itself
  AC-trivial, since AK(3)-equivalence to an AC-trivial presentation composes to
  an AC-trivialisation of AK(3). [Argument]
* So, unless AK(3) is AC-trivial, there are at most three PU classes of total
  length 13 that contain an AK(3)-equivalent presentation: A, B and possibly C.

Four is larger than three, so their cell of 4 is not a count of PU classes under
the relation of their Section 4.2. [Argument] The order convention gives 2 x 2 =
4 without using class C, and gives 10 = 2 x 5 and 70 = 2 x 35 at the next two
lengths. Two consequences follow. First, the round-2 conditional deduction is
withdrawn: their four length-13 entries do not witness two extra AK(3)-equivalent
presentations of total length 13. Second, their cell of 4 predicts that class C
is not AK(3)-equivalent, because a class count that included C would give at
least 5 at T = 13, whatever the counting convention for the two orders.
[Argument] Class C is the pair

    (x^2 y x y^2,  x y x^-1 y x y^-1)

and the question whether it is AK(3)-equivalent is open here. [Open] This is a
prediction for direction F4 to test.

## 5. Which length-13 members our box fails to reach

The cap-20 census has exactly twelve unordered classes of total length 13.
[Computed] They are exactly the twelve length-13 presentations that c14 labels
AK(3)-equivalent (6) or budget-stopped (6); a normalised membership test finds
none of the twelve missing and none of the other fourteen present. [Computed]
Four of the twelve lie in class A and eight lie in class B. [Computed]

Two of the three length-13 classes are inside the cap-20 box, and A and B
account for all twelve of those classes. The box misses class C: its eight
presentations are all outside, and since c14 exhausted its component at total
length 17 and our census covers total length 20, every AC path from AK(3) to any
of those eight, if one exists, has an intermediate pair of total length at least
21. [Computed as a bounded negative at cap 20, with c14's cap-17 exhaustion as an
independent smaller bound]

Three specific members of class A are worth recording, because they are the
images of AK(3) under the three generators of Aut(F_2) that the paper uses in
Lemmas 5.3 to 5.5. They send AK(3) to

    (y x y X Y X,  y^3 X^4)          total length 13,
    (x Y x y X y,  x^3 y^4)          total length 13,
    (x y x Y X X Y,  x^2 (YX)^4)     total length 16.

COORDINATOR CORRECTION, 2026-11-05 (round 5, from the Whitehead direction of
member m4 of swarm smw38010i, accepted after fresh refereeing; see
directions/whitehead/): the third image above has a one-letter typo. As
printed, x^2 (YX)^4 gives the pair total length 17 and exponent-matrix
determinant 2, so it is not an image of AK(3). The intended word is
x^2 (YX)^3 Y, the image of x^3 y^-4 under y -> y x; with it the pair has total
length 16, determinant 1, and lies in class A, as the text claims. All three
images are in class A once corrected. The same direction resolved the round-4
INCONCLUSIVE flag on the A/B labels: the four-eight split of this section is
correct, certified by twelve single-automorphism certificates, the printed
normal forms of A and B are the canonical least representatives of their
classes, and the audit's length-9 representative of class A was an artifact of
a mistyped relator in the audit's own input (xyXxyX for xyXyxY; that word is
conjugate to y^2 and the pair has determinant 8).

[Computed] All three lie in class A, and all three are inside the cap-20 census,
so they are reachable inside the box. [Computed] The paper proves that
automorphism moves are AC-moves for AK(n) (Corollary 5.7, with computer-assisted
proofs of Lemmas 5.3 to 5.5). [Reported] Their presence in the census is
consistent with that corollary and gives it a small computational check.

COORDINATOR NOTE, 2026-11-05, from the round-4 second-referee audit (member m7
of swarm smw2woueq, draft at directions/second-referees-3/, coordinator-verified
where checkable). The A and B labels of this section, and the four-eight split
of the twelve unordered length-13 classes between them, rest on the normal form
of directions/pu-enumeration/nf.py, whose Whitehead minimisation the audit did
not reimplement. The audit's own bounded orbit normal form (closure inside
total length 25) puts four of the six settled presentations in one class and
two in another, and finds a representative of total length 9 for the class this
file calls A, so the printed normal forms are not confirmed to be minimal
representatives of their automorphism orbits. The item is INCONCLUSIVE in the
audit, not unsound. What is unaffected: the six settled certificates end at
the relator pair of AK(3) (replayed independently in the audit and by the
coordinator), the twelve-classes count, and the class-C exclusion from the
cap-20 box with its cap-17 corroboration. A Round 5 item: reimplement the
Whitehead minimisation and re-derive the four-eight split.

## 6. Six of the 164 resisters fall

The six length-13 presentations that directions/c14/ labels
`resisting-budget-cap19` are in the AK(3) class with every intermediate pair of
total length at most 20, because they are classes of the cap-20 census.
[Computed] This file ships explicit certificates, composed from a short prefix
(conjugation and possibly inversion that presents the pair in the canonical form
of the census) and the reversed census certificate, and both independent
checkers accept all six [Computed]:

| presentation             | moves | checker 1 | checker 2 |
|--------------------------|------:|-----------|-----------|
| BAbABa,BBBAAAA           | 94    | verified  | verified  |
| BAbABa,BBBBAAA           | 91    | verified  | verified  |
| BBAbaa,BBBaabA           | 102   | verified  | verified  |
| BBAbaa,BBaaabA           | 103   | verified  | verified  |
| BBaabA,BBAbaaa           | 103   | verified  | verified  |
| BBaabA,BBBAbaa           | 100   | verified  | verified  |

Checker 1 is `directions/pu-enumeration/replay_certs.py`: "certificates checked:
6, verified: 6, failed: 0, total 593 moves". Checker 2 is the round-1 toolkit:
"toolkit cross-check: 6 lines, 6 verified, 0 failed, 593 elementary moves".
[Computed] The certificates end at the relator pair of AK(3), with the two
relators interchanged in the two swapped cases, which is notational. The
certificate file is `run/certs13_settled.txt`. This result belongs to direction
F4, and it credits directions/c14/ for the classification that produced the list.

These six do not change any class count, since they lie in classes A and B.
They do change the c14 table: 6 of its 22 budget-stopped resisters are now
decided, and the number of undecided presentations at total length 13 is 8.

## 7. The residual deficit at T = 16 to 20

After the doubling, their counts still exceed ours by 6, 46, 98, 808 and 908
entries, which is 3, 23, 49, 404 and 454 classes. [Computed] This part is a
matter of the box: a class-count reading of their cell at T = 16 already needs
43 classes where our box has 40, and two orders per class can give at most 80
entries from 40 classes. [Argument]

The documented differences between the two searches are the box and the moves.
Their box bounds each relator by L and the total by 2L + 2, so at L = 10 it
allows intermediates of total length up to 22, and at L = 20 up to 42; our box
allows 20. [Source] Their search uses ACM-moves, which they prove generate the
same equivalence as AC-moves [Source, Sections 2 and 3], and which can jump
further than the three plain moves at equal box size; our search uses the three
plain moves only. [Source, `rawbox.c` and `rawbox2.c`]

Their L = 10 column is informative: it already gives 4, 10 and 70 at T = 13, 14
and 15, the same values as the L = 20 run, while at T = 16 it gives 64 against
86. [Source] So the length-13 and length-14 counts in their table do not depend
on the per-relator bound at all, and the part of the deficit that starts at
T = 16 grows with the box.

## 8. What could not be completed

The cap-21 census did not finish on this VM. [Computed, bounded negative] A run
of `rawbox3` with T = 21, K = 1, parent pointers on and a hash table of 2^29
slots reached 200,608,294 states after 493 seconds with 4.7 GB of resident
memory and was then killed (exit status 137). The machine had 13.8 GB in use by
other directions' jobs at that moment, so no cap-21 or cap-22 number exists. The
growth from cap 20 to cap 21 is at least a factor 3.9, and a run with 8 bytes of
state, 4 bytes of parent and the hash table needs about 5.3 GB at 400 million
states. A disk-backed layer-by-layer traversal would fit on the 223 GB of free
disk, but the expansion of about 12 neighbours per state makes that a many-hour
job on 4 shared CPUs, and it was not attempted.

Consequences: every statement in this file about "no path with intermediates of
total length at most 20" is a bounded negative at cap 20, and nothing here says
anything about longer intermediates.

## 9. Negative result: the order-sensitive quotient is not canonical this way

To measure the order convention directly I implemented the relation without the
relator swap: automorphisms, inversion of one relator, conjugation of one
relator, with the same greedy Whitehead descent and the same least-cyclic normal
form that the paper uses (`quotients2.py`). On the cap-20 class list it reports
4, 10, 69, 80, 411, 491, 2418, 2448 for T = 13, ..., 20. [Computed] The first
two values coincide with theirs, and the third is one below theirs.

That computation does not pass its own invariance test, and I do not use it as
evidence. [Computed] On 200 sampled classes, applying one random automorphism
and recomputing the order-sensitive normal form changed the answer in 172 cases;
the paper's own normal form, with the swap included, changed in 0 of the same
1200 tests. The greedy descent plus the equal-length orbit at the minimum is
evidently not a complete canonical form once the two words are kept apart. The
factor-two statement in Section 4 therefore rests on the arithmetic 2 x 2 = 4,
2 x 5 = 10, 2 x 35 = 70 and on the class bound of three, and not on this
computation. The log is `logs/nosort_full.log` and the test is `nstest.py`.

## 10. What is not established

1. The reason for the crossing from ratio 2.00 to 2.74 is not measured. The box
   and the move set are both candidates, and neither is isolated here.
2. The class bound of three is conditional on AK(3) not being AC-trivial. If
   AK(3) were AC-trivial, some of the 18,076 length-13 AC-trivial presentations
   could be AK(3)-equivalent and the bound would fail.
3. Class C is not decided. The prediction that it is not AK(3)-equivalent is an
   argument from their cell of 4, not a computation.
4. Their set of four length-13 entries is not exhibited. The conclusion about
   the relator order is an inference from the exact factor two and from the
   class bound, not a reading of their data structures.
5. Their published (journal) table was not read; all numbers come from arXiv v1.
6. No cap-21 number exists, so no statement is made about intermediates of total
   length 21 or more.
7. The paper's Corollary 5.7 rests on its computer-assisted Lemmas 5.3 to 5.5,
   which I did not verify; I only checked that the three automorphism images are
   in class A and in the cap-20 census.

## 11. Files and exact commands

All commands are run in this directory, which is directions/pu-gap, so the round-2 programs are at ../pu-enumeration/ and the c14 files at ../c14/.

Build and run the new enumerator (agrees with `rawbox` at caps 13, 15, 17, 18,
20; 101 seconds and 2.7 GB at cap 20):

    gcc -O2 -march=native -o run/rawbox2 rawbox2.c
    ./run/rawbox2 20 1 -l run/cls2_20.txt -c run/cert2_20.txt

Replay its certificates with round 2's independent checker:

    python3 ../pu-enumeration/replay_certs.py run/cert2_20.txt
      certificates checked: 1124, verified: 1124, failed: 0

Count the PU classes of the cap-20 census with round 2's normal form:

    python3 ../pu-enumeration/puclass2.py run/cls2_20.txt
      selftest: 0 failures ; ~-classes: 2967 ; minlen 13..20 = 2,5,35,40,206,246,1209,1224

The length-13 analysis:

    python3 checks13.py        the six certified, the fourteen undecided, the three automorphism images
    python3 membership.py      convention-independent membership in the cap-20 class list

Compose and replay the six new certificates:

    python3 settle13d.py
    python3 ../pu-enumeration/replay_certs.py run/certs13_settled.txt
      certificates checked: 6, verified: 6, failed: 0
    python3 ../pu-enumeration/xcheck_toolkit.py run/certs13_settled.txt
      toolkit cross-check: 6 lines, 6 verified, 0 failed, 593 elementary moves

The order-sensitive quotient and its invariance test:

    python3 quotients2.py run/cls2_20.txt     (366 seconds, 4 processes)
    python3 nstest.py                          (172 of 200 failures)

Independent checks of the two premises used in Section 4:

    gap -q run/nontrivial13.g                  # order 120 for each of the 20 nontrivial length-13 presentations
    lean ../ak-status/ak_trivial.lean          # AK(n) presents the trivial group, standard axioms only

The failed cap-21 run:

    gcc -O2 -march=native -o run/rawbox3 rawbox3.c
    ./run/rawbox3 21 1 -P -l run/cls2_21.txt     # killed at 200,608,294 states, 4.7 GB

Files in this directory:

* `rawbox2.c`, the enumerator used for the numbers above; `rawbox3.c`, the same
  program with optional parent pointers and a per-40-million-state histogram.
* `checks13.py`, `membership.py`, `settle13d.py`, `quotients2.py`, `nstest.py`.
* `run/`: `cls2_20.txt` (39,840 classes of the cap-20 census, input to
  `puclass2.py`), `cert2_20.txt` (1,124 class certificates), `certs13_settled.txt`
  (the six new certificates). The binaries `run/rawbox2` and `run/rawbox3` are
  rebuilt by the `gcc` lines above.
* `run/nontrivial13.g`: the GAP script that enumerates the cosets of the 20
  nontrivial length-13 presentations.
* `logs/`: `puclass2_cls2_20.log`, `rawbox20.log` (the round-2 enumerator rerun),
  `checks13.log`, `membership.log`, `settle13d.log`, `replay_settled.log`,
  `xcheck_settled.log`, `nosort_full.log`, `rawbox2_caps.log`, `nontrivial13.gap.log`,
  `ak_trivial_rerun.log`.

## 12. Status of each claim

| claim | status | where checked |
|-------|--------|---------------|
| Table 1 cells are per-length counts | source quotation plus the internal monotonicity of the L = 10 column | Section 1 |
| our counts 2, 5, 35, 40, 206, 246, 1209, 1224 | computed twice, with two enumerators and one normal form | Section 2 |
| rawbox2 reproduces rawbox | computed at caps 13, 15, 17, 18, 20 | Section 2 |
| 2 x ours = 4, 10, 70 at T = 13, 14, 15 | arithmetic on computed numbers | Section 3 |
| at most three PU classes of length 13 | argument on c14's complete length-13 census, conditional on AK(3) not being AC-trivial | Section 4 |
| the 20 nontrivial length-13 presentations present a group of order 120 | computed, GAP coset enumeration | Section 4 |
| AK(3) presents the trivial group | computed, Lean rerun of directions/ak-status/ak_trivial.lean, standard axioms | Section 4 |
| the twelve length-13 census classes are c14's twelve AK(3)-listed presentations | computed, normalised membership both ways | Section 5 |
| class C needs intermediates of total length at least 21 | computed bounded negative at cap 20, and c14's cap-17 exhaustion | Section 5 |
| six budget-stopped resisters fall | computed, six certificates, two independent checkers | Section 6 |
| the cap-21 run | failed at 200,608,294 states, 4.7 GB, exit 137 | Section 8 |
| the order-sensitive quotient is not canonical this way | computed, 172 of 200 invariance failures | Section 9 |
