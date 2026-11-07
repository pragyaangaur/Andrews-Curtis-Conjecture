# H2 report: Whitehead minimisation and the A/B split of the twelve length-13 classes

Direction H2 of swarm smw38010i, member m4. All files are in
`.ultramath/smw38010i/m4/`, since the file tools refuse writes outside this
member directory (`fs_create directions/whitehead/probe.txt` answers
`permission_denied`). The deliverable that H2 asked for would sit at
`directions/whitehead/`. Its contents are in this directory and every path is
named below.

## 1. The four questions and the short answers

**(a) Does the twelve split four and eight as `directions/pu-gap/pu-gap.md`
Section 5 says?** Yes. The twelve length-13 conjugation classes of the cap-20
census split into four and eight, and the four are the class the file calls A,
whose normal form is printed there.

**(b) Can the printed normal forms be re-derived?** Yes. The printed forms of A,
B and C are exactly the canonical least representatives of their classes, and
each of the three classes has minimal total length 13 in its PU orbit. I
recomputed them from the definitions with an independent implementation and they
agree character for character.

**(c) Are the classes called A and B as `pu-gap.md` says?** Yes for the split,
for the membership of all twelve, and for both normal forms. One further claim
of Section 5 is wrong as printed, and it is not one of the two normal forms: the
third `Aut(F_2)` image of AK(3) has a one-letter typo, Section 7 below.

**(d) The round-4 audit's length-9 representative of class A?** It does not
exist. The audit mistyped the second relator of A, and its length-9 pair has
exponent-matrix determinant 8, so it is not even a balanced presentation.
Section 6 gives the exact diagnosis, and my engine reproduces the audit's
number 9 from the audit's literal input.

## 2. The objects, and why the PU relation is the `GL(2,Z)` action

Letters are `x=1`, `X=x^-1=-1`, `y=2`, `Y=y^-1=-2`. A cyclic word is a reduced
word modulo cyclic rotation and inversion. A state is an unordered pair of
cyclic words, which is exactly a PU class modulo the relation of
arXiv:1609.00325 Section 4.2: swap the two relators, invert one relator,
conjugate one relator, apply an automorphism of `F(x,y)`.

The PU moves include conjugation of a single relator, and inner automorphisms
act trivially on conjugacy classes. So the PU relation on states is exactly the
action of `Out(F_2) = GL(2,Z)`. The total length of a state is the sum of the
cyclic lengths of its two words, and a PU move changes it, so the least total
length in an orbit is an invariant of the PU class.

## 3. The twelve states

Taken from `directions/pu-enumeration/cls20k1.txt.gz`, which holds the 79,680
conjugation classes of the cap-20 census. Twenty-four rows have total length 13,
and they form twelve unordered states. `work/census_twelve.py` re-derives them
from the gzip file and compares them with the table hard-coded in the second
checker, so no transcription is trusted:

```
python3 census_twelve.py
census rows: 79680
total length distribution: {13: 24, 14: 80, 15: 1032, 16: 1112, 17: 5688, 18: 6456, 19: 31240, 20: 34048}
rows of total length 13: 24
distinct unordered states: 12
...
matched 12 of 12
VERDICT: PASS
```

| label | state (canonical pair) | total length | class |
|---|---|---|---|
| c1 | `(x^3 y^-4, x y x y^-1 x^-1 y^-1)` | 13 | A |
| c2 | `(x^4 y^-3, x y x y^-1 x^-1 y^-1)` | 13 | A |
| c3 | `(x^2 y^2 x^-1 y^-1, x^2 y^-1 x^-1 y^3)` | 13 | B |
| c4 | `(x^3 y^-1 x^-1 y^2, x^2 y^2 x^-1 y^-1)` | 13 | B |
| c5 | `(x^2 y^3 x^-1 y^-1, x^2 y^-1 x^-1 y^2)` | 13 | B |
| c6 | `(x^3 y^2 x^-1 y^-1, x^2 y^-1 x^-1 y^2)` | 13 | B |
| c7 | `(x^3 y^4, x y x^-1 y x y^-1)` | 13 | A |
| c8 | `(x^4 y^3, x y x^-1 y x y^-1)` | 13 | A |
| c9 | `(x^2 y x^-1 y^-3, x^2 y^-2 x^-1 y)` | 13 | B |
| c10 | `(x^2 y x^-1 y^-2, x^2 y^-3 x^-1 y)` | 13 | B |
| c11 | `(x^3 y^-2 x^-1 y, x^2 y x^-1 y^-2)` | 13 | B |
| c12 | `(x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y)` | 13 | B |

The exact printed pairs are in `work/verify_split.py` and in
`work/h2_results.txt` section 3, in the `x/X/y/Y` notation.

Six of the twelve are the length-13 rows of `directions/c14/final_classes.txt`
labelled `ak3-equivalent` (they are c1, c2, c3, c4, c5, c6), and the other six
are the length-13 rows labelled `resisting-budget-cap19` (c7 to c12). That is
the accounting of `pu-gap.md` Section 5: six settled, six formerly
budget-stopped. The six that `directions/pu-gap/run/certs13_settled.txt`
certifies are c7 to c12, so they are two in A and four in B, which is exactly
the "two PU classes" of `pu-gap.md`:

```
python3 settled_six.py
settled certificates: 6
  s1 (xxxxyyy, xyXyxY)        total length 13  reaches A  (orbit size 24, min total length 13)
  s2 (xxxyyyy, xyXyxY)        total length 13  reaches A  (orbit size 24, min total length 13)
  s3 (xxyXYYY, xxYYXy)        total length 13  reaches B  (orbit size 56, min total length 13)
  s4 (xxxyXYY, xxYYXy)        total length 13  reaches B  (orbit size 56, min total length 13)
  s5 (xxxYYXy, xxyXYY)        total length 13  reaches B  (orbit size 56, min total length 13)
  s6 (xxyXYY, xxYYYXy)        total length 13  reaches B  (orbit size 56, min total length 13)
split of the six: {'A': 2, 'B': 4}
VERDICT: PASS
```

## 4. The split, with a certificate per member

Each of the eight members of a class is carried to the class representative by
ONE automorphism. `work/certs_split.txt` is the certificate file, and
`work/verify_split.py` is a second checker written from the definitions with no
shared code, which first self-tests its own cyclic canonical form, then checks
that each table automorphism has its verified inverse, then checks the twelve
certificates:

```
python3 verify_split.py certs_split.txt
self test of the cyclic canonical form: 0 failures
automorphism table: 8 entries, 0 with a bad inverse
...
  c1   --id --> c1    OK
  c2   --Sw --> c1    OK
  c7   --D  --> c1    OK
  c8   --S  --> c1    OK
  c3   --id --> c3    OK
  c4   --B  --> c3    OK
  c5   --A  --> c3    OK
  c6   --Sw --> c3    OK
  c9   --D2 --> c3    OK
  c10  --D  --> c3    OK
  c11  --S  --> c3    OK
  c12  --Si --> c3    OK
class A states 4, class B states 8, intersection 0, twelve distinct True
certificates checked: 12 of 12
VERDICT: PASS
```

The automorphisms are `S: x->y, y->X`; `Si: x->Y, y->x`; `Sw: x->y, y->x`;
`D: x->X`; `D2: y->Y`; `A: x->X, y->Y`; `B: x->Y, y->X`. So class A is
`{c1, Sw c1, D c1, S c1}` and class B is
`{c3, B c3, A c3, Sw c3, D2 c3, D c3, S c3, Si c3}`.

The engine `work/wh.py` reaches the same partition by breadth-first search over
orbits of total length at most 18, and `work/h2_main.py` section 4 reports two
distinct orbit sets of sizes 24 and 56.

## 5. Minimal total length 13, and what makes the argument complete

The engine does not decide minimality by the greedy descent of
`directions/pu-enumeration/nf.py`. It uses Whitehead's peak reduction for
tuples, Lyndon and Schupp, Combinatorial Group Theory, Proposition I.4.20: if a
tuple of conjugacy classes is not of minimal total length in its automorphism
orbit, then some Whitehead automorphism strictly decreases its total length. I
confirmed the statement for tuples of conjugacy classes, with the total length as
the weight, from the statement quoted in the geometric topology paper
`msp.org/gt/2009/13-2/gt-v13-n2-p07-p.pdf` ("The peak reduction theorem for a
free group Fn states that there is a finite generating set for Aut Fn, called the
Whitehead automorphisms, such that Aut Fn has peak reduction with respect to any
k-tuple of conjugacy classes").

So the check is finite: at a state of total length 13, apply every generator in
the set and verify that none lowers the total length. `work/h2_main.py`
section 2 verifies that my 31-generator set contains the classical 20
Whitehead automorphisms of `F_2` (`0 missing`), and section 5 reports

```
class A: min total length 13, level set size 4, least generator image length from a minimal state 13
class B: min total length 13, level set size 8, least generator image length from a minimal state 13
class C: min total length 13, level set size 16, least generator image length from a minimal state 13
```

Since no generator lowers the length and a lowering Whitehead automorphism would
be in the set, 13 is the minimum by peak reduction. The level sets are exactly
the twelve census states for A and B, so those twelve are all the states of
minimal length in the two classes.

`work/cap_escalation.py` corroborates this without relying on the theorem: the
orbit of each class is closed up to total length 50 and no state below 13 ever
appears (`work/cap_escalation.log`). At cap 50 the class sizes are 420, 1416 and
1152 states. That run takes 45 seconds and 17 MB.

`work/level_set.py` asks how many states of minimal length each class has, and
whether the count grows with the cap. A minimal state reachable only through a
higher peak would appear only at a higher cap, so this measures how complete the
level set is:

```
cap 22  A: min 13 level  4 orbit    60 | B: min 13 level  8 orbit   152 | C: min 13 level 16 orbit   160
cap 36  A: min 13 level  4 orbit   200 | B: min 13 level  8 orbit   616 | C: min 13 level 16 orbit   560
cap 50  A: min 13 level  4 orbit   420 | B: min 13 level  8 orbit  1416 | C: min 13 level 16 orbit  1152
```

The counts are constant while the orbits grow by a factor of seven, so the four
and the eight are the whole level sets as far as this engine can see. The
minimum itself, 13, does not depend on this: peak reduction proves it.

## 6. The round-4 audit's length-9 representative: the exact diagnosis

`directions/second-referees-3/pu_normal_form.py` writes class A as
`names["A"] = ((1,1,1,1,2,2,2), (1,2,-1,1,2,-1))`. The second tuple is the
string `xyXxyX`, not `xyXyxY`. So the audit's A is
`(x^4 y^3, x y x^-1 x y x^-1)`, and `x y x^-1 x y x^-1` freely reduces to
`x y^2 x^-1`, a conjugate of `y^2`. The pair is therefore PU-equivalent to
`(x^4 y^3, y^2)`, of total length 9, and its exponent matrix has determinant
`4*2 - 3*0 = 8`, so it is not a balanced presentation of the trivial group at
all.

My engine reproduces the audit's number from the audit's literal input, and
gives 13 from the correct input:

```
python3 h2_main.py (section 9)
audit's A second relator literal xyXxyX: reduced xyyX cyclic yy
its pair (x^4 y^3, xyXxyX): orbit min total length 9, orbit size 48, least (xx, xxxYYYY)
exponent vectors (4, 3) (0, 2) determinant 8
the printed A with the correct relator xyx^-1yxy^-1: orbit min total length 13, orbit size 24
```

The audit's own engine shows the same thing, and it also shows that the audit's
own normal form routine returns 13, not 9, on the corrected input:

```
python3 audit_engine_probe.py
audit's literal second relator: (1, 2, -1, 1, 2, -1) = abAabA
  reduced: abbA
printed relator xyx^-1yxy^-1: (1, 2, -1, 2, 1, -2) = abAbaB

audit's literal A  minimum total length by bound: [(13, 9), (15, 9), (17, 9), (19, 9)]
   exponent vectors (4, 3) (0, 2) determinant 8
corrected A        minimum total length by bound: [(13, 13), (15, 13), (17, 13), (19, 13)]
   exponent vectors (4, 3) (1, 1) determinant 1
```

There is also a reason to expect the audit's finding to be impossible before
checking it. A state of total length at most 12 in the PU class of AK(3) would
be a balanced presentation of the trivial group of total length at most 12, so
it would be AC-trivial by Miasnikov and Myasnikov (2001), as recorded in
`survey/ak-status.md` [L, not read by me in the original], and the PU moves on
AK(3)-presentations are AC-moves by Panteleev and Ushakov's Corollary 5.7
[Reported]. That
chain would prove AK(3) AC-trivial. This is an argument and it is not a result
of this direction; it explains why the audit's number needed a diagnosis. I make
no claim about the AC-triviality of AK(3) anywhere in this report.

## 7. The printed normal forms, and the one wrong item in pu-gap Section 5

The canonical least representatives, computed as the least state of minimal
total length in the whole orbit of total length at most 18 under the letter order
`x < X < y < Y`, are:

```
class A: least representative (xxxxyyy, xyXyxY)  printed form (xxxxyyy, xyXyxY)  equal True
class B: least representative (xxxyXYY, xxYYXy)  printed form (xxxyXYY, xxYYXy)  equal True
class C: least representative (xxxyxyy, xyXyxY)  printed form (xxxyxyy, xyXyxY)  equal True
```

So `pu-gap.md`'s printed `A = (x^4 y^3, x y x^-1 y x y^-1)`,
`B = (x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y)` and the CORRECTED
`C = (x^3 y x y^2, x y x^-1 y x y^-1)` are all correct, and the round-4
coordinator correction of the class-C relator is confirmed. Note that
`nf.py`'s normal form is not the same function as the least state in the
orbit: it is the least state among those its greedy descent reaches, and on
these three classes the two agree. I also checked that `nf.py`'s normal form
behaves as a function of the class on 200 random automorphic images of each
representative, of length up to four generator applications, with no exception
(`work/nf_function_test.py`).

The third `Aut(F_2)` image of AK(3) printed in Section 5 is wrong as printed. It
says `(x y x Y X X Y, x^2 (YX)^4)` with total length 16. As printed the pair has
total length 17 and exponent-matrix determinant 2, so it cannot be an image of
AK(3). The intended word is `x^2 (YX)^3 Y`, which is the image of `x^3 y^-4`
under `y -> y x`; with that word the pair is the image of AK(3) under `y -> yx`,
has total length 16, determinant 1, and lies in class A:

```
python3 h2_main.py (section 10)
  yxyXYX,yyyXXXX           printed length 13, cyclic length 13, determinant -1, in class A: True  orbit min 13
  xYxyXy,xxxyyyy           printed length 13, cyclic length 13, determinant -1, in class A: True  orbit min 13
  xyxYXXY,xxYXYXYXY        printed length 16, cyclic length 16, determinant  1, in class A: True  orbit min 13
  xyxYXXY,xxYXYXYXYX       printed length 17, cyclic length 15, determinant -2, in class A: False orbit min 12
```

The first two images are the swap `x<->y` and the inversion `y -> y^-1` applied
to AK(3), and `work/h2_main.py` confirms that their canonical states are exactly
c2 and c7. So two of the three images are in class A as claimed, and the third
is in class A once the typo is corrected.

## 8. Why A, B and C are three different classes

A certificate cannot separate classes. The separation here is an invariant. For
a cyclic word `w` let `m(w)` be the least cyclic length in the `Aut(F_2)`-orbit
of its conjugacy class. An automorphism maps single-word orbits to single-word
orbits, single-relator inversion does not change the orbit, and swapping only
interchanges the two words, so the multiset `{m(u), m(v)}` is an invariant of
the PU class of the state `(u,v)`. `m` is computed exactly by Whitehead's peak
reduction for the single-word case, which is the classical theorem and part of
the tuple version cited in Section 5. The values are

```
[5, 7] on ['c1', 'c2', 'c7', 'c8']
[6, 7] on ['c3', 'c4', 'c5', 'c6', 'c9', 'c10', 'c11', 'c12']
invariant values: {'A': (5, 7), 'B': (6, 7), 'C': (5, 6)}
```

so the three classes are pairwise distinct. The shortening witnesses are one
generator each. For AK(3)'s second relator `x y x y^-1 x^-1 y^-1` the trail is
`Ti`, which sends `x` to `x y^-1`. For class C's first relator `x^3 y x y^2` the
trail is `W_x_c`, which sends `x` to `x^-1 y`, and for its second relator
`x y x^-1 y x y^-1` the trail is `T`, which sends `x` to `x y`
(`work/h2_main.py` section 7).

## 9. Class C, and a caution about PU classes

The eight length-13 rows of `directions/c14/final_classes.txt` labelled
`resisting-exhausted-cap17` all lie in the PU class of the corrected C, and the
corrected printed form is its least representative. The level set of class C at
total length 13 has sixteen states, not eight. The other eight are labelled
`ac-trivial` by `directions/c14/final_classes.txt`:

```
python3 class_c_level.py (output in work/class_c_level.txt)
class C minlen 13 level set 16
class C level states found in c14's length-13 list: 16
Counter({'resisting-exhausted-cap17': 8, 'ac-trivial': 8})
```

This is a caution for the campaign. It is an argument: the PU relation contains a change of generators applied to both
relators, which is not an AC-move in general, and the reason PU moves are
AC-moves on AK(3)-presentations is Panteleev and Ushakov's Corollary 5.7 as
read in `directions/pu-gap/pu-gap.md` [Reported, not read by me in the paper].
Class C's presentations are not known to be AK(3)-presentations, so the
corollary does not reach them, and two PU-equivalent presentations need not be
AC-equivalent. Class C exhibits that inside one class at one total length.

[Coordinator note, 6 November 2026 (round 7, from the cap-25 direction of
member m9 of swarm smw48or9f, accepted; coordinator-rerun): the last sentence
is WITHDRAWN — class C does not exhibit it. All sixteen states of the level
set above are AC-trivial: the eight labelled ac-trivial at exact minimal peak
15, and the eight labelled resisting-exhausted-cap17 at exact minimal peak 18
(cap-17 exhaustion at 136,576 states, cap-18 find), each with a replayed
certificate to the standard pair. So all sixteen are AC-equivalent to each
other, and the 8/8 split this section cites was the boundary of the round-2
c14 enumeration's AC-triviality test (the standard tuple's cap-15 ball), not
an AC distinction — see the dated note in `directions/c14/c14.md`. The
general point of the caution stands: the PU relation contains generator
changes that are not AC moves in general; class C is just no longer an example
of it. Consequence recorded in `directions/cap25/cap25-round7.md`: since a
member of class C is AC-trivial, class C is AK(3)-equivalent if and only if
AK(3) is AC-trivial, so the pu-gap prediction that class C is not
AK(3)-equivalent is exactly the prediction that AK(3) is not AC-trivial.]

## 10. Cross-checks against the other normal form implementations

`directions/cap21/punf.py`, written by member m5 in round 4 and sharing no code
with mine, gives two canonical forms with minimal length 13 and the same 4 and 8
split on the same twelve inputs (`work/twelve_punf.txt`, produced by
`work/run_all.sh` step 7). `directions/pu-enumeration/nf.py` gives the printed
forms `(xxxxyyy,xyXyxY)` for c1, c2, c7, c8 and `(xxxyXYY,xxYYXy)` for the other
eight. GAP confirms that all twelve present the trivial group, as they must
since the census contains them:

```
gap -q orders2.g          (mk_gap.py regenerates it from the census rows)
c1  abelian order = 1   coset size = 1
...
c12 abelian order = 1   coset size = 1
AK3 abelian order = 1   coset size = 1
```

## 11. Claims, with their status

| claim | status |
|---|---|
| the twelve length-13 census classes split 4 and 8 | computed, twelve single-generator certificates, verified by a second checker (`verify_split.py` PASS) |
| A = {c1,c2,c7,c8}, B = the other eight, and c1 is AK(3) itself | computed and certified |
| the printed A, B and corrected C are the canonical least representatives | computed, equal character for character |
| each of the three classes has minimal total length 13 | computed local minimality plus Lyndon-Schupp I.4.20 (argument, cited) |
| A, B and C are pairwise distinct classes | argument, invariant `{m(u),m(v)}` |
| no state of total length at most 12 in any of the three orbits, for orbit peaks up to 50 | computed (bounded statement) |
| the audit's length-9 representative of class A | refuted: the audit's relator literal is `xyXxyX`, which is conjugate to `y^2`; that pair has determinant 8 |
| the audit's qualitative count, four settled in B and two in another class | confirmed, with the other class being A |
| `pu-gap.md` Section 5's third `Aut(F_2)` image | one-letter typo; `x^2 (YX)^4` should be `x^2 (YX)^3 Y`; corrected, the claim holds |
| a length-at-most-12 member of class A would prove AK(3) AC-trivial | argument, not used as a result; no claim about AK(3) is made |

## 12. What I did not verify, and what stays uncertain

I did not re-run the cap-20 census. `work/census_twelve.py` reads its stored
class list `directions/pu-enumeration/cls20k1.txt.gz`, whose count 79,680 was
refereed in round 4. If that file is wrong, the twelve and everything built on
them are wrong.

Peak reduction is cited from Lyndon and Schupp and not formalised. Nothing in
this direction is in the Lean kernel. The finite part, that no generator of my
31 lowers the total length at a minimal state, is computed here, and
`work/h2_main.py` section 2 checks that the 31 contain the classical 20
Whitehead automorphisms.

The separation of A, B and C rests on the invariant `{m(u),m(v)}`. It is a
necessary condition only, so it separates and does not identify. The
identification of the members is done by the certificates.

The least representative of a class is the least state of minimal length that
the search reaches. A minimal state reachable only through a peak above 50 is
not excluded, so the phrase "canonical least representative" here is relative to
the level set the engine found. `work/level_set.py` shows that the level set
does not grow from cap 18 to cap 50, and the comparison that matters, with the
printed forms of A, B and C, is an equality of states and needs no canonicity
claim.

Whether class C is AK(3)-equivalent stays open here. My class C computation
concerns the PU relation only, and Section 9 shows that PU equivalence is
strictly weaker than AC equivalence at these lengths.

I did not prove anything about the peak heights a path between class A and class
B would need. The cap-50 search is a bounded statement about one engine's
radius.

All computations are deterministic. The only randomness is in
`work/test_wh.py` and `work/nf_function_test.py`, both seeded.

## 13. Files, and how to rerun everything

```
work/run_all.sh            one command, every check, about 110 s, 18 MB peak
work/wh.py                 the engine: cyclic canonical form, 31 automorphisms
                           with verified inverses, orbit search
work/wmin.py               single-word Whitehead minimisation and its witnesses
work/test_wh.py            engine unit checks: generator inverses, invariance
                           of the cyclic canonical form, 0 failures
work/census_twelve.py      re-derives the twelve from the census gzip and
                           compares them with the checker's table, 12 of 12
work/verify_split.py       standalone second checker of the split, PASS
work/certs_split.txt       the twelve certificates, one automorphism each
work/h2_main.py            the eleven sections quoted in this report
work/h2_results.txt        its full output
work/cap_escalation.py     the orbit search to total length 50
work/cap_escalation.log    its output, minimum 13 at every cap
work/nf_function_test.py   nf.py's normal form on 400 random automorphic images
work/settled_six.py        the six settled presentations sorted into A and B
work/nf_crosscheck.py      nf.py's own normal forms on the twelve, groups 4 and 8
work/twelve_cls.txt        the twelve in punf.py's input format
work/twelve_punf.txt       punf.py's output on them, two forms, split 4 and 8
work/mk_punf_in.py         writes twelve_cls.txt from the twelve
work/render_table.py       the power-notation table of Section 3, every row
                           re-parsed back to its state, 0 mismatches
work/gen_certs.py          regenerates certs_split.txt from the engine
work/audit_engine_probe.py the round-4 audit's own normal form on its literal
                           A and on the corrected A, giving 9 and 13
work/level_set.py          the minimal-length level set against the cap
work/class_c_level.py      the class C level set against c14's labels
work/class_c_level.txt     its output, 8 and 8
work/orders2.g             the GAP presentation check of the twelve
work/mk_gap.py             regenerates orders2.g
work/twelve.json           the twelve census rows, for mk_gap.py
work/run_all.log           the complete output of run_all.sh
explore/                   one-off scripts kept for completeness, not needed
```

Exact commands and their key output are in Section 4, 6 and 7 above, and in
`work/h2_results.txt`. The heavy runs take 10 seconds (`h2_main.py`), 45
seconds (`cap_escalation.py`) and 45 seconds (`level_set.py`). No run needed more than 18 MB of memory, so the
VM's 16 GB and 4 CPUs were never a constraint.
