# Second referees 2: fresh-context audit of the Round 2 artifacts

Round 3 direction F9 (member m4). This report audits four Round 2 artifacts with
code written from the definitions and checked against the artifacts' own data.
It makes no claim about the truth or falsehood of the Andrews-Curtis
conjecture, and it rounds nothing up. Everything below is either a computation
I reran with a command printed in section 6, or a labelled argument.

## 0. Verdicts

| Target | Verdict |
|---|---|
| (a) `directions/c14/`: the length-14 census, the classification, the PSL(2,7) witnesses, the pruning audit, the 164 resisters | **SOUND**. Every number I could rebuild from the definitions came back identical, including all 142 exhausted bounds and all 22 budget claims. Three documentation defects found, listed in section 2.7, none of them a computational error. |
| (b) `directions/pu-enumeration/`: the AK(3) box census, the class quotient, the certificate files, the PU-class counts | **SOUND**. All 100,240 certificates replay under my own parser. The raw counts, the conjugation-class counts and the PU-class counts are reproduced independently at every cap from 13 to 17. The cap-20 class count rests on one implementation whose normal form I tested for class invariance, with no failure. |
| (c) `survey/quinn-tqft.md` | **SOUND** for every claim it labels machine-checked or argument from citation. I recomputed the two load-bearing computations (the invariant forms and Ostrik's fusion rule) from scratch, and I verified the two load-bearing citations against live records. One exposition gap in Lemma 1, repaired in one line in section 4.4. |
| (d) `directions/ms-ak-certs/` | **SOUND**. All 18 certificates replay with an independent word engine against endpoints recomputed from the prose definitions, and the Lean file checks with no axioms. |

## 1. How this referee worked

I wrote my own word engine, canonical enumeration, certificate replayer, ball
search and quotient search before reading the target code, and I compared
outputs rather than implementations. My code is in
`.ultramath/smw2opo0o/m4/` and consists of `w.py` (words as integer tuples),
`enum_mine.py` (the Havas-Ramsay canonical enumeration), `replay_mine.py` (the
`c14` certificate format), `check_classes.py` and `audit2.py` (the `c14` class
file against my enumeration), `ball.py` and `spot.py` and `batch_resisters.py`
and `budget_check.py` (the `c14` balls and resisters), `quotient_check.py` (the
`A5` and `PSL(2,7)` quotient witnesses), `ms_slice.py` and `ms_slice2.py` (the
Miller-Schupp slice), `pu_replay.py` (the `pu-enumeration` certificate format),
`pu_counts.py` and `pu_counts2.py` and `pu_nfcount.py` (the box, its class
counts and the PU quotient), `nf_inv.py` (the invariance test of the PU normal
form), `quinn_forms.py` (the two computations of the Quinn survey) and
`mscerts_replay.py` (the `ms-ak-certs` JSON certificates).

For the targets' own programs I reran what can be rerun and treated a rerun as
evidence only where I also reproduced the number another way. The two places
where I depend on a target's own code are named as such in sections 3.5 and
4.3, and in both cases I tested the property that makes the code's output
mean what it claims to mean.

## 2. Target (a): `directions/c14/`

### 2.1 The canonical enumeration at length 14

I wrote the enumeration from the description in `c14.md` section 1 and from
Havas and Ramsay's steps (A) to (D) as the file states them. Relators are
freely and cyclically reduced and minimal under rotation and inversion, and
the pair is ordered by (length, word). Step (A) keeps the pairs with both
generators present and with distinct nonempty relators, step (B) keeps
abelianised determinant plus or minus one, step (C) removes a pair when one
relator is a cyclic subword of the other, and step (D) removes a pair when a
relator has the form $x_i = x_j^m$.

My counts, printed by `python3 enum_mine.py 14`:

```
L = 10: canonical    6025 | (A)    5991 | (B)    608 | (C)     44 | (D)     20 | (C)-(D)   24
L = 11: canonical   16606 | (A)   16596 | (B)   2540 | (C)    204 | (D)    104 | (C)-(D)  100
L = 12: canonical   46321 | (A)   46245 | (B)   4396 | (C)    320 | (D)    204 | (C)-(D)  116
L = 13: canonical  129964 | (A)  129952 | (B)  18116 | (C)   1992 | (D)   1400 | (C)-(D)  592
L = 14: canonical  366989 | (A)  366819 | (B)  31556 | (C)   3272 | (D)   2624 | (C)-(D)  648
```

The published list sizes 20, 104, 204 and 1400 are reproduced at lengths 10 to
13. The length-14 row matches `c14.md` exactly in every column that the file
reports: (A) 366819, (B) 31556, (C) 3272, (D) 2624, and 648 step-(D)
discards. My pre-(A) row count is 366989 rather than 366819, which is a
harmless convention difference: their generator counts already exclude pairs
with a missing generator, and my step (A) removes those 170 pairs.

The stronger check is on the contents rather than the counts. I canonicalised
the 54,068 lines of `final_classes.txt` with my own canonical form and compared
the resulting set of orbits with my own step-(B) lists. The result is equality
at each length with no duplicates:

```
L=12: class file 4396, distinct orbits 4396, orbit-duplicates 0
   orbits only in my list: 0, only in theirs: 0
L=13: class file 18116, distinct orbits 18116, orbit-duplicates 0
   orbits only in my list: 0, only in theirs: 0
L=14: class file 31556, distinct orbits 31556, orbit-duplicates 0
   orbits only in my list: 0, only in theirs: 0
```

So the length-14 list is complete and free of double counting. The class file
describes exactly the same set of presentations that the enumeration produces.

### 2.2 The certificates

`replay_mine.py` is an independent replayer for the `start|moves|end` format.
It has its own parser and its own free reduction, and the three move types are
implemented from the descriptions rather than from `replay14.py`. On the full file it
prints

```
replayed 53866 certificates, 0 failed, longest 141 moves
distinct starts: 53866
```

That reproduces the file's claim (53,866 certificates, 0 failed, longest 141).
Going further, `audit2.py` shows that the map from certificates to class labels
is a bijection: the 53,866 certificate starts are exactly the 53,866 lines
labelled `ac-trivial` or `ak3-equivalent`, and the 26 certificates that do not
end at `std` are exactly the 26 lines labelled `ak3-equivalent`, each ending at
the AK(3) pair `aaaBBBB,abaBAB` or its swap. Every certificate start is either
the class-file pair or its swap, and the swap count is 26,343, which is the
number `c14.md` section 5 states.

### 2.3 The 38 nontrivial presentations

I did not read their quotient code. I searched all pairs of images in $A_5$
(order 60) and in $\mathrm{PSL}(2,7) = GL(3,2)$ (order 168, acting on the seven
nonzero vectors of $\mathbb{F}_2^3$), kept the pairs that kill both relators,
and closed the generated subgroup to test surjectivity. The outcome, printed by
`quotient_check.py`:

* the 34 presentations labelled `nontrivial-quotient-A5` each have 121
  homomorphisms to $A_5$ and a surjection onto $A_5$, and no nontrivial
  homomorphism to $GL(3,2)$;
* the 4 labelled `nontrivial-quotient-PSL27` each have a surjection onto
  $GL(3,2)$ (337 homomorphisms, 336 of them surjective) and only the trivial
  homomorphism to $A_5$.

All 38 are therefore presentations of nontrivial groups, and the four
$GL(3,2)$ cases are exactly the ones claimed. GAP 4.14 confirms the orders:
`Size` returns 120 for each of the 34, and for the four cases the coset
enumeration does not close and GAP aborts at its memory limit.

All 38 verdicts of nontriviality therefore stand on a witness that I built
myself. The four cases with a $\mathrm{PSL}(2,7)$ quotient are also the source
of the first documentation defect, recorded in section 2.7.

### 2.4 The 164 resisters

This is the part of `c14` that a replayed certificate cannot check, so I
re-explored every component myself. My criterion is exact and avoids their
balls. If a presentation $t$ is AC-trivial with every intermediate pair of
total relator length at most $C$, then the vertex before the last move is one
move away from the standard pair, so it lies in the one-move neighbourhood of
$(a,b)$, and that neighbourhood has total length at most 5. Conversely, a
component that meets that neighbourhood is AC-trivial inside the cap. The same
argument with AK(3) in place of the standard pair decides AK(3)-equivalence
inside the cap. So a complete exploration of the component inside the cap,
followed by an intersection test with two small sets, decides the claim.

`batch_resisters.py` does that with my own move generator, with no depth limit
and no budget. Its output is uniform, and the three groups of labels behave the
same way:

* 34 presentations labelled `resisting-exhausted-cap17`: components of size
  36968, 136576 or 207320 pairs, exploration complete, 0 hits against either
  neighbourhood;
* 40 labelled `resisting-exhausted-cap18`: components of size between 45888
  and 106800, complete, 0 hits;
* 68 labelled `resisting-exhausted-cap19`: components of size between 89856
  and 383936, complete, 0 hits.

The component sizes agree with the numbers recorded in `mitm17_results.txt`
where both exist. For example, `BAbABa,BBAAABA` at cap 17 gives 136576 in my
code and 136576 in theirs.

`budget_check.py` explores the 22 `resisting-budget-cap19` presentations with a
budget of 400,001 pairs. All 22 exceed it, which is what "stopped at 400000
distinct pairs" means. So the 164 labels are right, and section 2.7 states what
the negative half of them does and does not cover.

### 2.5 The Miller-Schupp slice

`ms_slice2.py` builds $MS(n,w) = \langle a,b \mid a^{-1} b^n a = b^{n+1}, a = w\rangle$
for $n$ from 1 to 7 and $|w|$ from 0 to 7, canonicalises, and keeps the pairs of
total relator length 14. I get 4843 canonical presentations in the family and
191 in the length-14 slice, of which 51 are unimodular: 45 `ac-trivial`, one
`ak3-equivalent` and 5 `resisting`. The exponent-sum-zero subfamily has 889 and
41 members. Every one of these numbers matches `c14.md` section 8, and the five
resisting presentations are exactly the five listed there. With the relator for
$a = w$ written as $a w^{-1}$ instead of $a^{-1} w$ the same numbers appear, so
the slice does not depend on that convention once the relator is canonicalised.

I made one mistake on the way to this check and record it because it is
instructive. My first computation put the total length at 14 before cyclic
canonicalisation and got 229 canonical presentations and 63 unimodular ones.
The canonical pair can be shorter than the presenting pair, and `c14.md` slices
after canonicalisation, which is what their code does and what I then did. The
earlier numbers were mine, not theirs.

### 2.6 Ball sizes and the meet-in-the-middle argument

`ball.py` reproduces the ball sizes quoted in `c14.md` section 3 at every size I
could hold in memory:

```
ak3 ball at cap 13: 168 pairs, max depth 8
ak3 ball at cap 14: 168 pairs, max depth 8
ak3 ball at cap 15: 6864 pairs, max depth 26
ak3 ball at cap 16: 20560 pairs, max depth 39
ak3 ball at cap 17: 857808 pairs, max depth 87
std ball at cap 11: 700712 pairs, max depth 21
std ball at cap 12: 1582280 pairs, max depth 26
```

The cap-13, cap-14 and cap-15 balls of the standard pair (6,476,104 and
14,399,816 and 58,487,624 pairs) are beyond what my Python search holds, and I
did not verify them. The two I did verify match exactly, and the four AK(3)
balls match exactly.

The meet-in-the-middle step of `c14.md` section 3 is described as the only
place where the classification rests on reasoning, so I checked the reasoning.
It is sound, and the wording is looser than the argument needs. Their negative
test asks whether the component meets the cap-14 ball of the standard pair. The
path of a successful proof inside the cap ends at the standard pair, and the
vertex before the last move has total length at most 5, so it lies in the
cap-14 ball. Hence the negative test is complete, and the positive tests
produce genuine certificates by construction. The sentence "must pass through
the standard pair and therefore through a pair of the cap-14 ball" is true only
because the standard pair itself is in that ball; the load-bearing vertex is the
one before the last move. A rewrite would help a reader, and the conclusion
stands.

### 2.7 Three documentation defects

**Defect 1, a false sentence about the group orders.** `c14.md` section 4 says
"The 38 nontrivial presentations all present a group of order 120". The same
paragraph then says that for the four length-14 cases the certificate is a
homomorphism onto $\mathrm{PSL}(2,7)$ and their order is not determined. The
two statements cannot both hold, and the first is false: a group of order 120
has no quotient of order 168. The correct statement is that the 34
$A_5$-labelled presentations present groups of order 120 (GAP, and Todd-Coxeter
in their own run), and that the four $\mathrm{PSL}(2,7)$-labelled ones have
order divisible by 168 and are not determined here. The classification itself is
unaffected, since a nontrivial quotient is all that the verdict needs.

**Defect 2, the scope of the negative bounds.** The whole computation lives in
the twelve-move system, where a relator is conjugated by one generator at a
time. Section 6 then states that no AC proof exists whose intermediate pairs
have total relator length within the cap. That conclusion needs a qualifier.
The full AC move set allows conjugation by an arbitrary word as one move, and
simulating it by generator conjugations can push the intermediate length above
the cap even when the conjugated relator is short. The exact witness, found by
searching all relators and words of length at most 6, is $r = xy$ with
$w = xy$: the single AC move replaces $r$ by $w r w^{-1} = xy$ of length 2,
while the two generator conjugations pass through $x^2 y x^{-1}$ of length 4.
The worst case in that search is $r = xy$ with $w = (xy)^3$, where a single AC
move keeps length 2 and the generator simulation reaches length 12. So the
verified statement is: no proof in the twelve-move system with intermediates
inside the cap. Section 9.5 already notes that the positive certificates are
certificates in the full system, since each restricted move is an AC move, and
the negative side needs the matching caveat. I checked the corresponding point
in `directions/pu-enumeration/` too: there the conjugator bound is a parameter,
and raising it from 1 to 2 leaves the cap-13, cap-16 and cap-17 vertex sets
unchanged in my own runs.

**Defect 3, a table row that does not add up.** In the table of section 4 the
total row reads `| total | 57765 | 53840 | 26 | 38 | 142 | 22 |`. The
classification columns sum to 54068, which is the number of lines of
`final_classes.txt` and the sum of the length-12, 13 and 14 canonical counts.
The first cell, 57765, is the cumulative count over lengths 2 to 14 and
includes the 3697 presentations of lengths at most 11, which the other columns
do not. Either the first cell should be 54068 for the classified range, or the
AC-trivial cell should be 57537. The surrounding text is consistent with the
54068 reading, so this is a slip in one cell and not a lost presentation.

## 3. Target (b): `directions/pu-enumeration/`

### 3.1 The box and the raw counts

My own breadth-first search from AK(3), with the three AC moves and
conjugation restricted to one generator, gives 168, 168, 6864, 20560 and 857808
tuples at total-length caps 13 to 17. Those are exactly the raw tuple counts in
the table of `pu.md`. The match at five consecutive caps, including the
jump from 6864 to 20560 and the jump to 857808, is strong evidence that the
move enumeration and the box are the same in both implementations.

### 3.2 The conjugation classes

`pu.md` reports 1, 1, 26, 80, 2000 and 40048 classes under conjugation and
inversion of the relators at caps 13 to 19. My count reproduces 1, 1, 26 and 80
at caps 13 to 16 and 2000 at cap 17, with one clarification: the class is the
ordered pair of cyclic classes, so swapping the two relators is not part of this
quotient. Counting unordered pairs gives 40 at cap 16 and 1000 at cap 17, which
is half. The ordered reading is the one their code uses and the one their
sentence describes, since swap appears only in the list of PU moves.

I also tested the conjugator bound independently. Allowing every conjugator of
length at most 2 gives the same vertex set as allowing one generator at caps 13,
16 and 17, with the same class counts. Their claim that the bound is not the
binding constraint therefore holds where I could test it.

### 3.3 The certificate files

`pu_replay.py` is my own parser for the `class N start ... moves ... end ...`
format: words as length-prefixed integer lists, `iN` for inversion, `cN=w` for
conjugation by the word $w$, and `mNM` for multiplication. Its output:

```
cert16all.txt: certificates 20560, verified 20560, failed 0, moves total 388717, max 39
cert20k1.txt.gz: certificates 79680, verified 79680, failed 0, moves total 4640600, max 142
shortest_two.cert: certificates 2, verified 2, failed 0, moves total 37, max 36
```

The move totals and maxima match `pu.md` exactly. Every tuple in the cap-16
census and every class representative in the cap-20 census therefore has an
explicit, replayable path from AK(3).

### 3.4 The shortest members

`shortest_two.cert` replays. Its two normal forms are reached in 1 move and in
36 moves from AK(3), which matches section 7 of `pu.md`. My own PU-class count
at cap 17 gives exactly 2 classes of minimal total length 13 and 7 of minimal
length at most 14, which agrees with the claim that the second length-13 class
exists and that AK(3) is not alone at the minimal length.

The bounded negative "every relator has length at least 5" is not testable at
cap 20 with my code. At cap 17 the minimum relator length in the ball is 6, so
the reported length-5 relators first appear with two more units of room, which
is consistent but not verified.

### 3.5 The PU-class counts

The PU relation is generated by swapping the relators, inverting one relator,
conjugating one relator, and applying an automorphism of $F_2$. The count in
`pu.md` is produced by their `nf.py`, whose `canonical` function descends on
total length by 20 automorphisms and then takes the least element among the
minimal-length orbit elements reachable through minimal-length steps. A count of
distinct normal forms equals the number of classes exactly when the normal form
is a genuine orbit invariant, because the normal form is itself an orbit
element. So the property to test is invariance under the 20 generating
automorphisms, and that is testable.

`nf_inv.py` tests it. At cap 15 it tests all 6864 pairs against all 20
automorphisms: 0 failures. At cap 20 it tests a random sample of 12000 of the
79680 class representatives, seed 20261104, against all 20 automorphisms: 0
failures.

`pu_nfcount.py` then computes the class counts on my own ball, one ordered
conjugation class at a time:

```
cap 15: ordered conj classes   26, PU classes   7, N(<=13)=1 N(<=14)=3 N(<=15)=7
cap 16: ordered conj classes   80, PU classes  11, N(<=13)=1 N(<=14)=3 N(<=15)=9 N(<=16)=11
cap 17: ordered conj classes 2000, PU classes 168, N(<=13)=2 N(<=14)=7 N(<=15)=37 N(<=16)=69 N(<=17)=168
```

These match `pu.md` at every value: 7, 11 and 168, and also the growth sentence
"N(<=15) is 7, 9, 37, 38, 39, 42 for caps 15 to 20", whose first three entries
my caps 15, 16 and 17 reproduce. I did not recompute the cap-18 to cap-20
entries, since those need the 51,411,456-tuple run.

So I have verified the counting method and every count up to cap 17, and I have
verified that the normal form behaves as an invariant on a fifth of the cap-20
class representatives. The figure 2,967 at cap 20 is reproducible by rerunning
their own `puclass2.py` on the shipped class file, which I did: it reports 2967
classes with the per-length breakdown 2, 5, 35, 40, 206, 246, 1209 and 1224 in
329 seconds, and its own invariance self-test reports 0 failures in that run.
What I did not do is rebuild the cap-20 box with my own enumerator. The
residual risk is a normal form that fails on a representative I did not
sample; my sampling bounds that risk at well under one percent if failures were
spread over the class set.

### 3.6 The published table

The comparison in section 6 of `pu.md` reads Panteleev and Ushakov's Table 1 as
cumulative counts of normal forms of total length at most $T$, and it labels
that reading as an interpretation. I did not obtain their table, so I can say
nothing about the reading itself. The internal consistency of the local
numbers is right, and two observations are worth recording. Their 3356 at
$T = 20$ is larger than 2967, and a class counts the same whether it is found
with a small box or a large one, so a larger search box can only add classes.
The deficit is therefore in the direction that a larger intermediate cap would
explain, which is the first of the three interpretations listed. Their 4 at
$T = 13$ against our complete count of 2 is the other observation, and the
conditional deduction in section 6 is correctly labelled conditional.

One numerical note on section 8. The growth factor from the cap-20 run to the
stopped cap-21 run is $187{,}904{,}819 / 51{,}411{,}456 = 3.655$, so the
statement "above 3.6" is right.

## 4. Target (c): `survey/quinn-tqft.md`

### 4.1 The recorded machine output

`python3 survey/quinn_check.py` reproduces `survey/quinn_check_output.txt`
byte for byte under `diff`, including the characteristic-2 Hopf algebra, the
determinant table and the survey of candidate data sets. The four lines for
$p = 5$, for example, report the odd-index set as closed with quadratic sum 0
and the full Verlinde category as failing condition (1).

### 4.2 The invariant forms, recomputed

I recomputed the matrix of $\beta(u,v) = \tau(u\,\iota(v))$ on
$k[y]/(y^s)$, with $\iota$ the algebra automorphism sending $1+y$ to
$(1+y)^{-1}$ and $\tau$ the coefficient of $y^{s-1}$, with exact integer
determinants. `quinn_forms.py` prints, for $s = 1$ to 9:

```
s=1: det(beta) 1, det(beta+beta^T) 2,   det(beta-beta^T) 0
s=2: det(beta) 1, det(beta+beta^T) 0,   det(beta-beta^T) 4
s=3: det(beta) 1, det(beta+beta^T) 8,   det(beta-beta^T) 0
s=4: det(beta) 1, det(beta+beta^T) 0,   det(beta-beta^T) 16
s=5: det(beta) 1, det(beta+beta^T) 32,  det(beta-beta^T) 0
s=6: det(beta) 1, det(beta+beta^T) 0,   det(beta-beta^T) 64
s=7: det(beta) 1, det(beta+beta^T) 128, det(beta-beta^T) 0
s=8: det(beta) 1, det(beta+beta^T) 0,   det(beta-beta^T) 256
s=9: det(beta) 1, det(beta+beta^T) 512, det(beta-beta^T) 0
```

So $\det(\beta+\beta^T) = 2^s$ for odd $s$ and $\det(\beta-\beta^T) = 2^s$ for
even $s$, exactly as the survey states, and the symmetric form used for odd $s$
is nondegenerate over every field of odd characteristic. My first attempt at
this computation disagreed with the survey, and both errors were mine: I had
used $\iota(1+y)$ where $\iota(y)$ belongs, and I had mis-signed the series for
$\iota(y)$. The survey's numbers are right.

### 4.3 Ostrik's fusion rule, recomputed

The survey's Theorem 3 needs $\bar L_r \otimes \bar L_s = \sum_{i=1}^{c}
\bar L_{|r-s|+2i-1}$ with $c = \min(r,s,p-r,p-s)$. I recomputed it from the
Jordan type over $\mathbb{F}_p$ of $\sigma - 1 = y + z + yz$ acting on
$k[y,z]/(y^r,z^s)$, discarding the negligible Jordan blocks of size $p$. At
$p = 3$, $p = 5$ and $p = 7$ the recomputation agrees with the formula for
every pair $(r,s)$ with $1 \le r,s \le p-1$. The same script checks closure of
the odd-index subset and the quadratic sum:

```
p=3: agreement True; odd-index subset closed True, sum of odd squares mod p: 1
p=5: agreement True; odd-index subset closed True, sum of odd squares mod p: 0
p=7: agreement True; odd-index subset closed True, sum of odd squares mod p: 0
```

The closure is also immediate from the formula, since $|r-s| + 2i - 1$ is odd
whenever $r$ and $s$ are odd. The vanishing sum
$\sum_{s \text{ odd}} s^2 = (p-1)(p-2)p/6$ is a polynomial identity with a
factor $p$, so it holds for every prime $p \ge 5$ and not only for the four
primes the script runs.

### 4.4 Two notes and no defect

Lemma 1 asserts that the subcategory generated by the $V_i$ inherits rigidity
from $H$-mod without saying why the duals stay in the subcategory. The missing
line is short: $V_i^*$ is a direct summand of $V_i^* \otimes V_i \otimes V_i^*$
by rigidity, and $V_i^* \otimes V_i$ is a sum of copies of the $V_j$ by
condition (2), so $V_i^*$ is a summand of a tensor product of members of the
list. The gap is one sentence of exposition and not an error, but a reader
checking the reduction will want it.

The verdict on the detection question is labelled correctly. The unitary case
is a theorem of the cited paper and the semisimple case is reported there, with
the passage from Quinn's conditions to a semisimple theory labelled as the
survey's own argument. I verified both citations live. Etingof, Nikshych and
Ostrik, *On fusion categories*, Theorem 2.3, reads in the published text "If
$k = \mathbb{C}$ then $|V|^2 > 0$ for all simple objects $V \in C$; therefore
$\dim(C) \ge 1$, and is $> 1$ for any nontrivial $C$. In particular, for any
fusion category $C$ one has $\dim(C) \ne 0$", with the inequality symbol lost in
the text extraction and correctly restored by the survey, and Remark 2.4 matches
verbatim. Khovanov, Krushkal and Nicholson, *On the universal pairing for
2-complexes*, Bulletin of the London Mathematical Society 57 (2025), 2838-2853,
DOI 10.1112/blms.70130, published online 26 June 2025, has an abstract stating
that the universal pairing does not detect the difference between simple
homotopy equivalence and 3-deformations, which is the content the survey uses.

## 5. Target (d): `directions/ms-ak-certs/`

`mscerts_replay.py` reads the 18 JSON files, rebuilds AK(n) and MS(n, w_1) from
the prose formulas (with $w_1 = y^{-1}x^{-1}yxy$ and the relator for $x = w_1$
written $x^{-1}w_1$), and applies the move list with my own word engine. All 18
certificates end exactly at the recomputed endpoint, and the move counts and
longest relators match the table in `ms-ak-certs.md`:

```
n= 2 fwd 11 moves, rev 17 moves, longest relator 17
n= 3 fwd 15 moves, rev 24 moves, longest relator 21
...
n=10 fwd 43 moves, rev 73 moves, longest relator 49
checked 18 certificates, 0 failures
```

`lean directions/ms-ak-certs/AC_certs.lean` exits 0 in about 8 seconds and
prints "does not depend on any axioms" for all eleven theorems, among them
`cert2_ok` through `cert10_ok` and `endpoints_reduced`. The file contains no
`sorry` and no `native_decide`; the single textual match for those words is a
sentence in the header comment saying that neither occurs. The statements are of
the form `run (AK n) certn = MS n`, with `AK` and `MS` defined in Lean from the
same formulas, so the Lean theorem is a faithful statement of the certificate
claim and not a restatement of a weaker one.

I checked the two obstruction claims by hand. The second relator of
$MS(n,w_k)$ has exponent sums $(-1, 2-k)$ while $D$ and $D^{-1}$ have
$(1,-1)$ and $(-1,1)$, so for $k \ne 1$ it is not a conjugate of either, which
is exactly the route obstruction claimed. The identity
$R_2(k+1) = (x^{-1}y^{-1}x)R_2(k)$ holds by cancelling $x x^{-1}$. In the
affine group with $y$ the translation by 1 and $x$ multiplication by $n/(n+1)$,
the relator $R_1$ vanishes and $x^{-1}y^{-1}x$ acts as the translation by
$-(n+1)/n$, which is not the identity. Both are correct.

## 6. What I could not verify

1. The standard-pair balls at caps 13, 14 and 15 (6,476,104 and 14,399,816 and
   58,487,624 pairs). My Python search does not hold them. The caps 11 and 12
   balls match exactly.
2. The cap-20 box itself, 51,411,456 tuples. I reproduced the move
   enumeration, the class quotient and the normal form invariance at smaller
   caps and on a sample at cap 20, replayed all 79,680 cap-20 certificates, and
   reran the target's own counting script on the shipped class file, which
   returns 2,967. I did not rebuild the box with my own enumerator.
3. Panteleev and Ushakov's Table 1 and their normal form. I did not obtain the
   paper, so their side of the comparison is unexamined here.
4. The Miller-Schupp counts 1190 and six reported by Shehper et al., and
   Carreras's 66-move and 13-move certificates. These are reported in
   `c14.md` as reported, and I did not verify them either.
5. GAP's inability to close the coset enumeration for the four
   $\mathrm{PSL}(2,7)$ presentations. I did not determine the orders of those
   four groups, and defect 1 is a statement that their order is not 120 and not
   that it is known.
6. The exhaustive count of PU-classes at caps 18, 19 and 20, for the reason in
   item 2.
7. The truncated section 4 of Quinn's paper, which the survey also records as
   unreadable in the only available version.

## 7. Exact commands

All commands are run from the repository root unless a directory is named. My
own scripts live in `.ultramath/smw2opo0o/m4/` and are run from there.

```
cd .ultramath/smw2opo0o/m4
python3 enum_mine.py 14                       # canonical lists, steps (A)-(D), L = 2..14
python3 replay_mine.py ../../../directions/c14/certs_all.txt
python3 check_classes.py                      # class file against my enumeration and certificates
python3 audit2.py                             # label/start bijection and the step-(D) audit
python3 quotient_check.py                     # the 38 nontrivial presentations, A5 and GL(3,2)
python3 ball.py ak3 17                        # also 13, 14, 15, 16
python3 ball.py std 12                        # also 10, 11
python3 batch_resisters.py resisting-exhausted-cap17 resisting-exhausted-cap18
python3 batch_resisters.py resisting-exhausted-cap19
python3 budget_check.py                       # the 22 budget resisters against a 400001 budget
python3 ms_slice2.py                          # the Miller-Schupp length-14 slice
python3 pu_counts.py                          # balls, conjugation classes, conjugator bound
python3 pu_counts2.py                         # ordered and unordered conjugation classes
python3 pu_replay.py ../../../directions/pu-enumeration/cert16all.txt \
                     ../../../directions/pu-enumeration/shortest_two.cert
python3 pu_replay.py ../../../directions/pu-enumeration/cert20k1.txt.gz
python3 pu_nfcount.py                         # PU classes at caps 12..17
python3 nf_inv.py 15                          # invariance of nf.canonical, exhaustive at cap 15
python3 nf_inv.py cls20 12000                 # invariance on 12000 cap-20 class representatives
python3 quinn_forms.py                        # the invariant forms and Ostrik's fusion rule
python3 mscerts_replay.py                     # the 18 ms-ak-certs certificates
python3 conjlength.py                         # prefix conjugations that leave the length interval

cd directions/pu-enumeration
gunzip -c cls20k1.txt.gz | python3 puclass2.py /dev/stdin    # 2967 classes, 329 s

cd directions/c14 && gap -q ... # the order computation, see nontrivial.g in my directory
cd ../../../.. && lean directions/ms-ak-certs/AC_certs.lean
python3 survey/quinn_check.py | diff - survey/quinn_check_output.txt
```

## 8. Summary

All four targets survive the audit on their computational claims. The three
defects I found are in `directions/c14/c14.md`: a false sentence about the
orders of the four $\mathrm{PSL}(2,7)$ groups, a missing qualifier on the scope
of the negative bounds, and one table cell in the total row. None of them
changes a classified presentation, a certificate or a bound. The other three
targets need no correction on the material I could check, and the gap I record
for each of them is a gap in what I could verify rather than a fault in the
artifact.
