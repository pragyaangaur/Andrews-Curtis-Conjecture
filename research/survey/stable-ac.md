# The stable Andrews-Curtis conjecture: definitions, status, and reductions

Direction D10 of swarm smw2fzjic, written by member m12. Round 1 deliverable: a map, not a result.
Nothing in this file proves or disproves the Andrews-Curtis conjecture, its stable form, or any conjecture
about 2-complexes. Where I state a theorem I say who proved it and where I read it. Where I state something
I derived myself I mark it as an argument and write the derivation out.

## 0. Labels used in this file

* `[V-source]` the statement was read in a source I cite, and the citation was checked against a live page.
* `[V-compute]` the statement was checked by a deterministic computation in `survey/stable-ac-check.py`,
  rerunnable with `python3 survey/stable-ac-check.py`.
* `[Argument]` my own deduction from labelled statements, written out in full.
* `[Open]` I know of no proof and no disproof, and I say what I searched.
* `[Unverified]` I could not check it, and it should not be relied on.

## 1. Two move sets and two conjectures

A balanced presentation of rank `n` consists of `n` generators `x_1,...,x_n` and `n` relators
`r_1,...,r_n`, which are words in the free group `F_n = F(x_1,...,x_n)`. A relator tuple is written
`r = (r_1,...,r_n)`.

**The unstable move set.** The three moves below are the ones in the problem statement, and they are the
ones used by Wright in the paper that ties them to 2-complexes `[V-source: P. Wright, Group presentations
and formal deformations, Trans. Amer. Math. Soc. 208 (1975) 161-169, DOI 10.1090/S0002-9947-1975-0380813-5]`.

* (AC1) replace `r_i` by `r_i^{-1}`;
* (AC2) replace `r_i` by `r_i r_j`, for `i` different from `j`;
* (AC3) replace `r_i` by `w r_i w^{-1}`, for any word `w` in `F_n`.

Two small variants of (AC3) appear in print and they generate the same equivalence relation. Some sources
allow only `w` a single generator or its inverse, and iterating such moves gives conjugation by an arbitrary
word. `[V-compute]` Check [6] of the script verifies the identity
`w r w^{-1} = a_1 ( ... (a_k r a_k^{-1}) ... ) a_1^{-1}` for `w = a_1...a_k` on 200 seeded random instances,
as a guard on the implementation. A larger variant question is discussed in Section 7.

**The stable move set.** The two moves below are added to (AC1)-(AC3)
`[V-source: L. Fagan, The Stable Andrews-Curtis Conjecture and Generic 2-Polyhedra, PhD thesis, UC Santa
Barbara, November 2025, Definition 3.1; the same definition appears as Definition 5 of L. Fagan, Y. Qiu and
Z. Wang, Stable Andrews-Curtis Conjecture via Fake Surfaces and Zeeman Conjecture, arXiv:2412.12293]`.

* (AC4) add a new generator `x_{n+1}` together with the new relator `r_{n+1} = x_{n+1}`;
* (AC5) the inverse of (AC4): if some relator `r_i` is a single generator `x_j`, and `x_j` does not occur
  in any other relator, delete `r_i` and delete `x_j`.

The side condition in (AC5) is part of the definition and it is not a formality. `[V-compute]` Check [3] of
the script exhibits the presentation `<x1,x2 | x1, x1 x2>`, in which the first relator is the single
generator `x1`, and shows that the implementation refuses to delete that pair while `x1` still occurs in the
second relator. Without the side condition the move would not even produce a presentation.

**The two conjectures.** The two move sets produce two conjectures, and the second is the subject of this file.

* (AC) Every balanced presentation of the trivial group is AC-equivalent, using (AC1)-(AC3), to the
  standard presentation `<x_1,...,x_n | x_1,...,x_n>` of the same rank.
* (sACC) Every balanced presentation of the trivial group is stably AC-equivalent, using (AC1)-(AC5), to the
  empty presentation `< | >` `[V-source: Fagan thesis, Conjecture 3.1; Fagan-Qiu-Wang, Conjecture in
  Section 2]`.

**Lemma 1.** Under (AC1)-(AC5) the standard rank-`n` presentation reduces to the empty presentation. So the
two ways of phrasing the stable conjecture, "reaches the standard presentation" and "reaches the empty
presentation", are the same statement. `[Argument]` plus `[V-compute]` Check [1] for `n = 3`.

*Proof.* Each relator `x_i` of the standard presentation is a single generator, and `x_i` occurs in no other
relator, so (AC5) deletes the pair `(x_i, x_i)`, and repeating this `n` times gives the empty presentation.
In the other direction (AC4) adds the pairs back one at a time. Both directions are finite sequences of
stable moves. This completes the proof.

**Corollary 2.** If the Andrews-Curtis conjecture holds then the stable conjecture holds. `[Argument]` This
is immediate from Lemma 1, because the standard presentation is stably equivalent to the empty one and the
stable move set contains the unstable move set.

## 2. What the moves preserve, and why that is a problem

Every one of (AC1), (AC2), (AC3) replaces the relator tuple of a presentation by another relator tuple of the
same group, and (AC4) and (AC5) are the two halves of a Tietze transformation. So all five moves preserve
the isomorphism class of the presented group `[V-source: this is the standard fact about Tietze
transformations, stated for these moves in Fagan thesis, Section 3.1]`.

Two consequences fix the shape of the problem. First, no invariant that is computed from the presented group,
or from the presented group's quotients, can ever obstruct stable AC-triviality for a presentation of the
trivial group, because every such invariant takes its trivial value there. Second, the deficiency `n - m`
with `n` generators and `m` relators is preserved by both (AC4) and (AC5), so a balanced presentation stays
balanced and the question never becomes easier by dropping relators.

The abelianisation is a computable shadow of the moves and it is worth recording exactly what it does.
Writing `M(r)` for the `n` by `n` matrix whose `i`-th row is the vector of exponent sums of `r_i`,
(AC1) negates a row, (AC2) adds one row to another, (AC3) leaves `M(r)` unchanged, (AC4) passes from `M` to
the block matrix with `M` in the top left corner, a zero column on the right and a `1` in the bottom right,
and (AC5) is the inverse of that passage `[Argument]`. Hence the abelianisation, which is the cokernel of
`M(r)`, is exactly preserved, and its Smith normal form is a legitimate invariant to check implementations
against. `[V-compute]` Check [5] of the script draws 1515 random legal move sequences and confirms that the
Smith normal form of the exponent-sum matrix is unchanged at every step.

For the trivial group the abelianisation is trivial and carries no information. This is the same statement as
the previous paragraph seen from the other side, and it is the reason the remaining sections are about
presentations and 2-complexes rather than about group invariants.

## 3. The topological reformulation

Attach to a presentation `P` the 2-complex `K(P)` with one vertex, one 1-cell for each generator and one
2-cell for each relator, glued by the relator word `[V-source: Fagan thesis, Section 3.2.2]`. For a
balanced presentation this complex has Euler characteristic `1`, since `1 - n + n = 1` `[Argument]`.

**Wright's correspondence.** The stable AC moves on presentations correspond exactly to 3-deformations of
2-polyhedra, so stable AC-equivalence classes of presentations are the same thing as 3-deformation classes of
the associated 2-complexes `[V-source: Fagan thesis, Section 3.2.2, attributes the equivalence to Wright 1975
and to Hog-Angeloni, Metzler and Sieradski, Two-Dimensional Homotopy and Combinatorial Group Theory, LMS
Lecture Note Series 197, Cambridge University Press, 1993; Fagan-Qiu-Wang, Section 1, cites Wright 1975 for
the same point]`. The earlier paper of Wright on formal 3-deformations of 2-polyhedra is
`[V-source: P. Wright, Formal 3-deformations of 2-polyhedra, Proc. Amer. Math. Soc. 37 (1973) 305-308]`.
I did not read the proof in Wright's 1975 paper, so the correspondence itself is a literature claim in this
file rather than something I verified line by line.

**The topological form of the conjecture.** The stable conjecture says that every finite contractible
2-polyhedron can be 3-deformed to a point `[V-source: Fagan thesis, Conjecture 3.4; Fagan-Qiu-Wang,
Conjecture in Section 2, both citing Wright 1975]`. The correspondence above makes the reformulation exact,
so the topological statement and the group-theoretic one are equivalent.

**The dimension gap.** Wall's theorem says that if `m > 2` and two polyhedra of dimension at most `m` are
simple homotopy equivalent, then a sequence of elementary expansions and collapses using cells of dimension
at most `m + 1` takes one to the other `[V-source: Fagan thesis, Theorem 3.3, citing C. T. C. Wall, Formal
deformations, Proc. London Math. Soc. s3-16 (1966) 342-352, DOI 10.1112/plms/s3-16.1.342]`. In particular,
simple homotopy equivalent 2-polyhedra are 4-deformation equivalent. Now let `K` be a contractible
2-polyhedron. Then `K` is homotopy equivalent to a point, and the Whitehead torsion of that homotopy
equivalence lies in `Wh(1)`, which is trivial, so the equivalence is simple
`[V-source: J. H. C. Whitehead, Simple homotopy types, Amer. J. Math. 72 (1950) 1-57; that `Wh(1)` is
trivial is the standard computation of `K_1(Z)`]`. Combining the two statements, `[Argument]` every
contractible 2-polyhedron is 4-deformation equivalent to a point.

So the stable conjecture is exactly the question whether one dimension can be saved in Wall's theorem when
the target is a point and the source is a contractible 2-polyhedron `[Argument]`. This is, in my reading, the
cleanest available statement of what the stable version adds, and it explains why the stable version is the
one that appears in the topology literature.

## 4. Zeeman's conjecture and the spine dichotomy

Zeeman's conjecture says that for every contractible 2-polyhedron `K` the product `K x I` is collapsible
`[V-source: Fagan thesis, Conjecture 3.5; E. C. Zeeman, On the dunce hat, Topology 2 (1963) 341-358,
DOI 10.1016/0040-9383(63)90014-4]`. Zeeman proved that his conjecture implies the Poincare conjecture
`[V-source: Fagan thesis, Proposition 3.10, attributed to Zeeman 1963]`.

Zeeman's conjecture implies the stable Andrews-Curtis conjecture. The reason is short: `K` expands to
`K x I`, and then `K x I` collapses to a point `[V-source: Fagan thesis, Proposition 3.8, where the
implication is proved in one line]`. The reverse implication is not claimed anywhere I read.

Two results of M. M. Cohen bound how much the product trick can buy. For a contractible 2-polyhedron `K` the
sixfold product `K x I^6` is collapsible, and for every `n` at least 3 there is a contractible `n`-polyhedron
`K` for which `K x I` is not collapsible `[V-source: Fagan thesis, Theorems 3.6 and 3.7, citing M. M. Cohen,
Dimension estimates in collapsing X x I^q, Topology 14 (1975) 253-256, and M. M. Cohen, Whitehead torsion,
group extensions, and Zeeman's conjecture in high dimensions, Topology 16 (1977) 79-88]`. The second result is a warning. It shows that the product trick is a dimension-dependent accident in
dimension 2, and it says that the corresponding statement fails in higher dimensions.

Restricting to fake surfaces, that is to generic 2-polyhedra, loses nothing for the stable conjecture,
because every 2-complex can be 3-deformed into a fake surface
`[V-source: Fagan thesis, Section 4.4; Fagan-Qiu-Wang, Section 1]`. The Zeeman conjecture is likewise
studied through its fake-surface case `[V-source: Fagan thesis, Section 4.4]`. Within fake surfaces there is
a dichotomy. For fake surfaces that are spines of 3-manifolds, Zeeman's conjecture is
equivalent to the Poincare conjecture `[V-source: D. Gillman and D. Rolfsen, The Zeeman conjecture for
standard spines is equivalent to the Poincare conjecture, Topology 22 (1983) 315-323; stated as Theorem 3 of
that paper and quoted as Proposition 4.5 in Fagan thesis]`. For fake surfaces that are not spines, Zeeman's
conjecture is equivalent to the stable conjecture `[V-source: Fagan thesis, Section 4.4]`.

Since the Poincare conjecture is a theorem, Zeeman's conjecture holds for fake-surface spines `[Argument]`,
by combining the Gillman-Rolfsen equivalence with the Poincare theorem as stated in
`[V-source: Fagan thesis, Theorem 3.9, where the Poincare conjecture is listed as a theorem]`. So the whole
content of Zeeman's conjecture, and hence the interesting part of the stable conjecture, sits in the
non-spine case.

There is a discrepancy in the literature here that I could not resolve. The title of Matveev's 1987 paper
says Zeeman's conjecture for non-thickenable special polyhedra is equivalent to the *Andrews-Curtis*
conjecture `[V-source: S. V. Matveev, The Zeeman conjecture for nonthickenable special polyhedra is
equivalent to the Andrews-Curtis conjecture, Sibirsk. Mat. Zh. 28 (1987) no. 6, 66-80, 218, MR 928341]`,
whereas the 2025 thesis places the non-spine fake-surface case opposite the *stable* conjecture. If both
statements are meant literally then the two conjectures agree on that class, which is not stated in either
source. I record the discrepancy rather than pick a side `[Unverified]`.

## 5. What is actually proved about the stable conjecture

The proved statements are all low-complexity statements about fake surfaces. In each case the complexity in
question counts vertices of the fake surface rather than letters of a relator.

* Contractible fake surfaces of complexity less than 6 with connected 1-skeleton are 3-deformable to a
  point. Consequences stated in the same paper are that the stable conjecture holds for the presentations
  arising from them, that their regular neighbourhoods in 5-space are standard 5-balls, and that Zeeman's
  conjecture holds for them `[V-source: Fagan-Qiu-Wang, Theorem 1 and Corollaries 2, 3, 4; arXiv:2412.12293
  version 2 of 8 January 2026, a preprint]`.
* The inductive scheme behind that theorem is verified up to complexity 5, and acyclic cellular fake surfaces
  are classified up to complexity 4, giving 2, 17, 238 and 4618 surfaces of complexities 1 to 4
  `[V-source: Fagan thesis, abstract and Chapter 5]`.
* Ikeda's 1971 paper on acyclic fake surfaces contains the earlier case that Fagan-Qiu-Wang extend. The
  exact complexity covered by Ikeda was lost in the copy of the paper I read, so I do not state it
  `[V-source: H. Ikeda, Acyclic fake surfaces, Topology 10 (1971) 9-36, cited for this in Fagan-Qiu-Wang,
  Section 1]`.

None of these statements is a statement about relator length, so none of them can be quoted directly as
"all balanced presentations below some length are stably trivial". There is however a route from length to
complexity. The thesis gives the complexity of the fake surface produced from the standard 2-complex of a
rank-`k` presentation by the banana-pineapple construction as `2L - 4k - n + 2`, where `L` is the total
number of letter occurrences in the relators and `n` is the largest number of occurrences of a single
generator `[V-source: Fagan thesis, Proposition 4.4]`. Bounded relator length therefore gives bounded
complexity, and one expects the Fagan-Qiu-Wang theorem to yield stable AC-triviality for all balanced
presentations of the trivial group of very small total relator length. I have not checked the connected
1-skeleton hypothesis for the resulting surfaces, so I record this as an expectation and not as a theorem
`[Argument, incomplete]`.

For presentations of groups that are not trivial the stable move set certainly fails to be all-powerful,
and the obstruction is the presented group itself by Section 2. That is not a defect of the move set. It is
the reason the conjecture is stated only for the trivial group, and it is why every plausible counterexample
must be a balanced presentation of the trivial group.

## 6. The one serious attempt to separate the stable from the unstable version

A presentation is stably AC-trivial and not obviously AC-trivial in the following construction. Take a
diagram of the unknot with `n` crossings, write down its Wirtinger presentation with `n` generators and `n`
relators, note that one relator is a product of the others and may be dropped, and add instead a word `w`
of exponent sum plus or minus one. Such presentations are stably AC-trivial
`[V-source: Fagan thesis, Proposition 3.11, attributed to A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain,
On the Andrews-Curtis equivalence, Contemp. Math. 296 (2002) 183-198, DOI 10.1090/conm/296/05074]`. The
reason is that Reidemeister moves on the diagram lift to stable AC moves on the presentation, and a diagram
of the unknot reduces to the trivial diagram.

The interest of this family was that it might separate the two conjectures, by giving a stably trivial
presentation that is not AC-trivial `[V-source: Fagan thesis, Section 3.3, describes exactly this hope]`.
That hope fails. Every presentation of the family above is in fact AC-trivial, and presentations obtained
from it by further substitution moves are AC-trivial as well
`[V-source: Fagan thesis, Theorem 3.13 and the discussion after it]`.

Two caveats attach to that last statement. It is a theorem in a doctoral thesis, and I found no evidence
that the thesis passed journal refereeing, so it is weaker evidence than a journal article `[Unverified]`.
The theorem also rules out one family of candidates only, and it says nothing about a separation in general
`[Argument]`.

## 7. Where the literature's move sets differ

Statements of the form "the Andrews-Curtis conjecture is equivalent to a topological statement about
2-complexes" refer to the *stable* move set. This is a common source of confusion, because many papers call
the stable move set "the Andrews-Curtis moves".

The Encyclopedia of Mathematics entry on low-dimensional topology lists four moves, the fourth being "add a
generator `x_{n+1}` and a relation `w x_{n+1}`, with `w` any word in `x_1,...,x_n`", and then identifies the
resulting conjecture with the statement that any contractible finite 2-complex 3-deforms to a point
`[V-source: Encyclopedia of Mathematics, entry "Low-dimensional topology, problems in", section on the
Andrews-Curtis conjecture, read online]`. Wright's Corollary 3.1, as it appeared in the excerpt I read,
says that formal 3-deformations of 2-polyhedra correspond to transformations of induced presentations by
"operations (1)-(5)" `[V-source, partial: abstract and Corollary 3.1 read in a search excerpt of the AMS
page; I did not obtain the full text, so I do not know Wright's exact list of five operations]`.

A related point is the "replacement" move, which changes the generating set by a Nielsen transformation
applied to all generators and all relators. It is part of the extended move set studied by Bagherifard, who
observes that the extended equivalence class and the stable equivalence class coincide for presentations
whose 2-complex is simply connected `[V-source: N. Bagherifard, Three-manifolds with boundary and the
Andrews-Curtis transformations, arXiv:2109.13844, 2021, Section 2]`. For the trivial group this means that
allowing generator replacement costs nothing.

## 8. Status, stated exactly

* The stable Andrews-Curtis conjecture is open `[Open]`. I found no proof and no counterexample in the
  sources I read, and both current sources I read describe it as open
  `[V-source: Fagan-Qiu-Wang, Section 1; Fagan thesis, Chapter 3]`.
* It is implied by the unstable conjecture, by Corollary 2 above.
* Whether it is strictly weaker than the unstable conjecture is not known. The sentence I rely on is
  "It is unknown whether this variant is weaker than the standard Andrews-Curtis conjecture"
  `[V-source: Fagan thesis, Chapter 1]`.
* The prevailing opinion is that it is false, in the same sense in which that opinion is held about the
  unstable conjecture `[V-source: Fagan-Qiu-Wang, Section 1, "While sACC is widely believed to be false, no
  strong evidence has emerged"]`.
* I found no source that derives the unstable conjecture from the stable one. `[Open]` This is the precise
  gap that the "stable" direction leaves open, and it is narrower than the full conjecture.

## 9. What a counterexample would and would not deliver in dimension 4

The chain from the conjecture to 4-manifolds has three links, and each link is a separate theorem rather
than a formal consequence of the previous one. I state each link with the source in which I read it.

* If the Andrews-Curtis conjecture is true, then any regular neighbourhood of a finite contractible
  2-dimensional subcomplex of a combinatorial 5-manifold is a 5-cell. This is Theorem 2 of the original
  paper, and it is stated there as a consequence of the conjecture
  `[V-source: J. J. Andrews and M. L. Curtis, Free groups and handlebodies, Proc. Amer. Math. Soc. 16 (1965)
  192-195, DOI 10.1090/S0002-9939-1965-0173241-8; Theorem 2 read in the paper's text]`.
* Akbulut and Kirby construct a homotopy 4-sphere with two 1-handles and two 2-handles and no 3-handles,
  whose associated balanced presentation of the trivial group they do not know how to trivialise by
  Andrews-Curtis moves, and they say so explicitly `[V-source: S. Akbulut and R. Kirby, A potential smooth
  counterexample in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the
  Andrews-Curtis conjecture, Topology 24 (1985) 375-390, DOI 10.1016/0040-9383(85)90010-2; the relevant
  sentences are in the paper's opening list of properties (A) to (E)]`. The exact form of that presentation
  is treated in `survey/ak-status.md` and I do not restate it here.
* For the stable version the link to 4-manifolds is stated in the recent literature as follows. If `P` is
  stably AC-trivial then the boundary of a closed tubular neighbourhood of `K(P)` in 5-space is the standard
  smooth 4-sphere, so counterexamples to the smooth 4-dimensional Poincare conjecture cannot be produced
  from that construction `[V-source: Fagan-Qiu-Wang, Section 1]`.

The direction of that last implication matters, and it is easy to get backwards. A counterexample to the
stable conjecture would give a contractible 2-polyhedron that cannot be 3-deformed to a point. It would not
by itself give a smooth homotopy 4-sphere that is not standard, because what the literature supplies is the
implication from stable triviality to standardness of the boundary `[Argument]`. The honest statement is that
a failure of the stable conjecture would destroy this particular route to standardness and leave the
4-dimensional question open for those examples.

## 10. What the accompanying script checks, and what it does not

The script `survey/stable-ac-check.py` is a self-contained Python 3 program using only the standard library.
It runs in well under a second and prints one PASS line per check. Run it with

```
python3 survey/stable-ac-check.py
```

and the last line is `all checks passed`. The checks are the following.

* [1] The standard rank-3 presentation reduces to the empty presentation by three applications of (AC5).
  This is the computational half of Lemma 1.
* [2] and [4] Two non-standard balanced presentations of the trivial group, namely `<x1,x2 | x1, x1x2>` and
  `<x1,x2 | x1, x1^-1 x2>`, reduce to the empty presentation by explicit move sequences that use (AC1),
  (AC2), (AC3) and (AC5). Because AC moves are Tietze transformations, each sequence is itself a
  certificate that the starting presentation presents the trivial group, and no separate triviality test is
  needed.
* [3] The deletion move is refused for `<x1,x2 | x1, x1 x2>` at the relator `x1`, which is the side
  condition of (AC5) being enforced rather than assumed.
* [5] Over 1515 random legal moves the Smith normal form of the exponent-sum matrix is unchanged, which is
  the abelianisation invariance of Section 2 and a guard against implementation errors in the moves.
* [6] Conjugation by a word agrees with iterated conjugation by its letters.
* [7] Stabilising and then destabilising returns the original presentation exactly.
* [8] For `AK(3) = <x,y | xyx = yxy, x^3 = y^4>` the exponent-sum matrix is `[[1,-1],[3,-4]]`, its
  determinant is `-1`, and the abelianisation is trivial.

The script does not decide triviality of a presented group in general, and it does not search for moves. In
particular check [8] records two necessary conditions on `AK(3)` and says nothing about whether that group is
trivial or whether the presentation is stably trivial. Those questions belong to other directions of the
swarm.

## 11. Sources, with the detail I checked

1. J. J. Andrews and M. L. Curtis, Free groups and handlebodies, Proc. Amer. Math. Soc. 16 (1965) 192-195,
   DOI 10.1090/S0002-9939-1965-0173241-8. Origin of the conjecture; Theorem 2 is the regular-neighbourhood
   statement.
2. P. Wright, Formal 3-deformations of 2-polyhedra, Proc. Amer. Math. Soc. 37 (1973) 305-308. Precursor of
   the presentation to 3-deformation correspondence.
3. P. Wright, Group presentations and formal deformations, Trans. Amer. Math. Soc. 208 (1975) 161-169,
   DOI 10.1090/S0002-9947-1975-0380813-5. The correspondence between presentation moves and 3-deformations.
4. C. T. C. Wall, Formal deformations, Proc. London Math. Soc. s3-16 (1966) 342-352,
   DOI 10.1112/plms/s3-16.1.342. The dimension bookkeeping that produces the gap between 3- and
   4-deformations.
5. J. H. C. Whitehead, Simple homotopy types, Amer. J. Math. 72 (1950) 1-57. Simple homotopy equivalence and
   Whitehead torsion.
6. E. C. Zeeman, On the dunce hat, Topology 2 (1963) 341-358, DOI 10.1016/0040-9383(63)90014-4. Source of
   the collapsing conjecture.
7. M. M. Cohen, Dimension estimates in collapsing X x I^q, Topology 14 (1975) 253-256, and Whitehead torsion,
   group extensions, and Zeeman's conjecture in high dimensions, Topology 16 (1977) 79-88. The sixfold
   product result and the high-dimensional failure.
8. D. Gillman and D. Rolfsen, The Zeeman conjecture for standard spines is equivalent to the Poincare
   conjecture, Topology 22 (1983) 315-323. The spine case.
9. S. V. Matveev, The Zeeman conjecture for nonthickenable special polyhedra is equivalent to the
   Andrews-Curtis conjecture, Sibirsk. Mat. Zh. 28 (1987) no. 6, 66-80, 218, MR 928341. The non-spine case,
   with the discrepancy noted in Section 4.
10. H. Ikeda, Acyclic fake surfaces, Topology 10 (1971) 9-36. Early low-complexity case.
11. C. Hog-Angeloni, W. Metzler and A. J. Sieradski (eds.), Two-Dimensional Homotopy and Combinatorial Group
    Theory, LMS Lecture Note Series 197, Cambridge University Press, 1993, DOI 10.1017/CBO9780511629358.
    Chapter XII, by C. Hog-Angeloni and W. Metzler, The Andrews-Curtis Conjecture and its Generalizations,
    pages 365-380, DOI 10.1017/CBO9780511629358.014, is the standard survey.
12. S. Akbulut and R. Kirby, A potential smooth counterexample in dimension 4 to the Poincare conjecture, the
    Schoenflies conjecture, and the Andrews-Curtis conjecture, Topology 24 (1985) 375-390,
    DOI 10.1016/0040-9383(85)90010-2.
13. A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, On the Andrews-Curtis equivalence, Contemp. Math. 296
    (2002) 183-198, DOI 10.1090/conm/296/05074. Unknot diagrams and stable triviality.
14. N. Bagherifard, Three-manifolds with boundary and the Andrews-Curtis transformations, arXiv:2109.13844
    (2021). Extended move set, and the remark that extended and stable equivalence agree when the 2-complex
    is simply connected.
15. L. Fagan, Y. Qiu and Z. Wang, Stable Andrews-Curtis Conjecture via Fake Surfaces and Zeeman Conjecture,
    arXiv:2412.12293, version 2 of 8 January 2026. Preprint. Complexity below 6.
16. L. Fagan, The Stable Andrews-Curtis Conjecture and Generic 2-Polyhedra, PhD thesis, UC Santa Barbara,
    November 2025, eScholarship item 6fm617h4. Definitions, the topological formulation, the complexity
    statement, and Theorem 3.13 on unknot diagrams.
17. Encyclopedia of Mathematics, entry "Low-dimensional topology, problems in", section on the
    Andrews-Curtis conjecture. Read online; used only for the four-move formulation of Section 7.

## 12. What I could not verify

* Wright's exact list of five operations in the 1975 paper. I read the abstract and Corollary 3.1 in an
  excerpt and did not obtain the full text `[Unverified]`.
* Whether the Matveev 1987 statement is about the stable or the unstable conjecture. The title and the 2025
  thesis disagree on this point `[Unverified]`.
* Whether Fagan's Theorem 3.13 has appeared in a refereed journal. I found only the thesis `[Unverified]`.
* Whether the two recent sources, arXiv:2412.12293 and the thesis, have been checked by anyone other than
  their authors. Both are recent and I treat their results as reported rather than established
  `[Unverified]`.
* I did not look for a primary source due to Quinn on the stable version, although the direction brief
  mentions Quinn for the topology chain. Nothing in this file rests on such a source `[Unverified]`.

## 13. Questions about the stable version that a short run could attack

1. Can a machine search find a balanced presentation of the trivial group that is stably AC-trivial by a
   short explicit sequence and resists every AC search of comparable length? A positive answer would not
   prove a separation, and the failure record would still be informative.
2. Is the connected 1-skeleton hypothesis in the Fagan-Qiu-Wang theorem automatic for fake surfaces obtained
   from presentations by the banana-pineapple construction of their Proposition 4.4?
3. What is the smallest total relator length of a balanced presentation of the trivial group that is not
   known to be stably AC-trivial? Answering this is a literature question with a computable component.
4. Does the substitution and removal move of Fagan's Lemma 3.2 admit a bound on the number of stable moves
   needed to realise it, in terms of the relator lengths involved?
5. Can the Wall dimension gap of Section 3 be turned into an explicit invariant that is preserved by
   3-deformations but not by 4-deformations on contractible 2-polyhedra? An invariant that separates some
   contractible 2-polyhedron from a point would settle the stable conjecture, so the realistic version of
   this question is to find one defined on a restricted class.
