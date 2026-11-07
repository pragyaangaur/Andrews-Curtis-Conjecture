# Quinn's triangular Hopf algebra question: answer in characteristic 0, in characteristic 2, and in characteristic p at least 5

Round 2 direction E8. Author: member m6. Date: 4 November 2026.

This file answers the representation-theoretic question that Frank Quinn poses in
arXiv:hep-th/9202044, and it separates two things that the question paper joins: the
existence of the algebraic data, and the existence of a counterexample detector built
from that data.

Labels follow the run's rule that only a Lean 4 proof or a rerunnable exact computation
counts as a check. **MACHINE-CHECKED** means that the command in section 13 reproduces
the claim. **ARGUMENT FROM CITATION** means a complete derivation from theorems that are
identified in the cited papers and quoted here, so the claim is an argument in the run's
sense and not a machine-checked proof.

Quotations keep the wording of the source. Mathematical symbols inside quotations are
rendered in ASCII, for example `sum` for a running total and `ot` for the tensor product
of representations, because the PDF extraction does not preserve them.

## 0. Verdicts

| Claim | Status |
|---|---|
| Q9 over any field of characteristic 0: no such data exist | **ARGUMENT FROM CITATION**, resting on Etingof-Nikshych-Ostrik, *On fusion categories*, Theorem 2.3 (quoted in section 4) |
| Q9 over `F_2`: the data exist | **MACHINE-CHECKED**: an explicit 2-dimensional Hopf algebra, verified by `survey/quinn_check.py` |
| Q9 over `F_p` with p at least 5, at the level of the fusion category | **ARGUMENT FROM CITATION** for the fusion rules (Ostrik 2020) with the invariant form **MACHINE-CHECKED** for p at most 13; the form's determinant `2^s` is computed exactly |
| Q9 over `F_3` | **OPEN**. The two natural candidates fail, and no non-degenerate symmetric fusion category can work (argument in section 7) |
| Q9 over `Z` | **ARGUMENT**: impossible, since every rank is a unit and the only units of `Z` are `+1` and `-1` |
| Q9 over a general ring of characteristic 0 | **OPEN**. The arithmetic obstruction disappears over `Z[i]`, where `1^2 + i^2 = 0` |
| Quinn's programme detects a counterexample to the Andrews-Curtis conjecture | **REFUTED for the semisimple theories that his conditions produce**: Khovanov-Krushkal-Nicholson 2025 prove the unitary case and report the semisimple case of the statement that such TQFTs cannot distinguish stably equivalent 2-complexes, and a contractible 2-complex is stably equivalent to a point. The only escape, a non-semisimple theory, is excluded by Quinn's conditions (1) to (3) |

The short reading: Quinn's identity `sum (rank V_i)^2 = 0` is a statement that the
global dimension of a symmetric fusion category vanishes. Such a category cannot
exist over any field of characteristic 0, and it can exist in characteristic 2 with a
two-dimensional Hopf algebra. Two consequences matter for the campaign. The complex
numbers, which Quinn guessed would be a good ground field, is impossible, so the
programme can only run in positive characteristic. And the conditions (1) to (4) on
their own are satisfied by a trivial two-dimensional example, so those conditions
carry no information about the Andrews-Curtis conjecture. Whatever force the programme
has must come from the TQFT construction that Quinn sketches in his section 4, and that
construction is not complete in the source I could read. Section 10 adds a published
obstruction: the theories that his conditions produce are semisimple, and semisimple
TQFTs cannot distinguish a contractible 2-complex from a point.

## 1. The source

Quinn, *Representation theory, topological field theory, and the Andrews-Curtis
conjecture*, arXiv:hep-th/9202044, submitted 13 February 1992, version 2 dated
14 February 1992, six pages. Identifiers checked against the arXiv API on
4 November 2026: title, author Frank Quinn, published 1992-02-13, updated 1992-02-14.
The PDF is at `https://arxiv.org/pdf/hep-th/9202044`; I downloaded it and extracted
the text with `pdftotext -layout`.

The paper as distributed is **truncated**. Section 4 ends in the middle of a sentence,
and the bibliography has three entries. The PDF carries this note, which I quote
verbatim:

> Note added by Greg Kuperberg on 2/18/01: Garbled material mate-
> rial has been removed from the TeX submission here. A discontinuity
> in the narrative remains.

The last complete sentence of section 4 is followed by the fragment "Now define Z(G, P)
for a general finite graph. Cut the graph at points Q to make all components contra".
No value of the proposed invariant is computed anywhere in the available text. This
matters for the referee's verdict: the existence question can be settled, the detection
question cannot be settled from this source, and the paper does not even state a
conjecture that the invariant separates anything.

## 2. The question, quoted

Abstract, verbatim apart from the running-total symbol, which I write as `sum`:

> We pose a representation-theoretic question motivated by an attempt to
> resolve the Andrews-Curtis conjecture. Roughly, is there a triangular Hopf algebra
> with a collection of self-dual irreducible representations V_i so that the product of any
> two decomposes as a sum of copies of the V_i, and sum (rank V_i)^2 = 0? This data can
> be used to construct a "topological quantum field theory" on 2- complexes which
> stands a good chance of detecting counterexamples to the conjecture.

Section 2 explains why the vanishing is wanted, verbatim:

> If Z_{S^2} is a unit in R then we can recover Z_X from Z_{X vee S^2}, and Z cannot detect
> counterexamples to the conjecture. At the other extreme if Z_{X vee S^2} = 0 then Z has
> the same sort of "sudden death" instability that the Donaldson invariants do with
> respect to connected sum with S^2 x S^2.
>
> Therefore we seek TQFT on 2-complexes for which Z_{S^2} = 0. In the ones con-
> structed from representations Z_{S^2} = sum (rank V_i)^2, which is why we want this iden-
> tity. It is hard to imagine how such a TQFT could be nontrivial without detecting
> something new, but at present there is no general proof of this. It would have to
> be verified by calculations of examples.

Section 3 fixes the ground ring and the algebra, verbatim:

> Fix a commutative ring R. The complex numbers is probably a good choice: we
> will end up with units rank V_i and will want the sum of their squares to vanish. Let
> H be a Hopf algebra over R which is triangular in the sense of Drinfel'd [Dr1]. We
> really do mean triangular, and not quasitriangular.

The four conditions, verbatim, with Quinn's symbol for the tensor product written
as the circled times:

> (1) there are H-morphisms lambda_i : V_i ot V_i -> R which are symmetric in the sense
>     lambda_i = lambda_i Psi, and nondegenerate as bilinear forms;
> (2) each V_i ot V_j is isomorphic to a sum of copies of the V_*;
> (3) the V_i are irreducible and distinct; and
> (4) sum (rank V_i)^2 = 0.

Remark (ii) defines the rank, and it is exactly the categorical dimension for the
canonical spherical structure of a symmetric category. Verbatim in part:

> The rank used in (4) is the categorical one: the trace of the identity homomorphism.
> ... Form the composition
> R -> V^* ot V^{**} -> V^* ot V -> V ot V^* -> R
> then this is multiplication by some element of R. That element is defined to be the
> rank of V. It follows from (1) and (3) that rank V_i is a unit.

Remark (iv) says how to read condition (3) over a field, verbatim:

> Irreducibility. The condition in (3) is correct if R is an algebraically closed field
> (eg. C). The general conditions are E(V_i ot V_i) = R as an algebra, and
> E(V_i ot V_j) = 0 for i != j.

Remark (vi) proposes the construction strategy, verbatim in part:

> Perhaps one could begin with a Hopf algebra and representations V_i satisfying the
> first three conditions. Then adjust the R-matrix in H, from which Psi is defined, to
> make (4) true.

That strategy is exactly what Theorem 1 below rules out in characteristic 0: once
(1) to (3) hold, the left side of (4) is the global dimension of a fusion category, and
over a field of characteristic 0 that number is at least 1 for every choice of R-matrix.

## 3. Reduction to a fusion-category problem

**Lemma 1 (Argument).** Let k be a field, H a triangular Hopf algebra over k, and
V_0, ..., V_n finitely many H-modules satisfying Quinn's conditions (1) to (3), with
the V_i nonzero. Then the V_i are the simple objects of a symmetric fusion category
C over k, and `sum_i (rank V_i)^2 = dim C`.

*Proof.* By (3) and Remark (iv), each V_i has endomorphism ring k and the V_i are
distinct, so each is a simple H-module. By (2), every tensor product V_i ot V_j is a
direct sum of copies of the V_k, so the full subcategory of H-mod whose objects are
direct sums of copies of the V_i is closed under tensor product and under direct
summands. It inherits rigidity from H-mod, it has the zero object, and End(1) = k, so
it is a fusion category. It inherits the symmetry Psi from the triangular structure of
H. Condition (1) gives a nondegenerate morphism V_i ot V_i -> k, which is nonzero, so
the unit object 1 is a direct summand of V_i ot V_i, and by (2) the unit object is one
of the V_j. Therefore the simple objects of C are exactly the V_i. Quinn's rank is the
categorical dimension for the canonical spherical structure of a symmetric category,
which is the same composite that he writes in Remark (ii), and the global dimension of
a fusion category is the sum of the squares of the dimensions of its simple objects. QED

Three remarks place Lemma 1 in the literature. Ostrik gives Quinn's composite as the
canonical spherical structure of a symmetric category (Ostrik 2020, section 2.4, the
displayed formula). Etingof, Nikshych and Ostrik define the global dimension as the sum
of the squares of the dimensions of the simple objects (arXiv:math/0203060,
Definition 2.2). And for a triangular Hopf algebra the symmetry is the one from the
R-matrix, so the category is symmetric and not merely braided.

## 4. Theorem 1: no data over any field of characteristic 0

**Theorem 1 (ARGUMENT FROM CITATION).** Let k be a field of characteristic 0. There is no triangular
Hopf algebra H over k and no finite nonempty list of H-modules satisfying Quinn's
conditions (1) to (4), with condition (3) read as in Quinn's Remark (iv).

*Proof.* By Lemma 1 the data give a fusion category C over k whose simple objects are
the V_i and whose global dimension is `sum_i (rank V_i)^2`, which condition (4) sets
equal to 0. Etingof, Nikshych and Ostrik prove that this cannot happen. Verbatim from
their arXiv:math/0203060, Theorem 2.3:

> Theorem 2.3. If k = C then |V|^2 > 0 for all simple objects V in C; therefore
> dim(C) >= 1, and is > 1 for any nontrivial C. In particular, for any fusion category
> C one has dim(C) != 0.

Their Remark 2.4 supplies the passage from C to an arbitrary field of characteristic 0,
verbatim:

> Note that the second statement immediately follows from the first
> one, since C is always defined over a finitely generated subfield k' of k, which can
> be embedded into C.

Since |V_i|^2 = (rank V_i)^2 for a self-dual simple object with the canonical spherical
structure, Theorem 2.3 gives `sum_i (rank V_i)^2` at least 1, which is not 0 in k. QED

The same conclusion follows from the classification of triangular semisimple Hopf
algebras when H happens to be semisimple. Etingof and Gelaki proved in 1998 that over a
characteristic 0 field every triangular semisimple Hopf algebra is a twist of a group
algebra by a 2-cocycle. Their 2000 classification covers any characteristic for dimension prime to the
characteristic, and its abstract draws the consequence, verbatim: "This classification
implies, in particular, that any triangular semisimple and cosemisimple Hopf algebra
over k can be obtained from a group algebra by a twist." The same conclusion is
Corollary 6.2 of arXiv:math/9905168. A twist does not change the
algebra structure, so every simple module of such an H is one-dimensional, every rank
equals 1, and `sum (rank V_i)^2` equals the number of the V_i, which is at least 1.
Theorem 1 does not need the semisimplicity of H, and the Etingof-Gelaki route is an
independent check of the semisimple case.

Neither proof uses condition (1) beyond the existence of a nonzero map V_i ot V_i -> k,
which is what forces the unit object into the list.

## 5. Theorem 2: the data exist in characteristic 2

**Theorem 2 (MACHINE-CHECKED, with a hand proof).** Let k be a field of characteristic 2 and let
H be the coordinate Hopf algebra O(Z/2), which is k x k as an algebra, with the two
indicator functions of the points of Z/2 as a basis of orthogonal idempotents. Then H is a
two-dimensional semisimple cocommutative Hopf algebra, so it is triangular with
R = 1 ot 1, and its two simple modules V_0 and V_1 satisfy Quinn's conditions (1) to
(4).

*Proof.* The algebra is k x k, the comultiplication is determined by the group
structure of Z/2, and the antipode is the identity map, so H is a commutative and
cocommutative Hopf algebra, and R = 1 ot 1 is a triangular structure. The two simple
modules are one-dimensional, with the two idempotents acting by 1 and 0. They are
distinct. The product form on each is symmetric and nondegenerate in every
characteristic. Tensor products are given by adding the labels in Z/2, so the
collection is closed, and the ranks are 1 and 1. The sum of squares is 1 + 1, which is
0 in characteristic 2. QED

The point of the example is its size: a two-dimensional Hopf algebra already satisfies
conditions (1) to (4). Over a field of characteristic different from 2 the same
computation gives 1 + 1 = 2, so the example fails there, exactly as Theorem 1
requires.

Machine check. `survey/quinn_check.py`, part A, verifies all Hopf algebra axioms of
O(Z/2) by exhaustive computation over the basis, verifies that the two modules are
modules, verifies invariance of both forms using the coproduct,
verifies the fusion rule, and prints the sum of squared ranks. Output for p = 2 and
p = 3 (the complete output is in `survey/quinn_check_output.txt`):

    p = 2: Hopf axioms {'assoc': True, 'unit': True, 'coassoc': True, 'counit_ax': True, 'antipode': True, 'cocomm': True}, cocommutative True
            two simple modules V_0, V_1 of dimension 1, distinct: True
            symmetric nondegenerate invariant forms on both: True
            fusion V_g (x) V_h = V_(g+h): True; ranks 1, 1
            sum of squared ranks in F_2 = 0
            Quinn (1)-(4) hold: True
    p = 3: ...
            sum of squared ranks in F_3 = 2
            Quinn (1)-(4) hold: False

## 6. Theorem 3: categorical data in every characteristic p at least 5

Quinn's conditions are conditions on H-modules, and the data below are exhibited as a
symmetric fusion category. Whether one can find a triangular Hopf algebra H in odd
characteristic whose module category contains this fusion category as a fusion
subcategory is not settled here, and I flag that as the precise remaining gap in this
section.

**Theorem 3 (ARGUMENT FROM CITATION for the fusion rules, MACHINE-CHECKED for the forms
and for p at most 13).** Let p be a prime with p at least 5 and let k be a field of
characteristic p. Let Ver_p be the universal Verlinde category of Ostrik 2020, with
simple objects Lbar_1, ..., Lbar_{p-1} and dim Lbar_s = s. Then the full subcategory
Ver_p^+ generated by the simples with odd index has these properties: every simple
object is self-dual and carries a symmetric nondegenerate invariant form, it is closed
under tensor product, and `sum_s s^2` over odd s is `(p-1)(p-2)p/6`, which is 0 in k.

The proof has three parts, and the first is Ostrik's.

Fusion rules. Ostrik's formula (4) in section 3.2 of arXiv:1503.01492 gives
`[Lbar_r][Lbar_s] = sum_{i=1}^{c} [Lbar_{|r-s|+2i-1}]` with `c = min(r, s, p-r, p-s)`,
and his Proposition 3.3(ii) lists the fusion subcategories of Ver_p for p greater than
3 as Vec, sVec, Ver_p^+ and Ver_p. His Proposition 3.3(iii) records
`Ver_p = Ver_p^+ ot sVec`. The script recomputes the tensor product decomposition from
the Jordan type of the operator `sigma - 1` on `L_r ot L_s` for every pair at
p = 2, 3, 5, 7, and the recomputation agrees with formula (4) in every case
("tensor products agree with Ostrik 2015 formula (4) for all r,s: True" for each of
those primes).

Self-duality and forms. Write `L_s = k[y]/(y^s)` with `sigma` acting by multiplication
by `1+y`, which is Ostrik's model in section 3.1. Let `iota` be the algebra
automorphism of `k[y]/(y^s)` with `iota(1+y) = (1+y)^{-1}`, so `iota(y) = -y + y^2 -
y^3 + ...` truncated, and let `tau(w)` be the coefficient of `y^{s-1}` in `w`. Define

    beta(u, v) = tau(u iota(v)).

Then beta is invariant, because `iota` is an algebra map and
`beta((1+y)u, (1+y)v) = tau((1+y)u (1+y)^{-1} iota(v)) = beta(u,v)`. It is
nondegenerate, because `(u,w) -> tau(uw)` is the standard nondegenerate trace form on
`k[y]/(y^s)` and `iota` is invertible. Both `beta` and its transpose are invariant, so
`beta + beta^T` is a symmetric invariant form. The script computes the determinants over
the integers and finds

    s = 1: det(beta) 1, det(beta+beta^T) 2, det(beta-beta^T) 0
    s = 2: det(beta) 1, det(beta+beta^T) 0, det(beta-beta^T) 4
    s = 3: det(beta) 1, det(beta+beta^T) 8, det(beta-beta^T) 0
    s = 4: det(beta) 1, det(beta+beta^T) 0, det(beta-beta^T) 16
    ... and in general det(beta + beta^T) = 2^s for odd s, det(beta - beta^T) = 2^s for even s.

So for odd s and for every field of odd characteristic, `beta + beta^T` is a symmetric
nondegenerate invariant form on `L_s`. For even s the same computation gives an
alternating nondegenerate invariant form, and the script verifies that in that case the
symmetric part `beta + beta^T` is singular. Whether a symmetric nondegenerate invariant
form exists on an even-index simple object I did not settle, and the even-index objects
are not needed for Theorem 3.

Descent to Ver_p. The Verlinde category is `Rep(k[C_p])` modulo negligible morphisms
(Ostrik 2020, Definition 3.1), so its simple objects are the images of the `L_s` with
`s` at most `p-1` (loc. cit., Proposition 2.13 and section 3.2). A form that is
nondegenerate on `L_s` has `lambda(coev(1)) = s`, which is nonzero in k because `s` is
at most `p-1`, so its image is a nondegenerate form on `Lbar_s`. Symmetry and
invariance are equations between morphisms and pass to the quotient. So `Lbar_s` with
odd `s` carries a symmetric nondegenerate invariant form in Ver_p.

The vanishing sum. The squares of the odd numbers from 1 to `p-2` add up to
`(p-1)(p-2)p/6`, and the script evaluates the same sum term by term and prints 0 in
`F_p` for p = 5, 7, 11 and 13. For p at least 5 the factor p in the numerator survives
the division by 6, so the sum vanishes in `F_p` and the formula is not an accident of
the four primes the script runs.

The machine output for p = 5 is:

    Vec                   : closed True, every simple has a symmetric nondegenerate form True, quadratic sum = 1 in F_5, Quinn (1)-(4): False
    sVec                  : closed True, every simple has a symmetric nondegenerate form False, quadratic sum = 2 in F_5, Quinn (1)-(4): False
    Ver_p^+ (odd indices) : closed True, every simple has a symmetric nondegenerate form True, quadratic sum = 0 in F_5, Quinn (1)-(4): True
    Ver_p (all simples)   : closed True, every simple has a symmetric nondegenerate form False, quadratic sum = 0 in F_5, Quinn (1)-(4): False

and the same line for Ver_p^+ reads True at p = 7, 11 and 13.

Because the forms have determinant `2^s`, which is a unit in every odd characteristic,
the construction works for all p at least 5 and not merely for the primes the script
runs.

## 7. Characteristic 3

Ver_3 is equivalent to the category of super vector spaces (Ostrik 2020, Example
3.2(ii)), and it has two simple objects with dimensions 1 and -1. Every closed
self-dual collection drawn from Ver_3 has sum of squares 1 or 1 + 1 = 2, and neither is
0 in `F_3`; the script prints this for the four subcategories.

For a non-degenerate symmetric fusion category over `F_3` the argument is complete.
Ostrik's Proposition 2.8 gives a super fiber functor, so the category is
`Rep(G, epsilon)` for a finite group G with a central element epsilon of order at most
2, and his proof shows that `|G|` is not divisible by 3. Quinn's condition (1) forces
every V_i to be an even object, because the invariant form on an odd object is
alternating, so each V_i has dimension `dim V_i` at least 1 and rank `dim V_i`. Write D
for the fusion subcategory generated by the V_i. All objects of D are even, so D is a
fusion subcategory of the Tannakian category `Rep(G/<epsilon>)`, which means that D is
`Rep(H)` for a quotient group H of `G/<epsilon>`, and in particular `dim D = |H|` is
prime to 3. The unit object is one of the V_i by Lemma 1, so the simple objects of D
are exactly the V_i and `sum_i (rank V_i)^2 = dim D = |H|`, which is not 0 in `F_3`.
Therefore no non-degenerate symmetric fusion category over `F_3` satisfies (1) to (4),
and the remaining case is a degenerate symmetric fusion category over `F_3` larger than
Ver_3, which I have not classified. That is the exact point where this direction stops
on p = 3.

## 8. Ground rings

Over `Z`, every rank is a unit by Quinn's Remark (ii), the units of `Z` are 1 and -1,
and the sum of the squares of units is a positive integer, so condition (4) cannot hold.
Over `Z[i]` the arithmetic obstruction disappears, because `1^2 + i^2 = 0` and both 1
and i are units. Whether a triangular Hopf algebra over `Z[i]` with the other required
properties exists is not settled here. The honest statement is that the characteristic 0
impossibility is a field statement, proved in Theorem 1, and that the case of a general
ring of characteristic 0 is open.

## 9. Modular tensor categories

Quinn's Remark (i) compares his conditions to "modular Hopf algebras". The modular
version cannot help in characteristic 0 either, and for a simpler reason than the
symmetric case: Etingof-Nikshych-Ostrik Theorem 2.3 applies to every fusion category,
braided or not, and says the global dimension is nonzero in characteristic 0. Since the
global dimension of a ribbon or modular category is the sum of the squares of the
categorical dimensions of its simple objects, the modular analogue of condition (4) also
fails over every field of characteristic 0. What positive characteristic does to
modular categories is outside the scope of this note.

## 10. The detection question: a published obstruction

Quinn's construction produces a semisimple theory. By Lemma 1 the V_i are the simple
objects of a symmetric fusion category C, and his recipe in section 4 uses V as the sum
of the V_i, their fusion rules, the forms and the functor E, so everything depends on
the semisimple category C and on nothing else. A TQFT built that way is a semisimple
TQFT in the sense of the following theorem, which is the recent literature that cites
Quinn's paper on exactly this point.

Khovanov, Krushkal and Nicholson, *On the universal pairing for 2-complexes*, Bulletin
of the London Mathematical Society 57 (2025), no. 9, 2838-2853, DOI
10.1112/blms.70130, arXiv:2312.07429, Theorem 4.1 and the lines after it, verbatim
with ASCII symbols:

> Theorem 4.1. Let L_1, L_2 be 2-complexes such that pi_1(L_1) = pi_1(L_2) and
> chi(L_1) = chi(L_2). Then there exist n and L'_1, L'_2 in K_n such that
>   (i) For i = 1, 2, L_i is 2-deformation equivalent to L'_i.
>   (ii) x := L'_1 - L'_2 in kK_n satisfies x . x = 0, so in particular x is a null
>        vector for the universal pairing: <x, x> = 0.
>
> It follows that a unitary TQFT cannot distinguish between stable equivalence and
> 3-deformation of 2-complexes. Indeed, in a unitary TQFT, with k = C, the null-vector
> property <x, x> = 0 implies x = 0. This corollary, in the setting of semi-simple
> TQFTs over an algebraically closed field k, can also be established using methods
> analogous to [Re].

Their terminology needs one word of care. Their 3-deformation is what Quinn calls a
2-deformation, namely the Andrews-Curtis moves, as they explain in section 2: "(Some
authors, for example [Q1], refer to this equivalence relation as a 2-deformation. We
follow the convention in [HM1].)" Their 2-deformation is a stricter relation, and a
2-deformation is in particular a 3-deformation. So clause (i) of their theorem places
each L_i in the same Andrews-Curtis class as L'_i, which is what the argument below
needs.

The inference to Quinn's question is short. A contractible 2-complex and a point have
the same fundamental group and the same Euler characteristic, so they are stably
equivalent. A TQFT that is an invariant of 2-deformations, which is Quinn's word for
the Andrews-Curtis moves, gives the same value to L_i and to L'_i. In a semisimple
theory the null vector property forces x = 0, so the values on L'_1 and L'_2 agree.
Hence such a theory gives a contractible 2-complex and a point the same value, and it
cannot separate a counterexample from the standard complex.

Labels for this section. The unitary case over the complex numbers is proved in their
paper. The extension to semisimple TQFTs over an algebraically closed field is
**REPORTED** there, with the method attributed to Reutter's paper. The step from their
theorem to Quinn's construction, namely that Quinn's conditions (1) to (3) make his
theory semisimple, is my **ARGUMENT** and rests on Lemma 1.

Combining this section with Theorem 1 gives the verdict of this note. Over a field of
characteristic 0 Quinn's data cannot exist. Over a field of characteristic 2, and over
Ver_p^+ in characteristic p at least 5, the data exist, but they are semisimple data, so
any theory built from them falls under the obstruction above and cannot detect the
difference. The one escape is a theory that is not semisimple, and Quinn's conditions
(1) to (3) exclude that, because they make every V_i simple and every tensor product of
two of them a sum of the same V_i.

## 11. What this means for the programme

Four statements follow, each with its label. The first two are proved in this note, the
third is superseded by a published theorem, and the fourth is open.

1. **ARGUMENT FROM CITATION.** Quinn's conditions cannot be met over any field of characteristic 0, so
   his suggestion that "the complex numbers is probably a good choice" is impossible
   once the conditions (1) to (3) are imposed. His proposed remedy, adjusting the
   R-matrix to force the sum of squares to vanish (Remark (vi)), cannot work in
   characteristic 0.
2. **MACHINE-CHECKED.** The conditions can be met over `F_2`, by a two-dimensional Hopf algebra.
   Since the example is so small, conditions (1) to (4) alone have no bearing on the
   Andrews-Curtis conjecture. Any content of the programme has to lie in the TQFT
   construction and in what the resulting invariant computes.
3. **REPORTED, and superseded.** Quinn says that the data can be used to construct a
   TQFT on 2-complexes and that it "stands a good chance of detecting counterexamples".
   The construction is not complete in the arXiv source, no value of the invariant is
   computed there, and Quinn states that there was no general proof that such a theory
   is nontrivial. Khovanov, Krushkal and Nicholson prove the unitary case and report the
   semisimple case of the statement that theories of this kind cannot separate a
   contractible 2-complex from a point, which is the separation Quinn's programme
   needs.
4. **OPEN, and outside Quinn's conditions.** A non-semisimple theory could in principle
   escape the obstruction, and nothing in this note bears on one. Quinn's own conditions
   (1) to (3) exclude it, since they make the V_i the simple objects of a semisimple
   category, so leaving Quinn's framework is a change of programme and not a repair of
   it.

An outside check on the size of the question: the question list at the repository root
rates Q9 as C, on the ground that deciding the general question is far beyond a short
round. The existence question is now settled in characteristic 0 and in characteristic
2, open in characteristic 3, and the detection question is answered in the negative for
the semisimple theories that Quinn's conditions produce.

## 12. What I could not check

1. Quinn's construction of the invariant, section 4 of the arXiv text, is truncated in
   the only source I could read. I did not find a complete version of the paper.
2. The literature search was not exhaustive. A query of OpenAlex on 4 November 2026
   reports two works citing Quinn's paper: the Khovanov-Krushkal-Nicholson paper of item
   8, which I read, and a 2023 paper on semisimple four-dimensional topological field
   theories and exotic smooth structure (DOI 10.1112/topo.12288), which I did not read.
   I did not find a published answer to the existence question itself.
3. Deligne's original paper (*Categories tensorielles*, Moscow Math. J. 2 (2002)
   227-248) was not downloaded. The super-Tannakian statement I quote is quoted from
   two secondary sources, Ostrik's exposition arXiv:math/0401347 and Ostrik 2020, and I
   did not need it for the proof of Theorem 1, which uses only Etingof-Nikshych-Ostrik
   Theorem 2.3, read directly in arXiv:math/0203060.
4. The characteristic 3 case is open, and the gap is stated in section 7.
5. The gap between Theorem 3 and Quinn's literal wording, namely the absence of a
   triangular Hopf algebra over `F_p` in odd characteristic whose modules contain
   Ver_p^+, is not closed.
6. Whether an even-index simple object of Ver_p carries a symmetric nondegenerate
   invariant form is not settled here. The script shows that the symmetric part of the
   explicit form is singular for even `s`, and that is all it shows.

## 13. Reproduction

Files, all at the repository root:

* `survey/quinn-tqft.md`, this file.
* `survey/quinn_check.py`, the exact-arithmetic checker, standard library only.
* `survey/quinn_check_output.txt`, the recorded output of the command below.

Commands:

    python3 survey/quinn_check.py

The run takes less than one second on the VM and prints the part A and part B lines
quoted above. The script is deterministic: it uses no random numbers and no seeds.

## 14. Citations, with identifiers

1. F. Quinn, *Representation theory, topological field theory, and the Andrews-Curtis
   conjecture*, arXiv:hep-th/9202044v2 (1992). Verified through the arXiv API and by
   reading the PDF.
2. P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. (2) 162
   (2005), no. 2, 581-642, DOI 10.4007/annals.2005.162.581, arXiv:math/0203060.
   Theorem 2.3 and Definition 2.2 quoted from the arXiv text. Journal data checked on
   zbMATH.
3. V. Ostrik, *On symmetric fusion categories in positive characteristic*, Selecta
   Math. (N.S.) 26 (2020), no. 3, Paper No. 36, 19 pp., DOI 10.1007/s00029-020-00567-5,
   arXiv:1503.01492, Zbl 1440.18032. Sections 2.4, 2.5, 3.1, 3.2, Proposition 2.8,
   Proposition 2.13, Proposition 3.3, Example 3.2 read in the PDF.
4. P. Etingof, S. Gelaki, *The classification of triangular semisimple and cosemisimple
   Hopf algebras over an algebraically closed field*, Int. Math. Res. Not. 2000, no. 5,
   223-234, DOI 10.1155/S1073792800000131, arXiv:math/9905168, Zbl 0957.16029. The
   sentence quoted from Corollary 6.2 is in the arXiv text; the journal volume, issue
   and pages are from the zbMATH record.
5. P. Etingof, S. Gelaki, *Some properties of finite-dimensional semisimple Hopf
   algebras*, Math. Res. Lett. 5 (1998), 191-197, Zbl 0907.16016. Not read directly: the
   statement that a triangular semisimple Hopf algebra in characteristic 0 is a twist of
   a group algebra is quoted from the zbMATH review of item 4 and from the introduction
   of item 4.
6. P. Deligne, *Categories tensorielles*, Mosc. Math. J. 2 (2002), no. 2, 227-248,
   Zbl 1005.18009. Not read directly. The super-Tannakian statement is as quoted in
   Ostrik, *Tensor categories (after P. Deligne)*, arXiv:math/0401347, and in item 3.
7. V. Ostrik, *Tensor categories (after P. Deligne)*, arXiv:math/0401347 (2004).
   Corollary to Deligne's theorem, quoted: a semisimple symmetric tensor category with
   finitely many simple objects is equivalent to `Rep(G, epsilon)` for a finite group G
   and a central element epsilon of order at most 2.

8. M. Khovanov, V. Krushkal, J. Nicholson, *On the universal pairing for 2-complexes*,
   Bull. Lond. Math. Soc. 57 (2025), no. 9, 2838-2853, DOI 10.1112/blms.70130,
   arXiv:2312.07429. Theorem 4.1 and the paragraph after it quoted from the PDF.
   Journal data checked on zbMATH.

Items 1 to 4 and item 8 in the list were read directly and are quoted verbatim; items 5
and 6 are quoted from secondary sources and are flagged as such. Where a citation rests
on a secondary source, the statement it supports is also supported by an item read
directly, with the single exception of Deligne's theorem, which is background and not
used in any proof above.
