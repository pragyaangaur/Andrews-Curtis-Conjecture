# The topological side of the Andrews-Curtis conjecture

Round 1 survey, written by member m11 for direction D6 of swarm smw2fzjic. The subject is the
translation of the Andrews-Curtis conjecture into the topology of 2-dimensional CW complexes, the
deformation relations that appear there, Zeeman's collapsibility conjecture, the theory of spines, and
the chain that leads from AC moves to smooth 4-manifolds.

## 0. Labels, and how to read this file

Every claim below carries one of three labels, and the list that follows defines them.

* **VERIFIED** means I read the statement in the named source and quote or paraphrase it closely. Each
  source is given with a DOI or arXiv identifier, and section 8 records what I actually saw for it.
* **CHECKED** means the statement is the output of an exact computation that anyone can rerun. Section 7
  gives the command and the output, and the script is `survey/topology_check.py`.
* **ARGUMENT** means the statement is my own reasoning from labelled ingredients, and no source I read
  states it in that form.

Statements I could not verify are collected in section 9, and nothing in sections 1 to 7 depends on
them. Two conventions are fixed here. A *balanced* presentation has as many relators as generators, and
the problem's `AK(n)` is the presentation $\langle x,y \mid xyx = yxy,\ x^n = y^{n+1}\rangle$. Section 10
explains why the literature's indexing of this family differs from ours, and why that matters for
citation.

## 1. The dictionary between presentations and 2-complexes

### 1.1 The standard complex

Let $P = \langle x_1,\dots,x_n \mid r_1,\dots,r_m\rangle$. The *standard complex* $K(P)$ has one vertex
$v$, one 1-cell $e_i$ for each generator, and one 2-cell for each relator, attached along the loop that
spells $r_i$ in the rose of $n$ circles. Then $\pi_1 K(P) \cong F_n / \langle\!\langle r_1,\dots,r_m
\rangle\!\rangle$, by Seifert and van Kampen. When $P$ is balanced the Euler characteristic is
$\chi(K(P)) = 1 - n + n = 1$, so $K(P)$ has the Euler characteristic of a point.

### 1.2 What the three AC moves do to $K(P)$

Move (1), $r_i \mapsto r_i^{-1}$, replaces the characteristic map of one 2-cell by its composition with a
reflection of the circle. The image of the characteristic map and the resulting subcomplex are unchanged,
so at the level of complexes this move does nothing at all. **ARGUMENT**, and elementary.

Move (2), $r_i \mapsto r_i r_j$, is a slide of the 2-cell $e_i$ over the 2-cell $e_j$. Inside $K(P)$ the
loop $r_j$ bounds the 2-cell $e_j$, so $r_j$ is null-homotopic in $K(P)$ as a based loop, and therefore
$r_i r_j$ is homotopic to $r_i$ as a based loop in $K(P)$. The complex $K(P')$ differs from $K(P)$ only
in the attaching map of one 2-cell, and that attaching map has been changed by a homotopy inside
$K(P)$. **ARGUMENT**, and this is the standard reading of a 2-cell slide.

Move (3), $r_i \mapsto w r_i w^{-1}$, changes the attaching map by a move of the base path. As an unbased
loop the word $w r_i w^{-1}$ is freely homotopic to $r_i$ inside the 1-skeleton. **ARGUMENT**.

All three moves keep the presented group, because each is a Tietze transformation. Consequently every
invariant that factors through the presented group is constant on an AC-equivalence class. This one
sentence explains most of the negative results in the literature, and section 3 develops it.

### 1.3 Deformations of 2-complexes

Quinn defines the relevant relation as follows. **VERIFIED**, Quinn, *Dual 2-complexes in 4-manifolds*,
arXiv:math/0009234, Definition 1.7:

> Suppose $K$, $L$ are 2-dimensional CW complexes. A 2-deformation $K \to L$ is a sequence of moves
> starting with $K$ and ending with $L$. Each move is either an elementary expansion or collapse (of
> dimension $\le 2$), or change of attaching map of a 2-cell by homotopy. In some of the literature these
> are called "3-deformations" because homotopy of 2-cells is viewed as expansion and then collapse of a
> 3-cell. Our terminology follows Wall. Note that a 2-deformation determines a simple homotopy
> equivalence $K \to L$. The (generalized) Andrews-Curtis conjecture is that any simple equivalence of
> 2-complexes comes from a 2-deformation. No one expects this to be true, however.

The terminology warning is taken verbatim from that definition, and it causes real confusion in the
secondary literature. A "3-deformation" in the sense of Hog-Angeloni and Metzler is a "2-deformation" in
the sense of Quinn. I use Quinn's word and add "(3-deformation)" on first use.

Combining Definition 1.7 with section 1.2 gives the basic implication. **ARGUMENT.**

> Each of the three AC moves is a 2-deformation move. Hence AC-equivalent presentations have
> 2-deformation-equivalent standard complexes, and therefore simple homotopy equivalent standard
> complexes.

The converse direction is the generalized Andrews-Curtis conjecture, and Quinn states that it is
expected to be false. Section 2 records a theorem that kills one form of the converse.

## 2. The three relations Q, $Q^*$ and $Q^{**}$

Barmak gives definitions that are precise enough to quote. **VERIFIED**, Barmak, *An exotic presentation
of $\mathbb{Z}\times\mathbb{Z}$ and the Andrews-Curtis conjecture*, Algebr. Geom. Topol. 25 (2025)
345-355, DOI 10.2140/agt.2025.25.345, from the introduction. A finite presentation can be changed by:

> (i) Changing a relator $r_j$ by $r_j r_i$ for some $i \ne j$. (ii) Changing a relator $r_j$ by
> $r_j^{-1}$. (iii) Changing a relator $r_j$ by a conjugate $g r_j g^{-1}$ for some $g$ in the free group.
> (iv) Changing each relator $r_j$ by $\varphi(r_j)$, where $\varphi$ is an automorphism of the free
> group. (v) Adding a generator $x_{n+1}$ and a relator $r_{n+1}$ which coincides with $x_{n+1}$.
> (vi) The inverse of (v), when possible.
>
> Moves (i) to (iii) are called Q-transformations, (i) to (iv) are $Q^*$-transformations and moves (i) to
> (vi) are called $Q^{**}$-transformations.

So Q-transformations are exactly the three AC moves of our problem. Barmak does not include a move that
permutes the relators, and neither does our problem statement, while Kupers' list of extended Nielsen
operations does include one, so a reader comparing the two lists should check which version is meant.
The same page states the following three conjectures, and Barmak records that all three are open.
**VERIFIED.**

1. *AC or Q version*: any two balanced presentations of the trivial group are Q-equivalent.
2. *Weak AC or $Q^{**}$ version*: any two balanced presentations of the trivial group are
   $Q^{**}$-equivalent. Barmak writes: "The latter is equivalent to the statement that any contractible
   finite 2-dimensional CW-complex 3-deforms to a point."
3. *Generalized AC*: any two presentations whose standard complexes are simple homotopy equivalent are
   $Q^{**}$-equivalent. Barmak attributes the statement to Hog-Angeloni and Metzler, section 4.1.

The third statement is the only place where simple homotopy type enters as a hypothesis, and the
literature has already refuted its $Q^*$ form. **VERIFIED**, Barmak, Theorem 5 of the paper cited above:

> The standard complexes $K_P$ and $K_Q$ are simple homotopy equivalent, while $P$ and $Q$ are not
> $Q^*$-equivalent.

Here $P = \langle x,y \mid [x,y], 1\rangle$ and $Q$ is the other presentation displayed in the paper,
which presents $\mathbb{Z}\times\mathbb{Z}$ and so is not contractible. The relevance for us is
structural: simple homotopy equivalence does not imply $Q^*$-equivalence, so a proof of any generalized
form of AC would have to use the full $Q^{**}$ moves. One further convention matters for reading the
rest of the literature. Romary and Zupan record that sources differ on whether stabilization is
included in "AC-trivial", and they say "in this paper, AC-triviality will always allow moves (1)-(4)"
where their (4) is stabilization (**VERIFIED**, Romary and Zupan, *A family of Andrews-Curtis
trivializations via 4-manifold trisections*, Geom. Dedicata (2024), DOI 10.1007/s10711-024-00891-6,
Remark 1.3). The stable version in our problem statement is the (v) and (vi) part of $Q^{**}$ alone, so
it sits between the Q version and the $Q^{**}$ version.

## 3. Simple homotopy type is too coarse to see a counterexample

### 3.1 Every move is a simple homotopy equivalence

By section 1.3 each AC move is a 2-deformation move, and by Quinn's Definition 1.7 a 2-deformation
determines a simple homotopy equivalence. A $Q^*$-transformation applies an automorphism of $F_n$ to all
relators at once, which amounts to composing the attaching maps with a homotopy equivalence of the rose of
$n$ circles, and every homotopy equivalence of finite connected graphs is simple. So the same conclusion
holds for the $Q^*$ relation. **ARGUMENT.** Hence AC-equivalence is finer than simple homotopy equivalence
of standard complexes, and the published Theorem 5 of Barmak says that the inclusion is strict for the
$Q^*$ relation: his two presentations have simple homotopy equivalent standard complexes and are not
$Q^*$-equivalent (**VERIFIED**, Barmak, arXiv:1806.11493 and Algebr. Geom. Topol. 25 (2025), Theorem 5).

### 3.2 On the class of interest the simple homotopy type is a single point

If $K$ is a finite contractible 2-complex then the identity map $K \to \ast$ is a homotopy equivalence, and
its Whitehead torsion lies in $\mathrm{Wh}(1) = 0$. Hence every finite contractible 2-complex is simple
homotopy equivalent to a point, and any two of them are simple homotopy equivalent to each other.
**ARGUMENT**, using the triviality of the Whitehead group of the trivial group. The consequence is
immediate and it is the main obstruction on this map.

> No invariant of the simple homotopy type can distinguish a balanced presentation of the trivial group
> from the standard one. The class of candidates for a counterexample is a single simple homotopy type,
> and it is the type of a point.

In particular the Whitehead torsion, the chain complex of the universal cover, the homology of $K(P)$,
the Euler characteristic and the fundamental group are all constant on that class. Section 7 turns the
homological part of this into an exact computation.

### 3.3 The vanishing, exactly

For a balanced presentation $P$ of the trivial group the abelianisation of $G$ is trivial, so the
exponent-sum matrix $A$ of $P$, the $n \times n$ matrix whose $i$-th row records the exponent sums of
$r_i$ in the generators, satisfies $|\det A| = 1$. Then $H_1(K(P);\mathbb{Z}) = 0$, and since $\chi = 1$
one gets $b_2 = 0$ as well, so $K(P)$ is acyclic and has the integral homology of a point. **CHECKED** in
section 7 for the three presentations $\langle x,y \mid xyx = yxy, x^m = y^n\rangle$ with $(m,n) = (3,4)$,
$(5,4)$ and $(2,3)$; the exponent-sum matrices are $\begin{pmatrix}1&-1\\ m&-n\end{pmatrix}$ with
determinants $-1$, $1$ and $-1$. The general formula is also computed there: the determinant is $m-n$, so
the abelianisation is trivial exactly when $m = n \pm 1$. That last condition is exactly the condition
under which Quinn says these complexes are contractible, which is a pleasant cross-check between two
independent statements (**CHECKED** for $m-n$, **VERIFIED** for the contractibility criterion, Quinn,
*Representation theory, topological field theory, and the Andrews-Curtis conjecture*, arXiv:hep-th/9202044,
section 1).

### 3.4 The stability of invariants under wedging with 2-spheres

Quinn makes the point in a form worth quoting. **VERIFIED**, Quinn, arXiv:hep-th/9202044, section 1:

> The Andrews-Curtis problem has a very similar nilpotence property: Suppose $f: X \to Y$ is a simple
> homotopy equivalence of 2-complexes. Then for some $k$ the map $f \vee \mathrm{id}: X \vee kS^2 \to
> Y \vee kS^2$ is homotopic to a deformation through 2-complexes. Again traditional invariants of $f$
> can be recovered from those of $f \vee \mathrm{id}$, so cannot detect counterexamples to the
> conjecture.

So even away from the contractible case, an invariant that survives the operation of wedging with copies
of $S^2$ cannot separate. The upshot is that a separating invariant has to be an invariant of the
2-deformation class itself, and no such invariant is presently known to be nonzero on any candidate.
Quinn proposed constructing one from a topological field theory on 2-complexes (**VERIFIED** as a
proposal from the abstract of arXiv:hep-th/9202044, which asks for a triangular Hopf algebra with
self-dual irreducible representations $V_i$ such that the product of any two is a sum of copies of the
$V_i$ and $\sum (\dim V_i)^2 = 0$). Whether that programme can be completed is open as far as the sources
I read say, and I did not verify any claim that it has been.

## 4. Spines

The definitions are standard and I take them from Kupers' survey. **VERIFIED**, Kupers, *Zeeman's
conjecture*, Graduate J. Math. 6 (2021) 35-42, sections 1 and 2. An elementary collapse is the removal
of a pair of cells $\sigma \subset \tau$ with $\sigma$ a face of $\tau$ and no other coface in the
complex; $K$ collapses to $L$, written $K \searrow L$, if there is a finite sequence of elementary
collapses; $K$ is collapsible if $K \searrow \ast$. A finite complex $K$ is a *spine* of a compact
manifold $M$ if $M \searrow K$, that is, $M$ collapses onto $K$. Collapsibility implies contractibility,
and the converse fails, with the dunce cap and Bing's house with two rooms as the standard examples
(**VERIFIED**, Kupers, section 1 and Example 2.3).

Two classes of 2-complexes matter for us. A 2-polyhedron is *standard* if it locally looks like one of
three configurations, a definition due to Casler that Kupers records as Definition 3.5, and Kupers adds a
remark that "a standard 2-polyhedron, by a twist of fate, is sometimes also called a special 2-polyhedron"
(**VERIFIED**, Kupers, Definition 3.5 and Remark 3.6). Every connected compact 3-manifold with boundary
has a standard spine (**VERIFIED**, Kupers, Lemma 3.7, quoting Gillman and Rolfsen quoting Zeeman).

For 4-manifolds the parallel notion is a *2-handlebody*: a 4-manifold built from a 0-handle and
1-handles and 2-handles, which has a 2-complex spine, and whose boundary carries the attaching circles of
the 2-handles. Quinn studies deformations of such spines inside a 4-manifold and calls them ambient
2-deformations, "a sequence of handle moves in $M$ and homotopically trivial handle moves over handles in
the complement" (**VERIFIED**, arXiv:math/0009234, Definition 1.8). He adds that these deformations
"usually change the fundamental group of the complement", which is the reason the 4-dimensional theory
does not reduce to the 3-dimensional one.

## 5. Zeeman's conjecture

### 5.1 The statement and its status

**VERIFIED**, Kupers, Conjecture 2.1:

> If $K$ is a contractible 2-polyhedron, then $K \times I \searrow \ast$.

The conjecture is Zeeman's, from *On the dunce hat*, Topology 2 (1964) 341-358, DOI
10.1016/0040-9383(63)90014-4, and Kupers records that it "is still open, though we will later see that it
is partially settled by Perelman's proof of the Poincare conjecture". The same statement appears as
Conjecture (Z) in the book chapter of Matveev and Rolfsen, who call it "the rather audacious conjecture
put forward in 1964 by E. C. Zeeman" (**VERIFIED**, Matveev and Rolfsen, *Zeeman's collapsing conjecture*,
in Two-dimensional homotopy and combinatorial group theory, London Math. Soc. Lecture Note Ser. 197
(1993) 335-364, DOI 10.1017/CBO9780511629358.013).

### 5.2 What is proved

The following partial results are quoted from Kupers' survey, which cites the original papers.
**VERIFIED** as statements of the survey; I did not read the four original papers.

* For every contractible 2-polyhedron $K$ there is $k \ge 0$ with $K \times I^k$ collapsible (Dierker,
  Proc. Amer. Math. Soc. 19 (1968) 425-428).
* $K \times I^6$ is collapsible for every contractible 2-polyhedron $K$, and $K \times I^{2n}$ is
  collapsible for every contractible $n$-polyhedron (Cohen, Topology 14 (1975) 253-256).
* For every $n \ge 3$ there is a contractible $n$-polyhedron $K$ with $K \times I$ not collapsible
  (Cohen, Topology 16 (1977) 79-88). So the restriction to dimension 2 is essential.
* The dunce cap and Bing's house with two rooms do become collapsible after crossing with $I$ (Zeeman for
  the dunce cap, Gillman, Topology Appl. 24 (1986) 147-151, for Bing's house).
* Zeeman's conjecture holds for the standard polyhedra that are spines of 3-dimensional PL manifolds. The
  precise statement in Kupers is Proposition 3.8: "Zeeman's conjecture for standard 2-polyhedra that are
  spines of 3-dimensional PL-manifolds is equivalent to the Poincare conjecture". Since the Poincare
  conjecture is a theorem, so is that restricted case.

### 5.3 The exact relation to the Andrews-Curtis conjecture

The relation is stronger than an analogy, and it splits along the thickenable and non-thickenable cases.
**VERIFIED** from the opening of the Matveev and Rolfsen chapter:

> Zeeman's Conjecture (Z) If $P^2$ is a contractible 2-dimensional polyhedron, then $P^2$ is
> 1-collapsible, that is, $P^2 \times I$ collapses to a point. As already pointed out in Chapter I,
> section 4.2, (Z) implies both the Poincare conjecture (P) and the Andrews-Curtis conjecture (AC).

Matveev proved a converse for a restricted class. **VERIFIED** as quoted in Kupers' bibliography:
Matveev, *The Zeeman conjecture for nonthickenable special polyhedra is equivalent to the
Andrews-Curtis conjecture*, Sibirsk. Mat. Zh. 28 (1987) 66-80. I did not read the Russian original, and
I did not verify the direction of the equivalence beyond the title.

Putting the verified items together gives the sharpest statement I can support, and it is worth being
explicit about the case that is left open. **ARGUMENT**, from the three VERIFIED items above.

> Zeeman's conjecture implies AC. For the thickenable standard polyhedra it is true, since it reduces to
> the Poincare conjecture. For the non-thickenable special polyhedra it is equivalent to AC. What these
> statements do not settle is the class of contractible 2-polyhedra that are not standard, and that class
> is the one the recent preprint in the next paragraph addresses.

So AC is implied by Zeeman's conjecture, and a counterexample to AC built from a non-thickenable special
polyhedron would refute Zeeman's conjecture as well. **ARGUMENT**, immediate from the two equivalences.
What I cannot support from the sources I read is the cleaner claim that Zeeman's conjecture is equivalent
to AC together with the Poincare conjecture, because the non-standard case is not covered by the
statements above.

The classical attribution for the dictionary between the combinatorial relation and 3-deformations is
Wright, *Group presentations and formal deformations*, Trans. Amer. Math. Soc. 208 (1975) 161-169, DOI
10.1090/s0002-9947-1975-0380813-5. I located it through Crossref and through Kupers' bibliography and
could not read it, because the AMS page would not serve the PDF to an unauthenticated request, so the
dictionary in sections 1 to 3 rests on Quinn and Barmak and not on Wright. **NOT VERIFIED** for Wright's
own content.

A very recent preprint goes further. Dynnikov, *On Zeeman's collapsibility conjecture for non-standard
polyhedra*, arXiv:2608.23331 (submitted 24 August 2026), has the abstract "We prove that if Zeeman's
collapsibility conjecture holds for standard polyhedra, then it holds in general", and its introduction
says the aim is to establish the equivalence of Zeeman's conjecture with the stable Andrews-Curtis
conjecture. This is a preprint from a few months ago that I have not checked, and I flag one tension I
could not resolve without reading it in full: by the paragraph above, Zeeman's conjecture for the
thickenable standard polyhedra already follows from Perelman's theorem. Anyone relying on that preprint
should read its precise hypotheses. **NOT VERIFIED.**

COORDINATOR NOTE, 2026-11-04. The flagged tension above is a misreading, and survey/dynnikov.md
section 7 is the correction of record. The word that carries the weight is "thickenable": Perelman's
theorem together with Gillman-Rolfsen settles the standard polyhedra that are spines of 3-manifolds, and
says nothing about standard polyhedra that are not spines of any 3-manifold, which are exactly the class
to which Matveev's result applies and to which the preprint's hypothesis extends. There is no
inconsistency between the preprint's hypothesis and Perelman's theorem. Section 6.2 of the same file
also resolves the Matveev stable-versus-unstable ambiguity recorded in section 4 of
survey/stable-ac.md, in favour of the stable reading, on the strength of the zbMATH review of
Matveev 1987.

## 6. From spines to smooth 4-manifolds

### 6.1 Handle decompositions produce balanced presentations

Let $W$ be a compact smooth 4-manifold with a handle decomposition with one 0-handle, $n$ 1-handles, $n$
2-handles and one 4-handle, and no 3-handles. The boundary of the union of the 0-handle and the 1-handles
is $\#_n (S^1 \times S^2)$, and each 2-handle is attached along a knot in that 3-manifold. Choosing a base
point and paths gives $n$ words $r_1,\dots,r_n$ in $F_n$, and the 2-handles can be cancelled against the
1-handles when those words can be changed to the generators $x_1,\dots,x_n$ by isotopies and
slides. Slides of 2-handles over 2-handles and changes of the base path are the AC moves (2) and (3) of
section 1.2, and reversing an orientation is move (1). **ARGUMENT**, and this is the dictionary that the
Akbulut and Kirby paper uses. The consequence that matters is one-directional. **ARGUMENT.**

> If the presentation of such a $W$ is AC-trivial, then the 2-handles can be cancelled against the
> 1-handles, and $W$ is diffeomorphic to $B^4$.

The contrapositive is what a reader might hope for and it is false as stated: non-AC-triviality of the
presentation does not imply that $W$ is non-standard, because a diffeomorphism of $W$ to $B^4$ could be
built by other means. Sections 6.2 and 6.3 give the concrete instance.

The original topological consequence of the conjecture has the same shape one dimension higher.
**VERIFIED** as an extraction from the AMS page of Andrews and Curtis, Proc. Amer. Math. Soc. 16 (1965),
Theorem 2: "Let $K$ be a finite contractible 2-dimensional subcomplex of a combinatorial 5-manifold $M$,
and let $N$ be any regular neighborhood of $K$ in $M$. If the conjecture is true then $N$ is a 5-cell." A
regular neighbourhood of a contractible 2-complex in a combinatorial 5-manifold is a 5-dimensional
thickening of it, so the conjecture would make every such thickening a ball. This is the 5-dimensional
counterpart of the 4-dimensional question of this section, and it is where the conjecture came from.
**ARGUMENT** for the identification of the two questions.

### 6.2 The Akbulut-Kirby example

**VERIFIED** as an OCR extraction from the scanned published PDF of Akbulut and Kirby, *A potential smooth
counterexample in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the
Andrews-Curtis conjecture*, Topology 24 (1985) 375-390, DOI 10.1016/0040-9383(85)90010-2. The wording
below is from the OCR and may differ in small details from the printed page, and I could not read the
printed page itself.

> We describe a homotopy 4-sphere $X^4$, built with the usual zero and 4-handle and two 1-handles and two
> 2-handles (Figure 28). ... (B) The presentation of the trivial group arising from $X^4$ is
> $\{x, y \mid xyx = yxy, x^5 = y^4\}$; it is easy to show that this group is trivial, but it seems
> difficult to do so using Andrews-Curtis moves.

The same paper shows that $X^4$ is homeomorphic to $S^4$, using Freedman's theorem and the topological
Schoenflies theorem, and it leaves open whether $X^4$ is diffeomorphic to $S^4$. So the example was a
potential counterexample to the smooth 4-dimensional Poincare conjecture, and the route to showing that
it is standard was expected to be an AC-trivialization of the presentation. Note the shape of the
argument: AC-triviality would give standardness, and nothing was claimed about the converse.

### 6.3 Gompf kills the example

**VERIFIED** through the zbMATH review of Gompf, *Killing the Akbulut-Kirby 4-sphere, with relevance to
the Andrews-Curtis and Schoenflies problems*, Topology 30 (1991) 97-115, DOI 10.1016/0040-9383(91)90036-4,
zbMATH 0715.57016. The review states that the Akbulut-Kirby 4-sphere $\Sigma^4$ has a handle
decomposition with two 1-handles and two 2-handles and no 3-handles, that it was therefore regarded as a
potential counterexample to the smooth 4-dimensional Poincare conjecture, and that Gompf constructs a
concrete diffeomorphism $\Sigma^4 \cong S^4$. The review continues, in my translation from the German,
that Gompf's proof avoids the Andrews-Curtis problem by a sequence of handle decompositions in which
3-handles appear in between, and that if the presentation is nontrivial then a Morse-theoretic proof of
the smooth Schoenflies conjecture would have to reflect the necessity of those intermediate 3-handles.

This is the sharpest available illustration of section 6.1. The AC status of the presentation
$\{x,y \mid xyx = yxy, x^5 = y^4\}$ is still not known, and the manifold is known to be standard anyway.
So an AC counterexample is not a route to an exotic smooth structure by itself.

### 6.4 Quinn's duality theorem for 2-complexes in $S^4$

Quinn proves a theorem that says exactly how 2-deformation classes of 2-complexes are the combinatorial
data of 4-dimensional Heegaard splittings. **VERIFIED**, arXiv:math/0009234, Corollary 1.5:

> Two 2-complexes $K$, $L$ occur (up to 2-deformation) as dual spines of a Heegaard decomposition of
> $S^4$ if and only if they are connected and satisfy Alexander-Lefschetz duality $H_1(K) \cong H^2(L)$
> and $H_2(K) \cong H^1(L)$.

He also records the caution that makes the 4-dimensional theory hard, and I quote it because it bears
directly on any plan to read off 4-manifold invariants from 2-complexes. **VERIFIED**,
arXiv:math/0009234, section 2.2:

> There should be smooth 4-manifolds that are simple equivalent to 2-complexes but are not 2-handlebodies.
> ... It seems highly unlikely that 2-handlebody structures are unique in the sense that one can be
> deformed to any other through 2-handlebodies, even though the corresponding result is true for
> $k$-handlebodies, $k \ne 2$.

For the problem at hand the relevant reading is this. The 2-deformation relation is the right equivalence
on the topological side, and a contractible 2-complex has the simple homotopy type of a point, so every
simple homotopy invariant is constant on the class of candidates. The only theorems I found that produce
4-manifold data from 2-complexes pass through duality statements of the kind Quinn proves, and none of
them turns a failure of 2-deformability into a failure of standardness.

### 6.5 R-links and the recent positive cases

Akbulut and Kirby's construction has a modern formulation. **VERIFIED**, Romary and Zupan, Geom. Dedicata
(2024), DOI 10.1007/s10711-024-00891-6, introduction:

> An R-link is an $n$-component link $L$ in $S^3$ such that Dehn surgery on $L$ yields $\#^n(S^1 \times
> S^2)$. Every R-link $L$ gives rise to a geometrically simply-connected homotopy 4-sphere $X_L$, which in
> turn can be used to produce a balanced presentation of the trivial group. ... the family
> $L(3,2;2n/(2n+1))$ induces the infamous trivial group presentation $\langle x,y \mid xyx = yxy,
> x^{n+1} = y^n\rangle$, a popular collection of potential counterexamples to the Andrews-Curtis
> conjecture for $n \ge 3$. ... The presentations $P_n$ are not known to be AC-trivial for $n \ge 3$, and
> they are widely believed to be probable counterexamples to the Andrews-Curtis conjecture.

Their Theorem 1.2 says that every presentation $P(3,2;4/d)$ is AC-trivial, which is proved with trisections
of the associated 4-manifolds. Related work that I did not read is credited to Gompf, Scharlemann and
Thompson, and to Meier and Zupan. The methodological point for us is that the AC trivializations come from
4-manifold geometry, and the direction of the information flow is from a standard 4-manifold to an AC
trivialization. It is not from an exotic 4-manifold to a failure of AC.

### 6.6 What kind of counterexample would matter for smooth 4-manifolds

Collecting the verified pieces, the answer is the following, and it is worth stating slowly because it is
the point of this direction.

1. An AC counterexample is a balanced presentation $P$ of the trivial group that is not Q-equivalent to
   the standard presentation. A counterexample to the weak version is a balanced presentation of the
   trivial group that is not $Q^{**}$-equivalent to the standard one, and that is the same thing as a
   contractible finite 2-complex that does not 3-deform to a point. **VERIFIED** for both formulations,
   from Barmak's introduction and Quinn's Definition 1.7. The $Q^{**}$ version is the weaker of the two
   conjectures, because Q-equivalence implies $Q^{**}$-equivalence, so a counterexample to the
   $Q^{**}$ version would refute the Q version as well.
2. To matter for a smooth 4-manifold, the presentation has to be the attaching data of a 2-handlebody $W$,
   by the dictionary of section 6.1, and one needs an independent proof that $W$ is not diffeomorphic to
   the standard manifold of the same homeomorphism type. **ARGUMENT.**
3. The independent proof in step 2 is the hard part, and for the natural $W$ it is a counterexample to
   the smooth 4-dimensional Poincare conjecture. If $W$ is built from one 0-handle, $n$ 1-handles, $n$
   2-handles and one 4-handle with $\partial W$ simply connected, then $W$ is contractible and
   Freedman's theorem gives $W \cong B^4$ topologically. A smooth $W$ that is not diffeomorphic to $B^4$
   is a counterexample to the smooth 4-dimensional Poincare conjecture in the contractible case, so no
   failure of AC can produce one without that separate theorem. **ARGUMENT**, with the topological input
   from Freedman's theorem as used in the Akbulut-Kirby paper.
4. Quinn says explicitly that a false AC would have no direct manifold consequences. **VERIFIED**,
   arXiv:hep-th/9202044, section 1: "If it is false as expected there do not seem to be direct
   consequences for manifolds. In this case its greatest attraction may be as a model problem for
   invariants of smooth 4-manifolds".

So the phrase "a counterexample of a certain kind could lead toward an exotic smooth 4-sphere" has to be
read as a statement about a counterexample that comes with its own 4-manifold theorem. The kind that
would matter is a balanced presentation $P$ of the trivial group together with a pair of 4-manifolds
built from $P$ that are homeomorphic and not diffeomorphic, or a single 4-manifold built from $P$ with a
non-standard smooth structure established independently of the AC status of $P$. No such pair is known.
The Akbulut-Kirby example was the closest thing to it, and Gompf removed the manifold side of the pair
while leaving the group side open. **ARGUMENT**, from the sources quoted in 6.2 to 6.4.

## 7. The computation

The script `survey/topology_check.py` uses only the python standard library. From the repository root the
exact command is

```
python3 survey/topology_check.py
```

The key output lines are the following.

```
  AK(3) = <x,y | xyx=yxy, x^3=y^4>: matrix=[[1, -1], [3, -4]] det=-1 Smith diagonal=[1, 1]
  Akbulut-Kirby 1985 = <x,y | xyx=yxy, x^5=y^4>: matrix=[[1, -1], [5, -4]] det=1 Smith diagonal=[1, 1]
  Gersten case = <x,y | xyx=yxy, x^2=y^3>: matrix=[[1, -1], [2, -3]] det=-1 Smith diagonal=[1, 1]
  PASS: det = m - n, so the abelianisation is trivial exactly when m = n +- 1
  PASS: chi = 1 - 2 + 2 = 1 and b_0 = 1, b_1 = 0 give b_2 = 0, so the complex is acyclic
  PASS: Smith diagonal is (1,1) in both cases, so the relator images generate Z^2
  AK(4) with x,y swapped has the same normal closures as the family member with exponents (5,4)
  PASS: the two indexing conventions differ by a relabelling of the generators
  ALL CHECKS PASSED
```

What this buys is a negative result of the kind section 3 predicts. The exponent-sum matrix itself is not
invariant, since move (2) sends row $i$ to row $i$ plus row $j$, and move (1) changes the sign of a row.
What the moves preserve is the subgroup of $\mathbb{Z}^n$ generated by the rows, and on the class of
balanced presentations of the trivial group that subgroup is forced to be all of $\mathbb{Z}^n$, so the
Smith normal form is $(1,\dots,1)$ for every member of the class. The check confirms that the three named
presentations are indistinguishable by this invariant, as they must be. It follows that an invariant able
to separate would have to see more than the abelian data of the 2-complex, which is the content of
sections 3.2 and 3.4.

## 8. Provenance: what I actually looked at

Each entry records the source, its identifier, and what I read. Entries marked as not read are listed
so that a reader can see exactly which claims rest on a secondary source. The eight DOIs cited in this
file were each resolved through doi.org with the request header `Accept:
application/vnd.citationstyles.csl+json`, and in every case the returned Crossref record matched the
title, the authors, the journal, the volume and the pages stated here. One small discrepancy is worth
recording: the Crossref record for Zeeman's paper gives the issue year 1963 and the volume Topology 2,
and the customary citation year is 1964.

* Andrews and Curtis, *Free groups and handlebodies*, Proc. Amer. Math. Soc. 16 (1965) 192-195, DOI
  10.1090/S0002-9939-1965-0173241-8. I saw the article's opening and its Theorem 2 in a search-engine
  text extraction of the AMS page, not the printed page, and the quotation in section 6.1 is from that
  extraction. The opening of the paper, in the same extraction, reads: "The conjecture seems to be a
  natural extension of a theorem of Nielsen, and the main topological consequence is the theorem that
  regular neighborhoods of contractible 2-dimensional subcomplexes of combinatorial 5-manifolds are
  S-cells", where the last word is OCR for 5-cells. So the extraction corroborates the topological
  consequence in its own words.
* Andrews and Curtis, *Extended Nielsen operations in free groups*, Amer. Math. Monthly 73 (1966) 21-28.
  Bibliographic data only, taken from Kupers' reference list. Not read.
* Akbulut and Kirby, Topology 24 (1985), DOI 10.1016/0040-9383(85)90010-2. The scanned PDF at the authors'
  pages is an image, and `pdftotext` returns nothing for it. The quotations in section 6.2 are from a
  search-engine OCR extraction of that scan.
* Gompf, Topology 30 (1991) 97-115, DOI 10.1016/0040-9383(91)90036-4. I read the zbMATH review, zbMATH
  0715.57016, and not the paper.
* Quinn, *Dual 2-complexes in 4-manifolds*, arXiv:math/0009234. I downloaded the PDF and read sections 1
  and 2.2.
* Quinn, *Representation theory, topological field theory, and the Andrews-Curtis conjecture*,
  arXiv:hep-th/9202044. I downloaded the PDF and read section 1 and the abstract.
* Barmak, Algebr. Geom. Topol. 25 (2025) 345-355, DOI 10.2140/agt.2025.25.345, and arXiv:1806.11493. I
  downloaded the published PDF and read the introduction and the statement of Theorem 5.
* Kupers, *Zeeman's conjecture*, Graduate J. Math. 6 (2021) 35-42. I downloaded the author's PDF and read
  sections 1 to 4 and the bibliography, which is the source of the bibliographic data for Dierker,
  Cohen, Gillman, Matveev, Matveev and Rolfsen, Wall and Wright.
* Matveev and Rolfsen, London Math. Soc. Lecture Note Ser. 197 (1993) 335-364, DOI
  10.1017/CBO9780511629358.013. I saw the opening paragraph of the chapter in a search-engine extraction
  of the publisher's page.
* Zeeman, Topology 2 (1964) 341-358, DOI 10.1016/0040-9383(63)90014-4. Bibliographic data verified through
  the publisher landing page and Wikidata. Not read.
* Romary and Zupan, Geom. Dedicata (2024), DOI 10.1007/s10711-024-00891-6, arXiv:2304.03196. I saw the
  introduction and Theorem 1.2 in the arXiv HTML version and the abstract.
* Fernandez, *Morse theory for group presentations*, Trans. Amer. Math. Soc. 377 (2024) 2495-2523, DOI
  10.1090/tran/8958, arXiv:1912.00115. I read the abstract page, which states the equivalence between
  $Q^{**}$-transformations and 3-deformations of 2-complexes, and I did not read the paper. It is a
  source of positive results: the abstract says the technique shows "that some known potential
  counterexamples to the Andrews-Curtis conjecture do satisfy the conjecture".
* Dynnikov, arXiv:2608.23331. I read only the abstract page. See the flag in section 5.3.

## 9. What I did not verify

* I did not read the printed pages of Akbulut and Kirby, of Gompf, of Zeeman, or of Matveev, and the
  quotations attributed to the first of these come from an OCR extraction.
* I did not read Matveev's 1987 paper in Russian, and the equivalence in its title is quoted from Kupers'
  bibliography and from the use made of it in section 5.3.
* I did not read Gillman and Rolfsen, Dierker, Cohen's two papers or Gillman's paper, so the statements in
  section 5.2 are verified as statements of Kupers' survey and not against the originals.
* I did not verify that any of the proposed invariants of 2-deformation classes is nonzero on a candidate,
  and I did not read the numerical work on Quinn's invariant.
* The relation between Zeeman's conjecture and the stable Andrews-Curtis conjecture asserted in the
  introduction of arXiv:2608.23331 is not verified, and I flagged in section 5.3 a point that needs care.
* I could not read Wright, Trans. Amer. Math. Soc. 208 (1975) 161-169, and the dictionary of sections 1
  to 3 is sourced from Quinn and Barmak instead.
* Nothing in this file bears on the truth of the Andrews-Curtis conjecture, and no claim of proof or
  disproof is made anywhere.

## 10. Traps for the next reader

* **Indexing of the Akbulut-Kirby family.** Romary and Zupan write $P_n = \langle x,y \mid xyx = yxy,
  x^{n+1} = y^n\rangle$, and Akbulut and Kirby's own 4-sphere presentation is $\langle x,y \mid xyx = yxy,
  x^5 = y^4\rangle$. Our problem writes $AK(n) = \langle x,y \mid xyx = yxy, x^n = y^{n+1}\rangle$. The two
  conventions differ by swapping $x$ and $y$, since $xyx = yxy$ is symmetric under the swap, and by a
  shift of index. In particular Akbulut and Kirby's presentation is our $AK(4)$, and the case called
  $P_3$ in the recent literature is our $AK(3)$. **CHECKED** in check 6 of section 7: after the swap the
  two relators are a cyclic permutation of the inverse of the relators of the other member of the family,
  which preserves normal closures and therefore the presented group.
* **Which version of AC is being discussed.** "AC-trivial" sometimes includes stabilization and sometimes
  does not. The problem's stable version is the (v) and (vi) moves of Barmak's list, while the literature's
  weak version is the full $Q^{**}$ relation, which also allows automorphisms of the free group.
* **2-deformation or 3-deformation.** Quinn's "2-deformation" is Matveev and Rolfsen's and Hog-Angeloni and
  Metzler's "3-deformation". The numbers count different things.
* **Direction of the 4-manifold implication.** AC-triviality of the attaching data implies standardness of
  the manifold. The converse is false as a general principle, and the Akbulut-Kirby and Gompf story is the
  counterexample to the hope that it holds.
* **"Contractible" is not "collapsible".** The dunce cap is contractible and not collapsible, and that gap
  is the whole subject.
