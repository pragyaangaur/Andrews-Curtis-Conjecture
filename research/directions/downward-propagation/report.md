# Direction G7: downward propagation

Round 4 deliverable for direction G7 of swarm smw2woueq, member m8. The brief asks:
if $K$ collapses to $L$ by an elementary 3-collapse and $L \times I$ is collapsible, is
$K \times I$ collapsible? It asks for a proof of that implication or for the exact
obstruction, and it records that a positive answer together with the stable
conjecture would give Zeeman's conjecture, while a failure with $L$ a 2-polyhedron
would refute Zeeman.

Labels. **Argument** means a proof written out here. **Computation** means an exact
deterministic program with the command recorded in Section 8. **Cited** means a
statement read in a named source, with the identifier recorded in Section 9.
Nothing here proves or disproves Zeeman's conjecture, the Andrews-Curtis
conjecture, or its stable form.

| file | contents |
| --- | --- |
| `report.md` | this report |
| `collapse.py` | exact simplicial collapsibility engine, deterministic, with an independent replay of every positive answer |
| `collapse_small.out` | recorded output: the sanity checks and the 2-dimensional cancellation example |
| `collapse_main.out` | recorded output: the dunce hat, the attached 3-cell, the suspension, the bounded product searches |
| `certify_dunce.py` | certificate for the 8-vertex dunce hat triangulation |
| `certify_dunce.out` | recorded output, including the GAP run that shows the edge path group is trivial |
| `dunce_gap.g` | the GAP input written by `certify_dunce.py` |

## 1. Outcome

1. The question of the brief has a positive answer and the answer is elementary:
   an elementary 3-collapse from $K$ to $L$ produces one elementary 4-collapse from
   $K \times I$ to $L \times I$, so $L \times I$ collapsible implies $K \times I$
   collapsible. This is the round-3 theorem, and I confirm it here with the
   corrected reading of the definition of elementary collapse (Section 3).
   [Argument]
2. The open statement that the brief is really asking about is the same collapse
   read backwards: $K \times I$ collapsible implies $L \times I$ collapsible. Round
   3 named it downward propagation and I keep the name. I do not settle it.
   [Argument]
3. New, and needed for anything else: for every polyhedron $L$, every ball
   $B = D^2 \subset L$ and $K = L \cup_B D^3$, the quotient $K/L$ is the quotient
   $D^3/B$, which is contractible, so $L \to K$ is a homotopy equivalence and
   $\chi(K) = \chi(L)$. Consequences: the hypothesis of downward propagation
   forces $L \simeq *$, so the hypothesis is never met by a non-contractible
   $L$; and the guess $K \simeq L \vee S^3$ is false, although it is the guess a
   cell count suggests. [Argument]
4. New: Zeeman's conjecture implies downward propagation in the 2-dimensional form
   of the brief. So a counterexample to the brief's statement cannot exist without
   a counterexample to Zeeman, and every case where positivity of $L$ is known
   decides the statement for that $L$ in the affirmative. Downward propagation is
   therefore a consequence of the conjecture and a sufficient condition for the
   reverse implication between Zeeman and stable Andrews-Curtis, and it has no
   independent life outside the cases where Zeeman is unknown. [Argument]
5. New: the general cancellation principle that a proof of downward propagation
   would have to use is false. The statement "if $X \cup_{B^{n-1}} D^n$ is
   collapsible then $X$ is collapsible" fails for $n = 2$ with $X = S^1$: attach a
   2-ball to a circle along an arc and the result is a disc, which is collapsible,
   while the circle is not. The computation records the explicit collapse
   sequence. So downward propagation cannot follow from the collapse axioms alone,
   and a proof has to use the product structure of $X = L \times I$. [Argument,
   Computation]
6. New: I reduce downward propagation to a single step. The 4-ball adds two cells
   to $X = L \times I$, namely the interior of the 4-cell and the interior of the
   complement 3-ball $c'$ inside the boundary sphere, whose boundary is the
   sphere $\partial B^3$. A collapse of $K \times I$ therefore either removes the
   4-cell paired with $c'$, and then it has collapsed $L \times I$ to a collapsible
   subcomplex and the base is positive, or it removes the 4-cell paired with a
   3-cell $c$ of $L \times I$ inside $B^3$, and then the ball $c'$ survives and the
   complex that must collapse is $((L \times I)_1 \setminus \mathrm{int}(c)) \cup c'$.
   So DP reduces to Lemma 6 and the key step KS of Section 6. That step is not a
   formality: attaching a 3-ball along a 2-sphere can destroy collapsibility, since
   $D^3 \cup_{\partial D^3} D^3$ is the 3-sphere. [Argument]
7. New computations. The 8-vertex, 17-triangle dunce hat triangulation is
   certified contractible (trivial edge path group by GAP, Euler characteristic 1)
   and it has no free pair, so no simplicial collapse step is available in that
   triangulation. The engine decides collapsibility exactly for small complexes and replays
   every positive answer from scratch. Product complexes resist the search at this
   size, and I report those runs as bounded, never as negatives. [Computation]
8. New: downward propagation is not vacuous, and its first instances are decided
   in the affirmative. Take $L$ the dunce hat and any disc $B \subset L$. Then
   $K = L \cup_B D^3$ has $K \times I \searrow L \times I$ by Lemma 3, and
   $L \times I$ is collapsible by Zeeman's theorem for the dunce hat, so
   $K \times I$ is collapsible and so is $L \times I$. So the hypothesis and the
   conclusion of DP both hold for a base that is not collapsible, and the
   statement has content. My simplicial searches on that product did not collapse
   it, which is an artefact of the triangulation and not a counterexample, exactly
   as Kupers' Rudin example warns. [Argument, Cited]

## 2. Definitions, and the reading of elementary collapse

The PL category, with the definitions of Kupers' survey, which the repository uses
in `survey/topology.md` and which round 3 quoted. [Cited: Kupers, Definition 1.1]

**Definition 1** (Kupers 1.1(i), quoted verbatim). There is an elementary collapse
from $K$ to $L$, written $K \searrow_e L$, if $L \subset K$ and there is a PL ball
$D^n \subset K$ such that $K = D^n \cup_{D^{n-1}} L$ where $D^{n-1} \subset \partial D^n$
and $D^{n-1} \subset L$ are subpolyhedra.

**Definition 2** (Kupers 1.1(ii), 1.1(iii)). $K \searrow L$ if there is a finite
sequence of elementary collapses from $K$ to $L$. $K$ is collapsible if
$K \searrow *$.

**Definition 3** (positive, Zeeman's conjecture). A polyhedron $K$ is positive if
$K \times I$ is collapsible. Zeeman's conjecture says that every contractible finite
2-polyhedron is positive. [Cited: Kupers, Conjecture 2.1 and the survey]

Two readings of Definition 1 are in use and they agree, and the agreement matters
for the bookkeeping in Section 3.

*Reading A, attachment.* $K$ is obtained from $L$ by gluing the ball $D^n$ along
the ball $D^{n-1} \subset \partial D^n$, which is already part of $L$. The cells
that appear are the interior of $D^n$ and the interior of $\partial D^n \setminus
D^{n-1}$, which is a ball of dimension $n-1$. So an elementary expansion adds one
open cell in dimension $n$ and one in dimension $n-1$, and an elementary collapse
removes those two.

*Reading B, free face.* $K = L' \cup e \cup f$ with $e$ an open $n$-cell, $f$ an
open $(n-1)$-cell contained in the closure of $e$, $f$ not in $L'$, and no other
cell of $K$ having $f$ in its closure. The free face is $f$. Reading B is Reading A
with $L' = L$ and with $f$ the closure of $\partial D^n \setminus D^{n-1}$, that is,
the free face is the complement of the attaching ball in the boundary sphere.

I record the equivalence because the phrase "$D^{n-1} \subset L$" in Definition 1
invites the opposite identification, and the mistake is easy to make in the product
lemma of Section 4. An elementary collapse removes two cells in consecutive
dimensions, so it preserves the Euler characteristic. [Argument]

## 3. What an elementary 3-collapse does to the quotient

**Lemma 1.** Let $L$ be a finite polyhedron, let $B = D^2 \subset L$ be a disc, and
let $K = L \cup_B D^3$. Then $K/L \cong D^3/B$, this quotient is contractible,
$L \to K$ is a homotopy equivalence, and $\chi(K) = \chi(L)$.

*Proof.* $K$ is the pushout of $L \hookleftarrow B \hookrightarrow D^3$, so $K/L$ is
the pushout of a point $\leftarrow B \hookrightarrow D^3$, that is, the quotient
$D^3/B$. The inclusion $B \hookrightarrow D^3$ is a homotopy equivalence of
contractible spaces and a cofibration, so its cofiber $D^3/B$ is contractible, and
the cofiber of $L \to K$ is $K/L$, so $L \to K$ is a homotopy equivalence by the
long exact sequence of the cofiber. For the Euler characteristic, additivity over
the cofibration gives $\chi(K) = \chi(L) + \chi(K/L) - \chi(*) = \chi(L)$ since
$\chi(D^3/B) = 1$. $\square$

The trap is worth recording because I fell into it. A cell count can suggest that
$K$ is $L$ with a 3-cell attached along its whole boundary, which would give
$K \simeq L \vee S^3$ and $\chi(K) = \chi(L) + 1$. That is wrong: the ball $B$ is
attached along a disc, so the boundary sphere of the 3-cell is not glued anywhere,
and the quotient is a ball rather than a sphere. The two statements differ by
exactly the Euler characteristic, and the correct one is $\chi(K) = \chi(L)$.
[Argument]

**Corollary 2.** Downward propagation is a statement about contractible bases. If
$K \times I$ is collapsible then $K \simeq *$, hence $L \simeq *$ by Lemma 1, and
$L \times I \simeq *$. So the hypothesis of the brief's question already implies
that $L$ is contractible, with no appeal to the fact that $L$ is 2-dimensional.

*Proof.* $K \times I$ and $K$ are homotopy equivalent, so collapsibility of the
product makes $K$ contractible. Lemma 1 gives $L \simeq K$. $\square$

Corollary 2 sharpens part (b) of round 3's Proposition 7. Round 3 argued that a
counterexample with $L$ a 2-polyhedron would refute Zeeman by observing that $L$
would be a contractible 2-polyhedron with non-collapsible product; the observation
needs the homotopy equivalence $L \simeq K$, which Lemma 1 supplies.

## 4. The product shape, and the direction that is proved

**Lemma 3** (the product of an elementary 3-collapse, round-3 Theorem 1 with
$n = 3$). With $L$, $B$, $K$ as in Lemma 1,
$$K \times I = (L \times I) \cup_{B \times I} (D^3 \times I),$$
where $D^3 \times I$ is a 4-ball and $B \times I$ is a 3-ball in its boundary.
Hence $K \times I \searrow_e L \times I$, and $L$ positive implies $K$ positive.
[Argument; the same step is in Kupers' proof of Lemma 2.2, Cited]

*Proof.* Crossing the pushout with $I$ gives the displayed identity. The product
$D^3 \times I$ is a 4-ball, the product $B \times I = D^2 \times I$ is a 3-ball
inside its boundary, and the intersection of the two sides of the union is exactly
$B \times I$. Definition 1 with $n = 4$ applies. $\square$

So the brief's question has two halves. The half in the brief is Lemma 3 and is
true. The other half is:

**Downward propagation, DP.** Let $L$ be a finite polyhedron, $B = D^2 \subset L$ a
disc, $K = L \cup_B D^3$. If $K \times I$ is collapsible then $L \times I$ is
collapsible.

**Lemma 4.** Zeeman's conjecture implies DP for every 2-polyhedron $L$.

*Proof.* Assume Zeeman's conjecture. Let $L$ be a 2-polyhedron and suppose $K \times I$
collapsible. Corollary 2 gives $L \simeq *$, so $L$ is a contractible 2-polyhedron,
and Zeeman's conjecture gives that $L \times I$ is collapsible. $\square$

Lemma 4 has three consequences, and they are the reason I think DP should be
recorded as a form of Zeeman rather than as a separate problem.

* DP is decided, in the affirmative, for every $L$ whose positivity is known:
  collapsible $L$, the dunce hat, and Bing's house. [Cited for the last two:
  Kupers Example 2.3]
* A failure of DP with $L$ a 2-polyhedron is a failure of Zeeman, by Corollary 2.
  So DP cannot be refuted in any way that leaves Zeeman standing.
* DP is not refuted by $\neg$Zeeman either. If $L \times I$ is not collapsible, DP
  for that $L$ says precisely that no 3-expansion of $L$ has collapsible product,
  which is a statement about a fourth-dimensional complex and is open.

The last point is where DP is weaker than Zeeman, and the gap is the existence
question: does every contractible 2-polyhedron admit a disc $B$ for which
$(L \cup_B D^3) \times I$ is collapsible? I do not know the answer, and a positive
answer plus DP would give Zeeman by Lemma 4 read backwards.

**DP is not vacuous.** Let $L$ be the dunce hat, which is contractible and not
collapsible, and let $B \subset L$ be any disc. Then $L \times I$ is collapsible
by Zeeman's theorem for the dunce hat, and Lemma 3 gives
$(L \cup_B D^3) \times I \searrow L \times I$, so the hypothesis of DP and its
conclusion both hold for this base. The same argument applies to Bing's house.
[Argument, Cited: Kupers Example 2.3] So DP has instances with a non-collapsible
base, and it is satisfied in all of them. What the argument uses is positivity of
$L$, which is exactly the part of Zeeman that is known for these two examples, and
that is the sense in which I say in Section 7 that DP carries no information beyond
Zeeman on these cases. This is the precise
sense in which the brief's sentence "a positive answer plus the stable conjecture
gives Zeeman's conjecture" needs care: DP plus an existence theorem gives Zeeman,
and round 3's route through the stable conjecture uses DP step by step along a
3-deformation, which needs DP in dimensions at most 3 and not only in dimension 2.

## 5. The cancellation principle is false in dimension 2

**Lemma 5.** The statement "if $X \cup_{B^{n-1}} D^n$ is collapsible then $X$ is
collapsible" is false for $n = 2$.

*Proof and computation.* Let $X = S^1$ and let $B = D^1 \subset S^1$ be an arc.
Then $X \cup_B D^2 \cong D^2$, which is collapsible, and $X$ is not collapsible
because no edge of a simplicial circle has a free endpoint and no vertex is a free
facet of an edge. The engine records both verdicts, with the three step collapse
sequence of the disc replayed from scratch. See `collapse_small.out`, target
`cancel2`. $\square$

Lemma 5 is the exact obstruction to the naive proof. The proof of DP that one
would like to write is "collapse $K \times I$ to a point; the 4-cell is removed at
some stage; before that stage the collapses are collapses of $L \times I$; after
that stage the collapses are collapses of $L \times I$ with one open 3-cell
deleted; therefore $L \times I$ collapses". Lemma 5 shows that this shape of
argument is invalid: a collapsible complex that contains a non-collapsible
subcomplex of one dimension less is exactly what $S^1 \subset D^2$ is, and the
product $K \times I$ is of that form with $L \times I$ playing the role of $X$.

The reason that $S^1 \subset D^2$ is not a counterexample to DP is Corollary 2:
the hypothesis of DP forces $L$ to be contractible, and $S^1$ is not. So a
counterexample, if there is one, has to be built out of a contractible
non-positive 2-polyhedron, which is a Zeeman counterexample. I record this as the
exact sense in which DP sits between Zeeman and nothing: it is implied by Zeeman,
all of its refutations are refutations of Zeeman, and its content lives exactly on
the cases that Zeeman does not decide.

## 6. Where a proof has to work: the two cells that the 4-ball adds

This section reduces DP to one statement. The reduction needs the correct cell
count of the expansion, and the correction is the substance of the section: a
4-ball attached to a polyhedron along a 3-ball in its boundary adds **two** cells,
not one. The cells are the interior of $D^4$ and the interior of the complement
ball $c' = \mathrm{cl}(\partial D^4 \setminus B^3)$, whose boundary is the
2-sphere $\partial B^3$, a union of cells of $X$. So
$$Y = X \cup \mathrm{int}(D^4) \cup \mathrm{int}(c'),$$
and the elementary collapse $Y \searrow_e X$ of Lemma 3 read in this cell structure
is exactly the free pair $(D^4, c')$. [Argument]

**Lemma 6.** Let $X$ be a finite polyhedron, $B^3 \subset X$ a 3-ball, and
$Y = X \cup_{B^3} D^4$. Suppose $Y \searrow *$. Then there is a subpolyhedron
$X_1 \subset X$ with $X \searrow X_1$, and the collapse is of exactly one of two
kinds.

(a) *The harmless case.* The interior of $D^4$ is removed paired with $c'$. The
complex that remains is $X_1$, and the rest of the sequence gives $X_1 \searrow *$.
So $X \searrow X_1 \searrow *$ and $X$ is collapsible.

(b) *The case a proof of DP must handle.* The interior of $D^4$ is removed paired
with a 3-cell $c$ of $X_1 \cap B^3$. The complex that remains is
$$Z = (X_1 \setminus \mathrm{int}(c)) \cup c',$$
the ball $c'$ surviving the removal, and the rest of the sequence gives
$Z \searrow *$.

*Proof.* In $Y$ the only cells that are not cells of $X$ are $\mathrm{int}(D^4)$
and $\mathrm{int}(c')$. While the interior of $D^4$ is present, $c'$ is a facet of
it, so $c'$ is not maximal and no free pair has $c'$ as its coface. The cell $c'$
has no coface other than $D^4$, so it cannot be removed except as the free facet of
a pair whose coface is $D^4$. Hence every pair removed before the interior of $D^4$
has both cells in $X$, and since a pair that is free in $Y$ is free in $X$ when
both its cells lie in $X$, those steps are elementary collapses of $X$. They give
$X \searrow X_1$ with $X_1$ the complex present when the 4-cell is removed. The
facets of $D^4$ that are cells of $Y$ are $c'$ together with the 3-cells of $B^3$,
so the pairing is with $c'$ or with a 3-cell $c \subset B^3 \cap X_1$. Removing the
pair $(D^4, c')$ deletes the interiors of both and leaves $X_1$, because the
boundary cells of $c'$ are cells of $X$. Removing $(D^4, c)$ deletes the interiors
of both and leaves $(X_1 \setminus \mathrm{int}(c)) \cup c'$, because $c'$ is still
present and its boundary cells are cells of $X$. The rest of the collapse sequence
collapses whichever complex remains to a point. $\square$

So DP follows from the following statement about the product situation. Let
$X = L \times I$, $B^3 = B^2 \times I$, and let $X_1 \subset X$ be a subpolyhedron
with $X \searrow X_1$; let $c$ be a 3-cell of $X_1 \cap B^3$ and $c'$ the complement
ball. Then

**Key step (KS).** $Z = (X_1 \setminus \mathrm{int}(c)) \cup c' \searrow *$ implies
$X_1 \searrow *$.

By Lemma 6, KS for every $X_1$ and $c$ gives DP: a collapse of $K \times I$ either
ends in case (a), where $X$ has already been collapsed, or in case (b), where KS
supplies $X_1 \searrow *$ and hence $X \searrow X_1 \searrow *$. A counterexample to
DP would be a collapse whose case (b) data violate KS with $X$ not collapsible, so
KS is the statement that a proof has to establish. I do not know whether KS is
strictly stronger than DP, because the collapses $X \searrow X_1$ have to be
realizable inside $Y$, and there the 2-cells of $\partial B^3$ have the extra coface
$c'$ and are harder to remove than in $X$. I have no proof of KS and no
counterexample to it. The rest of this section records what makes KS hard.
[Argument]

**Lemma 7.** Attaching a 3-ball along a 2-sphere to a collapsible polyhedron need
not preserve collapsibility, and the ball $c'$ in KS is removable only when
$\partial B^3$ has a free 2-cell at the moment of its removal. Example:
$Z_0 = D^3$ with a 3-ball attached along $\partial D^3$ is the 3-sphere, which is
not collapsible, although $Z_0$ is collapsible. [Cited for the last fact: Kupers
Theorem 1.6, which records that a collapsible PL manifold is a ball]

COORDINATOR NOTE, 2026-11-05, at acceptance: the last sentence of the example
contradicts itself as written ("the 3-sphere, which is not collapsible, although
$Z_0$ is collapsible"). The intended and correct reading, which the referee
verified and which matches this lemma's use in Section 6, is: the base ball
$D^3 = X_1 \setminus \mathrm{int}(c)$ is collapsible, while the attached complex
$Z_0 = D^3 \cup_{\partial D^3} D^3 = S^3$ is not, by Kupers Theorem 1.6. The
example's mathematical content is unaffected.

Two consequences of Lemma 7. First, the hypothesis of KS is a strong condition on
how $\partial B^3$ sits inside $X_1$, and it cannot be checked from the cell count.
Second, the ball $c'$ is not a nuisance that can be discarded: in case (b) the
collapse of $Z$ has to remove $c'$ at some later stage, and it can do so only by
pairing it with a 2-cell of $\partial B^3$ that is free in the complex present at
that moment. So a proof of KS has to produce such a free 2-cell, or else produce a
different collapse of $X_1$, out of the product structure.

**Remark on where the product structure enters.** In the product situation the
attaching sphere is $\partial B^3 = \partial B^2 \times I \cup B^2 \times \partial I$,
and the part $B^2 \times \partial I$ lies in $\partial X = \partial L \times I \cup
L \times \partial I$, because $B^2 \subset L$ and $\partial I = \{0, 1\}$. So one
half of the attaching sphere of $c'$ sits on the boundary of $X$. That is the only
structural feature of the product that I can see being of use for KS, and I do not
have an argument that uses it. [Argument, open]

**Remark on the round-3 computation.** Lemma 6 also shows why the computation in
Section 5 of the round-3 report finds that the naive product cell structure does not
admit the collapse. The elementary 4-collapse of Lemma 3 uses the ball $D^3 \times I$
and the boundary ball $B^2 \times I$, that is, it uses the pair $(D^4, c')$ of case
(a) with $c'$ taken to be the closed complement ball, and in the product cell
structure the corresponding set of cells is not a single ball pair. My engine
reproduces this phenomenon in the simplicial category: the standard prism
triangulation of the dunce hat's product has 51 tetrahedra and the seeded search
does not collapse it (Section 8), while the same triangulation of a disc's product
collapses in 25 steps. Kupers records the general fact: a collapsible polyhedron can
have a triangulation that is not simplicially collapsible, with Rudin's
triangulation of the 3-ball as the example. [Cited: Kupers Example 1.2] So
simplicial verdicts on one triangulation are not verdicts about the polyhedron, and
I use them only as statements about the triangulation.

## 7. What this means for the campaign

1. The brief's question, read as it is written, is answered in the affirmative by
   Lemma 3, and round 3's proof of it is correct once the free face is identified
   with the complement of the attaching ball. [Argument]
2. The open statement is DP, and DP is a consequence of Zeeman by Lemma 4. It is
   not a route around Zeeman: it is a form of it. Recording DP as an open problem
   between the two conjectures is right, and recording it as the missing step of
   the reverse implication is also right, but the campaign should not expect a
   proof of DP that does not use whatever proves Zeeman for the unknown cases.
   [Argument]
3. The exact obstruction, in the form the brief asks for, is Lemma 5 together with
   the correction of Lemma 6: the cancellation step that a proof of DP needs fails
   in dimension 2 for an arbitrary base, and in the product setting the collapse
   reduces either to the harmless case (a), where it has already collapsed
   $L \times I$, or to case (b), where the complement ball $c'$ survives and the
   key step KS has to be verified. Lemma 7 shows that KS is not a formality,
   because a ball attached along a sphere can destroy collapsibility. [Argument,
   Computation]
4. What would refute what: a collapsible $K \times I$ with $L \times I$ not
   collapsible refutes DP and Zeeman at once (Corollary 2 and Lemma 4); a
   contractible 2-polyhedron with non-collapsible product refutes Zeeman and leaves
   DP possibly true; and no computation of the kind I ran can separate these, since
   both are statements about 4-dimensional collapsibility. [Argument]
5. One sub-question is worth putting on the list because it is what the brief's
   sentence actually needs: is there, for every contractible finite 2-polyhedron
   $L$, a disc $B \subset L$ such that $(L \cup_B D^3) \times I$ is collapsible? A
   positive answer together with DP would give Zeeman's conjecture. I do not know
   the answer, and I did not find one. [Argument, open]

## 8. Computations

The engine is `collapse.py`, python3 standard library only, deterministic. A
complex is given by its maximal simplices; the state of a search is a down closed
set of simplices. A free pair is a pair $(\sigma, \tau)$ with $\sigma$ maximal,
$\tau$ a facet of $\sigma$, and $\tau$ a facet of no other simplex, which is the
standard criterion for simplicial collapse. Every positive answer is replayed by a
separate function that rechecks each step from the original complex, and the replay
must end at a single vertex. Negative answers are exhaustive over all free pair
removals, so they are proofs about the given complex. Bounded runs print
`UNDECIDED` or `no sequence found inside the budget`, never a negative.

The commands, from this directory:

```
python3 certify_dunce.py && gap -q dunce_gap.g      # certificate for the dunce hat
python3 collapse.py small                          # sanity checks
python3 collapse.py cancel2                        # the dimension 2 cancellation example
python3 collapse.py sphere                         # 3-ball and 3-sphere
python3 collapse.py dunce                          # dunce hat, 3-cell, product
python3 collapse.py susp                           # suspension of the dunce hat
python3 collapse.py greedy                         # seeded greedy searches, bounded
```

Recorded output. `certify_dunce.out`:

```
1. triangles distinct: True (17 triangles)
2. vertices 8, edges 24, triangles 17, f-vector (8,24,17)
   edge degrees: 1:0 2:21 3:3 ; mixed degrees absent: True
3. Euler characteristic 1 (contractible needs 1): True
4. spanning tree edges 7, generators 17
generators 17 relators 17
abelian invariants [  ]
order 1
```

Let me say what this certifies. The 17 triangles are the list printed by Hachimori's
library and by Macaulay2's `dunceHatComplex`, and the two lists agree entry by
entry. Vertices 8, edges 24, triangles 17, every edge in two or three triangles,
Euler characteristic 1. The edge path group presentation computed from the
triangulation has 17 generators and 17 relators and GAP reports order 1, so the
complex is simply connected. Its first homology vanishes, and its second homology
is free because it is a subgroup of the free group of 2-chains, so the Euler
characteristic 1 forces the second Betti number to vanish as well. Hence every
reduced homology group vanishes, the complex is a homology point, and by Hurewicz
and Whitehead it is contractible. No edge lies in exactly one triangle, so the
triangulation has no free pair and admits no simplicial collapse step at all. The
non-collapsibility of the polyhedron itself is Kupers' Example 1.5, which proves it
through the links of the points, and my computation is the simplicial counterpart
of the sentence "there is no free face to get started". Together these give a
self-contained certificate that the complex I compute with is a contractible
non-collapsible 2-complex with the stated triangle list. [Computation, Cited]

Recorded output, `collapse_small.out`:

```
point                                f=[1]                  free pairs=  0  COLLAPSIBLE (0 steps, 1 states, replay ok)
interval                             f=[2, 1]               free pairs=  2  COLLAPSIBLE (1 steps, 2 states, replay ok)
circle                               f=[3, 3]               free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
disc (two triangles)                 f=[4, 5, 2]            free pairs=  4  COLLAPSIBLE (5 steps, 6 states, replay ok)
2-sphere                             f=[4, 6, 4]            free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
3-ball (tetrahedron)                 f=[4, 6, 4, 1]         free pairs=  4  COLLAPSIBLE (7 steps, 8 states, replay ok)
disc x I                             f=[8, 19, 18, 6]       free pairs= 12  COLLAPSIBLE (25 steps, 26 states, replay ok)
X = circle                           f=[3, 3]               free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
Y = X u_arc D^2 (a disc)             f=[3, 3, 1]            free pairs=  3  COLLAPSIBLE (3 steps, 4 states, replay ok)
3-ball (5 tets minus one)            f=[5, 10, 10, 4]       free pairs=  4  COLLAPSIBLE (14 steps, 15 states, replay ok)
3-sphere boundary                    f=[5, 10, 10, 5]       free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
```

The last two lines are the check that the engine does not confuse a ball with a
sphere, and the two lines before them are Lemma 5 with the collapse sequence
replayed. [Computation]

Recorded output, `collapse_main.out`:

```
dunce hat                            f=[8, 24, 17]          free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
   edge degrees: 1:0 2:21 3:3 ; interior triangles: 8
   attaching D^3 along the interior triangle (1, 5, 6)
K = D u_disc D^3                     f=[9, 27, 20, 1]       free pairs=  4  NOT COLLAPSIBLE (20 states, exhaustive)
K x I                                f=[18, 90, 134, 65, 4] free pairs= 46  UNDECIDED (budget 400000)
susp(dunce hat)                      f=[10, 40, 65, 34]     free pairs=  0  NOT COLLAPSIBLE (1 states, exhaustive)
Y = X u_tet D^4                      f=[11, 44, 71, 38, 1]  free pairs=  5  NOT COLLAPSIBLE (178 states, exhaustive)
dunce hat x I                        f=[16, 80, 116, 51]    greedy: no sequence found inside the budget
K x I                                f=[18, 90, 134, 65, 4] greedy: no sequence found inside the budget
```

These are the runs that matter for the topological discussion and they are
reported honestly as bounded or as statements about the triangulation.

* The dunce hat triangulation has no free pair, so no simplicial collapse step is
  available in it. Together with the certificate above this is a machine checked
  instance of a contractible complex with no free face, which is the combinatorial
  content of the dunce hat's non-collapsibility. [Computation, Cited]
* Attaching a 3-ball along an interior triangle gives a 3-complex with 9 vertices
  and one tetrahedron, and the exhaustive search finds no collapse in 20 states.
  This is a statement about that simplicial complex. Its interest is that the
  expanded complex is not collapsible, which is what Lemma 5 says can happen in
  reverse. [Computation]
* The suspension of the dunce hat has 34 tetrahedra, no free pair, and no collapse.
  Attaching a 4-simplex along an interior tetrahedron leaves a complex with no
  collapse in 178 states. So I did not find, by this route, a 3-dimensional example
  of a collapsible complex whose collapse requires the 4-cell, which is what a
  counterexample to the general form of DP would need. [Computation]
* The product runs are bounded. The prism triangulation of the dunce hat's product
  has 51 tetrahedra; the exhaustive search exceeded a budget of 400000 states and
  the seeded greedy search found no sequence in 40 attempts with a deterministic
  seed. Neither outcome is a negative, and by Kupers' Rudin example a specific
  triangulation can fail to be simplicially collapsible while the polyhedron is
  collapsible, so the only correct reading is that this triangulation was not
  collapsed by these searches. [Computation, and Cited for the Rudin phenomenon]

## 9. Sources

* A. Kupers, *Zeeman's conjecture*, Graduate Journal of Mathematics 6 (2021), no. 1,
  35-42. I downloaded the published PDF from
  `https://gradmath.org/wp-content/uploads/2021/07/GJM2021-Kupers.pdf` on
  2026-11-05 and extracted the text with `pdftotext`. Used: Definition 1.1(i) to
  (iii) quoted in Section 2; the sentence defining a simplicial collapse and
  quoting Whitehead's subdivision theorem; Example 1.2, Rudin's triangulation of
  the 3-disk which is not simplicially collapsible, used in Section 6; Example 1.5,
  the dunce cap as the 2-cell attached to a circle by the word $xxx^{-1}$, with the
  statements that it is contractible and not collapsible and that there is no free
  face to get started, used in Section 8; Theorem 1.6, a PL manifold is collapsible
  if and only if it is PL homeomorphic to a disk, used in Lemma 7; Conjecture 2.1
  and Lemma 2.2 with its proof, the step "if $L \searrow_e K$ and $L \searrow *$
  then $K \times I \searrow *$", used in Section 4; Example 2.3, the dunce cap and
  the house with two rooms become collapsible after taking the product with an
  interval, used in Lemma 4 and Section 7.
* The triangle list for the dunce hat: M. Hachimori's simplicial complex library,
  page `https://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/dunce_hat_eng.html`
  with data `https://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/dunce_hat.dat`,
  and the Macaulay2 documentation page for `dunceHatComplex`, which prints the same
  17 triangles in a different vertex labelling. Both were read on 2026-11-05, and
  the two lists agree entry by entry after relabelling. These are the two
  independent sources for the triangulation. [Cited]
* Naming. Kupers writes "dunce cap" and the triangulation libraries and the
  round-3 report write "dunce hat"; these names denote the same space, the quotient
  of a triangle with its three edges identified, which is the 2-cell attached to a
  circle by the word $xxx^{-1}$ in Kupers' Example 1.5.
* GAP 4.14 at `gap -q`, used for the order computation in Section 8. The input file
  is `dunce_gap.g`, written by the script, and the output is recorded.
  [Computation]
* Round 3's `directions/zeeman-positivity/zeeman-positivity.md`, read in full, for
  the dictionary, Proposition 7, Proposition 8 and the backward direction. My
  Lemma 1 fills the step that report's Proposition 7(b) asserts, and my Lemma 4 is
  the direction that report does not state. [Cited as a repository source]
* `survey/topology.md` and `survey/stable-ac.md` were not read by me in this round;
  the statements I use about the stable conjecture come from round 3's report,
  where they are labelled REPORTED or Cited. Nothing in Sections 3 to 6 uses them.

## 10. What I could not verify, and what remains uncertain

* I did not settle DP, in any dimension. Every statement of Section 1 that is a
  proof is about the implications between DP, Zeeman and the stable conjecture, and
  none of them decides the conjecture. The gap in my own reduction is the key step
  KS of Section 6, which I can neither prove nor refute, and an earlier version of
  Section 6 got the cell count of the expansion wrong by leaving out the complement
  ball $c'$; the correction is the content of that section.
* My computations decide collapsibility only for the specific simplicial complexes
  in Section 8 and only when the line says `exhaustive`. The product runs are
  bounded, and by Kupers' Example 1.2 (Rudin's triangulation of the 3-ball) a
  negative simplicial verdict would not be a negative PL verdict in any case. I did not
  attempt a subdivision, which is what a genuine PL certificate for a collapsible
  product would need.
* The claim that the hypothesis of DP is satisfiable for a non-collapsible $L$ is
  open as far as I know. If it is not satisfiable, DP is vacuous and says nothing
  about Zeeman; the campaign should not add DP to the list of statements that carry
  the reverse implication without the existence question of Section 7 item 5.
* I did not read Zeeman's paper, Matveev, Gillman and Rolfsen, or Wright. Every
  statement attributed to them is quoted from Kupers or from round 3's report, and
  the only facts I use from the literature are the collapsibility of the dunce
  hat's product with $I$ and the non-collapsibility of the dunce hat, both of which
  are in Kupers' Examples 1.5 and 2.3.
* The GAP computation checks the edge path group. It does not check higher homotopy.
  Contractibility follows from trivial fundamental group together with Euler
  characteristic 1 in a 2-complex, and that inference is written out in Section 8
  rather than machine checked.

## ROUND 5 NOTES, 2026-11-05, direction H6 (member m9, swarm smw38010i)

First note, withdrawn the same day. `keystep.md` in this directory first claimed that
the Key Step of Section 6 is equivalent to downward propagation. That claim used the
inference that a collapse image of a collapsible complex is collapsible, which is
false, and the referee rejected it. The counterexample is recorded in round 3 of
`STATE.md` and in the round-3 correction of `directions/invariant-ideas/idea.md`: the
dunce hat is not collapsible, its product with $I$ is collapsible, and the product
collapses onto the dunce hat.

Corrected note. `keystep.md` now proves what does follow. Lemma D: a collapse of
$X=L\times I$ that keeps the sphere $\partial B^3$ removes no cell of $B^3$, so
$B^3\subset X_1$, which closes the question Section 6 left open about realising
$X\searrow X_1$ inside $Y$. Lemma E: the chain identity $[\partial B^3]=[\partial c]$
in $H_2(X_1\setminus\mathrm{int}\,c)$. Lemma F: if $Z\searrow *$ then the two 3-cell
attachments are homotopy equivalent and $X_1$ is contractible. Proposition 1: a
failure of the Key Step therefore gives a contractible base $L$ with $K\times I$
collapsible, with $X_1$ a contractible non-collapsible collapse image of $L\times I$
containing the prism, so the Key Step sits between the hypothesis and the conclusion
of downward propagation. Proposition 4 localises the missing step: in any collapse of
$Z$ the cell $c'$ is removed paired with a 2-cell of $\partial B^3$, so what a proof
needs is a cancellation principle in dimension three, the analogue of Lemma 5 which
fails in dimension two. No counterexample to the Key Step was found over the dunce
hat base in 445 sampled collapse images. Files `ks_engine.py`, `ks_out.txt`,
`ks_dunce.py` and `ks_dunce.out` in this directory reproduce every check.
