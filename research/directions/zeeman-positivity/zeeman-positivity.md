# Direction F6: Zeeman positivity and the backward direction

Round 3 deliverable for direction F6 of swarm smw2opo0o, written by member m6. The
question was whether an elementary 3-collapse can destroy the collapsibility of a
product with the interval, and whether a positive answer makes Zeeman's conjecture
and the stable Andrews-Curtis conjecture the same statement.

| file | contents |
| --- | --- |
| `zeeman-positivity.md` | this report |
| `check_zeeman.py` | the self check, 23 checks, python3 standard library only |
| `check_zeeman.out` | recorded output of `python3 check_zeeman.py` |

Labels. **Argument** means a proof written out here. **Computation** means an exact
deterministic program with the command given in Section 8. **Cited** means a
statement taken from a named source, verified against a live record as recorded in
Section 9. Nothing in this file proves or disproves the Andrews-Curtis conjecture,
its stable form, or Zeeman's conjecture.

## 1. Outcome

1. The backward direction has a positive answer, and the answer is elementary. If
   $K$ collapses to $L$ by an elementary 3-collapse, then $K \times I$ collapses to
   $L \times I$ in one elementary collapse, because $K = L \cup_{D^2} D^3$ and
   crossing with $I$ gives
   $K \times I = (L \times I) \cup_{D^2 \times I} (D^3 \times I)$, where
   $D^3 \times I$ is a 4-ball and $D^2 \times I$ is a 3-ball in its boundary.
   Hence $L \times I$ collapsible implies $K \times I$ collapsible. [Argument]
2. The statement is the round-2 report's Lemma 7 with the two complexes renamed.
   An elementary 3-collapse from $K$ to $L$ is the same thing as an elementary
   3-expansion from $L$ to $K$, so the "open backward direction" of the report is
   not a second case. [Argument]
3. The proposed consequence does not follow. Positivity is monotone in the
   direction of elementary expansions, and a 3-deformation contains collapse steps
   that run in the opposite direction. Under the stable conjecture, Zeeman's
   conjecture is equivalent to the invariance of positivity under 3-deformations
   (Proposition 6), and the invariance is the missing statement. [Argument]
4. Because the answer is positive, no candidate $K$ of the kind the brief asked for
   exists. No counterexample to the opposite implication is available either: a
   counterexample to positivity passing from the expanded complex to the collapsed
   one would be a counterexample to Zeeman's conjecture (Proposition 7).
   [Argument]
5. Three items in the round-2 report need attention, and Section 6 records each of
   them. The example in Remark 8 does not work, because the Euler characteristic of
   the 3-complex it names is 1 while that of the 2-sphere is 2, and an elementary
   collapse preserves the Euler characteristic. The conclusion of Remark 8 is true,
   and the correct witness is the dunce cap, whose product with $I$ is collapsible
   by Zeeman's theorem while the dunce cap itself is not collapsible. The proof of
   Lemma 7 is correct for polyhedra, and the sentence that makes it correct is the
   one that identifies the new 4-cell with the ball $D^3 \times I$; the product cell
   structure suggests a sequence of three pair removals, and those are not
   elementary collapses of that structure (Section 5, Computation).
   [Argument, Computation, Cited]
6. The downward implication is true for every collapsible $L$, which re-proves the
   step Kupers uses to show that the dunce cap becomes collapsible after crossing
   with $I$. The open case is a contractible $L$ that is not collapsible
   (Proposition 8). [Argument, Cited]

The rest of the file fixes the definitions, proves the statements, records the
corrections, and lists what was checked and what could not be verified. Section 7
states what the direction recommends for the campaign record, and Section 10 lists
the points that remain open or unverified.

## 2. Definitions and conventions

The setting is the PL category, and the definitions are those of Kupers' survey,
which this repository already uses in `survey/topology.md` Section 4. The
definitions are reproduced in the form the proofs need, so that a reader can check
each step against a single source. [Cited]

A **polyhedron** is a topological space with a PL structure, and a **2-polyhedron**
is a polyhedron with no chart of dimension greater than 2. A **PL ball** $D^n$ is
the polyhedron of a standard simplex, and $S^{n-1} = \partial D^n$.

**Definition 1** (elementary collapse, Kupers Definition 1.1(i)). There is an
elementary collapse from $K$ to $L$, written $K \searrow_e L$, if $L \subset K$ and
there is a PL ball $D^n \subset K$ such that $K = D^n \cup_{D^{n-1}} L$, where
$D^{n-1} \subset \partial D^n$ and $D^{n-1} \subset L$ are subpolyhedra. In words,
$K$ is the union of $L$ and one ball, and the intersection of the two is a ball in
the boundary of the first. An **elementary expansion** is the same relation read
backwards.

**Definition 2** (collapse and collapsibility, Kupers Definition 1.1(ii) and (iii)).
$K$ collapses to $L$, written $K \searrow L$, if there is a finite sequence of
elementary collapses from $K$ to $L$. $K$ is **collapsible** if it collapses to a
point.

**Definition 3** (3-deformation, Quinn Definition 1.7, as quoted in
`survey/topology.md` Section 1.3). A 3-deformation is a finite sequence of
elementary expansions and elementary collapses, each involving cells of dimension at
most 3. Quinn calls this a 2-deformation and Hog-Angeloni and Metzler call it a
3-deformation, and this report uses the campaign's word. [Cited]

**Definition 4** (positivity). A polyhedron $K$ is **positive** if $K \times I$ is
collapsible. Zeeman's conjecture says that every contractible finite 2-polyhedron is
positive. [Cited]

**Definition 5** (stable Andrews-Curtis, topological form). The stable
Andrews-Curtis conjecture says that every finite contractible 2-polyhedron is a
3-deformation of a point. The equivalence of this form with the presentation form is
the Wright correspondence, recorded in `survey/stable-ac.md` Section 3 as a
literature claim. [Cited]

Two elementary facts are used repeatedly. An elementary collapse removes one open
cell in each of two consecutive dimensions, so it preserves the Euler
characteristic, and a collapse preserves homotopy type. Consequently a collapsible
polyhedron is contractible, and $\chi(K \times I) = \chi(K)$.

## 3. The product lemma and the answer to the question

**Theorem 1** (product lemma, both directions). Let $L$ be a finite polyhedron and
let $K = L \cup_{D^{n-1}} D^n$ be an elementary expansion of $L$. Then $K \times I$
collapses to $L \times I$ in one elementary collapse.

*Proof.* By Definition 1, $D^n \subset K$ is a ball, $D^{n-1} \subset \partial D^n$
and $D^{n-1} \subset L$, and $D^n \cap L = D^{n-1}$. Crossing with $I$ gives
$$K \times I = (D^n \times I) \cup_{D^{n-1} \times I} (L \times I).$$
The product $D^n \times I$ is a ball of dimension $n+1$. The product
$D^{n-1} \times I$ is a ball of dimension $n$, it lies in the boundary of
$D^n \times I$ because $D^{n-1}$ lies in the boundary of $D^n$, and it lies in
$L \times I$ because $D^{n-1}$ lies in $L$. The intersection of the two pieces is
exactly $D^{n-1} \times I$. So Definition 1 applies to the pair
$(D^n \times I, D^{n-1} \times I)$, and $K \times I \searrow_e L \times I$.
$\square$

**Corollary 2** (the backward direction asked about). Let $K = L \cup_{D^2} D^3$
be a finite polyhedron, so that $K$ collapses to $L$ by an elementary 3-collapse.
Then $K \times I$ collapses to $L \times I$. Consequently, if $L \times I$ is
collapsible then $K \times I$ is collapsible.

*Proof.* An elementary 3-collapse means $K = L \cup_{D^2} D^3$ with
$D^2 \subset \partial D^3$ and $D^2 \subset L$. Theorem 1 with $n = 3$ gives the
collapse, and a collapse of a collapsible polyhedron is collapsible. $\square$

**Corollary 3** (the same statement as the round-2 report's Lemma 7). If $K'$ is an
elementary 3-expansion of $K$, then $K' \times I \searrow K \times I$. This is
Theorem 1 with $L = K$ and $n = 3$. [Argument]

So the question of the brief and Lemma 7 of the round-2 report are the same
statement with the letters exchanged. There is no second case to settle, and the
answer is yes.

**Theorem 4** (a product with $I$ collapses back onto its base). For every finite
polyhedron $K$ there is a collapse $K \times I \searrow K \times \{0\}$.

*Proof.* Triangulate $K$. Take the prism decomposition of $K \times I$ whose cells
are $\sigma \times \{0\}$, $\sigma \times \{1\}$ and $\sigma \times I$ for the
simplices $\sigma$ of the triangulation. Process the simplices in order of
decreasing dimension. At the stage of $\sigma$, all cells $\tau \times I$ and
$\tau \times \{1\}$ with $\dim \tau > \dim \sigma$ have been removed. The cell
$\sigma \times \{1\}$ is then a face of no remaining cell except $\sigma \times I$,
and $\sigma \times I$ is a ball whose boundary is $\partial \sigma \times I$ together
with $\sigma \times \{0\}$ and $\sigma \times \{1\}$. Removing the open interiors of
$\sigma \times I$ and $\sigma \times \{1\}$ is an elementary collapse by Definition
1, with $D^n = \sigma \times I$ and $D^{n-1} = \partial(\sigma \times I)$ minus the
interior of $\sigma \times \{1\}$, which is a ball in the boundary of
$\sigma \times I$. After all simplices have been processed, the cells that remain
are the cells $\sigma \times \{0\}$, and their union is $K \times \{0\}$.
$\square$

**Corollary 5** (positivity implies 3-deformation triviality, so Zeeman implies
stable Andrews-Curtis). Every positive 2-polyhedron is a 3-deformation of a point.
Consequently Zeeman's conjecture implies the stable Andrews-Curtis conjecture.

*Proof.* Let $K$ be a positive 2-polyhedron. By Theorem 4 the product $K \times I$
collapses to $K \times \{0\}$, which is a copy of $K$. Since $K$ is 2-dimensional,
$K \times I$ is 3-dimensional, so the collapse of $K \times I$ onto $K \times \{0\}$
read backwards is a 3-deformation from $K$ to $K \times I$. Positivity says that
$K \times I$ collapses to a point, which is again a 3-deformation because
$K \times I$ is 3-dimensional. Composing the two gives a 3-deformation from $K$ to a
point. By Definition 5 this is the stable conjecture. $\square$

Corollary 5 is the one-line implication that Fagan's thesis states as Proposition
3.8, and the proof here is a written-out version of that one line. [Cited, and
Argument for the details] Nothing in Section 3 uses a presentation of a group, and
nothing in it depends on the Andrews-Curtis conjecture.

**Remark** (monotonicity, and where it stops). Corollary 2 says that positivity
passes from a polyhedron to its elementary expansions, so by induction it passes
from $L$ to every polyhedron obtained from $L$ by a sequence of elementary
expansions. It does not pass across an elementary collapse, that is, from an
expanded polyhedron to the one it was built from. Section 7 records the precise
form of the remaining gap: the reverse implication between the two conjectures
amounts to invariance of positivity under 3-deformations. [Argument]

## 4. What the answer does not give, and the exact obstruction

The round-2 report writes after Remark 8: "If it also propagated backwards across an
elementary 3-collapse, then Zeeman's conjecture would be equivalent to the stable
Andrews-Curtis conjecture on the contractible class, because stability would give
Zeeman positivity of every contractible $K$ from that of a point." The first half of
that sentence is now a theorem, and it is Lemma 7 itself. The second half does not
follow, and this section locates the failing step exactly.

**Proposition 6** (the equivalence needs invariance, not monotonicity). Assume the
stable Andrews-Curtis conjecture. Then Zeeman's conjecture is equivalent to the
following statement: any two contractible finite 2-polyhedra that are
3-deformation equivalent are both positive or both not positive.

*Proof.* If Zeeman's conjecture holds then every contractible 2-polyhedron is
positive, so the statement holds. Conversely, assume the statement and let $K$ be a
contractible finite 2-polyhedron. By the stable conjecture $K$ is
3-deformation equivalent to a point, and the point is positive because its product
with $I$ is an interval. So $K$ is positive by the statement. $\square$

**Proposition 7** (the missing implication, and why no counterexample is known).
Consider the following statement, called downward propagation: for every finite
polyhedron $L$ of dimension at most 3 and every elementary expansion
$K = L \cup_{D^{n-1}} D^n$ of $L$ with $n$ at most 3, if $K \times I$ is collapsible
then $L \times I$ is collapsible. Then four things hold.

(a) The proof of Theorem 1 does not give downward propagation. Theorem 1 gives
$K \times I \searrow L \times I$, and a collapse of a collapsible polyhedron onto a
subpolyhedron does not make the subpolyhedron collapsible. The dunce cap is the
witness, because $D \times I$ is collapsible, $D \times I$ collapses to $D$, and $D$
is not collapsible. [Argument, Cited]

(b) A counterexample to downward propagation with $L$ a 2-polyhedron would refute
Zeeman's conjecture. Suppose $K \times I$ is collapsible and $L \times I$ is not.
Then $K$ is contractible because it is homotopy equivalent to the collapsible
polyhedron $K \times I$, and $L$ is homotopy equivalent to $K$, so $L$ is a
contractible finite 2-polyhedron with non-collapsible product. [Argument]

(c) Downward propagation together with the stable conjecture implies Zeeman's
conjecture. Let $L$ be contractible and let $L = K_0, K_1, \dots, K_r = *$ be a
3-deformation from $L$ to a point, which exists by the stable conjecture. The point
is positive. Suppose $K_{i+1} \times I$ is collapsible. If $K_{i+1}$ is an
elementary expansion of $K_i$, then $K_i \times I$ is collapsible by downward
propagation. If $K_i$ is an elementary expansion of $K_{i+1}$, then
$K_i \times I \searrow K_{i+1} \times I$ by Theorem 1, so $K_i \times I$ is
collapsible. So positivity propagates from $i+1$ to $i$ in both cases, and induction
from $i = r$ down to $i = 0$ gives that $L \times I$ is collapsible. [Argument]

(d) Together with Corollary 5, part (c) shows that downward propagation is a
sufficient condition for the reverse implication, and so for the equivalence of the
two conjectures. It does not claim that downward propagation is necessary, and the
question whether it is necessary is not addressed here. [Argument]

**Proposition 8** (the collapsible case is not the problem). If $L$ is collapsible
then $L \times I$ is collapsible, and every polyhedron obtained from $L$ by
elementary expansions has collapsible product. Consequently downward propagation
holds for every collapsible $L$.

*Proof.* A sequence of elementary collapses from $L$ to a point gives, by Theorem 1
applied to each step, a sequence of collapses from $L \times I$ to
$* \times I = I$, and $I$ is collapsible. So $L \times I$ is collapsible. If $K$ is
an elementary expansion of $L$ then $K \times I \searrow L \times I$ by Theorem 1,
so $K \times I$ is collapsible. The statement of downward propagation is therefore
satisfied for a collapsible $L$, whatever $K$ is. $\square$

Proposition 8 is the claim that Kupers uses in the proof of his Lemma 2.2 and in
Example 2.3, where it shows that the dunce cap and Bing's house become collapsible
after crossing with $I$. [Cited] The proof here is an independent derivation from
Theorem 1, and it shows that the open case of downward propagation is a contractible
$L$ that is not collapsible, which is the class of the stable conjecture.

Part (b) is the reason the brief's request for an explicit $K$ where the 3-collapse
destroys collapsibility of the product cannot be met. Such a $K$ would come with the
polyhedron $L$ of part (b), and $L$ would be a counterexample to Zeeman's conjecture,
which is open. The exact obstruction to the round-2 report's proposed route is
therefore the single elementary expansion of downward propagation, and it is an open
problem that sits between the two conjectures.

## 5. The product cell structure: why not three elementary collapses

A reader who takes the product cell structure of $K \times I$ at face value might
expect the collapse of Theorem 1 to be a sequence of pair removals in that
structure: the cells over the new ball $D^n$ and its free face $D^{n-1}$ are
$e \times I$, $e \times \{0\}$, $e \times \{1\}$, $f \times I$, $f \times \{0\}$ and
$f \times \{1\}$ for the two cells $e = D^n$ and $f = D^{n-1}$, and the free-face
condition singles out one order. The computation in Section 8 checks that under the
free-face condition alone the three removals, in the order $e \times I$ with
$f \times I$, then $e \times \{1\}$ with $f \times \{1\}$, then $e \times \{0\}$ with
$f \times \{0\}$, remove exactly those six cells and leave the product cells of the
complement. [Computation]

The three removals are nevertheless not a sequence of elementary collapses of the
product cell structure, and the reason is the ball condition in Definition 1. The
sequence fails at the first removal. In the disc with cells $v$, $e$, $f$ and $v$ a
face of both $e$ and $f$, the cell $e \times \{0\}$ is a face of $e \times I$ and
it is not a face of $f \times I$, so what is left after removing the interiors of
$e \times I$ and $f \times I$ is not a ball. The computation records this for the
disc, and it also records that the second and the third removal do satisfy the ball
condition with respect to the cells that are left once the first has been made. [Computation] The collapse of Theorem 1 avoids the problem
because it uses the ball $D^n \times I$ and the boundary ball $D^{n-1} \times I$,
not the product cell decomposition. In the language of the report's Lemma 7, the
pair that crosses with $I$ is a pair of balls, and this is the step that makes the
collapse elementary. [Argument]

In the CW language of the round-2 report the collapse is still one elementary
collapse, provided the ball is taken to be the whole closed cell $\bar e$ times $I$.
That subcomplex consists of the product cells $e \times I$, $e \times \{0\}$ and
$e \times \{1\}$ together with $g \times I$, $g \times \{0\}$ and $g \times \{1\}$
for the proper faces $g$ of $e$, and its intersection with $L \times I$ is the whole
of $\bar f \times I$, which is a ball in its boundary. The cells removed are then all
the product cells over the interiors of $e$ and $f$. A reader who takes the free face
to be the single cell $f \times I$ obtains the three pair removals of the
computation, and those are not elementary collapses of the product cell structure.
[Argument, Computation]

Two further witnesses in the computation record that a face poset alone cannot
decide the question. The 2-sphere written as one vertex and one 2-cell admits the
free pair (2-cell, vertex) and satisfies the order-theoretic shadow of the ball
condition, and the 2-sphere is not collapsible. An edge with two distinct endpoints
admits the free pair (edge, endpoint), that pair is an elementary collapse by
Definition 1, and it fails the order-theoretic shadow. So the shadow is neither
necessary nor sufficient, and the ball condition has to be taken from the geometry.
[Computation] This is a limitation of the computation and not of the theorem, and it
is the reason the proof of Theorem 1 is given in the PL category.

## 6. Corrections to the round-2 report

**Correction 1** (Remark 8, the example). The report says: "the elementary 3-collapse
that removes the pair $(e^2, e^3)$ leaves the 2-sphere, which is not collapsible."
The complex is $e^0 \cup e^2 \cup e^3$, with the closed 2-cell attached to the vertex
by the constant map, and the elementary collapse removes the interiors of both cells
of the pair, so what remains is $e^0$, a point. The Euler characteristic gives a
sharper objection. The complex has characteristic $1 - 0 + 1 - 1 = 1$, the 2-sphere
has characteristic $2$, and an elementary collapse removes two cells in consecutive
dimensions and preserves the characteristic, so no collapse sequence from that
complex ends at the 2-sphere. [Argument, Computation]

**Correction 2** (Remark 8, the replacement). The conclusion of Remark 8 is true:
collapsibility is not preserved by 3-collapses. The witness is the dunce cap $D$. It
is contractible and not collapsible, so its product with $I$ is the interesting
case, and Zeeman proved that $D \times I$ is collapsible. Then Theorem 4 gives the
collapse $D \times I \searrow D \times \{0\}$, which is a 3-collapse of a collapsible
3-polyhedron onto a non-collapsible 2-polyhedron. So a 3-collapse can destroy
collapsibility, and positivity of the product is what survives it. [Cited for the
two facts about the dunce cap, Argument for the composition]

**Correction 3** (Lemma 7, a gap in the wording). The proof says that the product
"produces the corresponding pair of a 3-cell and a 4-cell in $K' \times I$, with the
3-cell again a free face, so $K' \times I$ collapses to $K \times I$ in one
elementary collapse". That is right in the PL category, because $D^3 \times I$ is a
4-ball and $D^2 \times I$ is a face in its boundary. The missing sentence is the one
that identifies the new 4-cell with the ball $D^3 \times I$; the product cell
structure gives a different decomposition, and in that decomposition the collapse is
not elementary. The computation in Section 8 shows this for the disc. [Argument,
Computation] With that sentence added, Lemma 7 is sound.

**Correction 4** (the sentence after Remark 8). The inference recorded in Section 4
fails. The propagation across an elementary 3-collapse is Lemma 7, and it does not
give invariance under 3-deformations, so it cannot transfer positivity from the
point to a contractible polyhedron along a 3-deformation. [Argument]

## 7. What this means for the campaign

The two conjectures are related as follows, and the record should state it in this
form. Zeeman implies stable Andrews-Curtis by Corollary 5, which is Fagan's
Proposition 3.8 and which needs only Theorem 4. The reverse implication is what
downward propagation supplies, by Proposition 7(c), and downward propagation is not
available. In the literature the reverse implication is obtained for the
non-thickenable special polyhedra by Matveev's 1987 theorem, for standard spines by
Gillman and Rolfsen together with Perelman's theorem, and for all contractible
2-polyhedra only in Dynnikov's 2026 preprint, which is unrefereed here. The
restricted equivalence is also recorded in the opening section of Fagan, Qiu and
Wang, arXiv:2412.12293, in the form that Zeeman's conjecture for the contractible
fake surfaces that do not embed in a 3-manifold is equivalent to the stable
conjecture. [Cited, with the last two items REPORTED]

So the sentence "a positive answer makes Zeeman's conjecture equivalent to the
stable Andrews-Curtis conjecture" is not supported by the positive answer. What is
supported is the sharper pair of statements: downward propagation, which concerns a
single elementary expansion, is sufficient for the reverse implication by
Proposition 7(c), and by Proposition 6 the reverse implication amounts to the
invariance of positivity under 3-deformations. The question of downward propagation
is itself an open problem between the two conjectures.

For `OPEN_QUESTIONS.md` the direction proposes one new entry, to be numbered after
Q20 and stated as a reformulation and not as a new conjecture: is positivity
invariant under 3-deformations, that is, does $K \times I$ collapsible imply
$L \times I$ collapsible whenever $L$ is an elementary 3-collapse of $K$?
Proposition 6 shows that, under the stable conjecture, this invariance is equivalent
to Zeeman's conjecture, and Proposition 7(b) shows that a counterexample to its
single-step form with $L$ a 2-polyhedron would refute Zeeman's conjecture. So the
entry should carry the status of the reverse implication between the two
conjectures and no separate status, and it is a sharpening of the topological side
of Q10 rather than a statement about presentations.

## 8. The checks

The script uses only the python3 standard library and runs in under a second on this
VM. It is deterministic: the sample of larger face posets uses the fixed seed
20261104, and the exhaustive part enumerates every graded face poset with at most
four cells.

```
cd .ultramath/smw2opo0o/m6/directions/zeeman-positivity
python3 check_zeeman.py
```

The run ends with the following lines, and the whole output is in
`check_zeeman.out`. The count of 23 is the count of checks, and every check prints
one PASS line.

```
checks 23, failures 0
ALL CHECKS PASSED
```

The bullets below say what each group of checks establishes, in the order of the
output. Each bullet names the checks it covers and the statement they support.

* A1 to A6: the Euler characteristic arithmetic. The complex $e^0 \cup e^2 \cup e^3$
  has characteristic 1, the 2-sphere has characteristic 2, the standard complex of
  the dunce cap has characteristic 1, the product cell structure of $D \times I$ has
  characteristic 1, and $\chi(K \times I) = \chi(K)$ for five sample complexes.
* B1 and B2: the free-face bookkeeping of the product cell structure over every
  graded face poset with at most four cells (5872 complexes and 6216 free pairs) and
  over a deterministic pseudo-random sample with five to seven cells (400 complexes
  and 549 free pairs). In every case the three removals in the order side, top,
  bottom satisfy the free-face condition and leave exactly the product cells of the
  complement.
* B3: in every enumerated case the top pair and the bottom pair are not free in the
  full product complex, because the free face is also a face of the corresponding
  side cell. So the order of the three removals is forced, as Section 5 says.
* C1: for the disc, the side removal fails the ball condition and the top and
  bottom removals satisfy it.
* C2: the 2-sphere poset admits the naive free pair (2-cell, vertex) and satisfies
  the order-theoretic shadow of the ball condition, and the 2-sphere is not
  collapsible.
* C3: the edge poset admits the free pair (edge, endpoint), which is an elementary
  collapse, and it fails the shadow.

The round-2 report's own self check was rerun in this direction, and it still
passes. The command is the one recorded in that report.

```
cd directions/invariant-ideas
python3 check_idea.py
```

It ends with `ALL CHECKS PASSED` after 34 checks in about 3 seconds on this VM, so
the results of that report that this direction relies on are unchanged. The only
results of that report used here are Lemma 7, which is reproved here with the
missing sentence supplied, and Remark 8, which is corrected here.

## 9. Sources

Each entry records what was read and where, and the entries marked as not read are
listed so that a reader can see which claims rest on a secondary source. All the
reading was done on 2026-11-04.

* A. Kupers, *Zeeman's conjecture*, Graduate Journal of Mathematics 6 (2021), no. 1,
  35-42. Read: the whole paper in the text extracted from the published PDF at
  `https://gradmath.org/wp-content/uploads/2021/07/GJM2021-Kupers.pdf`, with
  `pdftotext -layout`. Used for Definition 1.1 (elementary collapse, collapse,
  collapsible), Conjecture 2.1 (Zeeman's conjecture), Lemma 2.2, Example 2.3 (the
  dunce cap and Bing's house become collapsible after crossing with an interval),
  the Proposition 3.8 of that paper (Zeeman's conjecture for the standard polyhedra
  that are spines of 3-manifolds is equivalent to the Poincare conjecture, which is
  a different statement from Fagan's Proposition 3.8), and the bibliography for
  Zeeman, Dierker, Cohen, Gillman, Matveev, Matveev and Rolfsen, Wall and Wright.
  The journal page `https://gradmath.org/2021/zeemans-conjecture/` gives the volume,
  the issue and the pages.
* E. C. Zeeman, *On the dunce hat*, Topology 2 (1963) 341-358, DOI
  10.1016/0040-9383(63)90014-4. Bibliographic data checked against Crossref on
  2026-11-04, which returns the title, the container, the volume, the pages and the
  year 1963. The paper itself was not read. The two facts used about the dunce cap
  are quoted from Kupers.
* L. Fagan, thesis, University of California, Santa Barbara. Read: the passages
  quoted here in the text returned by a search-engine extraction of the published
  PDF at `https://escholarship.org/content/qt6fm617h4/qt6fm617h4.pdf`, namely
  Conjecture 3.4 (the topological form of the stable conjecture) and Proposition 3.8
  with its proof ("Any 2-polyhedron K expands to K x I. If K is contractible, then
  by the Zeeman conjecture, K x I collapses to a point."). Not read: the rest of the
  thesis, and the printed page.
* J. A. Barmak, *An exotic presentation of Z x Z and the Andrews-Curtis
  conjecture*, Algebr. Geom. Topol. 25 (2025) 345-355, DOI 10.2140/agt.2025.25.345.
  Not read here. The quoted statement that the weak Andrews-Curtis conjecture is
  equivalent to the statement that every contractible finite 2-complex 3-deforms to
  a point is taken from `survey/topology.md` Section 2, where the coordinator
  verified it against the published text.
* J. Quinn, *Dual 2-complexes in 4-manifolds*, arXiv:math/0009234, Definition 1.7.
  Not read here. The definition of a 2-deformation and the terminology warning are
  taken from `survey/topology.md` Section 1.3, where they were verified.
* S. V. Matveev, *The Zeeman conjecture for nonthickenable special polyhedra is
  equivalent to the Andrews-Curtis conjecture*, Sibirsk. Mat. Zh. 28 (1987) no. 6,
  66-80. Not read in any language. The statement is REPORTED, through the zbMATH
  review quoted in `survey/dynnikov.md` Section 6.2 and through Kupers'
  bibliography.
* D. Gillman and D. Rolfsen, *The Zeeman conjecture for standard spines is
  equivalent to the Poincare conjecture*, Topology 22 (1983) 315-323. Not read. The
  statement is REPORTED, through Kupers Proposition 3.8 and
  `survey/stable-ac.md` Section 4.
* I. Dynnikov, *On Zeeman's collapsibility conjecture for non-standard polyhedra*,
  arXiv:2608.23331 version 1. Not read here. The claim that Zeeman's conjecture and
  the Andrews-Curtis conjecture with stabilisations are equivalent, and the exact
  points where its proof is soft, are taken from `survey/dynnikov.md`, which read the
  preprint in full and labelled the relevant claims REPORTED. This direction does not
  rely on that claim.
* P. Wright, *Group presentations and formal deformations*, Trans. Amer. Math. Soc.
  208 (1975) 161-169, and P. Wright, *Formal 3-deformations of 2-polyhedra*, Proc.
  Amer. Math. Soc. 37 (1973) 305-308, DOI 10.1090/S0002-9939-1973-0331397-2. Not
  read. The correspondence between the stable moves and 3-deformations is a
  literature claim recorded in `survey/stable-ac.md` Section 3, and this direction
  quotes it as such. The 1973 abstract was seen in a search-engine extraction, and
  it states that a formal deformation of 2-polyhedra through polyhedra of dimension
  at most 3 is what is wanted and that the bound of 4 was not yet reduced to 3.
* L. Fagan, Y. Qiu and Z. Wang, *Stable Andrews-Curtis conjecture via fake surfaces
  and Zeeman conjecture*, arXiv:2412.12293. Read: the abstract and the opening
  section in the arXiv HTML version, which is the source of the sentence quoted in
  Section 7 about the non-embeddable fake surfaces. This is a preprint.

## 10. What I could not verify, and what remains uncertain

* I did not read Zeeman's paper, Gillman and Rolfsen, Matveev, Cohen's two papers,
  or Wright. Every statement attributed to them is labelled as quoted through
  Kupers' survey or through the repository's surveys, and none of the proofs in
  Sections 3, 4 and 6 depends on their content beyond the two facts about the dunce
  cap and the one-line implication of Fagan's Proposition 3.8.
* I did not settle whether positivity is invariant under 3-deformations. Section 4
  shows that this is the missing statement and that it is equivalent, given the
  stable conjecture, to the reverse implication between the two conjectures. The
  collapsible case of the single-step form is settled by Proposition 8, and the open
  case is a contractible polyhedron that is not collapsible. The question is open as
  far as I know, and the fact that the reverse implication needs Matveev's theorem,
  Gillman and Rolfsen with Perelman, and an unrefereed 2026 preprint in the
  literature is consistent with its not being elementary.
* The round-2 report's Remark 8 conclusion is true and its example is wrong. I
  corrected the example with the dunce cap, and I did not check whether the complex
  described in Remark 8 is homeomorphic to the 3-ball, because the Euler
  characteristic objection does not need that.
* The computation in Section 8 checks statements about face posets. Those statements
  are not a model of polyhedral collapse, and Section 5 records the two witnesses
  that show why. The proof of Theorem 1 is a pencil argument in the PL category, and
  it is short enough to be checked by hand in the form given above.
* Nothing here bears on the truth of the Andrews-Curtis conjecture or of Zeeman's
  conjecture, and no claim of proof or disproof is made.
