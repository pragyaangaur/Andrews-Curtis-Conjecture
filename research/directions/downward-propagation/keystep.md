# Direction H6: the Key Step of downward propagation, corrected

Round 5 deliverable for direction H6 of swarm smw38010i, member m9. This file
replaces the first version, which claimed that the Key Step (KS) of `report.md`
Section 6 is equivalent to downward propagation and that a KS failure refutes
Zeeman's conjecture. Both claims rested on a false inference, which Section 7
identifies. The lemmas and the computations stand; the two theorems are withdrawn.

Labels. **Argument** means a proof written out here. **Computation** means an exact
deterministic program with the command recorded in Section 9. **Conjecture** means a
statement supported by the computations and not proved.

| file | contents |
| --- | --- |
| `keystep.md` | this report |
| `ks_engine.py` | exact free-pair collapse engine for finite regular CW complexes, the product cell structure $L\times I$, the KS construction, and the checks on the disc models |
| `ks_out.txt` | recorded output of `python3 ks_engine.py` (16 s on this machine) |
| `ks_dunce.py` | the protected-collapse search for a KS datum over the dunce hat base |
| `ks_dunce.out` | recorded output of `python3 ks_dunce.py 0 150 300000` and the same command with choice 1 and choice 2 |

## 1. Outcome

1. **Withdrawn.** The first version of this report proved "KS is equivalent to
   downward propagation" and "Zeeman implies KS". The proofs used the inference
   that a collapse image of a collapsible complex is collapsible. That inference is
   false, and Section 7 exhibits the campaign's own counterexample: the dunce hat
   $D$ is not collapsible, $D\times I$ is collapsible by Zeeman's theorem for the
   dunce hat, and $D\times I$ collapses onto $D\times\{0\}\cong D$. The referee
   caught this, and the corrected report records what does follow. [Argument]
2. **The attaching ball survives every collapse.** Let $X=L\times I$ carry the
   product cell structure, let $B^2\subset L$ be a disc as in Section 2, and let
   $B^3=B^2\times I$. If $X_1$ is a collapse image of $X$ that contains the sphere
   $\partial B^3$, then $B^3\subset X_1$: no cell of the ball is ever removed. This
   is Lemma D. [Argument, Computation]
3. **A KS failure makes the two 3-cell attachments homotopy equivalent.** With
   $W=X_1\setminus\mathrm{int}\,c$, the chain $[B^3]-[c]$ is supported on $W$, so
   $[\partial B^3]=[\partial c]$ in $H_2(W)$ (Lemma E). If $Z=W\cup c'$ collapses to
   a point then $W$ is simply connected and the two attaching maps are homotopic, so
   $Z\simeq X_1$ and $X_1$ is contractible (Lemma F). [Argument]
4. **What a KS failure is.** A KS datum with $Z\searrow *$ and $X_1$ not collapsible
   gives: $L$ contractible, $X_1$ contractible and not collapsible, $X_1$ a collapse
   image of $L\times I$ containing the prism $B^3$, and $K=L\cup_{B^2}D^3$ with
   $K\times I$ collapsible. So the hypothesis of downward propagation holds at
   $(L,B^2)$, and the base $L\times I$ collapses onto a contractible non-collapsible
   3-complex. This is the dunce-hat pattern in a product, and it is consistent with
   everything known. This is Proposition 1. [Argument, Computation]
5. **The inference that is missing.** Whether $L\times I$ itself is collapsible is
   not decided by the KS failure. If it is not collapsible, the base is a Zeeman
   counterexample; if it is, the KS failure says nothing against Zeeman. This is
   exactly the gap, and it is the reason the two theorems are withdrawn.
   [Argument]
6. **A correct sufficient condition.** KS follows from the statement that every
   contractible collapse image of a product $L\times I$ that contains a prism is
   collapsible (Proposition 2). The special case $X_1=X$ of KS follows from Zeeman's
   conjecture alone (Proposition 3), so the gap lives entirely in the case where
   $X_1$ is a proper collapse image. [Argument]
7. **The missing step localised.** In any collapse of $Z$, the 3-cell $c'$ is
   removed paired with a 2-cell $f$ of the sphere $\partial B^3$, so $Z\searrow *$
   forces complexes $W\searrow W'$ with $W'\setminus\mathrm{int}\,f\searrow *$. What
   KS needs on top of that is a cancellation principle in dimension three. The
   round-4 report's Lemma 5 records that the analogous statement fails in dimension
   two. This is Proposition 4. [Argument]
8. **New computation: no KS counterexample at the dunce hat base.** Over the dunce
   hat triangulation, with $B^2$ one triangle and two other discs, 445 maximal
   protected collapse images $X_1$ were examined. In every one, $Z$ and $X_1$ have
   the same collapsibility status: 42 pairs both collapsible, 403 pairs both not
   collapsible, 0 differences. So no KS counterexample arises there. The pattern
   supports a conjecture which would make KS into an equivalence of two
   collapsibility statements for the same $W$. [Computation, Conjecture]

## 2. Framework and the statements

The framework is the one of `report.md` Section 6, made explicit. $L$ is a finite
regular CW complex of dimension 2 with at least one 2-cell. $I=[0,1]$ has cells
$\{0\}$, $\{1\}$ and $(0,1)$. $X=L\times I$ carries the product cell structure, so a
cell of $X$ is a product $a\times b$ with $a$ a cell of $L$ and $b$ a cell of $I$,
and its facets are the products $a'\times b$ with $a'$ a facet of $a$ and $a\times
b'$ with $b'$ a facet of $b$. $B^2\subset L$ is a subcomplex homeomorphic to a disc,
$e^2\subset B^2$ is a 2-cell, $B^3=B^2\times I$ and $c=e^2\times I$.

Two hypotheses on the cell structure of the disc are used, and every subdivision of a
disc satisfies them:

* (H1) every 1-cell of $B^2$ that does not lie on the boundary circle is a facet of
  exactly two 2-cells of $B^2$, and every 1-cell on the boundary circle is a facet of
  exactly one 2-cell of $B^2$;
* (H2) every 0-cell of $B^2$ is a facet of at least two 1-cells of $B^2$.

A free pair in a complex $W$ is a pair of cells $(e,f)$ such that $f$ is a facet of
$e$ and $f$ is a face of no cell of $W$ other than $e$. Removing the two open cells
of a free pair leaves a subcomplex, and this is the elementary collapse of Kupers
Definition 1.1 as the repository reads it. A collapse is a finite sequence of such
removals, and $W\searrow *$ means that $W$ collapses to a point.

The two remaining cells of the situation are the single 4-cell $D^4$ glued along
$B^3\subset\partial D^4$ and the single 3-cell $c'$ that is the closure of the
complement of $B^3$ in $\partial D^4$. This is the bookkeeping of `report.md` Lemma
6, in which $Y=K\times I=X\cup D^4\cup c'$ and the only cells of $Y$ that are not
cells of $X$ are $D^4$ and $c'$. Every face of $D^4$ is a cell of $B^3$ or is $c'$,
and every face of $c'$ is a cell of $\partial B^3$.

A **KS datum** is a subcomplex $X_1\subset X$ with $X\searrow X_1$,
$\partial B^3\subset X_1$ and $c\in X_1$, together with
$$Z=(X_1\setminus\mathrm{int}\,c)\cup c'.$$
The hypothesis $\partial B^3\subset X_1$ is not an extra assumption. $Z$ is the union
of $X_1\setminus\mathrm{int}\,c$ with $c'$ glued along $\partial B^3$, so $Z$ is a
complex only if $\partial B^3$ is a subcomplex of $X_1$, and `report.md` Section 6
leaves this implicit.

**Key Step (KS).** For every KS datum, $Z\searrow *$ implies $X_1\searrow *$.

**Remark.** In the application to $K\times I$ the hypothesis $\partial B^3\subset X_1$
is automatic. While $D^4$ is present, every cell of $B^3$ is a face of $D^4$, so no
cell of $B^3$ is removed before $D^4$ is, which is the first part of `report.md`
Lemma 6. Hence every collapse of $K\times I$ produces a KS datum at the stage where
$D^4$ is removed. [Argument]

**Downward propagation (DP)**, as in `report.md`: for every finite 2-polyhedron $L$
and every disc $B^2\subset L$, if $K=L\cup_{B^2}D^3$ and $K\times I$ is collapsible,
then $L\times I$ is collapsible.

## 3. Lemma D: the attaching ball survives

**Lemma D.** Let $X$, $B^2$, $B^3$ and $c$ be as in Section 2, let (H1) and (H2)
hold, and let $X_1\subset X$ be a subcomplex with $X\searrow X_1$ and
$\partial B^3\subset X_1$. Then $B^3\subset X_1$.

*Proof.* A collapse only removes cells, so no cell of $\partial B^3$ is removed once
$\partial B^3\subset X_1$. I prove by induction that all cells of $B^3$ are present at
every stage. Suppose they are, and let $(e,f)$ be the next free pair. If $f\notin
B^3$ then $e\notin B^3$ as well, because every facet of a cell of $B^3$ is a cell of
$B^3$ and no cell of $B^3$ is removed. So suppose $f\in B^3$ and examine the
possibilities for $f$, remembering that $f$ must be a face of no cell other than
$e$; in the list below I name the cells that have $f$ as a face.

* $f=v\times b$ is a 0-cell, with $v$ a 0-cell of $B^2$. The 1-cells $g\times b$
  with $g$ a 1-cell of $B^2$ through $v$ are present cells having $f$ as a face, and
  (H2) gives at least two of them.
* $f=v\times(0,1)$ is a 1-cell, with $v$ a 0-cell of $B^2$. The 2-cells
  $h\times(0,1)$ with $h$ a 2-cell of $B^2$ through $v$ have $f$ as a face. If $v$
  lies on the boundary circle then $f\subset\partial B^3$. If $v$ is not on the
  boundary circle then both 1-cells of $B^2$ through $v$ are interior 1-cells, so by
  (H1) each is a facet of two 2-cells and at least two distinct 2-cells of $B^2$ have
  $v$ on their boundary.
* $f=g\times b$ is a 1-cell, with $g$ a 1-cell of $B^2$ and $b\in\{0,1\}$. The
  2-cells $g\times(0,1)$ and $h\times b$, where $h$ is a 2-cell of $B^2$ containing
  $g$, are distinct present cells having $f$ as a face.
* $f=h\times b$ is a 2-cell, with $h$ a 2-cell of $B^2$ and $b\in\{0,1\}$. The only
  cell of $X$ that has $f$ as a facet is $h\times(0,1)$, so the only possible coface
  of $f$ is that cell, and $f$ is a cell of $\partial B^3$.
* $f=g\times(0,1)$ is a 2-cell, with $g$ a 1-cell of $B^2$. The 3-cells
  $h\times(0,1)$ with $h$ a 2-cell of $B^2$ containing $g$ have $f$ as a face. If $g$
  lies on the boundary circle then $f\subset\partial B^3$. If $g$ does not lie on the
  boundary circle then (H1) gives two 2-cells containing $g$.
* $f$ cannot be a 3-cell, because then $e$ would be a 4-cell and $X$ has none.

In every case either a present cell other than $e$ has $f$ as a face, so the pair is
not free, or $f$ is a cell of $\partial B^3$, which $X_1$ contains. Either way no cell
of $B^3$ is removed. $\square$

## 4. Lemmas E and F

Write $W=X_1\setminus\mathrm{int}\,c$, so that $X_1=W\cup_{\partial c}c$ and
$Z=W\cup_{\partial B^3}c'$.

**Lemma E.** With $B^3\subset X_1$ and $c\in X_1$, the 3-chain $[R]=[B^3]-[c]$ is
supported on $W$ and $\partial[R]=[\partial B^3]-[\partial c]$. Hence
$[\partial B^3]=[\partial c]$ in $H_2(W)$.

*Proof.* The 3-cells of $B^3$ are the cells $h\times(0,1)$ with $h$ a 2-cell of
$B^2$, and $c=e^2\times(0,1)$ is one of them. The chain $[B^3]$ is their sum with the
orientations of the complex and its boundary is the sum of the 2-cells of the sphere
$\partial B^3$ with the induced orientations, which is $[\partial B^3]$. The same
holds for $c$, whose boundary is $[\partial c]$. Both chains are chains of $X_1$, and
$[c]$ is subtracted, so the difference is supported outside the interior of $c$.
$\square$

That $[B^3]$ and $[c]$ are defined needs $B^3\subset X_1$, which is Lemma D.

**Lemma F.** With $B^3\subset X_1$ and $Z\searrow *$, the complexes $Z$ and $X_1$ are
homotopy equivalent, and $X_1$ is contractible.

*Proof.* Step 0: $W$ is path connected. Since $Z$ is collapsible, $Z$ is path
connected. Every component of $W$ other than the one containing $\partial B^3$ would
also be a component of $Z$, because $c'$ is attached only along $\partial B^3$. So
$W$ has one component.

Step 1: $\pi_1(Z)=\pi_1(W)$. The complex $Z$ is obtained from $W$ by attaching one
3-cell along the sphere $\partial B^3$. Van Kampen's theorem gives $\pi_1(Z)=\pi_1(W)$
modulo the normal closure of the image of $\pi_1(S^2)$, which is trivial, so a
3-cell attachment does not change the fundamental group.

Step 2: $W$ is simply connected. Since $Z$ is collapsible, $Z$ is contractible, so
$\pi_1(Z)=1$, and Step 1 gives $\pi_1(W)=1$.

Step 3: the two attaching maps are homotopic. Both $\partial c\to W$ and
$\partial B^3\to W$ are maps of a 2-sphere, and by Lemma E they induce the same class
in $H_2(W)$. Since $W$ is simply connected, the Hurewicz theorem gives
$\pi_2(W)\cong H_2(W)$, so the two maps are homotopic.

Step 4: $Z\simeq X_1$. If two maps of $S^2$ into $W$ are homotopic, the two spaces
obtained by attaching a 3-cell along them are homotopy equivalent, because the
mapping cylinder of the homotopy, glued to $W$, deformation retracts onto each of the
two. So $Z=W\cup_{\partial B^3}c'$ and $X_1=W\cup_{\partial c}c$ are homotopy
equivalent.

Step 5: $X_1\simeq Z\simeq *$. $\square$

## 5. Proposition 1: the shape of a KS failure

**Proposition 1.** Suppose a KS datum has $Z\searrow *$ and $X_1$ not collapsible.
Then $L$ is a contractible finite 2-polyhedron, $X_1$ is a contractible complex that
is not collapsible, $X_1$ is a collapse image of $L\times I$ containing $B^3$, and
$K=L\cup_{B^2}D^3$ satisfies $K\times I\searrow *$.

*Proof.* By Lemma D, $B^3\subset X_1$, so Lemma F applies and gives $X_1\simeq *$.
Since $X\searrow X_1$, the inclusion is a homotopy equivalence, so $L\times I\simeq
*$, hence $L\simeq *$. For the last claim, $K\times I=X\cup D^4\cup c'$. The collapse
$X\searrow X_1$ removes no cell of $B^3$, and no cell outside $B^3$ is a face of
$D^4$ or of $c'$, so each removed pair is free in $K\times I$ as well and $K\times
I\searrow X_1\cup D^4\cup c'$. There the pair $(D^4,c)$ is free, since $c$ is a facet
of $D^4$ and a face of no other present cell, and removing it leaves exactly $Z$,
which collapses to a point. $\square$

Proposition 1 is the honest content of the referee's diagnosis, and the computation
of Section 9 checks the three stages of the collapse cell by cell. It does not decide
whether $L\times I$ is collapsible.

## 6. What would close the gap

**Proposition 2.** Assume that every contractible collapse image $X_1$ of a product
$L\times I$, with $X_1$ containing a prism $B^3=B^2\times I$ over a disc, is
collapsible. Then the Key Step holds.

*Proof.* A KS datum with $Z\searrow *$ gives, by Lemma F, that $X_1$ is contractible
and, by Lemma D, that $X_1$ contains $B^3$. The hypothesis then gives $X_1\searrow
*$. $\square$

The assumption is not a consequence of anything in the campaign. The dunce hat is a
contractible complex that is not collapsible, and it is a collapse image of its own
product with $I$, so contractibility of collapse images of products is not
automatic. Section 7 records the example.

**Proposition 3.** Assume Zeeman's conjecture. Then the Key Step holds in the case
$X_1=X$: if $(X\setminus\mathrm{int}\,c)\cup c'$ collapses to a point, then
$X=L\times I$ is collapsible.

*Proof.* With $X_1=X$ the complex $Z$ is a collapse-style replacement of $c$ inside
$X$, and Lemma F gives $X\simeq *$. Hence $L\simeq *$, and Zeeman's conjecture gives
that $L\times I=X$ is collapsible. $\square$

So the gap lives entirely in the case where $X_1$ is a proper collapse image of $X$.

**Proposition 4.** Let $Z\searrow *$ be a KS datum. The cell $c'$ has no coface in
$Z$, so in the collapse sequence it is removed as the coface of a pair $(c',f)$ with
$f$ a facet of $c'$, that is, a 2-cell of $\partial B^3$. All pairs removed before
that step have both cells in $W$, so they give a collapse $W\searrow W'$, and after
the removal of $(c',f)$ the remaining complex is $W'\setminus\mathrm{int}\,f$, which
collapses to a point.

*Proof.* The cell $c'$ is 3-dimensional and $Z$ is 3-dimensional, so $c'$ has no
proper coface and is not the facet of any pair. Its facets are the 2-cells of
$\partial B^3$. The cells of $Z$ other than $c'$ are the cells of $W$, so a pair
removed while $c'$ is present and is not the coface has both cells in $W$, and it is
free in $W$ because the only extra cell is $c'$, whose faces meet $W$ in
$\partial B^3$. $\square$

So a proof of KS needs the following cancellation principle in dimension three: if
$W\searrow W'$ and $W'\setminus\mathrm{int}\,f\searrow *$ for a 2-cell $f$ of
$\partial B^3$, then $X_1=W\cup_{\partial c}c$ is collapsible. The round-4 report's
Lemma 5 shows that the dimension-two analogue, with $S^1$ in place of $X_1$ and an
arc in place of $f$, is false. I do not know whether the dimension-three statement
holds.

## 7. The false inference, and the campaign's own counterexample

The first version of this file used the sentence "a collapse image of a collapsible
complex is collapsible", in Theorem 1's step from "$X_1$ is not collapsible and
$X_1$ is a collapse image of $X$" to "$X$ is not collapsible", and again in Theorem
2's parenthetical. The inference is false.

The counterexample is the dunce hat $D$, the 8-vertex 17-triangle triangulation that
`certify_dunce.py` in this directory certifies to be contractible with no free pair,
so $D$ is not collapsible (`report.md` Section 8, Kupers Example 1.5). Its product
$D\times I$ is collapsible by Zeeman's theorem for the dunce hat (Kupers Example
2.3), and $D\times I$ collapses onto $D\times\{0\}$ by the standard product collapse:
remove each prism over a 2-cell paired with its top, then each pillar over a 1-cell
paired with its top, then each pillar over a 0-cell paired with its top. So a
collapsible complex collapses onto a non-collapsible one.

The campaign already recorded this. `STATE.md`, round-3 log, has the sentence "the
conclusion survives via the dunce cap (D x I collapsible by Zeeman, D x I collapses
to D, D not collapsible)", and it was the round-3 correction of Remark 8 in
`directions/invariant-ideas/idea.md`. My first version did not use the record
properly, and the referee was right to reject it.

Two consequences are worth stating plainly. First, a KS failure is compatible with
$L$ being positive, because $X_1$ can be a dunce-hat-shaped collapse image of a
collapsible $L\times I$. Second, the weakening of KS that the round-4 reduction
actually needs is not KS itself: it is the statement that a KS failure forces
$L\times I$ to be non-collapsible.

## 8. The conjecture supported by the computation

**Conjecture.** For every KS datum, $Z\searrow *$ if and only if $X_1\searrow *$.

The forward direction is KS. The backward direction is what makes the two complexes
interchangeable. Both directions held in every instance examined: 775 instances over
the disc models, where all of them collapse, and 445 instances over the dunce hat,
where 42 pairs are both collapsible and 403 pairs are both not collapsible, with no
disagreement. The conjecture is not proved, and the disc models cannot test the
backward direction because their products are collapsible.

## 9. Computations

The engine `ks_engine.py` is python3 with the standard library only, deterministic. A
complex is a graded face poset, a subcomplex is a down-closed set of cells held as an
integer bitmask, and a free pair is a pair $(e,f)$ with $f$ a facet of $e$ and $f$ a
face of no other present cell. Positive answers come with the collapse sequence and
are replayed from the original complex by a separate function. Negative answers are
exhaustive over all free-pair removals. Bounded runs print `cap reached` or
`UNDECIDED`, never a negative.

Command, from this directory:

```
python3 ks_engine.py
```

Recorded output, `ks_out.txt`. The six sanity rows reproduce `report.md` Section 8
with the same f-vectors and step counts:

```
point                     COLLAPSIBLE      f=[1] free=0 explored=1 steps=0 replay=True
interval                  COLLAPSIBLE      f=[2, 1] free=2 explored=2 steps=1 replay=True
circle                    NOT COLLAPSIBLE  f=[3, 3] free=0 explored=1
disc (two triangles)      COLLAPSIBLE      f=[4, 5, 2] free=4 explored=6 steps=5 replay=True
2-sphere (tetrahedron boundary) NOT COLLAPSIBLE f=[4, 6, 4] free=0 explored=1
3-ball (tetrahedron)      COLLAPSIBLE      f=[4, 6, 4, 1] free=4 explored=8 steps=7 replay=True
```

The four product models, with the check of Lemma D's hypotheses and of the shell
$R=\mathrm{cl}(B^3\setminus\mathrm{int}\,c)$:

```
M2 L = two-triangle disc, B^2 = L, e^2 = first triangle
   |X|=33 f=[8, 14, 9, 2] chi=1 |B3|=33 chi=1 |dB3|=30 |c'|=1
   R = (B^2 minus e^2)xI u e^2 x partial I    OK   chi(R)=2 |R|=32 |pred|=32
   hypotheses H1 (edge cofaces) and H2 (vertex degrees)  OK
M4 L = hexagon disc, B^2 = central plus one outer triangle
   |X|=57 f=[12, 24, 17, 4] chi=1 |B3|=33 chi=1 |dB3|=30 |c'|=1
   R = (B^2 minus e^2)xI u e^2 x partial I    OK   chi(R)=2 |R|=32 |pred|=32
   hypotheses H1 (edge cofaces) and H2 (vertex degrees)  OK
```

The shell identity is the one used in `report.md` Section 6: the cells of $B^3$ other
than $c$ are exactly the cells of $(B^2\setminus\mathrm{int}\,e^2)\times I$ together
with the cells of $e^2\times\partial I$. Both sides were computed as cell sets and
agree in all four models. The Euler characteristics are $\chi(B^3)=1$ and $\chi(R)=2$.
The end facets $e^2\times\{0\}$ and $e^2\times\{1\}$ are facets of exactly one 3-cell
of $X$ in all four models.

Lemma D, exhaustively over the reachable subcomplexes of $X$:

```
M2: reachable 8623 ; keeping the sphere of B^3: 1 ; missing a cell of B^3: 0
M4: reachable 200001 (cap reached) ; keeping the sphere of B^3: 1044 ; missing: 0
M3: reachable 200001 (cap reached) ; keeping the sphere of B^3: 1 ; missing: 0
```

The Key Step instances in the disc models, with $Z$ decided exactly:

```
M2: instances 1    ; Z collapsible 1    ; X1 collapsible 1    ; violations of KS: 0
M4: instances 774  ; Z collapsible 774  ; X1 collapsible 774  ; violations of KS: 0
```

A smallest certificate in M4 has $|Z|=43$ and collapses in 21 steps, and its first two
removals are

```
('X', ('t', '1', '2', '4'), ('i', 'E')) <- ('X', ('e', '1', '2'), ('i', 'E'))
('cp',) <- ('X', ('e', '1', '4'), ('i', 'E'))
```

so the collapse removes a 3-cell of $X$ first and then removes $c'$ paired with a
2-cell of $\partial B^3$ that has just become free. This is the mechanism Proposition
4 describes. Replay from the original complex: `True`.

Proposition 1's three-stage collapse was checked cell by cell on five instances of
model M4:

```
|X1|= 43 |Z|= 43 free pair (D^4,c) ok; removal leaves Z: True; Y collapsible: COLLAPSIBLE (steps 29, replay True)
|X1|= 51 |Z|= 51 free pair (D^4,c) ok; removal leaves Z: True; Y collapsible: COLLAPSIBLE (steps 29, replay True)
|X1|= 49 |Z|= 49 free pair (D^4,c) ok; removal leaves Z: True; Y collapsible: COLLAPSIBLE (steps 29, replay True)
|X1|= 49 |Z|= 49 free pair (D^4,c) ok; removal leaves Z: True; Y collapsible: COLLAPSIBLE (steps 29, replay True)
|X1|= 49 |Z|= 49 free pair (D^4,c) ok; removal leaves Z: True; Y collapsible: COLLAPSIBLE (steps 29, replay True)
```

The check `removal leaves Z: True` is a cell-set identity. The check of $Y$'s
collapsibility is a search in the full complex $X\cup D^4\cup c'$, which has 58 cells
in this model, and the positive answer is replayed.

The search over the dunce hat base is `ks_dunce.py`. $L$ is the 8-vertex 17-triangle
triangulation, $B^2$ is a single triangle for choice 0 and a union of two
triangles for choices 1 and 2, and $X=L\times I$ has 147 cells with $f$-vector
$(16,56,58,17)$ and $\chi=1$. The program removes free pairs whose two cells both lie
outside $B^3$, with a seeded tie-break, until no such pair remains, so every outcome
$X_1$ is a collapse image of $X$ containing $B^3$, and it decides $Z$ and $X_1$
exactly:

```
python3 ks_dunce.py 0 150 300000
python3 ks_dunce.py 1 150 300000
python3 ks_dunce.py 2 150 300000
```

Recorded output, `ks_dunce.out`:

```
=== B^2 choice 0 ===
X = L x I: 147 cells, f=[16, 56, 58, 17], chi=1
B^3 = B^2 x I: 21 cells; partial B^3: 20 cells; c': 1 cell
free pairs in X: 34 ; free pairs in X protected inside B^3: 32
of 150 pairs: Z collapsible 18, X1 collapsible 18, undecided 0, status differs 0
counterexamples to the Key Step found: 0
=== B^2 choice 1 ===
of 148 pairs: Z collapsible 17, X1 collapsible 17, undecided 0, status differs 0
counterexamples to the Key Step found: 0
=== B^2 choice 2 ===
of 147 pairs: Z collapsible 7, X1 collapsible 7, undecided 0, status differs 0
counterexamples to the Key Step found: 0
```

So the dunce hat base gives 403 KS data in which the hypothesis $Z\searrow *$ fails
as well, and 42 in which both complexes collapse. No KS counterexample was found, and
the search is a sample of maximal protected collapse images, not an exhaustive
enumeration.

## 10. What I could not verify, and what remains uncertain

1. The two theorems of the first version are withdrawn and nothing here replaces
   them. Whether KS holds, whether DP holds, and whether either follows from
   Zeeman's conjecture are all open in this document. [Argument, limit]
2. Both Lemmas are stated for collapses that are free-pair removals in the product
   cell structure, with $c'$ and $D^4$ single cells, which is the framework of
   `report.md` Lemma 6. Passing to PL collapsibility of an arbitrary subdivision is a
   separate step that neither document performs. [Argument, limit]
3. Lemma D needs (H1) and (H2). Every subdivision of a disc satisfies them, and the
   one model in which (H2) fails is the monogon. I did not work out whether Lemma D
   survives without (H2). [Argument, open]
4. The computations are statements about the models treated. Two of the
   reachable-state enumerations hit their cap, and the dunce hat search is a seeded
   sample of maximal protected collapse images. The exhaustive verdicts in it are
   verdicts about the complexes reached, not about the base. [Computation, limit]
5. The conjecture of Section 8 is supported by 1,220 instances and is not proved.
   [Conjecture]
