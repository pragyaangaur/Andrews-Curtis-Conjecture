# Direction E7: two invariant ideas, and the exact point where each one fails

Round 2 deliverable for direction E7 (invariant-ideas). The two proposals in the brief are
tested here. Both are killed, and each kill is an exact statement with a proof or a rerun.

The files of this direction are listed below. Section 6 gives the commands that regenerate
every number quoted here.

| file | contents |
| --- | --- |
| `idea.md` | this report |
| `winding.py` | Barmak's winding invariant: words, Laurent polynomials over `Z[X^+-1,Y^+-1]`, a geometric implementation from the grid curve, an algebraic implementation from the Fox derivative, and helpers for ideals |
| `check_idea.py` | the self check, 34 checks, exit 0 only if all pass |
| `check_idea.out` | recorded output of `python3 check_idea.py` |

Labels. **Argument** means a proof written out in this file. **Computation** means an exact
deterministic program with the command given in Section 6. **Cited** means a statement quoted from a
source named in Section 7 without reproof here. Nothing in this file proves or disproves the
Andrews-Curtis conjecture or its stable form, and nothing here is offered as evidence either
way.

## 1. Outcome

Proposal (i), Barmak's winding invariant, is killed in two independent ways, each recorded
below as a theorem. Both kills rest on the exponent-sum matrix, which the moves control
exactly.

- No balanced presentation of the trivial group can be moved into the commutator subgroup by
  Andrews-Curtis moves at any positive rank, and under stabilisation the only exception is the
  empty presentation at rank 0 (Theorem 1). That exception has no relators, so it carries no
  winding data, and the kill is unaffected. The set of presentations of rank at least 2 on
  which the winding polynomial is defined is therefore disjoint from the class of interest,
  and this is a property of the exponent-sum matrix, which the moves preserve up to an
  invertible integer row operation.
- The general form of the invariant, the abelianisation of the normal closure, is defined on
  the whole class of interest. There it is exactly the exponent-sum matrix (Theorem 2), and
  that matrix is unimodular on the class, so the invariant takes a single value up to
  `GL_n(Z)` and separates nothing.

Proposal (ii), a quantity that 3-deformations preserve and a 4-deformation changes, is killed as
a search and sharpened into a precise target. The target is the generalized Andrews-Curtis
conjecture in the form of a pair of complexes.

- Such a quantity exists on a class of pairwise simple homotopy equivalent 2-complexes exactly
  when the class contains two complexes that are not 3-deformation equivalent (Theorem 4). On
  the contractible class that condition is the failure of the stable Andrews-Curtis conjecture
  (Corollary 5). The search for the quantity is therefore equivalent to the search for a
  counterexample.
- The most prominent candidate pair, Barmak's pair of presentations of `Z x Z`, has simple
  homotopy equivalent standard complexes and was proved 3-deformation equivalent
  (Q**-equivalent) by Fernandez, as Barmak reports in the published version. So no known pair
  realises the gap.
- The winding invariant is a Q*-invariant, and stabilisation destroys the cocommutativity it
  needs, so it cannot be evaluated on a single Q**-class. Barmak's own pair is the explicit
  witness that this is fatal: Barmak proves it Q*-inequivalent, and Fernandez's theorem makes
  it Q**-equivalent.
- A corollary with a bound: on the class of balanced rank-2 presentations of the trivial
  group with total relator length at most 11, every member is 3-deformation equivalent to the
  point, so no quantity of the proposed kind exists there (Corollary 6). Any candidate must
  involve a presentation of length at least 12.

Section 2 treats proposal (i) and Section 3 treats proposal (ii). Section 4 lists the
candidates that were tested, each with its exact failure point, and Section 5 gives the Round 3
proposals. Section 6 holds the reproduction commands, Section 7 the sources, and Section 8 the
points I could not verify.

## 2. Proposal (i): Barmak's winding invariant

### 2.1 What the invariant is, and what the sources say

For a word `w` in the commutator subgroup `F_2'` of the free group on `x` and `y`, Barmak
associates a Laurent polynomial `P_w` in `Z[X^+-1,Y^+-1]`. The abstract of arXiv:1904.10072
states the construction: "Every element w in the commutator subgroup of the free group F_2 of
rank 2 determines a closed curve in the grid Z x R union R x Z inside R^2. The winding numbers
of this curve around the centers of the squares in the grid are the coefficients of a Laurent
polynomial P_w in two variables." [Cited]

Definition 2 of arXiv:1806.11493 gives the details, and I record the two worked values because
`check_idea.py` reproduces them: "Our notation for commutators is [u,v] = uvu^-1v^-1. So, for
instance the winding invariant of [x,y] is P_[x,y] = 1 in Z[X,X^-1,Y,Y^-1] and P_[y^-1,x] =
Y^-1." [Cited, then reproduced as checks A1 and A2]

The relevant property is Lemma 3 of arXiv:1806.11493, and check A6 reproduces its four items
on 7889 pairs of words: `P_ww' = P_w + P_w'`, `P_w^-1 = -P_w`, `P_uwu^-1 = X^kY^l P_w` where
`(k,l)` is the exponent-sum vector of `u`, and `P_[u,w] = (X^kY^l - 1)P_w`. [Cited, reproduced]
The third item is the one that governs the conjugation move, and the fourth describes how a
commutator word changes the polynomial.

A presentation is cocommutative when every relator lies in `F_2'`. From Lemma 3, Barmak's
Remark 4 concludes that a Q-transformation changes the vector `Lambda(P) = (P_r1,...,P_rm)` by
an elementary row operation, a sign change, or multiplication of one entry by a monomial, so
that `Lambda(Q)^t = E Lambda(P)^t` with `E` in `GE_m(R)`, where `R = Z[X^+-1,Y^+-1]`. [Cited]
Check B1 reproduces this on 240 random Q-moves: after each move the new vector equals the old
one acted on by exactly the predicted operation. [Computation]

The ring matters because it is not a Euclidean ring. `GE_2(R)` is a proper subgroup of
`GL_2(R)` for this `R`, by Bachmuth and Mochizuki as quoted by Barmak, and Evans gives an
explicit matrix in `GL_2(R)` outside `GE_2(R)`, quoted as Theorem 1 of arXiv:1806.11493.
[Cited; Evans' paper itself was not read, see Section 8] This is the only step of Barmak's
argument that this direction takes on trust, and the checks in Section 3.3 stop just before
it.

### 2.2 No presentation of the trivial group is cocommutative (Theorem 1)

**Theorem 1 (Argument).** Let `n >= 1` and let `P = (r_1,...,r_n)` be a tuple of words in
`F_n` whose normal closure is `F_n`, so `P` presents the trivial group. Then no tuple `Q` that
is AC-equivalent to `P` at rank `n` has all its relators in `F_n'`, and no tuple `Q` that is
stably AC-equivalent to `P` and has rank `m >= 1` has all its relators in `F_m'`.

*Proof.* Write `eps(w) = (eps_1(w),...,eps_n(w))` for the exponent-sum vector and `M(P)` for
the `n` by `n` matrix whose rows are `eps(r_i)`. A word lies in `F_n'` if and only if its
exponent-sum vector is zero, since the abelianisation of `F_n` is `Z^n` and `F_n'` is its
kernel.

For one AC move taking `P` to `P'`, the matrix changes by an invertible integer row
operation: inversion of `r_i` negates row `i`, multiplication of `r_i` by `r_j` adds row `j` to
row `i`, and conjugation of `r_i` by a word `w` leaves `eps(r_i)` unchanged because the
exponent-sum map is a homomorphism and `eps(w)` cancels. Hence `M(P') = U M(P)` with
`U` in `GL_n(Z)`. Since `U` is invertible, `M(P') = 0` if and only if `M(P) = 0`. It follows
by induction over the moves that `M(Q) = 0` if and only if `M(P) = 0`.

Now suppose `P` presents the trivial group. Then its abelianisation is trivial, that is, the
cokernel of `M(P)` is zero, which for a square integer matrix forces `det M(P) = +-1`. In
particular `M(P)` is not the zero matrix, because `n >= 1`. So `M(Q)` is not the zero matrix,
so some relator of `Q` has a nonzero exponent sum and does not lie in `F_n'`.

For the stable statement, the cokernel of the exponent-sum matrix is the abelianisation of the
presented group, and that abelianisation is unchanged by all six moves. Suppose that a tuple
`Q` of rank `m >= 1` stably equivalent to `P` had all relators in the commutator subgroup of
its own free group `F_m`. Then the exponent-sum matrix of `Q` is zero, so its cokernel is
`Z^m`, and the trivial abelianisation forces `m = 0`, which contradicts `m >= 1`. `Box`

**Remark (Argument, the rank-0 boundary).** The hypothesis `m >= 1` in the stable clause cannot
be dropped, and the exception is harmless. The empty presentation at rank 0 has no relators, so
the condition "all relators lie in the commutator subgroup of `F_0`" holds vacuously. The
destabilisation move deletes a generator together with the relator equal to that generator
whenever the generator occurs in no other relator, so the standard rank-`n` presentation
reaches the empty presentation in `n` such moves, and this is Lemma 1 of
[survey/stable-ac.md](../survey/stable-ac.md), which Round 1 checked. Hence the empty
presentation lies in the stable class of `P` exactly when `P` is stably AC-trivial, and it is
the unique cocommutative member of such a class. It carries no winding data: it has no
relators, and a winding polynomial is attached to a relator of a rank-2 presentation. Every
other member of the class has rank at least 1 and is non-cocommutative by the theorem. So the
kill stands on every presentation on which winding data could be evaluated, and the exception
adds nothing that the invariant could see.

**Corollary (Argument).** The exact answer to the question "which balanced presentations of the
trivial group can be moved into the commutator subgroup by AC moves" is: none, at every rank.
More generally, the AC class of a tuple `P` in `F_n` meets the cocommutative tuples if and only
if `P` is itself cocommutative. In the stable class of a presentation of the trivial group the
only cocommutative member is the empty presentation at rank 0, and it occurs exactly when the
class is stably trivial.

Theorem 1 is not in the Round 1 survey. Section 9 of [survey/invariants.md](../survey/invariants.md)
gives two reasons why the winding invariant does not reach AK(3): AK(3) is not cocommutative,
and the mechanism collapses for trivial groups. The corollary above strengthens the first
reason from "AK(3) is not cocommutative" to "no presentation of the trivial group is", and
Theorem 2 below makes the second reason exact.

Spot checks. Every one of the 785 balanced pairs of words in `F_2'` with total length at most 8
has zero exponent-sum matrix, hence abelianisation `Z^2` and hence a nontrivial group (check
D1). Every one of the 1157 certificate rows in the shipped Round 1 file
`survey/computational/certs_r10_c13.txt` has exponent-sum determinant of absolute value 1, hence
a nonzero matrix, and none is cocommutative (checks D2 to D4). Starting from AK(3) and applying
24 random AC and stable moves, the exponent-sum matrix stays square of determinant `+-1` and
never becomes zero (check D6). The rank-0 exception of Theorem 1 is checked directly: the
standard rank-2 tuple destabilises to the empty tuple at rank 0 in two moves, and the empty
tuple has no relator to evaluate a winding polynomial on (check D7). [Computation] The longer
rerun described in Section 6 produces 3697 certificate rows at total length at most 11, and the
independent checker replays all of them.

### 2.3 The general form degenerates to the exponent-sum matrix (Theorem 2)

Barmak defines a second, general invariant. In Section 8 of arXiv:1904.10072 he writes: "We can
call the abelianization map W: N(R) -> N(R)/N(R)' the winding invariant of P by analogy with
the original case", where `N(R)` is the normal closure of the relators in the free group, and
"The winding invariant satisfies then W(uwu^-1) = ubar W(w) for any w in N(R) and u in F(X)",
with `ubar` the image in `G = F(X)/N(R)`. [Cited]

**Theorem 2 (Argument).** Let `n >= 1` and let `P` be a balanced presentation of the trivial
group in `n` generators. For this presentation the general winding invariant is the
abelianisation map `W: F_n -> Z^n`, and the tuple `(W(r_1),...,W(r_n))` is the exponent-sum
matrix `M(P)`. Under the three AC moves the tuple changes by `GL_n(Z)` row operations, and on
the class of balanced presentations of the trivial group the orbit is the single orbit of the
identity matrix.

*Proof.* For a presentation of the trivial group the normal closure is `N(R) = F_n`, so
`N(R)/N(R)' = Z^n` and the presented group is `G = 1`, whose group ring is `Z`. The action of
`G` on `Z^n` is trivial, and `W` is the abelianisation of `F_n`, which sends `w` to its
exponent-sum vector. So the tuple of images of the relators is `M(P)`.

For the transformation law, inversion negates one row, multiplication of relators adds one row
to another, and conjugation changes nothing: in the equivariance formula the element `ubar`
lies in `Z[G] = Z` and equals the ring element 1, because `G` is trivial, so
`W(u w u^-1) = W(w)`. Thus the `GL_n(Z)` orbit of the tuple is an invariant. Since `P`
presents the trivial group its abelianisation is trivial, so `M(P)` is unimodular
(Proposition 5 of [survey/invariants.md](../survey/invariants.md)), and every unimodular
integer matrix is `GL_n(Z)`-equivalent to the identity. `Box`

Theorem 2 sharpens the corresponding sentence of Section 9 of
[survey/invariants.md](../survey/invariants.md), which says that the coefficient ring becomes
`Z` and that `Z` is Euclidean. That sentence is correct and I confirm it: `Z[G] = Z` for
`G = 1`. The sharper statement is that the invariant can be identified with a matrix the
survey already computes, and that its value on the class is the identity up to row operations,
so the general winding invariant contributes no more than the exponent-sum matrix.

### 2.4 Small cases, computed

`check_idea.py` computes `Lambda` for every cocommutative balanced rank-2 presentation with
total relator length at most 12, up to relator order, cyclic rotation and inversion. There are
143 of them (check E1), and all have abelianisation `Z^2` (check E2). Canonical relators in
`F_2'` number 0, 1, 10, 62 and 436 at lengths 2, 4, 6, 8 and 10 respectively, so the class is
already thin at this size.

The ideal generated by the entries of `Lambda` is a `GE_m(R)`-invariant, hence a Q-invariant.
On 140 of the 143 presentations it is the unit ideal, certified by an explicit certificate
(check E3). On the remaining 3 both entries of `Lambda` lie in the proper ideal
`(1+X, 1+Y)`, because each entry vanishes at `X = -1` or at `Y = -1`, and
`R/(1+X,1+Y)` is `Z` under evaluation at `(-1,-1)` (check E4). The three are

```
r1 = YYXyyx, r2 = YYXyyx   Lambda = (-X^-1Y^-2-X^-1Y^-1, -X^-1Y^-2-X^-1Y^-1)
r1 = YYXyyx, r2 = YXXyxx   Lambda = (-X^-1Y^-2-X^-1Y^-1, -X^-2Y^-1-X^-1Y^-1)
r1 = YXXyxx, r2 = YXXyxx   Lambda = (-X^-2Y^-1-X^-1Y^-1, -X^-2Y^-1-X^-1Y^-1)
```

So the ideal invariant is not constant on the small cocommutative class. It still cannot
separate Barmak's pair of presentations of `Z x Z`, whose two ideals are both the unit ideal
(checks C9 and C10). The decisive separation in that example happens at the level of
`GL_2(R)/GE_2(R)`, using Evans' matrix (checks C7 and C8), which is the point recorded in
Section 8.

### 2.5 The exact point of failure

Proposal (i) fails at the hypothesis that the relators lie in the commutator subgroup. On the
class of interest the exponent-sum matrix is unimodular, and Theorem 1 shows that unimodularity
is incompatible with cocommutativity at every positive rank and under stabilisation. The one
exception recorded in the remark after Theorem 1 is the empty presentation at rank 0, which has
no relators, and a winding polynomial needs a relator. The general form of the invariant escapes
the hypothesis and then loses all content, by Theorem 2.

A variant that reached the class of interest would need a function of the relator tuple that is
invariant under conjugation of one relator by an arbitrary word, is computable, and is defined
when the exponent-sum matrix is unimodular. The conjugation move destroys the subgroup
generated by the relators (Section 8 of [survey/invariants.md](../survey/invariants.md)), and
the general form of the invariant is a function of the normal closure and its abelianisation,
so the surviving structure is only the word-level combinatorics. I found no proposal of that
kind in the literature I read, and Theorem 2 shows that the winding programme in both of its
published forms cannot supply one.

## 3. Proposal (ii): the Wall 3-versus-4 gap

### 3.1 What the gap is, from the sources

The relevant definitions are standard. An elementary expansion of an `n`-complex attaches a
pair of cells of dimensions `n-1` and `n` with the smaller cell a free face, an elementary
collapse is the inverse, a formal deformation is a finite sequence of elementary expansions and
collapses, and an `n`-deformation is a formal deformation in which every cell used has
dimension at most `n`. [Argument, definition]

Myasnikov, Myasnikov and Shpilrain state the relation to the conjecture in the introduction of
[MMS02](https://web.stevens.edu/algebraic/alexeim/Publications/AC%20Conjecture/ac1.pdf):
"It is well-known (see e.g. [27] for details) that (stably) AC-equivalent sets of relators give
rise to simple-homotopy equivalent complexes, since the transformations (AC1-AC5) applied to
defining relators of the fundamental group of a 2-complex, are mimicked by elementary
expansions and collapses applied to this 2-complex. The point however is that those elementary
expansions/collapses that mimic the AC-transformations, only involve cells of dimension 3 or
lower, whereas to establish a simple-homotopy equivalence of two 2-complexes, one is allowed to
use cells of arbitrary dimensions. Now, it is known that any two 2-complexes with the trivial
fundamental group (i.e., 2-complexes contractible to a point) are simple-homotopy equivalent,
and by a result of Whitehead [26], one does not need to use cells of dimension higher than 4 to
establish a simple-homotopy equivalence in that situation. So, the point of the (topological)
Andrews-Curtis conjecture is that one does not actually have to use cells of dimension higher
than 3 when treating contractible 2-complexes. This is equivalent to the weak Andrews-Curtis
conjecture above (see [27])." [Cited] In that quotation [27] is P. Wright, Group presentations
and formal deformations, Trans. Amer. Math. Soc. 208 (1975) 161-169, and [26] is J. H. C.
Whitehead, Simplicial spaces, nuclei, and m-groups, Proc. London Math. Soc. 45 (1939) 243-327.
Whitehead's Theorem 21 in that paper gives a deformation of order at most `n+2` between
complexes of dimension at most `n` that are homotopy equivalent and satisfy his condition on
the fundamental group, which for `n = 2` is the bound of four dimensions used above.

Barmak states the same dictionary in the introduction of [Bar25]: "The weak version of the
Andrews-Curtis conjecture states that in the same situation the two presentations are just
Q**-equivalent. The latter is equivalent to the statement that any contractible finite
2-dimensional CW-complex 3-deforms to a point. The so-called generalized Andrews-Curtis
conjecture [13, Section 4.1] says that any two presentations P and Q with simple homotopy
equivalent standard complexes K_P and K_Q are Q**-equivalent. These three conjectures are
open." [Cited]

So the stable move set corresponds to 3-deformations, while simple homotopy equivalence of
2-complexes corresponds to 4-deformations. The general form of the correspondence between
Q**-equivalence and 3-deformation equivalence is recorded in Section 3 of
[survey/stable-ac.md](../survey/stable-ac.md), which attributes it to Wright. The gap between
the two move sets is a conjecture in two forms, the weak one for contractible complexes and the
generalized one for all complexes.

### 3.2 The quantity exists exactly when the gap is realised (Theorem 4)

**Theorem 4 (Argument).** Let `C` be a set of finite 2-complexes, any two of which are simple
homotopy equivalent, so that any two members are 4-deformation equivalent. Then the following
two statements are equivalent. The first is the existence of a separating quantity, and the
second is the existence of a pair that realises the gap.

(a) There is a function `Q` from `C` to some set such that `Q(K) = Q(L)` whenever `K` and `L`
in `C` are 3-deformation equivalent, and `Q(K)` is different from `Q(L)` for some pair in `C`
that is 4-deformation equivalent.

(b) `C` contains two complexes that are not 3-deformation equivalent.

*Proof.* Assume (b) and pick `K_0` and `L_0` in `C` that are not 3-deformation equivalent. Let
`Q` be the indicator function of the 3-deformation class of `K_0` inside `C`. It is preserved by
3-deformations by construction, and it takes different values on `K_0` and `L_0`, which are
4-deformation equivalent by the hypothesis on `C`. So (a) holds.

Assume (a) and suppose that all pairs in `C` are 3-deformation equivalent. Then `Q` is
constant, since it is preserved by 3-deformations, so no pair of members of `C` can differ in
`Q`, and the second half of (a) fails. So (b) holds. `Box`

The hypothesis that any two members of `C` are 4-deformation equivalent holds for any class of
pairwise simple homotopy equivalent finite 2-complexes, by the Whitehead bound quoted in
Section 3.1, and it holds in particular for the class of contractible 2-complexes, because
`Wh(1) = 0` makes every homotopy equivalence to a point simple. [Cited for `Wh(1) = 0`] The
proof of Theorem 4 is short, and its content is the identification of the hypothesis with the
standard literature statement that simple homotopy equivalent 2-complexes are 4-deformation
equivalent. The two halves of the equivalence are the two directions in which that
identification is used.

**Corollary 5 (Argument).** Let `C` be the class of finite contractible 2-complexes. A function
as in (a) exists if and only if the stable Andrews-Curtis conjecture fails.

*Proof.* All members of `C` are homotopy equivalent to a point, and `Wh(1) = 0`, so all members
are simple homotopy equivalent and hence 4-deformation equivalent by the Whitehead bound.
Deformation equivalence is transitive, because a formal deformation can be run backwards. So
condition (b) of Theorem 4 holds for `C` exactly when some member of `C` is not 3-deformation
equivalent to the point, and that is the negation of the stable conjecture. A function that factors
through a 4-deformation invariant is constant on `C`, since `C` is a single 4-deformation
class, so it cannot satisfy the second half of condition (a). `Box`

**Corollary 6 (Argument and Computation).** Let `C` be the class of standard complexes of
balanced rank-2 presentations of the trivial group with total relator length at most 11. No
function as in (a) exists on `C`.

*Proof.* Every such presentation is AC-trivial. The census enumerates one representative per
class under relator order, cyclic rotation and relator inversion, which are themselves generated
by the AC moves together with the renaming of relators, and it certifies every representative
that its abelianisation does not exclude. So every member of `C` is 3-deformation equivalent to
the standard complex of the standard tuple, which is a point, the class `C` has a single
3-deformation class, and Theorem 4 applies. The input is the exhaustive census of
[survey/computational.md](../survey/computational.md): 26182 canonical balanced rank-2
presentations at total length at most 11, of which 22485 have an exponent-sum determinant that
is not `+-1` and hence do not present the trivial group, 3697 are AC-trivial with a certificate
that replays, and 0 are unresolved. I reran the census and the independent certificate checker
in this direction, with the commands and output in Section 6. `Box`

Corollary 6 is the precise form of the statement that the proposed quantity cannot be found by
looking at small examples. Any candidate must involve a presentation of total relator length at
least 12. By Corollary 5 a complex in that class would be a counterexample to the stable
conjecture.

### 3.3 The candidate pair, and why it does not realise the gap

Barmak constructed a pair of presentations of `Z x Z` with simple homotopy equivalent standard
complexes. In the published version [Bar25] the pair is
`P = <x,y | [x,y], 1>` and `Q = <x,y | [x,[x,y^-1]]^2 y[y^-1,x]y^-1, [x,[[y^-1,x],x]]>`, and
Theorem 5 reads "The standard complexes K_P and K_Q are simple homotopy equivalent, while P and
Q are not Q*-equivalent. Moreover, the normal closures of both relator sets coincide." [Cited]

The published version also says, on its second page, "After the first version of this paper was
finished, X Fernandez [10] proved that the presentations P and Q are in fact Q**-equivalent",
where [10] is Fernandez, Morse theory for group presentations, Trans. Amer. Math. Soc. 377
(2024) 2495-2523. [Cited; the Fernandez paper was not read, see Section 8]

So the most prominent known pair does not realise the gap between 3-deformations and
4-deformations: it is 4-deformation equivalent, by simple homotopy equivalence and the
Whitehead bound, and it is 3-deformation equivalent by Fernandez's result. The generalized
Andrews-Curtis conjecture remains open, and no pair of simple homotopy equivalent 2-complexes
that are not 3-deformation equivalent is known to me from the sources I read.

`check_idea.py` reproduces the algebraic part of Barmak's argument. It recomputes both winding
vectors and matches the values printed in the paper (checks C4 and C5), it verifies that Evans'
matrix has determinant 1 (check C7), it verifies that its first column is `Lambda(Q)^t` (check
C8), it reproduces the two Fox matrices printed in the paper (checks C11 and C12), and it
verifies the chain condition `d'_2 M^t = d_2` (check C13). [Computation] Those checks certify the
non-Q*-equivalence argument up to Evans' theorem, which I did not read.

The reason this pair cannot be used for proposal (ii) is general. Barmak's `Lambda` is a
Q*-invariant, and stabilisation, move (v), adds a generator `x_(n+1)` and the relator
`x_(n+1)`. That relator has exponent sum 1 in the new generator, so the stabilised presentation
is not cocommutative and `Lambda` is not defined on it. A Q*-invariant is therefore blind to
Q**-classes, and Barmak's own pair is the explicit witness: Barmak proves that it is
Q*-inequivalent, and Fernandez's theorem makes it Q**-equivalent. Any invariant that could
serve proposal (ii) has to be a Q**-invariant, and no such invariant of winding type exists.
[Argument]

### 3.4 Candidates tested, each with its exact failure point

| candidate | what it would have to do | exact point where it fails |
| --- | --- | --- |
| `pi_1`, `pi_2`, relation modules, the Fox matrix class, twisted homology, the algebraic 2-type | separate 3-deformation classes | all are homotopy invariants, so every formal deformation preserves them and they are constant on the contractible class; Theorem 4 |
| the winding invariant `Lambda` | be defined on the class | Theorem 1: no presentation of the trivial group is cocommutative |
| `Lambda` read as a stable invariant | survive stabilisation | move (v) adds a generator as a relator, so cocommutativity is destroyed and `Lambda` is undefined; a Q*-invariant cannot see a Q**-class (Section 3.3) |
| the general winding invariant `W` | have content on the class | Theorem 2: it is the exponent-sum matrix there, with one value up to `GL_n(Z)` |
| test-group invariants, meaning homomorphisms to a fixed group `G*` | distinguish Q**-classes | Barmak quotes Hog-Angeloni and Metzler, Theorems 2.3 and 2.4, for the statement that "solvable groups are not useful as test groups to distinguish Q**-equivalence", which kills every solvable `G*`; I found no theorem that excludes a non-solvable `G*`, so this row is a partial kill with exactly the scope of the quoted theorems |
| minimal cell counts in the 3-deformation class | be 3-invariant and 4-sensitive | it is 3-invariant by construction, and on the contractible class it equals the stable conjecture itself, so this restates the question; its 4-invariant version is constant because the 4-deformation class of a contractible complex is the point |
| collapsibility, and Zeeman positivity meaning that `K x I` is collapsible | be preserved by 3-deformations and destroyed by a 4-deformation | collapsibility is already destroyed by a 2-collapse: the disk `e^0` union `e^1` union `e^2` is collapsible and collapses to the circle `e^0` union `e^1`, which is not. A three-dimensional example is in Remark 8. Whether Zeeman positivity is preserved by 3-deformations is open, and Lemma 7 below gives only one direction |

**Lemma 7 (Argument).** Let `K` be a 2-complex and let `K'` be obtained from `K` by one
elementary 3-expansion. Then `K' x I` collapses to `K x I`, and if `K x I` is collapsible then
`K' x I` is collapsible.

*Proof.* An elementary 3-expansion attaches a 3-cell along a 2-cell that is a free face. Taking
the product with `I` produces the corresponding pair of a 3-cell and a 4-cell in `K' x I`, with
the 3-cell again a free face, so `K' x I` collapses to `K x I` in one elementary collapse. If
`K x I` collapses to a point then so does `K' x I`. `Box`

**Remark 8 (Argument).** Collapsibility is not preserved by elementary 3-collapses, so it is not
a 3-deformation invariant. Take the 3-ball with the three-cell decomposition `e^0`, `e^2`, `e^3`:
the 2-cell is attached to the vertex by the constant map, so `e^0` union `e^2` is a 2-sphere, and
the 3-cell is attached so that one of its boundary hemispheres is a free face mapping
homeomorphically onto the 2-cell and the other hemisphere maps to the vertex. The space is
homeomorphic to the 3-ball, which is collapsible, and the elementary 3-collapse that removes the
pair `(e^2, e^3)` leaves the 2-sphere, which is not collapsible. So a 3-deformation can destroy
collapsibility in one step.

COORDINATOR CORRECTION, 2026-11-05, from the Round 3 direction
directions/zeeman-positivity/zeeman-positivity.md (member m6, swarm smw2opo0o),
checked by the coordinator. Three changes to this file. First, the example in
Remark 8 is wrong: the complex e^0 union e^2 union e^3 has Euler characteristic
1, the 2-sphere has characteristic 2, and an elementary collapse preserves the
characteristic, so no collapse of that complex ends at the 2-sphere. The
coordinator endorsed the example in the Round 2 verdict and records that as his
own error. Second, the conclusion of Remark 8 survives in the sequence form: a
3-collapse can destroy collapsibility, with the witness the dunce cap D, because
D x I is collapsible (Zeeman, via Kupers Example 2.3), D x I collapses to D by
the prism argument, and D is not collapsible. Third, the sentence after Remark 8
that proposes the backward direction as a route to the equivalence of Zeeman's
conjecture with the stable conjecture is mis-stated: propagation across an
elementary 3-collapse in the direction this file asked about is Lemma 7 itself,
and the genuinely missing statement is downward propagation (K x I collapsible
implies L x I collapsible for an elementary collapse K to L), which together
with the stable conjecture gives Zeeman's conjecture and whose failure with L a
2-polyhedron would refute Zeeman's conjecture. Lemma 7's proof also needs the
sentence identifying the new 4-cell with the ball D^3 x I rather than the
product cell structure; see the Round 3 file, Section 5.

Lemma 7 says that Zeeman positivity propagates along the expansion half of a 3-deformation. If
it also propagated backwards across an elementary 3-collapse, then Zeeman's conjecture would be
equivalent to the stable Andrews-Curtis conjecture on the contractible class, because
stability would give Zeeman positivity of every contractible `K` from that of a point. I did not
settle the backward direction. I record it as an open sub-question.

### 3.5 Verdict on proposal (ii)

Killed as a search, with three exact statements. Theorem 4 shows that the existence of the
quantity is the same statement as the existence of a pair of simple homotopy equivalent
2-complexes that are not 3-deformation equivalent. Corollary 5 shows that on the contractible
class this is the stable conjecture. Corollary 6 shows that no example exists at total relator
length at most 11. The one published candidate pair is 3-deformation equivalent, by
Fernandez's result as reported by Barmak, and the winding invariant cannot be pushed to the
stable move set because stabilisation destroys its hypothesis.

## 4. What this direction recommends for Round 3

The three proposals below are in the order I would rank them for a Round 3 allocation of one
member each. Each one is a self-contained job with a checkable deliverable.

1. **Settle the Q-double-star question for the smallest pair that is still open, by bounded
   search.**
   Fernandez's method is a combinatorial algorithm for Q**-transformations, and it is a
   certificate-producing search. Barmak's pair is settled, so the next natural target is a small
   pair of simple homotopy equivalent standard complexes with the same group where
   Q**-equivalence is not known. A bounded search that
   fails is a bounded negative in the style of Round 1, and a success adds a second
   confirmation of the generalized conjecture on a small case. This is a computation with
   certificates, so it fits the Round 1 toolkit directly.

2. **Decide whether Zeeman positivity is a 3-deformation invariant.** Lemma 7 gives one
   direction. The backward direction across an elementary 3-collapse is the whole content,
   and a positive answer would make Zeeman's conjecture and the stable conjecture equivalent
   on the contractible class, which is a sharper statement than the known one-way implication.
   A counterexample would need a contractible 2-complex `K` with `K x I` collapsible and a
   3-collapse of `K` whose product with `I` is not collapsible, and that is a concrete
   construction target.

3. **Formalize Theorem 1 in Lean.** The Round 1 Lean file `toolkit/lean/AC.lean` already
   contains the invariance of the exponent-sum span under the three moves. Theorem 1 needs in
   addition that a word in the commutator subgroup has zero exponent sums, and that a
   unimodular integer matrix is nonzero. Both are short, and the result would be the first
   machine-checked obstruction statement of the form "this published invariant cannot be
   applied to the class of interest".

## 5. What this direction did not do

I did not attempt to extend the winding invariant to rank 3 or to non-cocommutative
presentations beyond the general form of Section 2.3. I did not read Evans' paper, so the
non-membership of his matrix in `GE_2(R)` is a quotation. I did not read Fernandez's paper, so
the Q**-equivalence of Barmak's pair is a quotation from Barmak's published version. I did not
settle whether Zeeman positivity is preserved by 3-deformations. I did not prove or disprove any
form of the Andrews-Curtis conjecture. Theorem 4 is a statement about invariants, and it says
nothing about the truth of the conjecture.

## 6. Reproduction

The self check runs in about three seconds and prints 34 PASS lines. It needs only python3,
with no third-party package.

```
cd directions/invariant-ideas
python3 check_idea.py
```

The run ends with the following two lines. The file `check_idea.out` in this directory holds
the whole run, with one PASS line per check.

```
--------------------------------------------------------------------------
ALL CHECKS PASSED
```

The census used in Corollary 6 was rerun in this direction, from the Round 1 code. The two
commands and their key output follow.

```
cd survey/computational
python3 census.py 11 13 ../../.ultramath/smw2i9i4j/m7/.scratch/certs11.txt
python3 check_certs.py ../../.ultramath/smw2i9i4j/m7/.scratch/certs11.txt
```

The third argument of `census.py` is the path of the certificate file it writes, and any
writable path works. That file is regenerated on every run, so it is not part of the
deliverable.

The first command took 6 minutes 42 seconds on this VM and reported
`canonical presentations with total length <= 11: 26182`, `nontrivial, exponent-sum
determinant not +-1 : 22485`, `AC-trivial, certificate built and replayed : 3697`,
`unresolved : 0`, `PASS every canonical presentation at total length <= 11 is resolved`, and
`OVERALL PASS`. The second reported `checked 3697 certificates ...: 0 failed`, `RESULT PASS`.

Note on the Round 1 record: item 4 of [REPORT.md](../../REPORT.md) pairs the figure 26182 with
the command `python3 census.py 10 13 certs_r10_c13.txt` and with 1157 certificates. I reran
both settings. The setting `10 13` gives 9576 canonical presentations at total length at most
10, 8419 nontrivial by determinant, 1157 certificates and 0 unresolved, and the setting `11 13`
gives the 26182 and 3697 figures above. Both runs report PASS. The certificate file shipped in
Round 1, `survey/computational/certs_r10_c13.txt`, has 1157 rows and matches the `10 13`
setting. This is a documentation slip in REPORT.md and not an error in the census.

## 7. Sources

Each source was read at the address given, on 2026-11-04. Three entries record sources that I
did not read in full, and every claim that depends on one of them is marked in the text.

- J. A. Barmak, *The winding invariant*, arXiv:1904.10072 version 2 (submitted 22 April 2019,
  revised 27 August 2019), 60 pages. Read: the abstract, Definition 2, Lemma 3, Section 7
  (cocommutative presentations), and the Section 8 passage on the general winding invariant.
  Used for the definition, for Lemma 3, for Remark 4 and for the general form.
- J. A. Barmak, *A counterexample to a strong version of the Andrews-Curtis conjecture*,
  arXiv:1806.11493 version 1 (29 June 2018), 7 pages. Read in full. Used for Definition 2,
  Lemma 3, Remark 4, Evans' matrix as Theorem 1, Theorem 5, Lemma 6 and the proof of Theorem 5.
- J. A. Barmak, *An exotic presentation of Z x Z and the Andrews-Curtis conjecture*,
  Algebr. Geom. Topol. 25 (2025) 345-355, DOI 10.2140/agt.2025.25.345. Read from the publisher's
  open access PDF. Used for the Q, Q*, Q** dictionary, for the statement that the three
  conjectures are open, for the quotation of Fernandez's result, and for the reference list.
- A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, *On the Andrews-Curtis equivalence*,
  Contemp. Math. 296 (2002) 183-198, DOI 10.1090/conm/296/05074. Read from the author's PDF at
  web.stevens.edu. Used for the passage on 3-cells and 4-cells and for the topological form of
  the conjecture. I did not check the pagination of the printed version.
- X. Fernandez, *Morse theory for group presentations*, Trans. Amer. Math. Soc. 377 (2024)
  2495-2523, arXiv:1912.00115. Only the abstract was read, and the theorem that Barmak's pair is
  Q**-equivalent is quoted from Barmak's paper.
- M. J. Evans, *Primitive elements in the free metabelian group of rank 3*, J. Algebra 220 (1999)
  475-491. Not read. Evans' matrix and its non-membership in `GE_2(R)` are quoted from Theorem 1
  of arXiv:1806.11493.
- H. Bass, A. Heller and R. G. Swan, *The Whitehead group of a polynomial extension*, Inst. Hautes
  Etudes Sci. Publ. Math. 22 (1964) 61-79. Not read. `Wh(Z x Z) = 0` is quoted from
  arXiv:1806.11493, and `Wh(1) = 0` is the classical computation of `K_1(Z)`.
- P. Wright, *Group presentations and formal deformations*, Trans. Amer. Math. Soc. 208 (1975)
  161-169, and J. H. C. Whitehead, *Simplicial spaces, nuclei, and m-groups*, Proc. London Math.
  Soc. 45 (1939) 243-327. Neither was read. Both are used through the quotation in [MMS02] and
  through the reference list there, which identifies them as that paper's [27] and [26].

## 8. What I could not verify

- Evans' Theorem C, and therefore the non-membership of his matrix in `GE_2(R)`. Checks C7 and
  C8 verify that the matrix has determinant 1 and that its first column is `Lambda(Q)^t`. The
  step "outside `GE_2(R)`" is quoted from [Bar18] Theorem 1 and [Bar25].
- The Q**-equivalence of Barmak's pair in Fernandez's paper. I read Barmak's published statement
  of it and the abstract of Fernandez's paper. I did not read the proof.
- Whether the ideal generated by `Lambda` for the three presentations of Section 2.4 is exactly
  the intersection of `(1+X,1+Y)` with the ideal itself. I verified that the ideal is contained
  in the proper ideal `(1+X,1+Y)`, which is enough to show that it is not the unit ideal.
- Whether Zeeman positivity is preserved by 3-deformations. Lemma 7 proves the expansion
  direction only.
- The exact hypotheses of Wall's 1966 theorem. I use the statement in the introduction of
  [MMS02], which attributes to Whitehead the bound of four dimensions for simple homotopy
  equivalences between 2-complexes, and the reading of Wall's theorem in
  [survey/stable-ac.md](../survey/stable-ac.md) Section 3.
- Whether any invariant of the kind proposal (ii) asks for exists. Theorem 4 shows that the
  question is equivalent to a known open problem, and I claim no more than that.
