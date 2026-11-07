# The two stabilization move sets for balanced presentations of the trivial group

Direction F2 of swarm smw2opo0o, member m2. Round 3 deliverable.

Rounds 1 and 2 recorded a definitional hazard. The 2002 paper of Myasnikov, Myasnikov and
Shpilrain and the 2024 papers of Shehper et al. and of Fagan, Qiu and Wang both use the phrase
"stably AC-equivalent", and the round-2 note in `survey/stable-ak3-status.md` section 3 says that
their move sets "differ in form, since the MMS move changes the deficiency while the Shehper move
keeps the presentation balanced", and that neither source proves the two relations equal. This
file settles the question. The short answer is that the two published relations are the same
relation, on every class and not only on presentations of the trivial group: both (AC4) moves add a
new generator together with the relator equal to it, so the two move sets are the same move set.
The reading of the 2002 move which changes the deficiency is not supported by the 2002 text, and I
give four independent passages of that paper against it. Two further readings need to be compared.
The reading that adjoins a free generator and no relator gives a genuinely different relation, and
that relation is provably useless for the Andrews-Curtis problem, because adjoining free generators
does not change AC-equivalence at all (Theorem 4, machine-checked in Lean). The reading that uses
the general Tietze generator addition, which is what the 2002 paper actually does inside one proof,
gives the same relation as the printed (AC4) on presentations of the trivial group (Theorem 3) and
a strictly larger relation on presentations of nontrivial groups (Theorem 5). Since the stable
Andrews-Curtis conjecture is stated on presentations of the trivial group, the only reading that
differs from the printed move set on that class is the free-generator reading, and that one is
redundant.

Nothing in this file proves or disproves the Andrews-Curtis conjecture, its stable form, or any
statement about 2-complexes. Nothing in this file changes the stable status of AK(3), which stays
unresolved. The new statements are about the move sets themselves, and each one is either a
theorem written out here or a computation in `survey/stabilization-moves-check.py`, with the
retraction theorem also checked in `survey/stabilization-moves.lean`.

## 0. Labels

* `[V-source]` the statement was read in a primary source that I fetched and cite with an
  identifier, and the quotation below is verbatim from that fetch.
* `[V-compute]` checked by a deterministic computation in `survey/stabilization-moves-check.py`,
  rerunnable with `python3 survey/stabilization-moves-check.py`, which prints one PASS line per
  check and ends with `all checks passed`.
* `[V-lean]` checked by the Lean 4 file `survey/stabilization-moves.lean`, rerunnable with
  `lean survey/stabilization-moves.lean`, with the axioms of each theorem printed at the end of
  that file.
* `[Argument]` my own deduction from labelled statements, written out in full.
* `[Open]` I know of no proof and no disproof.
* `[Unverified]` I could not check it, and nothing here rests on it.

## 1. The four candidate relations, and the answer

Fix a free group `F_n = F(x_1,...,x_n)` and a tuple `Y = (y_1,...,y_m)` of relators in it. Write
`(n, m)` for a presentation with `n` generators and `m` relators, and call `m - n` its deficiency.
The first three of the following moves are the ones the sources use, and the fourth is the one that
the direction brief ascribes to the 2002 paper.

1. **Unstable moves.** (AC1) invert a relator, (AC2) multiply a relator on the right by another,
   (AC3) conjugate a relator. All of them preserve `(n, m)` and the normal closure of `Y` in `F_n`.
2. **Stabilization, balance-preserving.** Add a new generator `x_{n+1}` together with the relator
   `x_{n+1}`; the inverse move deletes such a pair. The pair `(n, m)` changes by `(+1, +1)` or by
   `(-1, -1)`, so the deficiency `m - n` is unchanged. This is (AC4)/(AC5) in the 2002 source under the
   reading defended in section 3, and it is (AC4)/(AC5) in the 2024 sources verbatim.
3. **Stabilization, general Tietze form.** Add a new generator `y` together with a relator `y w`,
   where `w` is any word in the old generators. The deficiency is unchanged, and the move is a
   Tietze transformation. This is how the 2002 source actually uses its (AC4) inside the proof of
   its Proposition 1.2.
4. **Free-generator move.** Adjoin a new generator and no relator. The deficiency changes by `-1`
   and the group presented changes from `G` to `G * Z`. This is the move that the direction brief
   ascribes to the 2002 paper.

The answer to the direction's question is the following.

* **Reading 2 against the 2024 sources: the relations are the same relation, by definition.**
  `[V-source]` Both (AC4) moves add a new generator together with the relator equal to it, so the
  two move sets are the same move set, and there is no equality to prove. `[V-compute]` Check [2]
  of the script compares the two definitions as functions on presentations on 100 seeded instances
  and finds identical output, and check [2] also verifies that both leave the deficiency and the
  exponent-sum matrix in the same shape.
* **Reading 3 against the 2024 sources: the relations are the same on presentations of the
  trivial group, and different on presentations of nontrivial groups.** `[Argument]` Theorem 3
  below derives the general Tietze form from (AC4) plus (AC1)-(AC3) whenever the presentation is of
  the trivial group, and that hypothesis holds at every step of a derivation that starts and ends at
  presentations of the trivial group, because every one of the moves preserves the presented group.
  Theorem 5 below exhibits a pair of presentations of `Z`, related by one general Tietze generator
  addition, which is separated by an invariant of the (AC1)-(AC5) relation, so the more generous
  reading is strictly larger off the trivial group. `[V-compute]` Checks [7] and [12]. This is the
  one place where the choice of move set has content, and the class the stable Andrews-Curtis
  conjecture is stated on is the side where there is none.
* **Reading 4 against the 2024 sources: the relations differ.** `[Argument]` The deficiency is
  invariant under (AC1)-(AC5) and changes under reading 4, so the pair
  `<x_1 | x_1> -> <x_1,x_2 | x_1>` is in the relation generated by reading 4 and in neither of the
  others. `[V-compute]` Checks [3], [4], [5]. This pair does not separate the two published move
  sets from each other; it separates reading 4 from both of them.
* **Reading 4 is also redundant**, which is the reason it cannot be what the 2002 paper meant.
  `[V-lean]` Theorem 4: if two tuples in `F_n` become AC-equivalent in `F_{n+k}` after `k` free
  letters are adjoined, they were already AC-equivalent in `F_n`. So under reading 4 the "weak"
  Andrews-Curtis conjecture of the 2002 paper would be the ordinary conjecture, which contradicts
  that paper's own presentation of the two conjectures as different, and its own description of
  the weak one as the one of greater interest in topology.

Section 8 records the exact place where the derivation in Theorem 3 stops when the group is not
trivial, proves that no derivation can be repaired there, and draws the consequence for the
topological move list. Section 12 lists what I did not verify.

## 2. The definitions as printed

### 2.1 Myasnikov, Myasnikov and Shpilrain 2002

Source: A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, *On the Andrews-Curtis equivalence*,
Contemporary Mathematics 296 (2002) 183-198, DOI 10.1090/conm/296/05074, author's LaTeX source
`arXiv:math/0302080v1` (file `ac.tex`, 1157 lines), and the author's posted PDF at
`https://shpilrain.ccny.cuny.edu/ac.pdf`. I fetched both files on 2026-11-04 and verified the arXiv
record live: title, three authors, submission date 7 February 2003, journal reference
"Contemp. Math., Amer. Math. Soc. 296 (2002), 183-198". The line numbers below are line numbers of
`ac.tex` as posted.

The setting, `[V-source, ac.tex lines 95-99]`:

> Let F = F_n be the free group of a finite rank n ≥ 2 with a set X = {x_1, ..., x_n} of free
> generators. Let Y = {y_1, ..., y_m} be an arbitrary finite tuple of elements of the group F.

The three elementary moves, `[V-source, ac.tex lines 103-114]`:

> (AC1) y_i is replaced by y_i y_j for some j ≠ i;
> (AC2) y_i is replaced by y_i^{-1};
> (AC3) y_i is replaced by g y_i g^{-1} for some g ∈ F.

The two stabilization moves, `[V-source, ac.tex lines 142-146]`:

> (AC4) Y is extended to {y_1, ..., y_m, x_ν}, where x_ν is a new free generator (i.e.,
> y_1, ..., y_m do not depend on x_ν).
> (AC5) the converse of (AC4).

The definition of the stable relation, `[V-source, ac.tex lines 148-151]`:

> If Ỹ can be obtained from Y by means of transformations (AC1--AC5), we say that Ỹ is *stably*
> AC-equivalent to Y.

The weak conjecture, `[V-source, ac.tex lines 153-157]`:

> (The weak Andrews-Curtis conjecture.) For a tuple Y = {y_1, ..., y_n}, one has ⟨Y⟩^F = F if and
> only if Y is stably AC-equivalent to X = {x_1, ..., x_n}.

### 2.2 Shehper et al. 2024 and Fagan, Qiu and Wang 2025

Source: A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu,
P. Kucharski, Z. Wang and S. Gukov, *What makes math problems hard for reinforcement learning: a
case study*, `arXiv:2408.15332`, version 2 of 11 February 2025, file `sec/stable.tex`. I fetched
the source of version 2 on 2026-11-04.

The moves, `[V-source, sec/stable.tex, the enumerate block of section 2.1]`:

> (AC4) Include a new generator and a trivial relator, i.e. replace
> ⟨x_1, ..., x_n | r_1, ..., r_n⟩ by ⟨x_1, ..., x_n, x_{n+1} | r_1, ..., r_n, x_{n+1}⟩.
> (AC5) Remove a trivial relator and the corresponding generator, i.e. the inverse of (AC4).

and the three unstable moves, `[V-source, sec/conjecture.tex, the enumerate block of section 1]`:

> (AC1) Substitute some r_i by r_i r_j for i ≠ j.
> (AC2) Replace some r_i by r_i^{-1}.
> (AC3) Change some r_i to g r_i g^{-1} where g is a generator or its inverse.

Source for the third statement of the same definition: L. Fagan, Y. Qiu and Z. Wang, *Stable
Andrews-Curtis conjecture via fake surfaces and Zeeman conjecture*, `arXiv:2412.12293`, version of
9 January 2026, file `main.tex`, `[V-source, main.tex lines 306-311]`:

> (AC4) Add a new generator x_{n+1} and trivial relator r_{n+1} = x_{n+1}
> (AC5) Remove a trivial relator and the generator, i.e., the inverse of (AC4)

### 2.3 What the two lists actually differ by

`[Argument]` Comparing the three quotations, the differences are these.

1. The order in which the unstable moves are numbered. Nothing depends on the numbering.
2. The 2002 paper writes (AC1) as `y_i -> y_i y_j` and the 2024 papers write it as
   `r_i -> r_i r_j` as well, so here there is no difference at all.
3. The 2002 paper allows conjugation by an arbitrary element of `F_n` in (AC3), and the 2024
   papers allow conjugation by a single generator or its inverse. Single-letter conjugations
   generate conjugations by words, so the two relations on tuples are the same; Lemma 1 below
   writes the identity out and check [1] of the script verifies it step by step.
4. The 2002 paper's (AC4) is stated as an operation on the relator tuple `Y` and leaves the
   generators implicit; the 2024 papers state it as an operation on the presentation. Section 3
   argues that the 2002 statement is the balance-preserving move and not the free-generator move.

There are two more differences that no quotation can settle, and I take them up in sections 3
and 8. The 2002 paper's own use of (AC4) is in the general Tietze form of reading 3, not in the form
`y w` with `w = 1`; Theorem 3 is what makes that harmless on the class of presentations of the
trivial group. The general Tietze form is also a strictly larger move than (AC4) on presentations of
nontrivial groups; Theorem 5 gives the separating pair and the invariant that separates it.

## 3. Why (AC4) in the 2002 paper deletes and adds a generator

`[Argument]` The text of (AC4) alone can be read in two ways, because it says only that the
relator tuple is extended by `x_ν`. Either the ambient free group gains the generator `x_ν` as
well, or the generators are unchanged and the new relator kills a letter that occurs in no
relator. The second reading is the one that changes the deficiency. Four independent passages of
the same paper decide between them.

1. **The deletion move removes a generator, and the paper says so while using it.** In the proof of
   their Theorem 1.4 they start from a Wirtinger presentation with 14 generators and 14 relators,
   discard one relator, and then eliminate generators one at a time. The elimination of `x_14` is
   described as follows `[V-source, ac.tex lines 794-798]`: "we ... replace x_14 by x_2 in all
   relators that involve x_14 (the 'basic substitution principle' again), and then get rid of x_14
   by applying the transformation (AC5)". The proof then lists eleven generators that are
   eliminated and ends with a presentation on three generators `x_5, x_7, x_12`. `[Argument]` A
   move that gets rid of a generator is a move that removes the generating letter; under the second
   reading (AC5) would remove only the relator and the count would not come out. So (AC5) removes
   a generator together with its relator, and (AC4), its converse, adds the pair.
2. **The deficiency count of that proof also fixes the direction of (AC4).** `[Argument]` The
   Wirtinger presentation has 14 generators and 14 relators. One relator is discarded, so the
   deficiency becomes `-1`. Eleven applications of (AC5) remove eleven generators and eleven
   relators, leaving 3 generators and 2 relators, which is again deficiency `-1`. Finally a relator
   `w` with exponent sum plus or minus one is added, giving 3 and 3, a balanced presentation of the
   trivial group. Every step of this bookkeeping uses (AC5) as the inverse of a balance-preserving
   (AC4). Under the second reading the eleven deletions would remove only relators, leaving 14
   generators and 2 relators, and the final step would give 14 generators and 3 relators, which is
   not the three-generator presentation that the theorem states.
3. **The paper says that the stable moves give simple-homotopy equivalent complexes.**
   `[V-source, ac.tex lines 171-176]`: "(stably) AC-equivalent sets of relators give rise to
   simple-homotopy equivalent complexes, since the transformations (AC1-AC5) applied to defining
   relators of the fundamental group of a 2-complex, are mimicked by elementary expansions and
   collapses applied to this 2-complex." `[Argument]` The free-generator move replaces the
   presented group `G` by `G * Z`, so it cannot be mimicked by expansions and collapses of
   `K(P)`, which preserve the homotopy type of `K(P)`. Under the second reading the new relator
   `x_ν` kills a generator that occurs in no other relator, so the presented group changes from
   `G * Z` to `G` and the sentence fails again. Under the first reading (AC4) adds a 1-cell and a
   2-cell that form a free pair, which is an elementary expansion, and (AC5) collapses the pair
   back, so the sentence holds exactly for the first reading.
4. **The paper compares the move with Suslin's stable tameness of matrices.**
   `[V-source, ac.tex lines 536-539 and 980-983]`: "every invertible square matrix over a Laurent
   polynomial ring is *stably tame*, which means one can extend this matrix by placing 1 on the
   diagonal and 0 elsewhere, such that the extended matrix is tame", and later "by a result of
   Suslin, ... stably tame, whence the result about stable AC-equivalence". `[Argument]` Under the
   first reading the exponent-sum matrix of (AC4) is the old matrix with a zero column appended and
   a 1 in the bottom right corner, which is exactly "placing 1 on the diagonal and 0 elsewhere",
   and the cokernel, which is the abelianisation, is unchanged. Under the second reading the
   exponent-sum matrix gains a row and the cokernel changes. The comparison identifies the first
   reading.

Two more points complete the picture.

* The parenthetical in (AC4), "i.e., `y_1, ..., y_m` do not depend on `x_ν`", is the statement
  that the new relator is the only relator in which the new letter occurs. It is needed for (AC5)
  to be well defined, and it is exactly the side condition of the 2024 papers.
* `[V-source]` The paper's own use of (AC4) in the proof of its Proposition 1.2 is the general
  Tietze form of reading 3. The displayed chain `[V-source, ac.tex lines 691-694]` contains the
  step
  `⟨x,y | x^2 = yxy, y^{-4}x^2 = x^2y^{-3}⟩ -> ⟨x,y,z | x^2 = yxy, y^{-4}x^2 = x^2y^{-3}, z = y^{-3}⟩`,
  which adjoins a generator `z` together with the relator `z y^3`. Under the literal (AC4) this is
  two steps: adjoin `z` with relator `z`, then multiply the new relator by `y^3`, which is legal
  because `y^3` lies in the normal closure of the other two relators, the group being trivial. The
  paper says at the start of that section that it is "skipping obvious steps sometimes". Theorem 3
  below is the general form of that observation, and it is the reason the general Tietze form of
  the 2002 move can be used without changing the relation on presentations of the trivial group.

## 4. Lemma 1: the unstable move sets generate the same relation

`[Argument]` Let `R_2002` be the equivalence relation on tuples generated by (AC1)-(AC3) as
printed in the 2002 paper, and `R_2024` the one generated by (AC1)-(AC3) as printed in the 2024
papers. Then `R_2002 = R_2024`.

*Proof.* Both lists contain `r_i -> r_i r_j` and `r_i -> r_i^{-1}`. A single-letter conjugation is
a special case of the 2002 conjugation, so `R_2024` is contained in `R_2002`. In the other
direction it is enough to derive `r_i -> r_i r_j^{-1}` and conjugation by a word, using only the
2024 list. For the first, apply the 2024 list three times: replace `r_j` by `r_j^{-1}`, replace
`r_i` by `r_i r_j^{-1}`, replace `r_j` by `r_j`. For the second, use the identity
`w r w^{-1} = a_1 ( ... (a_k r a_k^{-1}) ... ) a_1^{-1}` for `w = a_1 ... a_k`, whose right-hand
side is `k` single-letter conjugations of `r`, with each letter of `w` a generator or its inverse.
This completes the proof. `[V-compute]` Check [1] of the script verifies both derivations on 200
seeded instances, testing equality of the resulting tuple at every step, and it prints one worked
three-move example.

Two remarks. First, the identity in the second part is the same one that
`survey/stable-ac-check.py` check [6] verifies, and the two implementations agree. Second, since
the relations are equal as relations, the difference in the printed lists has no mathematical
content, and any claim of the form "the 2002 paper's relation is bigger" has to point at one of
the stabilization moves instead.

## 5. Lemma 2: the two (AC4) moves are the same move

`[Argument]` In the first reading of section 3, the 2002 (AC4) takes `(X; Y)` with `X = (x_1,...,
x_n)` and `Y` a tuple in `F_n` to the presentation with generators `X` extended by the new letter
`x_ν` and relators `Y` extended by `x_ν`. The 2024 (AC4) takes
`⟨x_1,...,x_n | r_1,...,r_n⟩` to `⟨x_1,...,x_n,x_{n+1} | r_1,...,r_n,x_{n+1}⟩`. These are the same
operation, written once as an operation on the relator tuple and once as an operation on the
presentation, and the only difference is the name of the new letter and the convention that in the
2024 papers it is the last one. Both are undone by the corresponding (AC5), and both have the
same side condition, namely that the new letter occurs in no old relator before the move and in no
other relator after it.

Consequences, all of them immediate from this identification.

* The deficiency `m - n` is preserved by (AC1)-(AC5). `[V-compute]` Check [3] runs a seeded random
  walk of 2213 moves, including (AC4) and (AC5) steps, and finds the deficiency constant.
* The exponent-sum matrix `M` of a presentation goes to the block matrix with `M` in the top left
  corner, a zero column on the right and a `1` in the bottom right corner. So the cokernel of `M`,
  which is the abelianisation of the presented group, is preserved. `[V-compute]` Check [2]
  verifies this on 100 seeded instances, and the same invariance is already checked in
  `survey/stable-ac-check.py` check [5].
* The side condition on (AC5) is syntactic. Without it the result of the deletion is a tuple that
  mentions a letter which is no longer a generator, so the result is not a presentation. `[Argument]`
  If the missing substitution is supplied by hand, the resulting presentation presents the same
  group, so the side condition is not protecting a group-theoretic distinction; it is protecting
  the statement of the move as a move on tuples. `[V-compute]` Check [9] exhibits the ill-formed
  tuple, and then shows that in that example the repaired move happens to be AC-realizable
  anyway, so nothing is lost there.
* Nothing in the repository's computations depends on the choice between the two readings of
  (AC4). `[V-compute]` The only file outside this deliverable that implements (AC4)/(AC5) is
  `survey/stable-ac-check.py`, and it implements the balance-preserving form: "add generator
  x_{n+1} and relator x_{n+1}". The round-2 computations in `directions/ak-ladder`,
  `directions/ms-ak-certs`, `directions/c14`, `directions/pu-enumeration` and
  `directions/invariant-ideas` use (AC1)-(AC3) only, apart from the rank-0 destabilisation check
  in `directions/invariant-ideas/check_idea.py`, which uses the same balance-preserving form. A
  search of the repository for the strings `AC4` and `AC5` outside the markdown files, run on
  2026-11-04, returns `survey/stable-ac-check.py` and no other file. The round-3 Lean file
  `toolkit/lean/AC3.lean` of another member, which was being written while this file was, defines
  its stabilization move at line 1567 as adding the last generator together with the relator equal
  to it, which is the same reading; that file is work in progress by its author and I do not rely
  on it.

## 6. Theorem 3: the general Tietze form reduces to (AC4) on presentations of the trivial group

**Theorem 3.** `[Argument]` Let `P = ⟨X | R⟩` be a presentation of the trivial group, with
`R = (r_1,...,r_m)` a tuple of words in `F(X)`, let `w` be any word in `F(X)`, and let `y` be a
letter not in `X`. Then the presentation `⟨X, y | R, y w⟩` is AC-equivalent to `⟨X, y | R, y⟩`,
where AC-equivalence uses (AC1)-(AC3), and hence the general Tietze generator addition is generated
by (AC4) together with (AC1)-(AC3).

*Proof.* Since `P` presents the trivial group, the normal closure of `R` in `F(X)` is all of
`F(X)`, so `w` lies in that normal closure. Write `w` as a product of conjugates of the relators,
`w = w_1 r_{i_1}^{ε_1} w_1^{-1} ... w_k r_{i_k}^{ε_k} w_k^{-1}`, with `w_j` words in `X` and
`ε_j = ±1`. This is possible because the normal closure of a set is the set of such products. Start
from `⟨X, y | R, y⟩`. The relator `y` can be replaced by its product with any element of the normal
closure of the other relators: conjugate `r_{i_j}` by `w_j` (move (AC3)), multiply the `y` relator
on the right by that conjugate (move (AC1), with the inverse move available by Lemma 1), and
repeat. The result is `⟨X, y | R, y w⟩`. This completes the proof.

Two remarks on the theorem.

* It is exactly the argument that the 2002 paper compresses into its displayed chain, and it is
  also the mechanism of the "substitution and removal" lemma of Shehper et al., which is their
  Lemma in section 2.1 `[V-source]`. Their proof of that lemma says in one line what the paragraph
  above says: the normal closure of the other relators gives the free group on the remaining
  generators, so `w` is a product of conjugates, so the new relator can be transformed into `y`
  and removed by (AC5). So the 2002 compression and the 2024 lemma are the same argument.
* The hypothesis that the group is trivial is used twice: to know that `w` lies in the normal
  closure of `R`, and to know that the target `⟨X,y | R, y w⟩` is a presentation of the same group.
  The hypothesis is sharp: Section 8 proves, with an explicit pair of presentations of `Z` and an
  invariant of the (AC1)-(AC5) relation, that the general Tietze form is strictly larger than the
  printed (AC4) once the presented group is not trivial.

`[V-compute]` Check [7] of the script prints an explicit certificate for the word `w = x_1 x_2^{-1}`
from `⟨x_1,x_2 | x_1, x_2⟩` to `⟨x_1,x_2,x_3 | x_1, x_2, x_3 x_1 x_2^{-1}⟩` and checks that each
step is legal, that the target is a presentation of the trivial group, and that it is balanced.

## 7. Theorem 4: the free-generator move is redundant

**Theorem 4.** `[Argument]`, `[V-lean]` Let `T` and `T'` be tuples of `m` words in `F_n`, let
`k` be a natural number, and regard `T` and `T'` as tuples in `F_{n+k}` by the inclusion of the
first `n` letters. If `T` and `T'` are AC-equivalent in `F_{n+k}`, using (AC1)-(AC3) with
conjugation by arbitrary words, then they are AC-equivalent in `F_n`.

*Proof.* Let `φ : F_{n+k} → F_n` be the retraction that fixes the first `n` letters and sends each
of the `k` new letters to `1`. It is a group homomorphism. Each of the three moves is carried by
`φ` to the same move on the image tuple: an inversion to an inversion, a product to a product, and
a conjugation by `g` to a conjugation by `φ(g)`. So `φ` applied to every tuple in an AC-derivation
from `T` to `T'` gives an AC-derivation from `φ(T) = T` to `φ(T') = T'`. This completes the proof.

The theorem is the exact statement that adjoining free generators does not change
AC-equivalence. Three consequences.

1. **The free-generator move adds nothing to the AC move set.** `[Argument]` If a derivation uses
   the free-generator move, the hypothesis of Theorem 4 holds at the two ends after the free
   letters are named, so the original tuples were already AC-equivalent. Consequently reading 4 of
   the stabilization move yields exactly the AC relation among tuples with a fixed number of
   relators, and in particular a balanced presentation is trivially equivalent to the standard one
   under reading 4 if and only if it is AC-trivial in the ordinary sense.
2. **Reading 4 cannot be the 2002 move.** `[Argument]` The 2002 paper introduces the stable
   relation as "a weaker form of this conjecture (which is of greater interest in topology)"
   `[V-source, ac.tex lines 138-139]`, states the weak conjecture separately from the ordinary one,
   and devotes its section 2 to presentations which are stably but not obviously AC-equivalent.
   Under reading 4 the weak conjecture is the ordinary conjecture by the previous item, and the
   paper's Proposition 1.2, which exhibits a presentation "not known to be AC-equivalent" to
   AK(3) but stably AC-equivalent to it, would be a statement about a pair of presentations that
   are AC-equivalent if and only if AK(3) is AC-trivial. That is not what the paper says about it.
   So reading 4 makes nonsense of the paper's own framing, in addition to contradicting its
   deletion bookkeeping of section 3.
3. **Reading 4 cannot be the 2024 move either.** `[Argument]`, `[V-source]` The 2024 (AC4) is
   printed as an operation on balanced presentations, with the relator `x_{n+1}` included, so it is
   balance-preserving by inspection.

`[V-lean]` The Lean file `survey/stabilization-moves.lean` proves Theorem 4 for arbitrary `m`, `n`
and `k`, in the form `free_generator_redundant`, together with the corollary
`acTrivial_of_free_generators` (a balanced presentation that becomes AC-trivial after free
generators are adjoined was already AC-trivial) and the contrapositive
`not_acTrivial_of_free_generators`. The file also proves `equiv_map`, the statement that a
homomorphism of free groups carries AC-equivalence to AC-equivalence of the image tuples, which is
the engine of the argument. `#print axioms` at the end of the file reports exactly
`[propext, Quot.sound]` for each of the five theorems, with no `sorryAx` and no extra axiom. The
file uses only `import Mathlib`.

`[V-compute]` Check [6] of the script runs the retraction over 5400 seeded random moves in
`F_{n+k}`, with the conjugating words biased towards the new letters, and verifies move by move
that the retracted trace is the expected AC trace in `F_n`; 3058 of the 5400 steps changed the
retracted tuple and 2342 left it unchanged, so the check is not vacuous. The check also prints one
explicit trace in `F_3` which conjugates by the free letter, multiplies by a relator, conjugates
back and multiplies by the inverse, and shows the retracted trace in `F_2`.

## 8. Theorem 5: the general Tietze form is strictly larger off the trivial group

`[Argument]` Theorem 3 has a hypothesis that cannot be dropped: the presentation must present the
trivial group. This section records what happens without it, and the answer is a theorem with an
explicit witness, not an open question.

**The failure point of the argument of Theorem 3.** The proof needs `w ∈ ncl(R)`, the normal
closure of the old relator tuple in the old free group. When `P = ⟨X | R⟩` presents a nontrivial
group `G`, the word `w` is in `ncl(R)` exactly when `w` is trivial in `G`, and for a general Tietze
substitution `y ↦ w` there is no reason for that. A witness with nothing to spare is the pair

    A = ⟨z | ⟩            and            B = ⟨z, y | y z⟩,

with `B` obtained from `A` by adjoining `y` with the relator `y z`, that is, `y = z^{-1}`. Both
present `Z`: for `A` this is immediate, and for `B` the relator `y z` is a primitive element of
`F(z,y)`, so the presented group is free of rank one. `[V-compute]` Check [8] of the script
verifies that the abelianisations agree and are `Z`, and that the two relator tuples have different
normal closures in `F(z,y)`. To simulate
this move by (AC4) plus (AC1)-(AC3) one would apply (AC4) to `A` and then have to pass from
`⟨z,y | y⟩` to `⟨z,y | y z⟩` by multiplying the relator `y` by `z`, which Theorem 3 does by
exhibiting `z` as an element of the normal closure of the other relators. Here there are no other
relators, so the construction needs `z ∈ ncl(∅) = {1}` in `F(z)`, which is false.

That shows that this proof stops. The next theorem shows that no proof can succeed.

**Theorem 5.** `[Argument]` The presentations `A = ⟨z | ⟩` and `B = ⟨z, y | y z⟩` are not stably
AC-equivalent in the sense of (AC1)-(AC5), although `B` is obtained from `A` by one general Tietze
generator addition.

*Proof.* For a presentation with `n` generators and relator tuple `R`, let `L ⊆ Z^n` be the
subgroup generated by the exponent-sum vectors of the relators, and let `D` be the span of the
coordinate vectors `e_i` that lie in `L`. Put `ρ = rank(L) - dim(D)`, the rank of the quotient
lattice `L/D`. I claim that `ρ` is unchanged by every one of the five moves.

* (AC1) `r_i → r_i r_j` replaces one row of the exponent-sum matrix by the sum of two rows, and
  (AC2) `r_i → r_i^{-1}` negates a row, so `L` is unchanged. (AC3) conjugation preserves the
  exponent sum of each letter, so each row is unchanged and `L` is unchanged. So `ρ` is unchanged
  by the unstable moves.
* (AC4) appends the new coordinate vector `e_{n+1}` to the generating set of the lattice, so `L`
  becomes `L ⊕ Z e_{n+1}` and `D` becomes `D ⊕ Z e_{n+1}`. Both ranks increase by one and `ρ` is
  unchanged.
* (AC5) applies only when some relator is a single letter `x_s` whose letter occurs in no other
  relator, so `e_s ∈ L`. Deleting the generator `s` and that relator replaces `L` by
  `L / Z e_s` and `D` by `D / Z e_s`, using that `e_s` is a primitive vector and that `e_s ∈ D`.
  Both ranks drop by one and `ρ` is unchanged.

For `A` the relator tuple is empty, so `L = 0`, `D = 0` and `ρ = 0`. For `B` the relator is `y z`,
whose exponent-sum vector is `(1,1)` in the basis `(z,y)`, so `L = ⟨(1,1)⟩`, `L` contains no
coordinate vector, `D = 0` and `ρ = 1`. Hence `A` and `B` lie in different classes of the (AC1)-(AC5)
relation. This completes the proof.

`[V-compute]` Check [12] of the script computes `ρ` with an exact integer lattice basis (Hermite
normal form, with an independent membership test) and verifies `ρ(A) = 0` and `ρ(B) = 1`. The same
check also runs a breadth-first search from `B` over (AC1)-(AC5) inside the box of rank at most 3,
at most 3 relators and total relator length at most 7, which reaches 14,004 presentations, finds
`ρ = 1` at every one of them and never reaches `A`. That is a bounded negative with the bounds
stated, and it corroborates the invariant rather than replacing it. The two presentations present
the same group `Z` and have the same deficiency, so neither the presented group nor any quotient of
it, and no invariant computed from the deficiency, can separate them.

**Consequence for the topological move list.** `[Argument]` The two 2-complexes `K(A)` and `K(B)`
are related by one elementary expansion and one elementary collapse. In `K(B)` the 1-cell of the
generator `y` occurs exactly once in the attaching word `y z` of the single 2-cell and in no other
2-cell, so that 2-cell and that 1-cell form a free pair, and collapsing it leaves the 1-cell of `z`
with no 2-cells, which is `K(A)`. Reading the same sequence backwards, `K(B)` is `K(A)` with a free
pair adjoined, which is an elementary expansion. So `K(A)` and `K(B)` are 3-deformation equivalent,
while `A` and `B` are not stably AC-equivalent in the sense of (AC4). If the topological
correspondence between 3-deformations and stable AC-equivalence used the move set with `w = 1`, this
pair would be a counterexample to it. The reading that avoids this is that the topological move list
contains the general Tietze generator addition, which is what the Encyclopedia of Mathematics entry
recorded in `survey/stable-ac.md` section 7 says, and which is also consistent with the 2002 paper's
use of the general form. I did not read Wright's paper, so this paragraph is an inference from the
pair above and not a quotation. `[Unverified]`

**Why this does not destabilise the 2024 definition.** `[Argument]` The stable Andrews-Curtis
conjecture is stated for balanced presentations of the trivial group, and on that class Theorem 3
identifies the relation generated by (AC4) with the relation generated by the general Tietze form.
So the 2024 papers can use the printed (AC4) with `w = 1` and still be talking about the relation
that the topological literature uses, and the difference in Theorem 5 lives entirely off the class
where the conjecture is stated. The 2002 paper is in the same position: its compressed use of the
general form in the proof of Proposition 1.2 is on a presentation of the trivial group, where
Theorem 3 licenses it.

**What Theorem 5 does not say.** `[Argument]` It does not say that the 2002 move set differs from
the 2024 move set. It says that the general Tietze form, which the 2002 paper uses but does not
print as its (AC4), is strictly larger than the printed (AC4) of both papers. It also does not
settle whether some other published list of stable moves coincides with one or the other; the only
list I checked is the one in the two 2024 sources and the 2002 source.

## 9. What this changes, and what it does not

**It does not change any verified result in the repository.** `[Argument]` The stable status of
AK(3) is unresolved for a reason that has nothing to do with the choice of stabilization move: the
argument of Shehper et al. version 1 used a printed relator of the 2002 paper which the authors
later identified as a misprint, and the published version of Lisitsa's article in 2025 concedes
that the status is unresolved. The survey `survey/stable-ak3-status.md` records that chronology with identifiers. Since
the two stabilization move sets are the same move set, no statement about the two move sets can
affect that verdict either way.

**It corrects one sentence of the round-2 record.** `survey/stable-ak3-status.md` section 3 says
the MMS move changes the deficiency. Section 3 of this file shows otherwise, and the following
replacement paragraph is proposed for that passage. The coordinator can apply it; I did not edit
another member's file.

> A definitional hazard belongs here, and it resolves in favour of the sources agreeing. MMS define
> the stable moves as (AC1) to (AC3) together with (AC4), "Y is extended to {y_1,...,y_m,x_nu},
> where x_nu is a new free generator", and (AC5), the converse [L: ac.tex, the list after the
> statement of the weak conjecture]. Shehper et al. define (AC4) as adding a generator together
> with the trivial relator, and (AC5) as the inverse move [L: arXiv:2408.15332v2, sec/stable.tex].
> The two are the same move: in both, a new generator and the relator equal to it enter or leave
> together, so the deficiency is unchanged by both. That the MMS move deletes the generator is
> fixed by MMS's own use of it, since the proof of their Theorem 1.4 removes eleven generators from
> a fourteen-generator presentation "by applying the transformation (AC5)" [L: ac.tex, line 798,
> with the generator counts of that proof]. An earlier reading of this paragraph, which said that
> the MMS move changes the deficiency, is corrected in survey/stabilization-moves.md, section 3.

**It gives the 2002 paper's compressed step a proof.** `[Argument]` The displayed chain of the
proof of Proposition 1.2 adjoins a generator with a defining relator `z = y^{-3}`. Under the
printed (AC4) that is a two-step composite, and Theorem 3 is the general statement that licenses
it. So the 2002 proofs can be read as they stand, without any extra convention.

**It makes "stably AC-equivalent" unambiguous across the three sources on the class that
matters.** `[Argument]` On balanced presentations of the trivial group, the 2002 relation, the 2024
relation and the relation generated by (AC4) plus the general Tietze generator addition are the
same relation, by Lemma 2 and Theorem 3. The only reading under which they differ is reading 4, and
that relation is the AC relation itself by Theorem 4. Off that class the general Tietze form is
strictly larger by Theorem 5, and that difference is invisible to every statement that quantifies
over presentations of the trivial group.

**It settles the relation between the two published move sets and the move set that the topology
literature uses.** `[Argument]` Theorem 5 gives the exact content of the difference: `ρ = 0` for
one presentation of `Z` and `ρ = 1` for the presentation obtained from it by one general Tietze
generator addition, while `ρ` is invariant under (AC1)-(AC5). So the printed (AC4) is not the
general Tietze move, and the general Tietze move is not derivable from it. Section 8 also records
the topological side of the same computation, namely that the two 2-complexes are related by an
elementary expansion and collapse, which is the reason the topological literature needs the general
form in its list.

**It closes the question of where the 2002 paper applies its move.** In `ac.tex` the strings
`(AC4)` and `(AC5)` occur only at the definition (lines 142-146) and at line 798, where the move is
used to delete a generator from a presentation of the trivial group, and the compressed use inside
the chain of Proposition 1.2 is again on a presentation of the trivial group. So every application
of the move in that paper carries the hypothesis of Theorem 3, and the printed special case of
(AC4) suffices for the paper's own arguments.

## 10. What the two accompanying files check

`survey/stabilization-moves-check.py` is a Python 3 program that uses the standard library and,
for the integer lattice invariant of check [12], sympy; if sympy is absent that one check is
skipped and the rest run. It takes about five seconds, and it prints one PASS line per check,
ending with `all checks passed`; the run on 2026-11-04 printed 29 PASS lines and no failure. Its
randomness comes from `random.Random(20261104)` only, so it is deterministic. The checks are the
following.

* [1] The two (AC1)-(AC3) conventions generate the same relation, by the two derivations of
  Lemma 1, each verified step by step on 200 seeded instances.
* [2] The two (AC4) definitions produce the same presentation, the deficiency is unchanged, and
  the exponent-sum matrix goes to the block matrix with a `1` in the corner, on 100 seeded
  instances.
* [3] The deficiency is invariant over a seeded random walk of 2213 moves that includes (AC4) and
  (AC5) steps.
* [4] The free-generator move changes the deficiency from 0 to -1 and the group from trivial to
  `Z`, on the pair `<x_1 | x_1>` and `<x_1,x_2 | x_1>`.
* [5] Hence the free-generator move is outside the (AC1)-(AC5) relation, so that pair separates
  reading 4 from both published move sets.
* [6] The retraction of Theorem 4, verified move by move over 5400 seeded moves, plus one explicit
  printed trace in `F_3` and its retraction in `F_2`.
* [7] An explicit certificate for Theorem 3 with `w = x_1 x_2^{-1}`, and a second certificate in
  which the word `w` is reached through a conjugate, so that the derivation uses (AC3).
* [8] The failure point of section 8: two presentations of `Z` with different normal closures of
  the relator tuple, certified by the abelianisation.
* [9] The side condition of (AC5): the unrestricted deletion produces an ill-formed tuple, and the
  repaired move is AC-realizable in the example, so the side condition is syntactic.
* [10] Interoperability: the three moves implemented here agree with `toolkit/ac.py`, the
  repository's own engine, on 200 seeded balanced tuples.
* [11] The eighteen certificates in `directions/ms-ak-certs/` (AK(n) to MS(n, w_1) for n = 2 to 10,
  forward and reverse) replay through this engine in 648 moves, all of them (AC1)-(AC3), with every
  endpoint matching the declared one. That is the concrete sense in which the round-2 results do
  not depend on the stabilization move at all.
* [12] Theorem 5: the invariant `ρ = rank L - dim D` computed with an exact integer lattice basis
  gives `ρ = 0` for `<z | >` and `ρ = 1` for `<z,y | y z>`, the two presentations present the same
  group, and a breadth-first search from the second over (AC1)-(AC5) inside the box of rank at most
  3, at most 3 relators and total length at most 7 reaches 14,004 presentations with `ρ = 1` at
  every one and never reaches the first.

`survey/stabilization-moves.lean` proves Theorem 4 and its corollary for arbitrary numbers of
relators and free generators. It contains no `sorry`, no `native_decide` and no new axiom, and its
`#print axioms` lines report `[propext, Quot.sound]` for all five theorems. It does not formalize
Lemma 1, Lemma 2, Theorem 3 or Theorem 5, and it does not formalize anything about the presented
group.

## 11. Sources, with the detail I checked

1. A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, *On the Andrews-Curtis equivalence*,
   Contemporary Mathematics 296 (2002) 183-198, DOI 10.1090/conm/296/05074. Author's LaTeX source
   `arXiv:math/0302080v1`, 1157 lines, and posted PDF `https://shpilrain.ccny.cuny.edu/ac.pdf`.
   I fetched both on 2026-11-04 and checked the arXiv record live for title, authors, submission
   date and journal reference. Quoted: the setting at lines 95-99, (AC1)-(AC3) at lines 103-114,
   (AC4)/(AC5) at lines 142-146, the definition of stable equivalence at lines 148-151, the weak
   conjecture at lines 153-157, the framing "a weaker form of this conjecture" at lines 138-139,
   the simple-homotopy paragraph at lines 171-176, the stable tameness comparison at lines 536-539
   and 980-983, the Proposition 1.2 chain at lines 691-694, and the account of the elimination of
   `x_14` at lines 794-798.
2. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu, P. Kucharski,
   Z. Wang and S. Gukov, *What makes math problems hard for reinforcement learning: a case study*,
   `arXiv:2408.15332`, version 2 of 11 February 2025. Source fetched 2026-11-04. Quoted:
   (AC1)-(AC3) from `sec/conjecture.tex`, and (AC4)/(AC5) plus the substitution and removal lemma
   from `sec/stable.tex`.
3. L. Fagan, Y. Qiu and Z. Wang, *Stable Andrews-Curtis conjecture via fake surfaces and Zeeman
   conjecture*, `arXiv:2412.12293`, version of 9 January 2026. Source fetched 2026-11-04. Quoted:
   (AC4)/(AC5) at `main.tex` lines 306-311.
4. L. Fagan, *The stable Andrews-Curtis conjecture and generic 2-polyhedra*, PhD thesis, UC Santa
   Barbara, November 2025. Definition 3.1 is quoted for the same move in `survey/stable-ac.md`,
   which I read. I did not fetch the thesis, so I do not quote it first-hand. `[Unverified]`
5. P. Wright, *Group presentations and formal deformations*, Trans. Amer. Math. Soc. 208 (1975)
   161-169, DOI 10.1090/S0002-9947-1975-0380813-5, and the Encyclopedia of Mathematics entry
   "Low-dimensional topology, problems in", are cited in `survey/stable-ac.md` section 7 for the
   four-move formulation with the general Tietze form "add a generator `x_{n+1}` and a relation
   `w x_{n+1}`". The encyclopedia server returned HTTP 502 on 2026-11-04 when I tried to re-read
   the page, so that quotation rests on the round-1 reading and not on mine. `[Unverified]`
   Nothing in this file depends on it, because Theorem 3 covers that form on the class of
   presentations of the trivial group.
6. `toolkit/lean/AC2.lean`, theorem `nclRange_eq_of_acEquiv`, for the normal closure invariance that
   section 8 cites. I read the file and the theorem statement; the round-2 record reports the file
   checked with no axioms beyond the standard ones, and I did not rerun it for this file.

## 12. What I could not verify

* The Fagan thesis Definition 3.1, first-hand (item 4 of the sources). The two sources I did fetch
  agree with each other, and with the round-1 reading of the thesis.
* Wright's list of five operations and the encyclopedia's fourth move, first-hand, because the
  encyclopedia server returned HTTP 502. Section 6 of this file does not depend on them.
* Whether the 2002 paper's (AC4) is "really" intended as the general Tietze form rather than as the
  printed special case. I argued that the printed case is enough for every use in the paper, so the
  question has no consequence for the relation on presentations of the trivial group. `[Open]`
* Whether some third published list of stable moves, in particular Wright's operations (1)-(5),
  agrees with the general Tietze form or with the printed (AC4). Section 8 shows that the pair of
  Theorem 5 forces any list that supports the 3-deformation correspondence to contain the general
  form, but I did not read Wright's list, so I do not know what it says. `[Open]`
* Theorem 5 is proved here and corroborated by a bounded search, but it is not formalized in Lean.
  The Lean file covers Theorem 4 only.
