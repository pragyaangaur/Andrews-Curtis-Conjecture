# Q-transformations and Q**-equivalence

Member m10, swarm smw2fzjic, direction d14. This file states the definitions of
Q-, Q*- and Q**-transformations, relates them to Andrews-Curtis moves and to
3-deformations of 2-complexes, and records which classes of complexes have
positive results. Every statement carries a label.

Labels used below.

- [proved here]: an argument written out in this file, checkable line by line.
- [computed here]: a deterministic computation, rerun by the command in §8.
- [quoted]: a statement taken from a cited source; the source data are in §10.
- [argument]: a proof sketch that I did not write out in full.
- [unverified]: a claim I saw stated but could not check against a primary
  source in this session.

Nothing in this file comes close to a proof or a disproof of the Andrews-Curtis
conjecture. The conjecture, its Q** version and the generalized version are all
recorded as open in a 2025 paper that I read in full [quoted: Barmak 2025, §1].

## 1. Presentations and the standard complex

A finite presentation is a pair P = (g; R_1,...,R_h) of a number g of generators
a_1,...,a_g and a tuple of relators, each a word in the free group
F(a_1,...,a_g). It is balanced when g = h. Its standard complex K_P has one
0-cell, one 1-cell for each generator and one 2-cell for each relator, attached
along the loop spelled by that relator in the 1-skeleton. The group presented by
P is F(a_1,...,a_g) modulo the normal closure N(R_1,...,R_h) of the relators.

Reading a presentation off a finite connected 2-complex uses a spanning tree, a
base point, orientations, connecting arcs and attaching maps. Hog-Angeloni and
Metzler record that different choices change the presentation only by replacing
a relator R_j with a conjugate w R_j w^{-1}, and by changing the basis of the
fundamental group [quoted: Hog-Angeloni-Metzler 1993, Ch. I, (25) and footnote
16].

Lemma 1 [proved here, standard]. If P is a balanced presentation of the trivial
group then K_P is contractible. Conversely, every finite contractible
2-complex collapses to the standard complex of a balanced presentation of the
trivial group.

Proof. Suppose P is balanced with g = h and presents the trivial group. Then
pi_1(K_P) = 1, so H_1(K_P) = 0. The Euler characteristic is 1 - g + h = 1.
Since K_P is 2-dimensional, H_2(K_P) is a subgroup of the free abelian group of
2-chains, hence free abelian, and 1 = chi = 1 - 0 + rank H_2 gives rank H_2 = 0,
so H_2(K_P) = 0. A simply connected CW complex with vanishing reduced homology
is contractible by Hurewicz and Whitehead. Conversely, if K is a finite
contractible 2-complex with g 1-cells and h 2-cells, then pi_1(K) = 1 and
1 = chi(K) = 1 - g + h, so g = h, and after collapsing a maximal tree the
attaching words of the 2-cells read off a balanced presentation of the trivial
group whose standard complex is the collapsed complex. QED

Lemma 1 has a consequence that matters for everything below. All standard
complexes of balanced presentations of the trivial group are contractible, hence
homotopy equivalent to each other, hence simple homotopy equivalent to each
other, because the Whitehead group of the trivial group is trivial and every
homotopy equivalence of simply connected finite complexes therefore has zero
torsion [argument; the vanishing of the Whitehead group of the trivial group is
standard, and the relevant theory is Whitehead's, see Whitehead 1941 in §10].

## 2. The three relations Q, Q*, Q**

The definitions are those of Hog-Angeloni and Metzler [quoted: 1993, Ch. I,
p. 21] and of Barmak [quoted: Barmak 2025, §1]. Let
P = (a_1,...,a_g; R_1,...,R_h) be a finite presentation.

Q-transformations are finite sequences of the following elementary moves, in
which only the relator with the displayed index changes.

- (26)a  R_j is replaced by w R_j w^{-1} for some word w in the generators.
- (26)b  R_j is replaced by R_j^{-1}.
- (26)c  R_j is replaced by R_j R_k or by R_k R_j, for some k different from j.

Q*-transformations admit, in addition, the elementary Nielsen transformations of
the generators [quoted: Hog-Angeloni-Metzler 1993, (27)]: throughout all
relators, one generator a_i is replaced by a_i^{-1}, or by a_i a_j, or by a_j a_i
with j different from i. These elementary operations generate all Nielsen
transformations, that is, all automorphisms of the free group [quoted: ibid.,
(27) and footnote 11].

Q**-transformations admit, in addition, prolongation and its inverse
[quoted: ibid., (28)]: adjoin a new generator a with the single new relator a,
or delete such a generator and relator when the generator occurs in no other
relator.

Barmak states the same three relations as lists (i) to (vi): (i) replace a
relator r_j by r_j r_i, (ii) by r_j^{-1}, (iii) by a conjugate, (iv) apply an
automorphism of the free group to every relator, (v) add a generator x_{n+1}
with the relator x_{n+1}, (vi) the inverse of (v). Moves (i) to (iii) are
Q-transformations, (i) to (iv) are Q*-transformations and (i) to (vi) are
Q**-transformations [quoted: Barmak 2025, §1].

Lemma 2 [proved here]. The relation generated by (26)a,b,c is the relation
generated by the three Andrews-Curtis moves of the problem statement, namely
inversion of a relator, right multiplication of one relator by another, and
conjugation of a relator.

Proof. Every Andrews-Curtis move is a move of type (26), so one inclusion is
immediate. For the other, only left multiplication R_j -> R_k R_j in (26)c needs
work, since it is not among the three Andrews-Curtis moves as usually listed.
Conjugating R_j by R_k gives R_k R_j R_k^{-1}, and multiplying that on the right
by R_k gives R_k R_j. Both steps are Andrews-Curtis moves. QED

Three terminological warnings, all relevant when reading the literature.

First, left multiplication is often omitted from the list of moves, as in
Barmak's (i), because it is derivable as in Lemma 2. Second, permutations of the
relators are also derivable, and Hog-Angeloni and Metzler note this in a
footnote [quoted: 1993, Ch. I, footnote 17]. Third, and most important, some
papers call Q**-transformations "Andrews-Curtis moves". Hog-Angeloni and
Metzler note that the terminology "extended Nielsen transformations" is used for
Q** in earlier work [quoted: 1993, Ch. I, footnote 18], and Bobtcheva's paper on
Quinn's invariants lists six operations, including stabilisation, as "AC-moves"
[quoted: Bobtcheva 2000, §1]. A positive result stated for those six operations
is a Q** result, and it does not give a sequence of Andrews-Curtis moves.

Lemma 3 [proved here]. Each of Q, Q* and Q** preserves the group presented.

Proof. The presented group is F/N where N is the normal closure of the relators.
Replacing a relator by its inverse, by a conjugate, or by a product with another
relator leaves the normal closure unchanged, since each new relator lies in the
old normal closure and each old relator is recovered from the new ones. An
automorphism of F carries normal closures to normal closures. A prolongation
adds a generator a and the relator a, and the natural map from the old group to
the new one is an isomorphism. QED

## 3. Deformations of 2-complexes

The following definitions are those of Hog-Angeloni and Metzler
[quoted: 1993, Ch. I, §2.1]. An elementary collapse of dimension n, written
K down-arrow L, is the passage from K to L when K is obtained from L by
adjoining two cells e^n and e^{n-1} that form a standard ball pair, with the precise conditions (12) and (13) of the
source on the characteristic map. An elementary
expansion is the inverse passage. A deformation, written K zigzag L, is a finite
sequence of elementary collapses and expansions. An n-dimensional deformation is
one in which all cells involved have dimension at most n. A simple homotopy
equivalence is a map homotopic to a deformation [quoted: ibid., §2.1, after
Whitehead 1950 and Cohen 1973].

A 3-deformation of 2-complexes is a 3-dimensional deformation. Each elementary
collapse and each elementary expansion is a homotopy equivalence, so every
3-deformation is a simple homotopy equivalence [argument, immediate from the
definitions].

The engine of the whole theory is one lemma.

Lemma 4 [quoted: Hog-Angeloni-Metzler 1993, Lemma 2.1]. Let K be an
n-dimensional complex and let phi and psi be homotopic maps from the (n-1)-sphere
to the (n-1)-skeleton of K, used as attaching maps for n-cells. Then
K union_phi D^n and K union_psi D^n are related by a deformation that expands a
single (n+1)-cell and collapses it again. The authors call such a step an
(n+1)-dimensional exchange, or a transient move.

## 4. The dictionary between presentations and 3-deformation types

Theorem 5 [quoted: Hog-Angeloni-Metzler 1993, Theorem 2.4]. The assignment of a
compact connected 2-complex to its presentation class induces a bijection between
3-deformation types of compact connected 2-dimensional CW-complexes and
Q**-classes of finite presentations. The inverse bijection sends a presentation
to its standard complex. The piecewise linear version of the statement is due to
Wright [quoted: Hog-Angeloni-Metzler 1993, remark after Theorem 2.4, citing
Wright 1975].

The half of Theorem 5 that can be checked by hand is the implication from
Q**-equivalence to 3-deformation, and the argument is short enough to record
here. It is my reconstruction of the proof given by Hog-Angeloni and Metzler
[argument, following quoted: 1993, proof of Theorem 2.4].

Step one, prolongation. Adjoining a generator a with relator a replaces K_P by
K_P with a 1-cell and a 2-cell added in a cancelling pair, which is an
elementary 2-expansion. Deleting such a pair is an elementary 2-collapse.
Hog-Angeloni and Metzler note that a generalised prolongation, adjoining a
generator a with relator w^{-1} a, is available from (27) and (28) together
[quoted: 1993, Ch. I, (31)].

Step two, a single Q-move. A move of type (26) changes exactly one attaching
map, from a loop R_j to another loop in the same 1-skeleton. In the complex with
the j-th 2-cell removed, the two loops are homotopic. For inversion, the two
attaching maps differ by a reflection of the circle, and the two complexes are
homeomorphic. For conjugation, conjugate loops are freely homotopic. For
multiplication R_j -> R_j R_k, the loop R_k is null-homotopic in the complement
of the j-th 2-cell because the k-th 2-cell is still present. Lemma 4 with n = 2
now gives a transient 3-deformation.

Step three, automorphisms. The moves (27) need no separate treatment, because
Hog-Angeloni and Metzler observe that free transformations of the generators can
be replaced by generalised prolongations together with Q-transformations
[quoted: 1993, proof of Theorem 2.4, item (31) and the sentence following it].

Corollary 6 [quoted: Hog-Angeloni-Metzler 1993, Ch. I, (29) and the lines after
(32)]. Q**-transformations preserve the deficiency h - g of a presentation, and
3-deformations preserve the Euler characteristic of the complex.

## 5. The hierarchy, and what is known to be strict

The relations nest as follows. Every Q-transformation is a Q*-transformation
because (i) to (iii) are included in (i) to (iv), and every Q*-transformation is
a Q**-transformation, so

  Q is contained in Q*, which is contained in Q**, which is contained in simple
  homotopy equivalence of standard complexes.

The last inclusion follows from the definitions quoted in §3: a 3-deformation is
a deformation, and a deformation is a simple homotopy equivalence. The strictness results I found are the following.

Q* is strictly finer than Q**, so Q** is strictly coarser than Q* [quoted:
Barmak 2025, §1, reporting Zieschang 1970, McCool-Pietrowski 1973 and Metzler
1976]. The first example, which Barmak attributes probably to Zieschang, is the pair of
one-relator presentations with relators x^3 y^5 and x^3 y^3 x^3 y^2, which are
Q**-equivalent but not Q*-equivalent because the relators have different minimal
length in their orbit under the automorphisms of the free group of rank two.
McCool and Pietrowski give the family with relators x^k y^{pt+1} and
(x^k y^t)^p y for k, p, t at least 2. Metzler's example is the pair with
relators x^5, y^5, [x,y] and x^5, y^5, [x^2,y]; here the normal closures of the
two relator sets coincide, so the example is not of the easy normal-closure kind.

Simple homotopy equivalence is strictly coarser than Q* [quoted: Barmak 2025,
abstract and Theorem 5]. Barmak's pair is

  P = ( x, y ; [x,y], 1 )
  Q = ( x, y ; [x,[x,y^{-1}]]^2 y [y^{-1},x] y^{-1}, [x,[[y^{-1},x],x]] ).

The two standard complexes are simple homotopy equivalent, both present the free
abelian group of rank two, and the presentations are not Q*-equivalent. The obstruction is a basis change matrix over the Laurent
polynomial ring in two variables which is not a product of elementary and
diagonal matrices, together with a winding invariant of words in the commutator
subgroup [quoted: Barmak 2025, §1 and §2]. Fernandez later proved that the same
two presentations are Q**-equivalent [quoted: Barmak 2025, §1, citing
Fernandez 2024]. By Theorem 5 this is the same statement as: the two standard
complexes are 3-deformation equivalent.

Whether simple homotopy equivalence implies Q**-equivalence in general is
precisely the generalized Andrews-Curtis conjecture, and it is open
[quoted: Barmak 2025, §1, citing Hog-Angeloni-Metzler 1993, Section 4.1].

## 6. The three conjectures, and why Q is not Q**

The three statements, in the form in which Barmak states them
[quoted: Barmak 2025, §1].

1. Andrews-Curtis conjecture: any two presentations of the trivial group with g
   generators and h = g relators are Q-equivalent.
2. Weak Andrews-Curtis conjecture: in the same situation the two presentations
   are Q**-equivalent. This is equivalent to the statement that every
   contractible finite 2-dimensional CW complex 3-deforms to a point.
3. Generalized Andrews-Curtis conjecture: any two presentations whose standard
   complexes are simple homotopy equivalent are Q**-equivalent. The reference
   given is Section 4.1 of Hog-Angeloni and Metzler 1993.

Barmak writes that all three conjectures are open, and that the original
conjecture asserts that in some cases a Q**-equivalence is a Q-equivalence
[quoted: Barmak 2025, §1].

The difference between statements 1 and 2 is exactly the difference between
presentations and complexes, and Lemma 1 makes this precise. All balanced
presentations of the trivial group have contractible standard complexes, so all
of those complexes are simple homotopy equivalent, and statement 2 says that
they all lie in a single 3-deformation type. Statement 1 says more: it says that
the cell structures can be matched by Andrews-Curtis moves, that is, by the part
of the Q** relation that does not use prolongation or automorphisms of the free
group. A proof of Q**-equivalence for a pair of balanced presentations of the
trivial group, or a proof of Q*-equivalence, therefore does not produce an
Andrews-Curtis move sequence, and a computational search that only looks for
Q** steps answers a different question. This is why the positive results in §7
are sorted by the relation they use.

## 7. Classes with positive results

### 7.1 Small rank, and presentations where n-1 relators are generators

Lemma 7 [proved here]. A balanced presentation of the trivial group with one
generator is Q-equivalent to the standard presentation.

Proof. The only relator is a power x^k. The group is trivial exactly when
k = 1 or k = -1, and inversion of the relator is a Q-move. QED

Lemma 8 [proved here, computed here]. Let P be a balanced presentation with n
generators x_1,...,x_n and n relators, of which the first n-1 are single
generators x_1,...,x_{n-1} up to sign. Suppose P presents the trivial group.
Then P is Q-equivalent to the standard presentation. The proof gives an explicit
move sequence of six moves per letter of the last relator, and these sequences
are produced and replayed by the script of §8.

Proof. Write the last relator as w. Let N be the normal closure of the first n-1
relators, which is also the normal closure of x_1,...,x_{n-1}. The quotient of
the free group by N is infinite cyclic, generated by the image of x_n. Since the
whole group is trivial, the image of w in that quotient has order one, so the
exponent sum e of x_n in w satisfies e = 1 or e = -1. The element
w^{-1} x_n^{e} lies in N, so w can be turned into x_n^{e} by multiplying it by
elements of N. Every element of N is a product of conjugates of the relators
x_j^{+-1}, and the moves (26)a,b,c multiply a chosen relator by such conjugates:
conjugating by a word, multiplying by a relator, and conjugating back realises
multiplication by a conjugate. One step of this kind deletes one letter: if
w = u x_j^{f} v with j smaller than n, then left multiplication by the conjugate
u x_j^{-f} u^{-1} of the relator x_j turns w into u v. After finitely many
deletions w is x_n^{e}, and one inversion finishes. QED

The deletion step needs six basic moves, or four when the deleted letter has
sign -1: invert the helper relator x_j, conjugate it by u, conjugate the relator
w by the resulting conjugate, multiply w by the helper on the right, conjugate
the helper back by u^{-1}, and invert it again. The script below performs
exactly these moves, checks that each intermediate relator is the reduced word
predicted by the proof, and replays the whole sequence from the original
presentation.

### 7.2 Collapsing results, and how far they reach

The following results give positive 3-deformation statements only in special
cases, and I state the reason after the list.

- Zeeman proved that the dunce hat becomes collapsible after taking the product
  with an interval, and that the dunce hat itself is contractible and not
  collapsible [quoted: Zeeman 1964, as reported in Kupers' notes and in the
  Encyclopedia of Mathematics entry cited in §10].
- Dierker proved that for every compact contractible 2-polyhedron K there is an
  integer n with K times the n-cube collapsible [quoted: Dierker 1968, title and
  venue in §10; statement from the Encyclopedia of Mathematics entry].
- Lickorish treated the same collapsing question [quoted: Lickorish 1970, title
  in §10].
- Cohen proved that the sixth power of the interval suffices for every
  contractible 2-complex: K times the 6-cube is collapsible
  [quoted: Cohen 1975, title in §10; statement from the Encyclopedia of
  Mathematics entry, which says n = 6 suffices for all K].
- Gillman treated Bing's house and its relation to the Zeeman conjecture
  [quoted: Gillman 1986, title in §10].

These are collapsibility results, and collapsibility of K times the n-cube is a
3-deformation of K to a point only when n = 1, because a 3-deformation may use
cells of dimension at most three. For n larger than one the deformation passes
through complexes of dimension 2 + n. The case n = 1 for all contractible
2-complexes is Zeeman's conjecture, and Zeeman's conjecture implies the
Andrews-Curtis conjecture, since K expands to K times the interval and then
collapses to a point, which is a 3-deformation [quoted: Encyclopedia of
Mathematics, entry on low-dimensional topology; Gillman-Rolfsen 1983 and
Kreher-Metzler 1983 are listed there as work on the Zeeman conjecture]. Two
equivalences of the Zeeman conjecture are recorded in the same entry and in its
bibliography: with the Poincare conjecture for standard spines
[quoted: Gillman-Rolfsen 1983] and with the Andrews-Curtis conjecture for
unthickenable special polyhedra [quoted: Matveev 1987]. I verified the titles and
venues of those two papers, and I did not verify their statements.

### 7.3 Positive results for Q** proper

- Hog-Angeloni and Metzler prove that after Q**-transformations the relators of
  two presentations with the same normal closure and equal deficiency can be
  made equal modulo the commutator subgroup of the relator group
  [quoted: Barmak 2025, §1, describing Hog-Angeloni-Metzler 1993, Theorem 2.3].
- The same authors show that solvable groups are not useful as test groups for
  distinguishing Q**-equivalence [quoted: Barmak 2025, §1, citing
  Hog-Angeloni-Metzler 1993, Theorems 2.3 and 2.4].
- Suslin's theorem that the general linear group of rank three over the Laurent
  polynomial ring in two variables is generated by elementary and diagonal
  matrices shows that the obstruction used against Q*-equivalence in Barmak's
  example is invisible in rank three, which Barmak reads as weak evidence that his pair
  might be Q**-equivalent [quoted: Barmak 2025, §1 and §2].
- Fernandez develops a discrete Morse theory for group presentations that
  produces explicit 3-deformations, proves that some known potential
  counterexamples to the Andrews-Curtis conjecture do satisfy the conjecture in
  its Q** form, and, as reported by Barmak, proves that Barmak's exotic pair is
  Q**-equivalent [quoted: Fernandez 2024 abstract and Barmak 2025, §1].

The abstract of Fernandez's paper says that her method studies
Q**-transformations of group presentations, equivalently 3-deformations of
2-dimensional CW complexes, and that she applies it to show that some known
potential counterexamples "do satisfy the conjecture". Because her framework is
Q**, that sentence cannot be read as a proof of Q-equivalence, and I do not read
it that way.

### 7.4 A family that the literature calls AC-trivial, which I could not verify

The Encyclopedia of Mathematics entry states that the standard complexes of the
two-generator two-relator presentations with relators a^p b^q and a^r b^s, where
ps - qr is plus or minus one, are Andrews-Curtis equivalent to the empty
presentation, and that even so the corresponding collapsing statement for K
times the interval was not established, as of 1999, for most of them [unverified: quoted from
the Encyclopedia of Mathematics entry; I did not find the primary source, and
the entry does not say whether it means Q, Q* or Q** equivalence].

What I can check in that direction is the abelian obstruction, and it is absent.
For such a presentation the exponent-sum matrix has determinant ps - qr, which is
plus or minus one by hypothesis, so the abelianisation is trivial and the
matrix imposes no restriction. The same computation for the Akbulut-Kirby
presentations, with relators xyx(yxy)^{-1} and x^n y^{-(n+1)}, gives determinant
-1 for n from 1 to 6 [computed here, §8, check 6]. No abelian invariant can
distinguish these presentations from the standard one, which is why the
search for a counterexample has to use finer structure.

## 8. The checks I ran

The script `q-transformations-check.py` sits next to this file and in my own
working directory. It is deterministic, with seed 20240601, and it takes under a
second.

    $ python3 survey/q-transformations-check.py

    PASS word_arithmetic: 6 cases
    PASS q_moves_preserve_expsum_snf: S3 (1, 2); A5 (1, 1); AK3 (1, 1); Z5xZ5 (5, 5)
    PASS q_moves_preserve_group_order: S3 6->6 (want 6); A5 60->60 (want 60); Z5xZ5 25->25 (want 25); AK3 1->1 (want 1)
    PASS qstar_moves_preserve_group_order: S3 -> 6; A5 -> 60; Z5xZ5 -> 25
    PASS prolongation_preserves_group_order: S3 prolonged 6 retracted 6; Z5xZ5 prolonged 25 retracted 25
    PASS AK_abelianization_trivial: AK(1) det=-1; AK(2) det=-1; AK(3) det=-1; AK(4) det=-1; AK(5) det=-1; AK(6) det=-1
    PASS constructive_reduction_instances: n=2 w=y x^2 y x^-1 y^-1: 16 moves, standard; n=2 w=y^-1 x y x y: 12 moves, standard; n=3 w=x1 x2 x3 x2^-1: 16 moves, standard
    PASS group_order_sanity: <x|x^2> -> 2; <x|x^3> -> 3; <x,y|y> infinite -> None; <x,y|xy> infinite -> None

    ALL 8 CHECKS PASSED

What these checks establish, and what they do not. Checks 2 to 5 treat the
implemented moves as data and verify two invariants after random sequences of
moves: the Smith normal form of the exponent-sum matrix and the order of the
presented group, the latter computed by coset enumeration of the trivial
subgroup. The test presentations and their orders are the symmetric group of
degree three (order 6), the alternating group of degree five (order 60), the
group of order 25 with relators x^5, y^5 and the commutator, and the
Akbulut-Kirby presentation with n = 3. The last entry is a check on the
presentation and not a new result: coset enumeration returns order 1 for the
group with relators xyx(yxy)^{-1} and x^3 y^{-4} [computed here]. Check 7
produces the move sequences of Lemma 8 for three presentations and replays them
from the original presentation to the standard one, so those three instances of
Lemma 8 are certificates and not only arguments. None of these checks says
anything about the Andrews-Curtis conjecture, since each instance is one for
which the moves were constructed by the proof of Lemma 8.

## 9. What I could not verify, and what remains uncertain

- Section 4.1 of Hog-Angeloni and Metzler 1993, where the generalized
  Andrews-Curtis conjecture is stated, was not accessible to me. I quote the
  statement from Barmak 2025 and Barmak's 2018 preprint, both of which cite that
  section.
- Theorem 2.3 of Hog-Angeloni and Metzler 1993 is quoted from Barmak's summary.
- The exact form of Lemma 2.1 and of Theorem 2.4 is quoted from a preview of
  Chapter I of Hog-Angeloni and Metzler 1993 that I read in part; page numbers in
  it run 1 to 50, while the bibliography of Barmak's 2018 preprint gives 1 to 35
  for that chapter.
  The discrepancy is in the bibliographic data and does not affect the content.
- Zeeman 1964 is behind a paywall. I quote the dunce hat facts from Kupers'
  expository notes and from the Encyclopedia of Mathematics entry, and I verified
  the title and venue of Zeeman's paper only.
- Dierker 1968, Lickorish 1970, Cohen 1975, Gillman 1986, Gillman-Rolfsen 1983,
  Kreher-Metzler 1983 and Matveev 1987 are known to me from the bibliography of
  the Encyclopedia of Mathematics entry. I verified the bibliographic data there
  and did not read the papers, so their statements in §7.2 are second-hand and
  labelled.
- Wright 1975 is known to me by title, venue and DOI only; I did not read it.
- The claim that all three conjectures are open is quoted from a 2025
  publication. I did not search for a resolution later than that.
- The family in §7.4 is unverified, as stated there.

## 10. References

Verified bibliographic data, with where I saw each item.

1. J. J. Andrews, M. L. Curtis, Free groups and handlebodies, Proc. Amer. Math.
   Soc. 16 (1965) 192-195. Seen in the reference lists of Barmak 2025 and of the
   Encyclopedia of Mathematics entry (DOI 10.1090/S0002-9939-1965-0173241-8
   appears in the latter).
2. J. A. Barmak, A counterexample to a strong version of the Andrews-Curtis
   conjecture, preprint 2018, arXiv:1806.11493. Read in large part (introduction,
   definitions, Lemma 3, the statement and part of the proof of Theorem 5,
   references) from
   http://mate.dm.uba.ar/~jbarmak/andrewscurtisa.pdf.
3. J. A. Barmak, An exotic presentation of Z x Z and the Andrews-Curtis
   conjecture, Algebr. Geom. Topol. 25 (2025) 345-355, DOI
   10.2140/agt.2025.25.345. Read in part (introduction, definitions, main theorem
   statements, references).
4. J. A. Barmak, The winding invariant, arXiv:1904.10072 (2019). Title and
   identifier from the reference lists of items 2 and 3; not read.
5. I. Bobtcheva, On Quinn's invariants of 2-dimensional CW-complexes,
   arXiv:math/0012121 (2000). Read; source of the remark that six operations
   including stabilisation are called AC-moves there.
6. M. M. Cohen, Dimension estimates in collapsing X times I^2, Topology 14
   (1975) 253-256. Bibliographic data from the Encyclopedia of Mathematics
   entry; not read.
7. P. Dierker, Notes on collapsing K times I where K is a contractible
   polyhedron, Proc. Amer. Math. Soc. 19 (1968) 425-428. Bibliographic data from
   the Encyclopedia of Mathematics entry; not read.
8. X. Fernandez, Morse theory for group presentations, Trans. Amer. Math. Soc.
   377 (2024) 2495-2523, DOI 10.1090/tran/8958, arXiv:1912.00115. Abstract read
   from the arXiv API.
9. D. Gillman, Bing's house and the Zeeman conjecture, Topology Appl. 24 (1986)
   147-151. Bibliographic data from the Encyclopedia of Mathematics entry; not
   read.
10. D. Gillman, D. Rolfsen, The Zeeman conjecture for standard spines is
    equivalent to the Poincare conjecture, Topology 22 (1983) 315-323.
    Bibliographic data from the Encyclopedia of Mathematics entry; not read.
11. C. Hog-Angeloni, W. Metzler, Geometric aspects of two dimensional complexes,
    in Two-dimensional homotopy and combinatorial group theory, London Math. Soc.
    Lecture Note Ser. 197, Cambridge Univ. Press (1993) 1-50. I read in part
    the publisher's preview of Chapter I; it contains (25) to (33),
    Lemmas 2.1 and 2.2 and Theorems 2.3 and 2.4, and I read the text around (25)
    to (33), around Lemma 2.1 and around Theorem 2.4.
12. C. Hog-Angeloni, W. Metzler, The Andrews-Curtis conjecture and its
    generalizations, in the same volume (1993) 365-380. Cited through items 2, 3
    and 11; not read.
13. C. Hog-Angeloni, W. Metzler, Further results concerning the Andrews-Curtis
    conjecture and its generalizations, London Math. Soc. Lecture Note Ser. 446,
    Cambridge Univ. Press (2018) 27-35. Bibliographic data from item 3; not read.
14. R. Kreher, W. Metzler, Simpliziale Transformationen von Polyedren und die
    Zeeman-Vermutung, Topology 22 (1983) 19-26. Bibliographic data from the
    Encyclopedia of Mathematics entry; not read.
15. W. B. R. Lickorish, On collapsing X^2 times I, in Topology of Manifolds,
    Markham (1970) 157-160. Bibliographic data from the Encyclopedia of
    Mathematics entry; not read.
16. S. V. Matveev, Zeeman conjecture for unthickenable special polyhedra is
    equivalent to the Andrews-Curtis conjecture, Sibirsk. Mat. Zh. 28 (1987)
    66-80. Bibliographic data from the Encyclopedia of Mathematics entry; not
    read.
17. J. McCool, A. Pietrowski, On a conjecture of W. Magnus, in Word problems,
    Stud. Logic Found. Math. 71, North-Holland (1973) 453-456. Bibliographic
    data from item 3; statement via item 3.
18. W. Metzler, Ueber den Homotopietyp zweidimensionaler CW-Komplexe und
    Elementartransformationen bei Darstellungen von Gruppen durch Erzeugende und
    definierende Relationen, J. Reine Angew. Math. 285 (1976) 7-23.
    Bibliographic data from item 3; statement via item 3.
19. E. S. Rapaport, Groups of order 1: some properties of presentations, Acta
    Math. 121 (1968) 127-150. Bibliographic data from the Encyclopedia of
    Mathematics entry (item [a42]). Hog-Angeloni and Metzler cite this paper for
    the notion of Q-transformation.
20. Encyclopedia of Mathematics, entry "Low-dimensional topology, problems in",
    https://encyclopediaofmath.org/wiki/Low-dimensional_topology,_problems_in,
    accessed through a search result in this session, because a direct fetch of the
    page returned a server error. Source of the formulation
    of the Andrews-Curtis conjecture as 3-deformability of contractible
    2-complexes, of the Zeeman conjecture and of the two equivalences in §7.2,
    and of the bibliography items 6, 7, 9, 10, 14, 15, 16 and 19.
21. A. Kupers, notes on Zeeman's conjecture,
    https://www.utsc.utoronto.ca/people/kupers/wp-content/uploads/sites/50/zeemansconjecture.pdf, read in excerpt through a search result. Source of the
    description of the dunce hat as a 2-cell attached to a
    circle by a map homotopic to the identity, of the statement that it is
    contractible and not collapsible, and of Cohen's sixth-power result.
22. J. H. C. Whitehead, On adding relations to homotopy groups, Ann. of Math. 42
    (1941) 409-428. Bibliographic data from the Encyclopedia of Mathematics
    entry (item [a30]); the theory of simple homotopy is his.
23. P. Wright, Group presentations and formal deformations, Trans. Amer. Math.
    Soc. 208 (1975) 161-169, DOI 10.1090/S0002-9947-1975-0380813-5.
    Bibliographic data from the Encyclopedia of Mathematics entry and from a
    search result; not read.
24. H. Zieschang, Ueber die Nielsensche Kuerzungsmethode in freien Produkten mit
    Amalgam, Invent. Math. 10 (1970) 4-37. Bibliographic data from item 3;
    statement via item 3.

## 11. One-paragraph summary

Q-equivalence is the Andrews-Curtis relation itself, Q**-equivalence is
3-deformation of standard complexes by a published theorem, and the two differ
by exactly the moves that change the cell structure without changing the
complex's deformation type. The literature's positive results are mostly stated
for Q**, and the gap between Q and Q** on balanced presentations of the trivial
group is the open problem. The two positive classes that I can prove here are
the rank-one case and presentations in which all but one relator are generators,
and the second class comes with explicit move sequences that the script checks.
