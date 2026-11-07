# Dynnikov, "On Zeeman's collapsibility conjecture for non-standard polyhedra": a referee report

Direction E2 of swarm smw2i9i4j (Round 2), written by member m2. The task was to read arXiv:2608.23331
in full, to establish what it proves, whether the standard-polyhedra reduction is proved, and what the
combination with Gillman and Rolfsen 1983 and with Perelman would and would not give, and to compare the
result with `survey/topology.md` section 5.3.

Nothing in this file proves or disproves the Andrews-Curtis conjecture, its stable form, or Zeeman's
conjecture. The only new mathematics below is bookkeeping: two short derivations (section 3) and one
exhaustive computation on cubic graphs (section 4). Everything else is a check of the preprint against
its own text and against sources I name.

**Paths.** The named deliverable is `survey/dynnikov.md` and the check script is `survey/dynnikov_check.py`.
The file tools of a swarm member may write only inside the member's own directory, so as written both files
live at `.ultramath/smw2i9i4j/m2/survey/dynnikov.md` and `.ultramath/smw2i9i4j/m2/dynnikov_check.py`. The
coordinator can place them at the named paths with
`cp .ultramath/smw2i9i4j/m2/survey/dynnikov.md survey/dynnikov.md` and
`cp .ultramath/smw2i9i4j/m2/dynnikov_check.py survey/dynnikov_check.py`. The script's output does not depend
on where it is run from.

## 0. What I read, and what the labels mean

I read the whole preprint, including every proof and every figure reference. The record I read is arXiv:2608.23331 version 1: submitted
24 August 2026, 14:43:35 UTC; author Ivan Dynnikov (Steklov Mathematical Institute); 18 pages, 4 figures;
primary class math.GT; MSC 57Q99 and 20F05; licence CC BY 4.0; no journal reference; the submission history
lists one version only, so there is no revised text to compare with. The arXiv DataCite DOI is
10.48550/arXiv.2608.23331.

I downloaded the LaTeX source from `https://arxiv.org/e-print/2608.23331` and read it in full. The archive
is 22477 bytes gzipped and contains `zeeman-non-standard.tex`, 73277 bytes and 1198 lines, with SHA-256
`b6c275bc8359cc407fff9e123aaa6b0ed8be3f63d1832562dda7605e63be5eb0`. All quotations below are that file
with the LaTeX markup removed, and the wording is the author's. I also fetched the generated HTML to fix
the numbering independently of the source: Conjectures 1.1, 1.2 and 1.3, Theorems 1.4 and 1.5,
Definitions 2.1 to 2.4, Theorem 2.5, Lemma 3.1, Definitions 4.1 and 4.2, Lemmas 4.3, 4.4 and 4.5,
Remark 4.6, Definition 4.7, Lemma 4.8, Lemma 4.9, Remark 4.10, Lemma 4.11, and Lemmas 5.1, 5.2 and 5.3.

I use three labels and I apply them strictly. Section 2 applies exactly one to each claim.

* **PROVED**: the preprint states the claim and gives an argument, and I checked every step of that
  argument that carries mathematical content, by hand or by the computation of section 4. A PROVED label
  says nothing about whether the claim is new.
* **REPORTED**: the preprint states the claim, but its argument rests on at least one step I could not
  check. The step is named in the basis column. REPORTED is not a claim that the statement is false, and
  I found no error in the preprint.
* **REFUTED**: I found an error.

Claims about other people's papers are REPORTED by this definition. I verified their bibliographic data
through Crossref or the arXiv API, and their content through named secondary sources that quote or
restate them; I did not read the Russian originals of Matveev, and I could not obtain the full text of
Gillman and Rolfsen. Section 6 records exactly what I saw for each source.

## 1. What the preprint states

The paper is short and its architecture is easy to describe. Conjecture 1.1 is Zeeman's conjecture: "Let K
be a contractible compact two-dimensional polyhedron. Then K x [0;1] is collapsible." It is abbreviated
ZCC. Conjecture 1.2 is the Andrews-Curtis conjecture with stabilizations, abbreviated ACCS: a balanced
presentation of the trivial group "can be transformed into a trivial balanced presentation" by permuting
relators, inverting a relator, replacing a relator by a product, conjugating a relator, and adjoining a new
generator with the new relator equal to it. Conjecture 1.3 is its topological form: "Any contractible
compact two-polyhedron is three-deformable to a point."

The main results are Theorem 1.4, Theorem 1.5 and the theorem they both follow from, Theorem 2.5. Their
statements, verbatim:

> **Theorem 1.4.** Suppose that there exists a compact contractible two-polyhedron K that is not
> r-collapsible for some r in N. Then there exists a standard contractible two-polyhedron K' which is not
> r-collapsible.

> **Theorem 1.5.** ZCC holds for polyhedra embeddable into three-manifolds.

> **Theorem 2.5.** Let K be a compact contractible two-polyhedron. Then there exists a semi-standard
> two-polyhedron K' = K_1 # K_2 # ... # K_m such that (1) K is three-deformable to K'; (2) if K embeds
> into a three-manifold, then so does K'; (3) if r is in N and each K_i is r-collapsible, then K is also
> r-collapsible.

Two terminological points matter for a reader. First, Definition 2.3 defines r-deformability as the
relation generated by elementary collapses in either direction, through polyhedra of dimension at most r,
so "three-deformable" here means through dimension three. That is Quinn's "2-deformation" and the
Hog-Angeloni-Metzler "3-deformation"; the trap is recorded in `survey/topology.md` section 1.3, and
Dynnikov's usage agrees with Barmak's, as quoted there in section 2. Second, "standard" in this paper is
Definition 2.1: every point of the interior of a 1-cell has link Theta_3 and every vertex has link the
complete graph on four vertices. "Semi-standard" is a connected sum of standard polyhedra.

Remark 4.10 is worth quoting because it is the author's own account of what the extra properties in
Theorem 2.5 cost: "Property (2) in Definition 4.1 is important only for establishing Theorem 1.5. To prove
Theorem 1.4, one can use any transformations that satisfy only Properties (1) and (3). However, the author
is not aware of any type of transformation for which one can prove (3) without Property (2) holding true."

## 2. Verdict table

Fourteen claims, of which two are PROVED, twelve are REPORTED, and none is REFUTED. "Section" refers to
this file except where it names the preprint's own sections.

| # | Claim, verbatim and located | Verdict | Basis |
|---|---|---|---|
| C1 | Abstract and section 1: "We prove that if Zeeman's collapsibility conjecture holds for standard polyhedra, then it holds in general." | REPORTED | Theorem 1.4 with r = 1 gives it immediately (section 3.3), and Theorem 1.4 follows from Theorem 2.5 (3) plus the contractibility of the summands (section 3.5). Theorem 2.5's proof contains the soft steps listed in section 5. |
| C2 | Section 1: "It is well known that this conjecture (which we abbreviate as ZCC) implies the Andrews-Curtis conjecture with stabilizations (ACCS), which states the following." | REPORTED | The paper gives no proof. Section 3.1 gives a two-line derivation from the Wright correspondence, which I did not verify myself. Four sources state the implication: Dynnikov's Conjecture 1.3 is Barmak's reformulation quoted in `survey/topology.md` section 2, and Kupers' Proposition 4.2 and Fagan's thesis Proposition 3.8 state it directly, while Fagan, Qiu and Wang arXiv:2412.12293 state the restricted form they need, that Zeeman for non-embeddable contractible fake surfaces is equivalent to sACC. |
| C3 | Section 1: "PC and ACCS together imply ZCC restricted to the class of standard polyhedra." | PROVED | This is a logical composition of C4 and C5 and I checked the split: a standard contractible polyhedron either is a spine of a compact 3-manifold or it is not, and the two cases are covered. Conditional on C4 and C5, which are REPORTED. |
| C4 | Section 1: "PC implies ZCC restricted to standard spines of compact three-manifolds, as shown by D. Gillman and D. Rolfsen in [GR83]" | REPORTED | Bibliographic data verified by DOI. The statement is verified at second hand from Kupers' Proposition 3.8, which cites Theorem 3 of GR83, and whose wording omits the word "compact". I did not read GR83. Section 6.1. |
| C5 | Section 1: "ACCS implies ZCC for standard polyhedra that are not spines of three-manifolds, which is a result due to S. Matveev [mat87]" | REPORTED | Verified through the zbMATH review of Matveev 1987, which states the theorem with the hypothesis "3-deforms to a point", and through two later sources that place the result opposite the stable conjecture. Kupers 2021 places it opposite the unstable one. Section 6.2. |
| C6 | Section 1: "The aim of the present paper is to show that 'standard' can be omitted from the aforementioned results by Gillman-Rolfsen and Matveev. Thus, since the Poincare conjecture has been proven by G. Perelman, we establish the equivalence of ACCS and ZCC." | REPORTED | The direction ZCC to ACCS is C2. The direction ACCS to ZCC needs Theorem 2.5 with property (3), C4 and C5, and the preprint does not write the derivation out; section 3.2 does. |
| C7 | Theorem 1.4, quoted in section 1 | REPORTED | Derivation in section 3.3. Needs Theorem 2.5 plus the contractibility of the K_i, which the printed statement of Theorem 2.5 omits and the proof of Lemma 5.3 supplies. |
| C8 | Theorem 1.5, quoted in section 1 | REPORTED | The preprint supports it with one sentence: "The Poincare-Perelman theorem, together with the Gillman-Rolfsen theorem and Theorem 2.5 below, also implies the following." Derivation in section 3.4. The theorem is stronger than Gillman-Rolfsen, since it drops standardness. |
| C9 | Theorem 2.5, quoted in section 1 | REPORTED | Assembly of Lemma 5.3 with Lemmas 5.1, 5.2, 4.3, 4.4, 4.5, 4.9 and 4.11. The induction on the non-standardness measure is well founded (section 5, item 7). Lemma 5.3's proof carries the soft steps of section 5. |
| C10 | Lemma 3.1: a contractible compact two-polyhedron satisfies at least one of (K1) standard, (K2) non-empty boundary, (K3) a separating vertex, (K4) a true edge of degree at least four, (K5) a vertex whose link contains two disjoint cycles, (K6) a vertex whose link is K_{3,3}, (K7) a component of the complement of the true 1-skeleton that is not simply connected. | REPORTED | Its graph-theoretic core is machine-checked here for all connected simple cubic graphs on at most 18 vertices (section 4), and the three facts it uses about special trees are proved by hand there. Two reductions in the text are left implicit: that the link of a true vertex may be taken to be a simple graph, and that the case of a disc is covered by condition (K2). Neither looks harmful to me and neither is written out. |
| C11 | Lemma 4.3: if K' is obtained from K by contracting L to L' via a trivial I-fibration f, and K' is collapsible, then K is collapsible. | PROVED | I checked the case analysis. The three cases are sigma and eta both outside L', both inside L', and eta inside with sigma outside; the third uses the trivial I-fibration exactly where the proof says it does. |
| C12 | Lemma 4.4: if K' is obtained from K by a contraction and K' is r-collapsible then K is r-collapsible. Lemma 4.5: a contraction preserves three-deformability and embeddability in a three-manifold. | REPORTED | Lemma 4.4 reduces an arbitrary contraction to disc contractions and then inducts on the dimension of the disc; the reduction is asserted and I did not check it. Lemma 4.5 (ii) contracts L inside a three-manifold and asserts the result is a three-manifold, which needs L to have a ball regular neighbourhood; Definition 4.2 allows any collapsible L. |
| C13 | Lemma 4.9: K x I collapses to a subpolyhedron homeomorphic to s(K,T_1,T_2) x I. Lemma 4.11: every Matveev move decomposes into contractions and special extractions. | REPORTED | Lemma 4.9 is an explicit construction with four cases and two figures. I checked that the displayed formulas for the M_i are consistent with the stated boundaries and I did not check the collapses. Lemma 4.11 identifies Matveev's moves with special extractions and contractions, and sends the reader to [mat87] for the definitions of those moves. |
| C14 | Lemma 5.3: if K is in the class C of contractible polyhedra with empty boundary and no separating vertex, and K is not standard, then K transforms into K_1 # ... # K_m with each K_i in C and smaller non-standardness. | REPORTED | Case (K7) carries the load-bearing delegation to Matveev's technique and an unjustified minimality step. Section 5. |

## 3. The derivations, written out

The preprint leaves three steps to the reader. I write them here so that a referee can attack them
individually. Labels in this section are my own reasoning from labelled ingredients.

### 3.1 Zeeman implies stable Andrews-Curtis (C2)

Let P = <x_1,...,x_n | r_1,...,r_n> be a balanced presentation of the trivial group and let K(P) be its
standard 2-complex. Then K(P) is contractible: the fundamental group is trivial by Seifert and van Kampen,
the Euler characteristic is 1 because the presentation is balanced, so H_2 vanishes and all higher homotopy
This is an **ARGUMENT** from classical facts.

Under ZCC, K(P) x I collapses to a point. The passage from K(P) to K(P) x I is an elementary expansion and
the collapse is a sequence of elementary collapses, and every polyhedron in the sequence has dimension at
most three. So K(P) is three-deformable to a point. By the correspondence between three-deformations of
2-complexes and stable AC moves, P is stably AC-equivalent to the trivial presentation. This is an
**ARGUMENT** conditional on the correspondence.

I did not verify the correspondence myself. It is stated as Definition and Proposition in Fagan's thesis
section 3.2.2 and in Barmak's reformulation quoted in `survey/topology.md` section 2, and Fagan, Qiu and
Wang use the stable form throughout arXiv:2412.12293. That is the reason for the REPORTED verdict on C2 in
section 2.

### 3.2 Stable Andrews-Curtis implies Zeeman (C6, forward direction)

Let K be a compact contractible 2-polyhedron and assume ACCS. Apply Theorem 2.5 and get K' = K_1 # ... # K_m,
semi-standard, three-deformable from K, with property (2) and property (3). By section 3.5 below each K_i is
contractible. Each K_i is standard by construction. A standard contractible polyhedron falls in exactly one
of two classes. If it is a spine of a compact 3-manifold, then that manifold is a regular neighbourhood of
K_i and is contractible, hence a 3-ball by the Poincare theorem, and C4 gives that K_i x I is collapsible.
If it is not a spine of any 3-manifold, then C5 applies, since ACCS gives that K_i, being contractible,
three-deforms to a point; hence K_i x I is collapsible. So each K_i is 1-collapsible, and property (3) with
r = 1 gives that K is 1-collapsible, that is, K x I collapses to a point. This derivation is an
**ARGUMENT** from the sources cited.

Two things are worth recording about this derivation. The preprint does not state it, and in particular it does
not state the contractibility of the K_i, which is needed for C5. The claim "K_i is a spine of a compact
3-manifold" for a standard K_i embedded in a three-manifold is immediate because a regular neighbourhood of
K_i in that manifold is a compact 3-manifold that collapses to K_i. This is an **ARGUMENT**.

### 3.3 Theorem 1.4 from Theorem 2.5

Apply Theorem 2.5 to K and get K_1,...,K_m. If every K_i were r-collapsible then property (3) would make K
r-collapsible, which contradicts the hypothesis. So some K_i is not r-collapsible. That K_i is standard and
contractible, so it is the K' of Theorem 1.4. This is an **ARGUMENT**, and it is the whole content of the sentence
"This theorem follows from Theorem 2.5, which is given in the next section."

### 3.4 Theorem 1.5

Let K be a compact contractible 2-polyhedron that embeds into a three-manifold. Apply Theorem 2.5 and get
K_1,...,K_m. Property (2) says each K_i embeds into a three-manifold, so each K_i is a spine of a compact
3-manifold, and the argument of section 3.2 gives that each K_i is 1-collapsible, using C4 and the Poincare
theorem. Property (3) with r = 1 gives that K is 1-collapsible. This is an **ARGUMENT**.

This derivation needs the same contractibility of the K_i as section 3.2, and it needs C4 to apply to
standard spines of compact 3-manifolds that are not closed. Kupers' statement of Gillman and Rolfsen's
Theorem 3 is about "standard 2-polyhedra that are spines of 3-dimensional PL manifolds", and Kupers'
Lemma 3.7, quoting Gillman and Rolfsen quoting Zeeman, is about "connected 3-dimensional PL manifold with
boundary". So the boundary case is covered by the secondary sources I read, and not by a reading of GR83
itself.

### 3.5 A contractible connected sum has contractible summands

Let K' = K_1 # ... # K_m be a connected sum of connected 2-polyhedra at points, and suppose K' is
contractible. Then each K_i is contractible. This is an **ARGUMENT**, and here is the proof, because both derivations
above use it and the preprint does not state it.

The fundamental group of a connected sum at a point is the free product of the fundamental groups, by van
Kampen applied to the two open pieces. A free product is trivial only if every factor is trivial, so each
K_i is simply connected. For 2-dimensional complexes the Mayer-Vietoris sequence of the same decomposition
gives H_2(K') isomorphic to the direct sum of the H_2(K_i), and the higher homology of a 2-complex vanishes,
so each H_2(K_i) is zero. A simply connected 2-dimensional CW complex with vanishing H_2 has vanishing
second homotopy group by Hurewicz, and all higher homotopy groups vanish for dimension reasons, so it is
contractible by Whitehead's theorem. This completes the argument.

## 4. What I checked by computation

The only part of the preprint that I could turn into an exhaustive check is the graph theory inside the
proof of Lemma 3.1. Here is the reduction. In the proof, after (K2) and (K7) are excluded, a cell
decomposition is chosen with true 1-skeleton equal to the 1-skeleton and true vertices equal to the
vertices. If K is not standard and has no true edge of degree different from three, then there is a vertex v
whose link G is a connected 3-regular graph other than K_4. The proof then takes a shortest cycle s of G of
length m, argues that the complement of s is a forest when (K5) fails, and concludes m is at most 4, with
G equal to K_4 when m = 3 and G equal to K_{3,3} or the triangular prism when m = 4.

I checked two statements about connected simple cubic graphs, exhaustively, with nauty:

* (S1) Every connected simple cubic graph other than K_4, K_{3,3} and the triangular prism contains two
  vertex-disjoint cycles. If (K5) fails then G is one of these three exceptions, which is what the case
  analysis needs.
* (S2) For every connected simple cubic graph G and every shortest cycle s of G such that deleting the
  vertices of s leaves a forest, the length of s is at most 4.

Both hold for all connected cubic graphs on 4, 6, ..., 18 vertices, which is 45982 graphs. The count is
112 graphs up to 12 vertices, 4681 up to 16 vertices, and 45982 up to 18 vertices. The run up to 16
vertices takes 13 seconds and the run up to 18 vertices takes 5 minutes 11 seconds. The script is
`survey/dynnikov_check.py` and the exact commands and outputs are in section 9.

(S1) with vertex-disjoint cycles implies the edge-disjoint reading as well, so the check covers both
readings of the word "disjoint" in (K5). What the check does not cover is the case of a link that is not a
simple graph. Definition 2.1 of the preprint allows non-regular cell complexes ("we do not require the
attaching map of each cell to be injective"), and the proof of Lemma 3.1 does not say why the link of a true
vertex can be taken to be a simple graph. A regular subdivision would give a simple link, and the proof
already allows choosing the cell decomposition, so I expect the gap is only in the writing. I could not
close it from the text.

The proof also uses three facts about what the preprint calls special trees, meaning trees all of whose
vertices have degree one or three. They are that such a tree has at least two leaves, that it has exactly
two leaves only when it is a single edge, and that two of its leaves are at distance at most two. These
have short proofs, which I give because the exhaustive check does not cover them. Write L for the number of
leaves and I for the number of internal vertices; counting degrees gives L + 3I = 2(L + I - 1), so I = L - 2
and L is at least 2. If L = 2 then I = 0 and the tree is a single edge. For the distance claim, take a
longest path v_0 ... v_k and look at v_1: it has degree three, one of its neighbours is v_0, and at most one
of its other neighbours can be internal, since two internal neighbours would allow a longer path; so v_1 has
a second leaf neighbour at distance two from v_0. This is an **ARGUMENT** from elementary counting.

## 5. Where the proof is soft, in order of load-bearingness

The preprint is written in the compressed style of expert PL topology, with four figures carrying part of
the argument. I list every place where the text asserts something and does not prove it, with the line
number in the LaTeX source, so that a later referee can go straight to the weakest point. These are the
reasons for the REPORTED labels in section 2.

1. **The passage to Matveev moves in Case (K7), lines 1105 and 1111.** This is the weakest point in the
   paper. The text says: "Using Matveev's technique, one can deduce from this that the transition from Q to
   Q_1 can be performed by a sequence of Matveev moves. It is explained in [mat87, section 3] how to produce
   a sequence of T_i^{+-1}-moves, i = 1,2,3, and the method of excluding T_3-moves is described in [mat87,
   section 5]." It then says: "Since the polyhedra Q and Q_1 are not standard, one cannot apply the results
   of [mat87] directly; however one can see that the procedure described in [mat87] works perfectly well in
   the present situation." Everything here depends on a reading of a 1987 Russian paper, and the transfer
   from standard polyhedra to the non-standard Q and Q_1 is asserted, not proved. A referee cannot certify
   this step without redoing sections 3 and 5 of Matveev 1987 for the non-standard case.
2. **The minimality of P in Case (K7), lines 1016 to 1045.** The text begins "Let P be a minimal
   contractible subpolyhedron of K such that the boundary of the regular neighbourhood of P is a disjoint
   union (possibly empty) of essential simple closed curves." The family in question contains K itself, with
   empty boundary, so the statement is not vacuous. The paper gives no argument that a minimal element
   exists, and the family of subpolyhedra is infinite. A proof would fix a finite cell decomposition and
   minimise over subcomplexes, or minimise a numerical measure. The subsequent contradiction uses the
   minimality essentially. I could not fill this in from the text.
3. **The two-sentence treatment of Case (K6), lines 999 to 1012.** "One can see that there exists a bigon
   whose boundary contains a_2 and a_3." The claim is about the two figures `k33t1.eps` and `k33aaa.eps`,
   which I did not check. The figures are 762 and 1545 bytes of encapsulated PostScript and I read neither
   picture.
4. **The assertion in Case (K5), line 972.** "One can see that no true edge of degree strictly greater than
   three can arise." This is a check on the effect of a T_1,T_2-extraction on the true 1-skeleton, and it is
   plausible from Definition 4.7, which I did read. I did not verify it.
5. **The long construction in Lemma 4.9, lines 503 to 739.** The polyhedra M_1, M_2 and M_3 are written
   down explicitly and I checked that the displayed formulas for their boundaries are mutually consistent,
   including the two identifications of the boundary of the regular neighbourhood with G_1 and G_2. The four
   cases of the collapsing argument, and the two figures `tilde-hat-1.eps` and `tilde-hat-2.eps`, I did not
   check.
6. **Lemma 4.11, lines 766 to 807.** The lemma identifies Matveev's T-moves with special extractions and
   contractions, and the paper itself says "The reader is referred to [mat87] for the definitions of the
   moves." So the lemma's statement cannot be checked without Matveev 1987, and I did not read it.
7. **The induction in Lemma 5.3, lines 834 to 878.** This one I did check, because an induction on a
   lexicographic order of sequences is exactly the kind of step that goes wrong silently. The measure is the
   quadruple of the lexicographically ordered sequence of degrees of true edges of degree at least four, the
   lexicographically ordered sequence of first Betti numbers of links of non-standard vertices, the number of
   true vertices, and the first Betti number of the complement of the true 1-skeleton. Finite sequences of
   natural numbers in lexicographic order, with a proper prefix smaller than its extensions, are well ordered
   of type omega to the omega, so the quadruple is well founded, and the paper's claim that it is well
   ordered is correct. The claim that removing one entry equal to the maximum degree and adding finitely many
   strictly smaller entries decreases the sequence is also correct. So this step is sound.

## 6. What the cited sources actually say

The preprint cites eleven items. I verified the bibliographic data of the ones that carry weight through
Crossref or the arXiv API, and I checked their content through secondary sources that quote or restate them.
None of this is a reading of the original papers, and I say so for each item.

### 6.1 Gillman and Rolfsen 1983

D. Gillman and D. Rolfsen, "The Zeeman conjecture for standard spines is equivalent to the Poincare
conjecture", Topology 22 (1983), no. 3, 315-323, DOI 10.1016/0040-9383(83)90017-4. Crossref returns the
title, the journal, the volume, the issue, the pages and the author names exactly as the preprint gives
them. I could not obtain the paper itself.

The statement the preprint attributes to it is verified at second hand from Kupers' survey, Proposition
3.8: "Zeeman's conjecture for standard 2-polyhedra that are spines of 3-dimensional PL manifolds is
equivalent the Poincare conjecture", attributed there to Theorem 3 of GR83, with a sketch in which the
reverse implication runs through the fact that if M is a homotopy ball and K is a standard spine then
K x I collapses to something homeomorphic to M. The missing "to" in that quotation is Kupers'. So
Dynnikov's "PC implies ZCC restricted to standard spines of compact three-manifolds" is the correct
direction, and the word "compact" does not appear in Kupers' statement of it.

### 6.2 Matveev 1987, and the question whether the result is about AC or about stable AC

S. V. Matveev, "The Zeeman conjecture for nonthickenable special polyhedra is equivalent to the
Andrews-Curtis conjecture", Sibirsk. Mat. Zh. 28 (1987), no. 6, 66-80; English translation in Siberian
Math. J. 28 (1987), no. 6, 917-928, DOI 10.1007/bf00969470. Crossref returns the translation title as
"Zeeman's conjecture for unthickened special polyhedra is equivalent to the Andrews-Curtis conjecture", the
volume 28, the issue 6, the pages 917-928 and the author Matveev. The zbMATH record is Zbl 0638.57002.

The content matters, because the preprint uses the result as "ACCS implies ZCC" and the title says
"Andrews-Curtis conjecture", and those are different conjectures. The zbMATH review of Zbl 0638.57002
states the main theorem as follows, and I quote it exactly: "Theorem. The special polyhedron Q cannot be
embedded in a 3-manifold. If Q 3-deforms to a 2-dimensional polyhedron X, then Q x I collapses to a subset
which is homeomorphic with X." The review continues: "This implies that the Zeeman conjecture is true for
each special polyhedron Q, which 3-deforms to the point and is unthickenable (i.e. cannot be embedded in a
3-manifold). The equivalence mentioned in the title is the consequence of this fact."

The hypothesis in that theorem is that Q three-deforms to a point, which is the topological form of stable
AC-triviality, not of AC-triviality. So the zbMATH review supports the preprint's reading, and not the
reading in which the hypothesis is the unstable conjecture. Three later sources agree. Fagan's thesis,
Proposition 4.6, states "The Zeeman conjecture for non-spine fake surfaces is equivalent to the stable
Andrews-Curtis conjecture", citing Matveev's book, Corollary 1.3.57. Gorelov, arXiv:2103.16464 version 2 of
6 March 2026, writes in the introduction that "another special case is equivalent to the stable
Andrews-Curtis conjecture", citing Matveev's paper, and refers to subsection 1.3.4 of Matveev's book for
the proofs of both equivalences. Dynnikov's preprint says the same. Kupers' 2021 survey is the exception:
its Proposition 4.3 reads "Zeeman's conjecture for standard complexes that are not spines of 3-manifolds is
equivalent to the Andrews-Curtis conjecture", which I now regard as loose phrasing. The print source that would settle it is subsection 1.3.4 of S. Matveev, Algorithmic
Topology and Classification of 3-Manifolds, second edition, Algorithms and Computation in Mathematics 9,
Springer 2007, DOI 10.1007/978-3-540-45899-9, which I did not read.

This resolves, in favour of the stable reading, the discrepancy that `survey/stable-ac.md` section 4 records
and leaves open. The resolution rests on one review and two secondary restatements, and not on the Russian
original.

There is a second point of content. Matveev's class is the set of polyhedra that cannot be embedded in a
three-manifold; the preprint says "standard polyhedra that are not spines of three-manifolds". For a
standard polyhedron the two conditions agree, because a regular neighbourhood of the polyhedron in a
three-manifold is a compact 3-manifold that collapses to it. This is an **ARGUMENT**.

### 6.3 Kupers 2021

A. Kupers, "Zeeman's conjecture", Graduate Journal of Mathematics 6 (2021) 35-42; I read the author's PDF
from his Toronto page, 393 lines of extracted text. This is the survey that `survey/topology.md` relies on
in section 5. Its Proposition 3.8 and its Proposition 4.3 are quoted above. Its Proposition 4.2, "Zeeman's
conjecture implies the Andrews-Curtis conjecture", is stated in the unstable form, which is stronger than
what the preprint asserts in C2 and stronger than what Barmak's reformulation supports. Since
`survey/topology.md` section 2 quotes Barmak saying that the Q** form is the one equivalent to
three-deformability to a point, I record Kupers' unstable phrasing as a second place where a survey uses
"Andrews-Curtis" loosely.

[Coordinator note, 6 November 2026, from the round-6 citation audit (.ultramath/smw3ow2dp/m3/audit.md,
C16), confirmed against the live gradmath.org PDF (sha256 6d9d1263b3cdb547..., byte-identical to the
audit's copy): the paragraph above is wrong on both the number and the form. The live PDF's section 4
has Conjecture 4.1, Remark 4.2 (on which printed moves are consequences of the others), Proposition 4.3
("Zeeman's conjecture implies the Andrews-Curtis conjecture with stabilisations"), Remark 4.4 and
Proposition 4.5. There is no Proposition 4.2 of the quoted content, and Proposition 4.3 states the
implication in the STABLE form, which is weaker than the unstable form and is exactly the form Barmak's
Q** reformulation supports. The charge that Kupers "uses Andrews-Curtis loosely" is therefore withdrawn
for this implication; Kupers states the stable form, correctly. Two related numberings in this survey are
also off by the same shift: the C2 row of the claim table cites "Kupers' Proposition 4.2" for the
implication (read Proposition 4.3), and section 6.2 quotes "its Proposition 4.3" for the non-spine
equivalence (that is Proposition 4.5 in the PDF). The citation of Kupers for the polyhedral definition of
collapsibility, used by the downward-propagation direction, is sound.]

### 6.4 Items verified for bibliographic data only

Zeeman, "On the dunce hat", Topology 2 (1964) 341-358, DOI 10.1016/0040-9383(63)90014-4; Crossref returns
issue year 1963 for the volume dated 1964, which is the same anomaly `survey/topology.md` section 8 records.
M. M. Cohen, "Dimension estimates in collapsing X x I^q", Topology 14 (1975) no. 3, 253-256, DOI
10.1016/0040-9383(75)90006-3; verified. Matveev's second 1987 paper, "Transformations of special spines and
the Zeeman conjecture", Izv. Akad. Nauk SSSR Ser. Mat. 51 (1987) no. 5, 1104-1116, is zbMATH Zbl 0642.57003,
and its review states that any two special spines of a 3-manifold are connected by a finite sequence of
elementary transformations, which is the technique the preprint invokes. Andrews-Curtis 1965, the three
Perelman preprints and Morgan-Tian I did not check, since nothing in the verdicts depends on them.

### 6.5 What was on record before 24 August 2026

I searched for an earlier statement of the unrestricted equivalence. What I found is the following. Gorelov
writes, in a version of March 2026, that a special case of Zeeman's conjecture is equivalent to the stable
conjecture and that "as far as the author knows, the latter two problems remain open". Fagan's thesis, of
November 2025, proves the equivalence only after restricting to fake surfaces, and separately for the spine
case. Fagan, Qiu and Wang, arXiv:2412.12293, likewise restrict to fake surfaces. The Tao SAIR competition
post of 11 September 2026 says that the stable conjecture "is also equivalent to a restricted form of
another easy-to-state hard-to-prove open conjecture in low-dimensional topology: Zeeman's conjecture".

So on the record I could find, the equivalence of the unrestricted Zeeman conjecture with the stable
Andrews-Curtis conjecture was not stated before this preprint, and every earlier statement restricts to a
class. I did not search the printed literature exhaustively, and I did not read Matveev's book section
1.3.4. The claim that the unrestricted equivalence is new is therefore a statement about what I found, not
a priority claim.

## 7. Comparison with `survey/topology.md` section 5.3

The Round 1 survey flagged one tension and asked a later referee to read the preprint in full. Here is the
comparison, with a dated note. I have not edited `survey/topology.md`, because it is another member's file;
this section is the correction of record.

**What the survey got right.** It recorded that Zeeman's conjecture implies AC, that the thickenable
standard case reduces to the Poincare conjecture, that Matveev proved a converse for a restricted class,
and that a counterexample to AC built from a non-thickenable special polyhedron would refute Zeeman's
conjecture. It was also right to refuse the claim that Zeeman's conjecture is equivalent to AC together with
the Poincare conjecture, because the non-standard case was not covered by its sources.

**The flagged tension is a misreading, and it is in the survey.** Section 5.3 says "by the paragraph above,
Zeeman's conjecture for the thickenable standard polyhedra already follows from Perelman's theorem. Anyone
relying on that preprint should read its precise hypotheses." The word that carries the weight is
"thickenable". Perelman's theorem together with Gillman and Rolfsen settles the standard polyhedra that are
spines of 3-manifolds. It says nothing about standard polyhedra that are not spines of any 3-manifold, and
those are exactly the class to which Matveev's result applies and to which the preprint's hypothesis
extends. So the preprint's hypothesis, "Zeeman's conjecture holds for standard polyhedra", is not known to
hold, and there is no inconsistency between it and Perelman's theorem. The survey's sentence conflated
"standard" with "thickenable".

**Two corrections.** First, the survey writes that for the non-thickenable special polyhedra the conjecture
"is equivalent to AC". The weight of the sources I read is that the equivalence is with the stable
conjecture, as set out in section 6.2. Second, the survey's paragraph on the preprint should not be read as
a warning about a false claim; it is a warning about reading a hypothesis that is not known to be
satisfied, which is correct but is not the point it makes.

**What the preprint adds to the survey's picture.** The survey's picture leaves a gap between
non-thickenable standard polyhedra and arbitrary contractible 2-polyhedra. Theorem 2.5 is exactly a
statement that closes the gap, subject to the soft steps of section 5. If it holds, the picture becomes:
Zeeman's conjecture is equivalent to the stable Andrews-Curtis conjecture, and the Poincare theorem settles
the part of it that concerns spines of 3-manifolds. That is a cleaner statement than anything in the Round 1
survey, and it is the first place in this campaign where the stable conjecture and Zeeman's conjecture are
identified without a restriction.

## 8. What this gives the campaign, and what stays uncertain

If the preprint is correct, then Zeeman's conjecture and the stable Andrews-Curtis conjecture are the same
problem. Three consequences follow for this campaign. Any theorem that establishes stable triviality for a
class of presentations transfers to Zeeman's conjecture for the corresponding 2-complexes, so the
complexity-five theorem of Fagan, Qiu and Wang transfers as its authors already intended. Conversely, a
counterexample to the stable conjecture would refute Zeeman's conjecture, which makes the bounded searches
of the campaign relevant to a topological statement. And the stable status of AK(3), which is the subject of
direction E1, is a question about the stable conjecture, so it is also a question about Zeeman's conjecture
for the corresponding 2-complex.

Nothing here bears on the unstable Andrews-Curtis conjecture. The preprint does not claim a proof or a
disproof of any open conjecture, and neither do I.

What stays uncertain is the proof of Theorem 2.5, and through it the headline. My verdict is REPORTED, for one reason: the proof of Lemma 5.3 delegates a step to Matveev's technique and asserts that the
technique transfers to non-standard polyhedra, and I cannot check that assertion without the Russian paper
and without more time than a referee has. The rest of the proof I followed, and the parts I could check
hold. Two smaller uncertainties are worth recording. The paper is a first version with no journal
reference and no revision history, so nothing about it has been refereed or corrected. The acknowledgements
say "Google Gemini (Web version) was used solely for the purpose of final language editing", which I record
as provenance and not as a criticism; the four figures and the "one can see" steps are the places where a
reader should look hardest.

Two cosmetic defects suggest that the text was not proofread after the final edit. Section 1 has "is also an
quick corollary". Lemma 4.4 begins "Let K' be a polyhedrn obtained from a compact polyhedron K". Lemma 5.2
has malformed emphasis markup, written `\emph(` and `\emph)` where braces were intended, which will misprint
the parenthesis in the remark. None of these affects the mathematics.

## 9. Commands and outputs

The preprint and its source:

```
curl -sS -L -o paper/src.bin https://arxiv.org/e-print/2608.23331
gunzip -c paper/src.bin > paper/src.tar && tar -xf paper/src.tar
sha256sum paper/zeeman-non-standard.tex
# b6c275bc8359cc407fff9e123aaa6b0ed8be3f63d1832562dda7605e63be5eb0
```

The arXiv record, listing one version:

```
curl -sS "http://export.arxiv.org/api/query?id_list=2608.23331"
# totalResults 1; published 2026-08-24T14:43:35Z; comment "18 pages, 4 figures"
```

The bibliographic checks, all of which returned the data quoted in section 6:

```
curl -sS https://api.crossref.org/works/10.1016/0040-9383(83)90017-4   # Gillman-Rolfsen
curl -sS https://api.crossref.org/works/10.1016/0040-9383(63)90014-4   # Zeeman
curl -sS https://api.crossref.org/works/10.1016/0040-9383(75)90006-3   # Cohen
curl -sS https://api.crossref.org/works/10.1007/bf00969470            # Matveev, Siberian Math. J.
curl -sS https://api.crossref.org/works/10.1007/978-3-540-45899-9     # Matveev, book
curl -sS "https://api.zbmath.org/v1/document/_search?search_string=an%3A0632.57004"   # Matveev, Zbl
```

The computation of section 4, whose output is reproduced verbatim:

```
python3 survey/dynnikov_check.py 16
# graphs checked: 4681 for n = 4 to 16 step 2
# (S1) ... without two vertex-disjoint cycles: 0
# (S2) ... length exceeds 4: 0
# OVERALL PASS

python3 survey/dynnikov_check.py 18
# graphs checked: 45982 for n = 4 to 18 step 2
# (S1) ... without two vertex-disjoint cycles: 0
# (S2) ... length exceeds 4: 0
# OVERALL PASS
```

The first run takes 13 seconds and the second 5 minutes 11 seconds on this VM. The script calls
`nauty-geng -c -d3 -D3 n` and makes no random choices, so the output is a function of the input alone.

## 10. What I could not verify

1. The content of Matveev 1987, in either the Russian original or the English translation. I read the
   zbMATH review and two later restatements, and I read the review of the companion paper.
2. The content of Gillman and Rolfsen 1983. I read Kupers' statement of their Theorem 3 and his sketch of
   its proof.
3. Subsection 1.3.4 of Matveev's book, which is where the equivalence with the stable conjecture is
   proved according to Fagan and to Gorelov.
4. The four figures of the preprint, and therefore the two steps in Cases (K5) and (K6) that refer to them.
5. The transfer of Matveev's technique to non-standard polyhedra, which is the load-bearing step of Case
   (K7), and the existence of the minimal P in the same case.
6. The correspondence between three-deformations and stable AC moves, which is a literature statement in
   `survey/stable-ac.md` section 3 and in Fagan's thesis, and which I did not verify.

None of these six items changes a verdict from REPORTED to PROVED, and none of them produces a refutation.
The preprint's central claim is unrefuted and unverified by me, and that is the honest summary.
