# Andrews-Curtis conjecture: a bibliography with checked identifiers

Compiled for the swarm's Round 1, as the canonical reference list for the run.
Nothing in this file is a mathematical claim made by me. Each entry records what a
listed work is and what it is useful for. Where a source states a mathematical
fact, the statement is attributed to that source and no further.

## 0. Reading path for this campaign

A reader who needs the definitions should take 1.1, 2.1 and 2.3 in that order.
For the topological side the core is 4.2, 4.3 and 4.5, with 1.4 and 1.7 behind them.
For complexity the core is 5.1, 5.4 and 5.6. For the computational baseline the two
papers to reproduce are 6.1 and 6.2, and the current frontier is in 6.7, 6.8, 6.9,
7.3, 7.4, 7.5 and 7.6. The finite-group analogue, which is the one place where the
question is settled, is 8.1 and 8.3. The two named families are in 4.2 and 10.2, and
the most recent statements about their status are 6.7, 7.5 and 2.9.

## How the entries were checked

Every entry carries a status label.

- **[V]** The item's own bibliographic record was seen in this run, at a publisher
  landing page, a MathSciNet relay record, a zbMATH or MaRDI record, or the arXiv
  abstract page. Title, authors, year, venue and identifier were read off that record.
- **[S]** The item was seen cited with full bibliographic data in a published
  reference list or another author's own publication list, and its own record was
  not opened. Volume and page data rest on that secondary witness.
- **[U]** Listed at the end under unverified items, with a statement of what was seen.

Section 13 is the list of [U] items, so those entries carry no label of their own.
The legend above applies to sections 1 to 12 and does not extend to them.

The tools available in this run were a web search tool and direct HTTP fetches. A
rerunnable check of the machine-readable identifiers, that is the DOIs and the arXiv
identifiers, is in `check_refs.py`, with its recorded output in `check_refs.out`.
For each identifier the script asks the registration agency for metadata and
requires the returned title to contain an expected fragment, so it tests that the
identifier belongs to the work named here and not only that it resolves. It does not
test the volume, the pages or the year, and it does not test the relevance line.

Two bibliographic cautions were earned in this run. A search engine returned two
different JSTOR DOIs for the Andrews-Curtis paper, and one widely quoted arXiv
number for Bridson's paper is wrong by two digits. Both are corrected below. Both
are reasons to treat an identifier absent from this list with suspicion.

## 1. Origin and foundations

1.1 **[V]** J. J. Andrews and M. L. Curtis, *Free groups and handlebodies*,
Proc. Amer. Math. Soc. 16 (1965), no. 2, 192-195.
DOI: 10.1090/S0002-9939-1965-0173241-8. JSTOR 2033843. zbMATH 0131.38301.
Use: the origin of the conjecture. The paper states it, gives the topological
consequence that regular neighbourhoods of contractible 2-dimensional subcomplexes
of combinatorial 5-manifolds would be 5-cells, and records a referee's remark on a
weakened form of the conjecture.

1.2 **[V]** J. J. Andrews and M. L. Curtis, *Extended Nielsen operations in free
groups*, Amer. Math. Monthly 73 (1966), 21-28.
DOI: 10.1080/00029890.1966.11970717 (JSTOR form 10.2307/2313917).
Use: the source of the phrase "extended Nielsen operations", which Miller and
Schupp and Hog-Angeloni and Metzler use for what other papers call Q**-moves.

1.3 **[V]** J. Nielsen, *Die Isomorphismengruppe der freien Gruppen*,
Math. Ann. 91 (1924), 169-209. MR1512188. EuDML record 159045.
Use: Nielsen transformations. These are the free-group automorphisms behind the
first two types of Andrews-Curtis move.

1.4 **[V]** J. H. C. Whitehead, *Simplicial spaces, nuclei and m-groups*,
Proc. London Math. Soc. (2) 45 (1939), 243-327. DOI: 10.1112/plms/s2-45.1.243.
Use: simple homotopy, elementary expansions and collapses. It is the framework in
which Andrews-Curtis moves correspond to 3-deformations of 2-complexes.

1.5 **[V]** R. H. Fox, *Free differential calculus I: Derivation in the free group
ring*, Ann. of Math. (2) 57 (1953), 547-560. DOI: 10.2307/1969736.
Use: Fox derivatives. The Alexander matrix and its elementary ideals are the
standard algebraic invariants computed from a presentation, so any discussion of
presentation invariants for this conjecture starts here.

1.6 **[V]** R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*,
Classics in Mathematics, Springer, 2001, a reprint of the 1977 edition, Ergebnisse
der Mathematik und ihrer Grenzgebiete 89. DOI: 10.1007/978-3-642-61896-3.
Use: standard reference for free groups, Nielsen transformations, Tietze
transformations and the geometry of presentations.

1.7 **[V]** M. M. Cohen, *A Course in Simple-Homotopy Theory*, Graduate Texts in
Mathematics 10, Springer, 1973. DOI: 10.1007/978-1-4684-9372-6.
Use: textbook treatment of simple homotopy types, the Whitehead group, and the
dimension obstruction that makes 2-complexes special.

## 2. Surveys and problem lists

2.1 **[V]** R. G. Burns and O. Macedonska, *Balanced presentations of the trivial
group*, Bull. London Math. Soc. 25 (1993), no. 6, 513-526. DOI: 10.1112/blms/25.6.513.
Use: the group-theoretic survey of partial results. It sets up annihilating
$n$-tuples, the elementary M-transformation, and a reformulation of the conjecture
as finiteness of the complexity of every annihilating tuple. Both Miller and Schupp
and Baumslag, Myasnikov and Shpilrain point to this survey.

2.2 **[V]** C. Hog-Angeloni, W. Metzler and A. J. Sieradski (eds.),
*Two-Dimensional Homotopy and Combinatorial Group Theory*, London Mathematical
Society Lecture Note Series 197, Cambridge University Press, 1993.
DOI: 10.1017/CBO9780511629358.
Use: the standard book-length treatment of 2-complexes and presentations, with
chapters on the Zeeman, Whitehead and Andrews-Curtis conjectures.

2.3 **[V]** C. Hog-Angeloni and W. Metzler, *The Andrews-Curtis conjecture and its
generalizations*, in the volume above, pp. 365-380.
DOI: 10.1017/CBO9780511629358.014.
Use: the precise move definitions used in this literature. Q-transformations are
sequences of conjugation, inversion and multiplication of a relator by another
relator. Q*-transformations add substitutions of generators inside relators.
Q**-transformations add extension by a new generator and a relator equal to that
generator. Its Theorem 2.4 states that 3-deformation types of compact connected
2-dimensional CW-complexes correspond bijectively to Q**-classes of finite
presentations. It also records that Q**-transformations preserve the deficiency.

2.4 **[V]** S. Matveev and D. Rolfsen, *Zeeman's collapsing conjecture*, in the
volume above, pp. 335-363. DOI of the chapter not confirmed.
Use: the survey of Zeeman's conjecture that $K \times I$ is collapsible for every
contractible 2-polyhedron $K$, which is the topological relative of the stable
statement.

2.5 **[V]** G. Baumslag, A. Myasnikov and V. Shpilrain, *Open problems in
combinatorial group theory. Second edition*, Contemp. Math. 296 (2002), Amer.
Math. Soc., pp. 1-38. DOI: 10.1090/conm/296/05067.
Use: problem O1 is the conjecture. The entry collects the standard formulations,
the stabilisation formulation and a reading list, and it records the claim that all
presentations of the trivial group with total relator length at most 12 satisfy the
conjecture.

2.6 **[V]** R. Kirby, *Problems in low dimensional manifold theory*, Proc. Sympos.
Pure Math. 32, part 2 (1978), 273-312. DOI: 10.1090/pspum/032.2/520548.
MR0520548.
Use: the 1978 problem list. The Akbulut-Kirby paper refers to its problems 5.1 and
5.2 in connection with their presentation, so this is where the topological
question was first put in list form.

2.7 **[V]** R. Kirby (ed.), *Problems in low-dimensional topology*, in Geometric
Topology, Athens, Georgia, 1993, AMS/IP Studies in Advanced Mathematics 2.2,
American Mathematical Society, 1997, pp. 35-473. MR1470751.
Use: the later problem list, which carries the updated entry on the conjecture and
on the Akbulut-Kirby 4-sphere.

2.8 **[S]** V. D. Mazurov and E. I. Khukhro, *Unsolved problems in group theory:
the Kourovka Notebook*, no. 18, arXiv:1401.0300.
Use: the standard collection of open problems in group theory. Lishak cites it as a
place where the conjecture is recorded among open problems.

2.9 **[V]** T. Tao, *SAIR competition: Andrews-Curtis challenge*, blog post,
11 September 2026.
https://terrytao.wordpress.com/2026/09/11/sair-competition-andrew-curtis-challenge/
Use: a current, non-peer-reviewed statement of the state of play, and the
announcement of an active competition with a discovery track and a proof track. It
asserts that AC-triviality of the Akbulut-Kirby family is open for $n \geq 3$, that
total relator length 13 is the shortest possible two-generator counterexample up to
AC-equivalence, and that lower bounds such as Bridson's survive stabilisation. Treat
it as a secondary source dated 2026.

## 3. Q-transformations, 3-deformations and simple homotopy

3.1 **[V]** P. Wright, *Group presentations and formal deformations*, Trans. Amer.
Math. Soc. 208 (1975), 161-169. DOI: 10.1090/S0002-9947-1975-0380813-5
(JSTOR form 10.2307/1997282).
Use: the paper that makes the presentation-move and 3-deformation dictionary
precise. It lists presentation operations, namely cyclic permutation of a relator,
inversion, adding a generator together with a relator $aw$, and deleting such a
pair. It realises them by expansions and collapses of the standard 2-complex, and
it proves an equivalence between formal 3-deformation of 2-polyhedra and
transformation of presentations by the operations (1) to (5) listed in the paper.

3.2 **[V]** S. G. Ivanov, *Q-transformations and Q-equivalence*, Mathematical
Notes 68 (2000), 661-663. DOI: 10.1023/A:1026683910833. zbMATH 1001.20029.
Use: a purely combinatorial characterisation of Q-equivalence for balanced
presentations of the trivial group, by inversion, conjugation and a truncation move.
Its zbMATH review states the main theorem in those terms.

3.3 **[V]** J. H. C. Whitehead, see 1.4, and M. M. Cohen, see 1.7.
Use: the two references for the relation between simple homotopy equivalence of
2-complexes and formal deformations, which is the step where the conjecture becomes
a statement about an obstruction computed from the presentation.

3.4 **[V]** W. Metzler, *On the generalized Andrews-Curtis problem: a disproof of
the relative case*, arXiv:2102.03212, submitted 5 February 2021. The arXiv metadata
prints the title with a double hyphen where a dash is meant. Publication status not
confirmed in this run.
Use: a claimed counterexample to a relative form of the generalised conjecture,
where subcomplexes are required to stay fixed during the deformation. It bears on
the boundary between what Q**-moves can and cannot do.

## 4. Topology: 2-complexes, spines and 4-manifolds

4.1 **[V]** E. C. Zeeman, *On the dunce hat*, Topology 2 (1963), 341-358.
DOI: 10.1016/0040-9383(63)90014-4.
Use: the dunce hat as the standard example of a contractible 2-complex that is not
collapsible, and the observation that it becomes collapsible after crossing with an
interval. This is the origin of Zeeman's conjecture.

4.2 **[V]** S. Akbulut and R. Kirby, *A potential smooth counterexample in
dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the
Andrews-Curtis conjecture*, Topology 24 (1985), no. 4, 375-390.
DOI: 10.1016/0040-9383(85)90010-2. MR0816520.
Use: the source of the family. The presentation printed in the paper is
$\langle x, y \mid xyx = yxy,\ x^5 = y^4 \rangle$, and the paper says that the group
is easily seen to be trivial while trivialisation by Andrews-Curtis moves seems
difficult. The family later indexed as $AK(n) = \langle x,y \mid xyx = yxy,\
x^n = y^{n+1}\rangle$ agrees with the printed one at $n = 4$ after exchanging $x$
and $y$, which is immediate from the relations. The paper also builds the
associated homotopy 4-sphere from two 1-handles and two 2-handles, with no
3-handles.

4.3 **[V]** R. E. Gompf, *Killing the Akbulut-Kirby 4-sphere, with relevance to the
Andrews-Curtis and Schoenflies problems*, Topology 30 (1991), no. 1, 97-115.
DOI: 10.1016/0040-9383(91)90036-4. zbMATH 0715.57016.
Use: the paper that shows the Akbulut-Kirby homotopy 4-sphere is standard, by handle
moves that pass through intermediate 3-handles. The zbMATH review states that it
avoids the Andrews-Curtis question in doing so. This is the basic example of why a
counterexample of the right kind would matter, and of why killing the manifold does
not settle the presentation.

4.4 **[V]** M. H. Freedman, *The topology of four-dimensional manifolds*,
J. Differential Geom. 17 (1982), 357-453. DOI: 10.4310/jdg/1214437136.
Use: the topological classification of simply connected 4-manifolds. It is why the
Akbulut-Kirby manifold is homeomorphic to $S^4$ and why the remaining question is
smooth.

4.5 **[V]** M. H. Freedman and F. Quinn, *Topology of 4-Manifolds*, Princeton
Mathematical Series 39, Princeton University Press, 1990. JSTOR stable identifier
j.ctt7ztz2d.
Use: the book-length account, including topological handle theory.

4.6 **[S]** F. Quinn, *Isotopy of four-manifolds*, J. Differential Geom. 24 (1986),
343-372.
Use: cited in later work on isotopy and concordance of 4-manifolds. I did not read
it in this run, so no content claim is made here.

4.7 **[S]** M. G. Scharlemann, *The four-dimensional Schoenflies conjecture is true
for genus two imbeddings*, Topology 23 (1984), no. 2, 211-217.
DOI: 10.1016/0040-9383(84)90040-5.
Use: the partial result on the smooth Schoenflies conjecture that the
Akbulut-Kirby paper compares its own example with.

4.8 **[V]** E. Romary and A. Zupan, *A family of Andrews-Curtis trivializations via
4-manifold trisections*, Geometriae Dedicata (2024).
DOI: 10.1007/s10711-024-00891-6. arXiv:2304.03196.
Use: a topological construction of trivialisations. R-links $L(3,2;c/d)$ give
balanced presentations, and the paper proves that every presentation of the form
$P(3,2;4/d)$ is AC-trivial, by trisection arguments. It also records that
$L(3,2;2n/(2n+1))$ induces $\langle x,y \mid xyx = yxy,\ x^{n+1} = y^n\rangle$,
which is the Akbulut-Kirby family with the generators exchanged.

4.9 **[S]** B. Lishak and A. Nabutovsky, *Sizes of spaces of triangulations of
4-manifold and balanced presentations of the trivial group*, J. Topol. Anal. 11
(2019), no. 2. DOI not confirmed.
Use: the published companion of arXiv:1504.05927, connecting balanced presentations
to the geometry of spaces of triangulations.

4.10 **[V]** M. Bestvina and N. Brady, *Morse theory and finiteness properties of
groups*, Invent. Math. 129 (1997), 445-470. DOI: 10.1007/s002220050168.
Use: the standard source for groups of type $FP_2$ that are not finitely presented,
which is part of the background for why 2-complexes behave differently from higher
dimensional complexes.

## 5. Complexity and lower bounds on path length

5.1 **[V]** M. R. Bridson, *The complexity of balanced presentations and the
Andrews-Curtis conjecture*, arXiv:1504.04187 (2015).
Note that the identifier is 1504.04187, not 1504.04165 as sometimes quoted.
Use: large lower bounds on the number of Andrews-Curtis moves needed for
trivialisation, beginning in rank 4. The abstract says the bounds come from a new
understanding of how Dehn functions behave under certain push-outs: from groups $S$
of deficiency 1 with technical hypotheses one builds balanced presentations $P_w$
indexed by words $w$, and if $w = 1$ in $S$ then $P_w$ is AC-trivialisable with a
move count bounded above and below in terms of how hard it is to prove $w = 1$ in
$S$.

5.2 **[S]** S. M. Gersten, *Dehn functions and $l^1$-norms of finite presentations*,
in Algorithms and Classification in Combinatorial Group Theory, MSRI Publications
23, Springer, 1992, pp. 195-224.
Use: the foundational paper on Dehn functions of finite presentations, which is the
machinery Bridson's lower bounds use. Gersten's own publication list gives the
volume year as 1991 and the citation in a later paper gives 1992, so the imprint
year is not settled here.

5.3 **[S]** M. R. Bridson, *The geometry of the word problem*, in Invitations to
Geometry and Topology, Oxford Graduate Texts in Mathematics 7, Oxford University
Press, 2002, pp. 29-91.
Use: a survey of the word problem and isoperimetric functions, useful as the
background for 5.1.

5.4 **[V]** B. Lishak, *Balanced finite presentations of the trivial group*,
J. Topol. Anal. 9 (2017), no. 2, 363-378. DOI: 10.1142/S1793525317500182.
Use: two-generator two-relator presentations of the trivial group for which the
minimal number of relations needed to show that a generator is trivial grows faster
than any fixed-height tower of exponentials in the length of the presentation. The
measure in the paper is the number of relations, not the number of Andrews-Curtis
moves. This is evidence that triviality can be very expensive in rank 2. It is not a
lower bound on move counts. Tao's blog post, see 2.9, attributes families of
this kind jointly to Bridson and Lishak; the verifiable published sources are 5.1
and 5.4 here.

5.5 **[V]** B. Lishak and A. Nabutovsky, *Balanced presentations of the trivial
group and four-dimensional geometry*, arXiv:1504.05927, submitted 22 April 2015.
Use: the companion preprint to 5.4 and 4.9. The title above is the one the arXiv
API returns. The reference list of the published paper 5.4 gives a longer title,
*Balanced finite presentations of the trivial group and their applications in
geometry of 4-dimensional manifolds*, which is presumably an earlier title of the
same preprint. The identifier check is what caught this, and the arXiv title should
be used in citations.

5.6 **[V]** M. Lackenby, *The stable Andrews-Curtis conjecture and thickenable
presentations of the trivial group*, arXiv:2606.06122, submitted 4 June 2026,
27 pages.
Use: an explicit bound. For a thickenable balanced presentation $P$ of the trivial
group of length $\ell$, the paper states that the number of stable
Andrews-Curtis moves needed is at most $2^{2^{c\ell^2}}$ with $c = 2 \cdot 10^6$.
It also states a proof that thickenable balanced presentations of the trivial group
satisfy the unstable Andrews-Curtis conjecture. Its introduction records that the
stable triviality of thickenable presentations already follows from the Poincare
conjecture.

5.7 **[V]** M. Bestvina and N. Brady, see 4.10.
Use: background on deficiency and finiteness conditions, which is what separates
the rank-2 world from the rank-4 lower bounds.

## 6. Computational attacks

6.1 **[V]** A. D. Miasnikov, *Genetic algorithms and the Andrews-Curtis
conjecture*, Internat. J. Algebra Comput. 9 (1999), no. 6, 671-686.
DOI: 10.1142/S0218196799000370. arXiv:math/0304306.
Use: the genetic-algorithm attack. The paper states that all balanced presentations
of the trivial group known to the author with total relator length at most 12
satisfy the conjecture, and it gives a chain of 21 transformations reducing
$\langle x,y \mid xyx = yxy,\ x^2 = y^3\rangle$, that is $AK(2)$, to the standard
presentation. It lists the four sources of candidates then known: two sporadic
presentations, the family $x^n = y^{n+1}$, $xyx = yxy$, and the Miller-Schupp
family.

6.2 **[V]** G. Havas and C. Ramsay, *Breadth-first search and the Andrews-Curtis
conjecture*, Internat. J. Algebra Comput. 13 (2003), no. 1, 61-68.
DOI: 10.1142/S0218196703001365. Code and data at
https://staff.itee.uq.edu.au/havas/ACME/ .
Use: the ACME breadth-first search over presentations with bounded total relator
length. The stated theorem is this. Let $G$ have a balanced two-generator
presentation with total relator length at most 13. If $G$ has trivial abelianisation
then $G$ is trivial or is $L_2(5)$, the unique perfect group of order 120. If $G$ is
trivial then its presentation is AC-equivalent to the standard presentation or to
$\langle x,y \mid x^3 = y^4,\ xyx = yxy\rangle$, which is $AK(3)$. The paper also
says that up to equivalence there is a unique minimum potential counterexample. Its
search ran in C on a 400 MHz machine.

6.3 **[V]** G. Havas and C. Ramsay, *Andrews-Curtis and Todd-Coxeter proof words*,
in Groups St Andrews 2001 in Oxford, Cambridge University Press, 2003, pp. 232-237.
DOI: 10.1017/CBO9780511542770.022.
Use: the companion paper on extracting proof words from such searches.

6.4 **[V]** J. Swan, G. Ochoa, G. Kendall and M. Edjvet, *Fitness landscapes and
the Andrews-Curtis conjecture*, Internat. J. Algebra Comput. 22 (2012), no. 2,
1250009. DOI: 10.1142/S0218196711006753.
Use: an empirical study of the fitness landscape of this search problem. The later
paper 6.5 summarises the earlier analysis as having found that none of several
heuristic measures of search progress offered useful guidance.

6.5 **[V]** K. Krawiec and J. Swan, *Distance metric ensemble learning and the
Andrews-Curtis conjecture*, arXiv:1606.01412 (2016).
Use: learned distance measures used to drive search, with the claim that 19
potential counterexamples whose status had been unknown are eliminated.

6.6 **[V]** D. Panteleev and A. Ushakov, *Conjugacy search problem and the
Andrews-Curtis conjecture*, Groups Complex. Cryptol. 11 (2019), no. 1, 43-60.
DOI: 10.1515/gcc-2019-2005.
Use: the connection between conjugacy search and Andrews-Curtis search, which is
where the cryptographic literature meets this problem.

6.7 **[V]** A. Shehper, A. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen,
Y. Qiu, P. Kucharski, Z. Wang and S. Gukov, *What makes math problems hard for
reinforcement learning: a case study*, NeurIPS 2025 proceedings, arXiv:2408.15332.
Use: search by classical methods, reinforcement learning and language models on
these presentations. The abstract claims length reducibility of all but two
presentations in the Akbulut-Kirby series, and resolution of various Miller-Schupp
potential counterexamples, including three infinite subfamilies. The abstract dates
the two families to 1981 and 1991, while the primary sources listed here are dated
1985 and 1999.

6.8 **[V]** L. Fagan, M. Tarquini, A. Shehper, M. Manko, A. Gruen, C. Huang,
G. Butbaia, D. Passaro and S. Gukov, *The Two-Hump problem: bridging the difficulty
gap in mathematical reinforcement learning*, arXiv:2606.21611 (2026).
Use: the current large-scale computational study. It reports that on the
1190-presentation Miller-Schupp benchmark, greedy search solves 604 presentations
within 10,000 nodes, that a hundredfold increase in budget adds 36, and that a
budget of ten million nodes leaves 550 unsolved. It releases two data sets, AC-19
with 125,192 presentations of total length at most 19 and AC-1M with 1,136,154
presentations of length at most 30.

6.9 **[V]** J. Carreras, *Machine-checkable equivalence certificates at the
length-14 Andrews-Curtis frontier*, arXiv:2607.23611 (2026).
Use: explicit move sequences for four AC-equivalences among the six hard
length-14 presentations, presented as certificates replayable by a small verifier.
The abstract states the rank-2 frontier as follows: unconditional verification
stands at total relator length 12, and at length 13 every balanced trivial-group
presentation is AC-trivial or AC-equivalent to $AK(3)$, which is open.

6.10 **[S]** L. Fagan, *The stable Andrews-Curtis conjecture and generic
2-polyhedra*, doctoral dissertation, University of California, Santa Barbara, 2025.
https://escholarship.org/content/qt6fm617h4/qt6fm617h4.pdf
Use: a thesis with a chapter on length reduction for the Akbulut-Kirby series and
Miller-Schupp cases, and a chapter that states the stable moves (AC4) and (AC5)
explicitly and relates the stable conjecture to the Zeeman conjecture.

## 7. Automated reasoning and formalisation

7.1 **[V]** A. Lisitsa, *The Andrews-Curtis conjecture, term rewriting and
first-order proofs*, in Artificial Intelligence and Symbolic Computation, Lecture
Notes in Computer Science, Springer, 2018, pp. 343-351.
DOI: 10.1007/978-3-319-96418-8_41.
Use: the first-order rewriting encoding of Andrews-Curtis moves that the later
Prover9 proofs use.

7.2 **[V]** A. Lisitsa, *Towards computer-assisted proofs of parametric
Andrews-Curtis simplifications*, abstract, AITP 2023.
https://aitp-conference.org/2023/abstract/AITP_2023_paper_26.pdf
Use: the first public statement that the presentations $MS_n(w_*)$ with
$w_* = b^{-1}aba^{-1}$ are AC-trivial for $n = 3,4,5,6$, together with a conjecture
on the shape of the simplifications for all $n \geq 3$.

7.3 **[V]** A. Lisitsa, *New Andrews-Curtis trivializations for Miller-Schupp group
presentations*, Examples and Counterexamples 6 (2024), 100168.
DOI: 10.1016/j.exco.2024.100168.
Use: extends 7.2 to $n = 3,4,5,6,7,8$ and formulates two conjectures on the
structure of the simplification sequences.

7.4 **[V]** A. Lisitsa, *Automated theorem proving reveals a lengthy Andrews-Curtis
trivialization for a Miller-Schupp trivial group presentation*, Examples and
Counterexamples (2025), 100201. DOI: 10.1016/j.exco.2025.100201.
Use: $MS_9(w_*)$, with a simplification of 8634 elementary moves, produced by
Prover9 in about 74 days with more than 56 GB of memory. This is the largest move
count reported for a single presentation in the sources read here.

7.5 **[V]** A. Lisitsa, *Stable Andrews-Curtis trivialization of AK(3) revisited.
A case study using automated deduction*, J. Comput. Algebra (2025), 100041.
DOI: 10.1016/j.jaca.2025.100041. Preprint arXiv:2501.18601.
Use: the record of a reversal, and the single most delicate status item in this
list. The arXiv version, submitted 17 January 2025, asserts that $AK(3)$ is stably
AC-equivalent to the trivial presentation and supplies five transformation
sequences extracted from two Prover9 proofs. The journal version, dated 15 October
2025, says that it gives an independent reduction of $AK(3)$ to a presentation $P$
and that the earlier theoretical claim about the stable AC-trivialisability of $P$,
on which the Shehper et al. result relied, was based on an incorrect theorem.
It concludes that the status of $AK(3)$ remains unresolved. Read both versions
before using either claim.

7.6 **[V]** M. Fairbank, A. Lisitsa and A. Vernitski, *Probabilistic automaton
classifier applied to examples related to the Andrews-Curtis conjecture*,
J. Autom. Reason. 70 (2026), article 11. DOI: 10.1007/s10817-026-09759-8.
Use: a classifier and a search algorithm for these instances, compared against
automated reasoning, with the conclusion that combining the two helps on some
instances and not on others.

7.7 **[V]** C. Zhang, A. Zhou, R. J. George, S. Gukov and A. Anandkumar,
*AI-driven mathematical discovery for the Andrews-Curtis conjecture*, NeurIPS 2025
Workshop on Mathematical Reasoning and AI.
https://carolinezhang1.github.io/pdfs/AC_math_discovery.pdf
Use: a Lean formalisation of the moves with a deterministic autoformaliser that
turns a proposed trivialisation path into a Lean proof, and a claim that 753
Miller-Schupp presentations were solved across all runs. The same workshop paper is
listed elsewhere under the title *Mathematical Discovery and Formalization Towards
the AC Conjecture*, with the second author named as Aaron Zhao. That discrepancy is
unresolved here.

7.8 **[V]** R. J. George, *Formalizing the Andrews-Curtis conjecture*, public
write-up, https://www.robertj1.com/ai4science/ac-conjecture-aristotle/
Use: a non-peer-reviewed account of a Lean formalisation in which the rank-two move
set is expanded to twelve primitive moves and a general arbitrary-rank move
relation is proved to receive them. Useful as a map of the formalisation choices,
for example whether inversion is primitive and which conjugating words are allowed.

7.9 **[V]** SAIR Foundation, *The Andrews-Curtis conjecture challenge*, competition
site, https://competition.sair.foundation/competitions/acc/proof-track
Use: a public statement of the two conjectures, stable and unstable, and of a shared
formal statement file named AC.lean, with a discovery track and a proof track. It is
competition material and not peer reviewed.

## 8. Nielsen equivalence and the product replacement algorithm

8.1 **[V]** A. Lubotzky and I. Pak, *The product replacement algorithm and
Kazhdan's property (T)*, J. Amer. Math. Soc. 14 (2001), no. 2, 347-363.
DOI: 10.1090/S0894-0347-00-00356-8.
Use: the finite-group analogue in detail. The vertices are the generating $k$-tuples
$\Gamma_k(G)$, identified with $\mathrm{Epi}(F_k, G)$, and the moves are the four
operations $R^\pm_{i,j}$ and $L^\pm_{i,j}$ on a tuple. The paper observes that these
moves correspond to Nielsen moves on $\Gamma_k(F_k)$ and deduces that the graphs are
quotients of the Cayley graph of the special automorphism group of $F_k$. That is the
precise sense in which the product replacement graph is the finite shadow of the
Andrews-Curtis graph.

8.2 **[S]** I. Pak, *The product replacement algorithm is polynomial*, Proc. 41st
Annual IEEE Symposium on Foundations of Computer Science, 2000.
Author's PDF at https://www.math.ucla.edu/~pak/papers/PRfocs6.pdf .
Use: a polynomial mixing-time bound for $k = \Omega(\log |G| \log\log |G|)$. Pages
and the exact proceedings data are not confirmed here.

8.3 **[V]** A. V. Borovik, A. Lubotzky and A. Myasnikov, *The finitary
Andrews-Curtis conjecture*, in Infinite Groups: Geometric, Combinatorial and
Dynamical Aspects, Progress in Mathematics 248, Birkhauser, 2005, and
arXiv:1103.1295.
Use: the theorem that for a finite group $G$ and $k \geq \max\{d_G(G), 2\}$, two
$k$-tuples that generate $G$ as a normal subgroup are AC-equivalent if and only if
their images in the abelianisation are, so the connected components of the
Andrews-Curtis graph of $G$ are the preimages of those of its abelianisation. The
corollary recorded there is that no computation in a finite group can produce a
counterexample to the classical conjecture. It also restates the Akbulut-Kirby
candidate pairs in the form $(xyxy^{-1}x^{-1}y^{-1},\ x^n y^{-(n+1)})$.

8.4 **[V]** J. Nielsen, see 1.3, and J. J. Andrews and M. L. Curtis, see 1.2.
Use: the two classical sources for the Nielsen side of the story.

## 9. The stable version

9.1 **[V]** L. Fagan, dissertation, see 6.10, Definition 3.1.
Use: an explicit written-down pair of stabilisation moves. (AC4) adds a new
generator $x_{n+1}$ together with the relator $x_{n+1}$. (AC5) is its inverse, and
it applies when a relator is a single generator that occurs in no other relator.
Two presentations are stably AC-equivalent when one is reachable from the other by
(AC1) to (AC5). The thesis states the stable conjecture in that language.

9.2 **[V]** M. Lackenby, see 5.6, and A. Lisitsa, see 7.5, and A. Shehper et al.,
see 6.7.
Use: the three most recent sources read here that work on the stable variant. For a
reader who wants the current state, these three must be read together, because they
disagree about the stable status of $AK(3)$ and the disagreement is documented in
7.5.

9.3 **[V]** G. Baumslag, A. Myasnikov and V. Shpilrain, see 2.5.
Use: the entry states the conjecture with stabilisation allowed, and states that in
that form it is equivalent to a statement about two contractible 2-polyhedra both
embedding in a 3-dimensional polyhedron that geometrically contracts to each of
them. The entry attributes that equivalence to Wright, see 3.1.

9.4 **[V]** S. Matveev and D. Rolfsen, see 2.4, and E. C. Zeeman, see 4.1.
Use: the topological side of the stable statement, through Zeeman's conjecture that
$K \times I$ is collapsible for every contractible 2-polyhedron $K$.

## 10. The Akbulut-Kirby and Miller-Schupp families

10.1 **[V]** S. Akbulut and R. Kirby, see 4.2.
Use: the family $AK(n) = \langle x,y \mid xyx = yxy,\ x^n = y^{n+1}\rangle$ and its
printed instance at $n = 4$. Anyone quoting the family should also quote the printed
form, because the indexing convention has varied.

10.2 **[V]** C. F. Miller III and P. E. Schupp, *Some presentations of the trivial
group*, Contemp. Math. 250 (1999), Amer. Math. Soc.
DOI: 10.1090/conm/250/03848. Pages 113-115.
Use: the family
$\langle a,b \mid a^{-1}b^n a = b^{n+1},\ a = w\rangle$ with $w$ of exponent sum zero
in $a$. The paper proves that a perfect two-generator group satisfying
$a^{-1}b^n a = b^m$ with $n, m$ coprime positive is trivial, and deduces that every
presentation of that shape is a presentation of the trivial group. The paper records
that Havas's coset enumeration programs were used experimentally on the family
before the proof was found.

10.3 **[V]** A. D. Miasnikov, see 6.1, and G. Havas and C. Ramsay, see 6.2.
Use: the two computational milestones on the families. $AK(2)$ is AC-trivial by a
21-move chain. At total relator length 13 the only two-generator balanced trivial
group presentations not covered are those AC-equivalent to $AK(3)$.

10.4 **[V]** E. Romary and A. Zupan, see 4.8, and A. Shehper et al., see 6.7,
and A. Lisitsa, see 7.3 and 7.4, and J. Carreras, see 6.9.
Use: the recent work on the two families. Romary and Zupan give topologically
constructed trivialisations for one family of R-link presentations. Shehper et al.
claim length reduction for all but two presentations in the Akbulut-Kirby series.
Lisitsa gives trivialisations for $MS_n(w_*)$ up to $n = 9$. Carreras gives
machine-checkable certificates for part of the length-14 frontier.

10.5 **[V]** T. Tao, see 2.9.
Use: a 2026 secondary statement that AC-triviality of the Akbulut-Kirby family is
open for $n \geq 3$ and that $AK(3)$ is the shortest possible two-generator
counterexample up to AC-equivalence.

## 11. Invariants: the reference backbone

This section lists the sources a survey of invariants would rest on. It does not
survey the invariants themselves, which is a separate deliverable.

11.1 **[V]** R. H. Fox, see 1.5.
Use: Fox derivatives, the Alexander matrix, and elementary ideals, all computed
from a presentation and all standard candidates for presentation invariants.

11.2 **[V]** R. G. Burns and O. Macedonska, see 2.1.
Use: the survey that organises the partial results in terms of the complexity of
annihilating tuples.

11.3 **[V]** A. V. Borovik, A. Lubotzky and A. Myasnikov, see 8.3.
Use: the reason finite quotients cannot help. Any balanced presentation of the
trivial group presents the trivial group, so all of them have the same finite
quotients, and the theorem in 8.3 says that the finite-group Andrews-Curtis graph
cannot separate tuples whose images agree in the abelianisation.

11.4 **[V]** B. Lishak, see 5.4, and M. R. Bridson, see 5.1.
Use: the two sources that show how large the gap can be between a presentation
being trivial and a short proof of triviality, which is why invariant-based and
length-based approaches have to be kept apart.

## 12. Status notes that the listed sources carry

Each line is attributed and is not my own conclusion.

12.1 $AK(2)$ is AC-trivial, by a 21-move chain (6.1).
12.2 Every two-generator balanced trivial-group presentation of total relator length
at most 13 is AC-trivial or AC-equivalent to $AK(3)$, which is $x^3 = y^4$ together
with $xyx = yxy$ (6.2, restated in 2.9 and 6.9).
12.3 All but two presentations in the Akbulut-Kirby series admit a length reduction
(6.7, abstract). The abstract does not say which two.
12.4 $MS_n(w_*)$ is AC-trivial for $n = 3, 4, 5, 6, 7, 8$ (7.3) and for $n = 9$ with
a 8634-move simplification (7.4).
12.5 The stable status of $AK(3)$ is asserted in the January 2025 preprint (7.5) and
declared unresolved in the October 2025 journal version of the same paper (7.5).
12.6 Thickenable balanced presentations satisfy the unstable conjecture, with an
explicit stable bound (5.6).
12.7 A computation in a finite group cannot produce a counterexample (8.3).
12.8 No source read in this run claims a proof or a disproof of the conjecture.

## 13. Unverified or only partly verified items

These are recorded with what was seen, so that nobody mistakes them for checked
entries. Each item states what was seen and where, so that a later reader can
finish the check in one step.

13.1 S. Akbulut, *4-Manifolds*, Oxford Graduate Texts in Mathematics 25, Oxford
University Press, 2016. Known from trained knowledge only. Not checked in this run.
13.2 R. E. Gompf and A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate
Studies in Mathematics 20, American Mathematical Society, 1999. Known from trained
knowledge only. Not checked in this run.
13.3 W. Magnus, A. Karrass and D. Solitar, *Combinatorial Group Theory*,
Interscience 1966, Dover reprint 1976. Known from trained knowledge only. Not
checked in this run.
13.4 M. O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of
Math. 67 (1958), 172-194, and S. I. Adian's 1955 unsolvability announcement. Known
from trained knowledge only. In addition, I did not verify any statement about
whether triviality is undecidable for balanced presentations, so no such statement
is made in this file.
13.5 K. Madlener and F. Otto, work on word-problem algorithms for finitely
presented monoids and groups. Known from trained knowledge only. Not checked.
13.6 A. G. Myasnikov, *Extended Nielsen transformations and the trivial group*,
Mat. Zametki 35 (1984), no. 4, 491-495, MR0744511. The Russian original is verified
through the MathSciNet relay record. The English translation in Mathematical Notes
35 (1984) is not verified here, and its pages are unknown to me.
13.7 S. G. Ivanov's volume and pages were unverified at first and are now
confirmed by the identifier check in section 14.
13.8 F. Quinn, *Isotopy of four-manifolds*: volume and pages rest on a citation in
another paper's reference list.
13.9 The chapter DOI for Matveev and Rolfsen is not confirmed. The title and page
range 335-363 come from the book's own table of contents.
13.10 A third-party page at problemhive.org, dated 21 October 2026, summarises the
state of $AK(3)$ and the Miller-Schupp search counts. It was returned by search and
is not an authored publication. Its specific numbers, for example the counts of
presentations solved by specific search budgets, were not checked by me against the
papers, and the account of them in 6.7 and 6.8 is limited to what the papers'
abstracts say.

## 14. Results of the identifier check

The script `check_refs.py` was run in this directory with `python3 check_refs.py`.
It compares each DOI against the CSL-JSON record served by doi.org and each arXiv
identifier against the arXiv Atom API, and it requires the registry title to contain
an expected fragment. The recorded output is `check_refs.out`.

The run made 33 DOI checks and 13 arXiv checks. All 46 matched. The first run
produced two mismatches, and both were real.

- The fragment for the Romary and Zupan DOI failed because the registry title uses a
  dash character in the middle of the name "Andrews-Curtis" where the fragment used a
  plain hyphen. The script now folds dash characters and strips HTML tags before
  comparing, and the entry itself was already correct.
- The arXiv identifier 1504.05927 returns the title *Balanced presentations of the
  trivial group and four-dimensional geometry*, not the longer title printed in the
  reference list of the published Lishak paper. Entry 5.5 was corrected to the
  arXiv title and the discrepancy was recorded there.

Registry metadata also settled volume and page data for several entries. These are
Ivanov (volume 68, pages 661-663), Miller and Schupp (pages 113-115), Baumslag,
Myasnikov and Shpilrain (pages 1-38), and the Hog-Angeloni and Metzler chapter
(pages 365-380). The same check confirmed the 2026 dates of the Lackenby and
Carreras preprints and the 2024 and 2025 dates of the three Lisitsa papers.

The check does not confirm authors for most entries, and it does not confirm that
the content of a paper is what the relevance line says. Items marked [S] or [U]
receive no support from it at all.

## 15. What this file does not contain

This list contains no proof, no disproof and no partial mathematical result of my
own. It also does not survey invariants, does not state Bridson's bounds numerically
beyond what his abstract says, and does not adjudicate the disagreement about the
stable status of $AK(3)$ in 7.5. Each of those is a separate deliverable with its own
evidence standard, and the sources listed here are the ones such a deliverable should
start from.
