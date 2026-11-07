# Computational attacks on the Andrews–Curtis conjecture

Direction D4 of round 1, swarm smw2fzjic, member m7.

This file records what computational work on the Andrews–Curtis conjecture has
actually been done, how far it reached, on which families, with which methods and
on which hardware, and which parts of the published record I was able to check
myself. Claims are labelled as follows. **Quoted** means the words are in the
source and I checked them against the source text. **Computed** means I ran code
in this repository and the exact command is given in Section 11. **Argument**
means reasoning of mine, not a published statement. **Unverified** marks anything
I could not check.

Nothing here is a claim about the truth of the conjecture. The conjecture is open
and this file contains no progress on it.

## 0. Summary

The computational record has three parts, in chronological order. Genetic
algorithms were applied by Miasnikov in 1999 to the two named families and by
Miasnikov and Myasnikov in 2001 to all two-generator balanced presentations of the
trivial group; both papers report AC-triviality in the range of total relator length at
most 12. Constrained breadth-first
search was applied by Havas and Ramsay in 2003; they extended the range to total
relator length 13, proved that up to AC-equivalence there is a single minimum
potential counterexample at that length, and published explicit chains. Breadth-first
search on secondary storage was reported by Bowman and McCaul in 2006, who solved
ten presentations of relator length 14 and enumerated one family exhaustively to
larger total length without finding a trivialisation. A study of fitness landscapes
by Swan, Ochoa, Kendall and Edjvet in 2012 examined why the heuristic methods
struggle on this problem.

My own contribution to the map is a set of independent replays and one census.
I replayed every published chain I could obtain (Miasnikov's nineteen printed steps
for the two-generator Akbulut–Kirby presentation, Havas and Ramsay's chains of 11,
14 and 32 moves), reproduced two published numerical tables exactly (the
unconstrained breadth-first level counts and the canonical list sizes 20, 104, 204,
1400), and ran a complete census of two-generator balanced presentations of total
relator length at most 11, in which every AC-trivial case comes with a machine-checked
certificate and every other case is proved nontrivial by its exponent-sum determinant.
The certificate checker is a separate program that shares no code with the search.

## 1. The moves, and why published move counts differ

The three Andrews–Curtis moves on an $n$-tuple of relators $(r_1,\dots,r_n)$ of the
free group $F_n$ are: replace $r_i$ by $r_i^{-1}$; replace $r_i$ by $r_i r_j$ with
$i \neq j$; replace $r_i$ by $w r_i w^{-1}$ for a word $w$. Two presentations are
AC-equivalent when one can be reached from the other by a finite sequence of these
moves (Andrews and Curtis 1965).

Miasnikov numbers five operations (Miasnikov 1999, Section 1, **quoted**): AC1 is
$r_i \mapsto r_i r_j$; AC2 is inversion; AC3 is conjugation; AC4 is reordering the
relators; AC5 introduces or deletes a generator together with the relator that
generates it, that is, a stabilisation. His searches use AC1 to AC4 and he reports
that AC5 did not help. Havas and Ramsay use AC1, AC2 and AC3 with the conjugating
word restricted to a generator or the inverse of a generator, and they note
(**quoted**) that "arbitrary conjugation is simply a succession of AC3 moves".

The total relator length of a presentation is the sum of the lengths of its relator
words. For a relation written as $u = v$ this is $|u| + |v|$, which equals the length of
the relator $u v^{-1}$, so the two ways of counting agree.

Two counting conventions are in use and they explain most of the apparent
disagreements in the literature.

* A **displayed step** is one arrow in a printed chain.
* An **elementary move** is one application of AC1, AC2 or AC3 with a single generator
  as conjugator.

A displayed step in which the relator is conjugated by a word of length $m$ costs
$m$ elementary moves. This is exactly the difference between Miasnikov's count of
21 transformations and Havas and Ramsay's count of eighteen essential moves for the
same presentation. Miasnikov prints nineteen steps, and his ninth step conjugates by
the three-letter word $ba^{-1}b$. That step expands into three elementary moves, so
the printed chain has $19 - 1 + 3 = 21$ elementary moves. **Computed**: my replay
confirms the expansion, the count 21, and the peak total relator length 25, which is
the same peak that Havas and Ramsay report for this proof.

Havas and Ramsay also subtract "nonessential" moves, meaning moves that only cyclically
permute or invert a relator, before comparing lengths with Miasnikov's counts.

For $n$ generators and their restricted conjugation there are $3n^2$ moves: inversion
of one relator, $n-1$ multiplications by another relator, and $2n$ conjugations by a
generator or its inverse. At rank 2 this gives 12 moves, the branching factor used in
all the rank-2 search reports below.

## 2. Genetic algorithms

### 2.1 Miasnikov 1999

Alexei D. Miasnikov, "Genetic algorithms and the Andrews–Curtis conjecture",
International Journal of Algebra and Computation 9 (1999), no. 6, 671–686,
DOI 10.1142/S0218196799000370, arXiv:math/0304306.

The paper describes a genetic algorithm whose individuals are sequences of
transformations, with a fitness function that scores how close the transformed
presentation is to the trivial one, plus selection, crossover and mutation. The
parameters are stated in the paper (**quoted**): "The probabilities of mutation and
crossover were 95% and 85% correspondingly". The moves used are AC1 to AC4; AC5 is
not used (**quoted**: "all of our solutions were obtained without using the
transformation (AC5) and we were unable to improve efficiency by adding this
operation").

The mathematical claim is stated as a theorem (**quoted**): "Theorem 1. All
presentations from the series (3) and (4) with the total length of relators at most 12
satisfy the Andrews–Curtis conjecture", where series (3) is
$\langle x,y; x^n = y^{n+1}, xyx = yxy\rangle$ with $n \ge 2$ and series (4) is the
Miller–Schupp family $\langle x,y; x^{-1}y^n x = y^{n+1}, x = w\rangle$ with $w$ of
exponent sum zero in $x$. The paper says (**quoted**) that "Altogether there are 273
presentations with the total length ≤ 12 in these series". An earlier sentence in the
same paper puts the claim more cautiously (**quoted**): "all balanced presentations of
the trivial group that we are aware of where the total length of defining relators is
at most 12 satisfy the conjecture".

The paper prints a proof for the $n = 2$ member of series (3), that is
$\langle a,b; aba = bab, a^2 = b^3\rangle$ (**quoted**: "the only one in the series (3)
with the total length of relators ≤ 12"), as a chain of nineteen steps, and it
reports "a chain of 21 transformations" in the introduction. **Computed**: I replayed
the nineteen printed steps move by move. The chain runs from the relator pair
$(a^2b^{-3},\, aba b^{-1}a^{-1}b^{-1})$ to $(b^{-1}, a^{-1})$ and uses 21 elementary
moves, with total relator length rising to 25 at step 8. This confirms the paper's own
count and the independent remark of Havas and Ramsay that this proof grows the
presentation to length twenty-five.

Two remarks on effort appear in the paper (**quoted**). For exhaustive enumeration:
"We ran the total enumeration procedure on a machine with an Alpha processor running
at 500 mhz and only managed to test sequences of length up to seven in two days."
For a meet-in-the-middle version: the number of computations drops to about
$12^{11}$, but "it requires a lot of a fast access memory (more than 60 Gb in our
example)". **Computed**: $12^{10} = 61\,917\,364\,224$ and $12^{11} = 743\,008\,370\,688$.
The 60 Gb figure is therefore the size of the radius-10 ball counted as one byte per
enumerated sequence. **Argument**: no implementation stores a presentation in one
byte, so 60 Gb is a lower bound for that method and a realistic implementation needs
substantially more.

### 2.2 Miasnikov and Myasnikov 2001

Alexei Miasnikov and Alexei Myasnikov, "Balanced presentations of the trivial group on
two generators and the Andrews–Curtis conjecture", in Groups and Computation III
(W. Kantor and A. Seress, editors), Ohio State University Mathematical Research
Institute Publications 8, Walter de Gruyter, 2001, pages 257–263, DOI
10.1515/9783110872743.257, arXiv:math/0304305. The publisher record lists pages
257–264 while the authors' own arXiv journal reference and Havas and Ramsay both give
257–263; I record the range as 257–263 and note the discrepancy.

The abstract (**quoted**) says: "In this paper we describe all balanced presentations of
the trivial group on two generators and with the total length of relators <= 12. We show
that all these presentations satisfy the Andrews–Curtis conjecture." A review record
adds (**quoted**) that "The proof of the main result is based on computer computations
with the software package MAGNUS."

**Argument**: this paper is where the claim is upgraded from "all known to us" to "all".
The upgrade rests on an enumeration of all two-generator balanced presentations of the
trivial group with total relator length at most 12, not on a better search. The search
itself is the genetic algorithm of the 1999 paper. Havas and Ramsay describe the result
as "the conjecture holds for all balanced presentations of the trivial group on two
generators with the total length of the relators at most twelve" (**quoted**), and their
own enumeration, which I reproduce in Section 8, extends the range to length 13.

### 2.3 What a genetic algorithm result does and does not give

**Argument**: a run of a genetic algorithm is not reproducible from its published
description, because it depends on a random initial population and on random choices in
selection, crossover and mutation. The reproducible content of such a paper is the
explicit chain. Miasnikov prints one chain in full, for the $n = 2$ Akbulut–Kirby
presentation, and I verified it. The remaining 272 presentations of his theorem are
reported as solved, and I did not find their chains in the paper, so I did not verify
them. The later breadth-first work of Havas and Ramsay independently confirms the
range up to length 12 and extends it, which is stronger evidence for the range than the
genetic algorithm reports alone.

## 3. Constrained breadth-first search: Havas and Ramsay

### 3.1 Method and hardware

George Havas and Colin Ramsay, "Breadth-first search and the Andrews–Curtis conjecture",
International Journal of Algebra and Computation 13 (2003), no. 1, 61–68,
DOI 10.1142/S0218196703001365. I obtained the authors' PDF of the typeset article from
Havas's web page and read it in full.

The machine is stated (**quoted**): "Our test machine was a SUN Enterprise 450 system
running SunOS 5.8 and clocked at 400 MHz. Our programming was done in C, and we used the
gcc compiler, with level 3 optimization." The program is ACME, an Andrews–Curtis move
enumerator.

The decisive idea is that an upper bound on the length of presentations during a search
makes the search space finite, which the paper says has "a dramatic impact on the size of
the search space" (**quoted phrase**). Each presentation is recorded when first seen and ignored
if seen again. A constrained search is not exhaustive, and when it completes with no
result it gives a lower bound on the length increase that any proof would need.

**Computed**: I reproduced the paper's unconstrained level counts for the length-ten
presentation $\langle a,b \mid ab = a^2, ba = b^2\rangle$, given in the paper as
relators $BabAA$ and $AbaBB$. The published counts at levels 0 to 8 are
1, 12, 101, 782, 5906, 44048, 326200, 2406914 and 17724982. My independent
implementation produces exactly the same numbers at levels 0 to 7, and reaches level 7
in about 14 seconds using 843 MB. The paper says that the level-8 run exhausted its
memory; my run confirms the growth rate that makes this plausible. At level 7 there
are 2406914 distinct presentations against $12^7 = 35\,831\,808$ sequences of moves,
so deduplication already removes a factor of about fifteen.

### 3.2 Length ten and eleven

For $\langle a,b \mid ab = a^2, ba = b^2\rangle$ the paper prints an eleven-move chain and
notes that Miasnikov's chain for the same presentation takes thirteen moves. **Computed**:
I replayed the eleven-move chain, which uses three multiplications, three inversions
and five conjugations by generators, never exceeds total length 10, and ends at $(b,a)$.
With the relator lengths capped at five the whole search tree contains 31240
presentations and completes in 1.5 seconds, as the paper reports. The paper also states
that exhaustive testing over the 100 possible cyclically permuted or inverted forms of
the relators establishes seven essential moves as the shortest possible. I did not
reproduce that optimality claim.

### 3.3 The two-generator Akbulut–Kirby presentation

Here and below I use the notation of the paper's Section 3: the family is
$\langle a,b \mid a^m = b^{m+1}, aba = bab\rangle$ with $m \ge 2$. The parameter $m$
plays the role of $n$ in the problem statement of this swarm, so $m = 2$ is
$\langle a,b \mid a^2 = b^3, aba = bab\rangle$ and $m = 3$ is the length-thirteen
presentation $\langle a,b \mid a^3 = b^4, aba = bab\rangle$.

The reported results for $m = 2$ are (**quoted**): Miasnikov gave "a proof chain of
eighteen essential moves; this proof requires the presentation to grow to length
twenty-five"; with ACME, "no proof is possible if the intermediate presentations are
limited in length to at most twelve. If length thirteen is allowed, then a proof in
nineteen essential moves is possible. If the length is allowed to grow to fifteen, then
a proof in fourteen essential moves is possible". The paper prints that fourteen-move
chain, and it states that a bidirectional search established the absence of any shorter
proof, taking 37 minutes of CPU time and about 2 gigabytes of memory.

**Computed**: I replayed the fourteen-move chain from $(aBBB a, BAbabA)$ to $(B,A)$. It
uses seven multiplications, two inversions and five conjugations by generators, and its
maximum total relator length is 15. This verifies the "grow to fifteen" claim of the
paper and, together with my replay of Miasnikov's chain, verifies that
$\langle a,b \mid a^2 = b^3, aba = bab\rangle$ is AC-trivial. The optimality claim
(no proof in fewer than fourteen essential moves) is a search result and I did not
reproduce it.

### 3.4 The Miller–Schupp examples

The paper reports that Miasnikov gave a seventeen-move proof for one of the four
length-twelve Miller–Schupp presentations with $w = y^{\pm 1} x y^{\pm 1} X$, and that
this proof used two Whitehead automorphisms outside AC1 to AC3, which can be replaced by
AC moves at the cost of a longer proof. Using ACME the authors extracted direct proofs
for all four (**quoted**): "Two of the proofs had fourteen essential moves and the other
two had twenty-three." Those chains are not printed in the paper, so I did not verify
them.

### 3.5 The theorem at total length thirteen

The paper's main result (**quoted**): "Let $G$ be a group defined by a balanced
presentation on two generators, with the sum of the relator lengths at most thirteen.
Then: (i) if $G$ has trivial abelianization, $G$ is trivial or is isomorphic to
$L_2(5)$, the unique perfect group of order 120; (ii) if $G$ is trivial, its presentation
is AC-equivalent to the standard presentation or to the presentation
$\langle x,y \mid x^3 = y^4, xyx = yxy\rangle$."

Part (i) was decided by coset enumeration with the program ACE, part (ii) by ACME. The
paper reports list sizes for its canonical enumeration at total relator length
$l = 10, 11, 12, 13$ of 20, 104, 204 and 1400. In the $l = 12$ list four presentations
have order 120, and in the $l = 13$ list twenty do.

For the $l = 13$ list the paper reports that, when relators are allowed to grow to
length eighteen, all but twelve presentations reduce to the standard one. The twelve
remaining fall into two orbits under the extended symmetric group, with representatives
$a^3 = b^4, aba = bab$ and $ab = bbaa, ba = aaabb$. An exhaustive search on a machine
with about 8 gigabytes of memory established that no chain exists if each relator is
allowed to grow in length by at most five. The paper then shows with a printed 32-move
chain that the two representatives are AC-equivalent (**quoted**: "the first
representative can be transformed to the second in thirty-two essential moves").

**Computed**: I replayed that 32-move chain. It uses sixteen conjugations by generators,
eleven multiplications and five inversions, its maximum total relator length is 21, and
it ends at $(AAAbaBB, abAABB)$, which is the second representative. The figure 21 is my
own measurement and is not reported in the paper.

### 3.6 The scale of the search

**Computed**: $12^{13} = 106\,993\,205\,379\,072$. My breadth-first ball of the standard
presentation, capped at total relator length 13, contains 6476104 tuples, which is fewer
by a factor of about $1.65 \times 10^7$ than the number of move sequences of the same
length. The cap does the work, as the paper argues.

### 3.7 Todd–Coxeter proof words

George Havas and Colin Ramsay, "Andrews–Curtis and Todd–Coxeter proof words", in Groups
St Andrews 2001 in Oxford, London Mathematical Society Lecture Note Series 304,
Cambridge University Press, 2003, pages 232–237, DOI 10.1017/cbo9780511542770.022.

The utility PEACE extracts proof words from Todd–Coxeter coset enumerations. The paper
asks whether such proof words correspond to AC proofs and obtains a constructive positive
answer in restricted cases (**quoted**): "Only in the case where there are two relators
and the PEACE proofs contain one of the relators exactly once can we consistently extract
an AC-proof", and "We have no systematic method of determining whether or not the
extraction is possible in general". **Argument**: this line of work produced a method for
finding proofs by hand or by coset enumeration in special cases, and it did not extend the
radius reached by search.

## 4. Secondary storage: Bowman and McCaul

R. Sean Bowman and Stephen B. McCaul, "Fast searching for Andrews–Curtis trivializations",
Experimental Mathematics 15 (2006), no. 2, pages 193–197, DOI 10.1080/10586458.2006.10128962,
zbMATH Zbl 1112.20027.

The abstract (**quoted**) says: "A high-performance computer program for searching a tree
of words in the group generated by Andrews–Curtis transformations is presented. The program
enumerates words in this group using a disk-based hash table to store words already seen. We
discuss several issues that affect the performance of the program and examine the growth of
the size of the Cayley graph being searched."

**Unverified**: I did not obtain the full text of this paper. The following two quantitative
claims about it are taken from a later paper's summary and are quoted there, not from Bowman
and McCaul themselves: "Bowman and McCaul [4] extended the breadth-first search approach by
making extensive use of secondary storage indexed via an in-memory hashing scheme, solving all
10 presentations of the form $\langle a,b \mid a = [a^m,b^n], b = [a^p,b^q]\rangle$ with
$m,n,p,q \in \mathbb{N}$ having relator length 14. By employing constraints on the maximum
permissible total relator length for intermediate presentations, they also exhaustively
enumerated the $m = 3$ case for Akbulut–Kirby (currently the smallest potential
counterexample) for total relator lengths from 10 to 17 inclusive, but were unable to find an
Andrews–Curtis trivialization." The source of this quotation is Swan, Ochoa, Kendall and
Edjvet 2012, Section 1. Because the two claims matter for the map, I mark them as reported but
not verified.

Bowman's program is distributed as `ac-mem` in the GitHub repository `rsbowman/ac-mem`. The
repository description is public and consistent with the abstract (**quoted**): the moves used
are "slightly different from (but equivalent to) the Andrews–Curtis moves: instead of
conjugation by a generator, we consider all cyclic permutations of relators", the hash is
built so that the table fits in memory, and for the input `abaBAB aaBBB`, which is the
two-generator Akbulut–Kirby presentation $\langle a,b \mid aba = bab, a^2 = b^3\rangle$, the
program "should tell you that after popping about 26M presentations off the front of the
queue" that the presentation is AC-trivial. **Argument**: 26 million presentations is the
scale at which a disk-backed search operates, and it is consistent with my own measurement
that the length-capped ball grows to hundreds of thousands of tuples within a few moves.

There is a citation discrepancy worth recording. Swan et al. cite this paper as Experimental
Mathematics 15(3) (2006). The publisher page, zbMATH, EUDML and OpenAlex all give
15(2), 193–197, and one Project Euclid harvest record gives 15(1), 193–198. I record
15(2), 193–197 as the correct reference and flag the variants.

## 5. Why the heuristic methods struggle

Jerry Swan, Gabriela Ochoa, Graham Kendall and Martin Edjvet, "Fitness landscapes and the
Andrews–Curtis conjecture", International Journal of Algebra and Computation 22 (2012),
no. 2, article 1250009, DOI 10.1142/S0218196711006753. I checked the author list, venue and
year against the publisher record.

The paper computes fitness-landscape metrics for both the perturbative state space (the graph
of presentations under AC moves) and the constructive state space (sequences of moves), for
several named balanced presentations, and examines fitness histograms and plateau-connection
graphs. Its conclusion is (**quoted**): "the existence of large plateaus in the search space is
the most significant contribution to the intractability of potential counterexamples". It
suggests that this explains "Miasnikov's genetic algorithm requiring an uncommonly high (95%)
mutation probability, effectively degenerating into random search".

**Argument**: this is evidence about search behaviour, and it is consistent with my own
observation that the number of distinct presentations reachable in a few moves is far smaller
than the number of move sequences. It says nothing about the truth of the conjecture.

## 6. Adjacent work

Michael Fairbank, Alexei Lisitsa and Alexei Vernitski, Journal of Automated Reasoning 70
(2026), no. 2, DOI 10.1007/s10817-026-09759-8, applies a probabilistic automaton classifier to
examples related to the conjecture. The DOI record gives the title "Probabilistic Automaton
Classifier Applied to Examples Related to the Andrews–Curtis Conjecture"; a search snippet for
the same DOI showed the longer title "Automated reasoning boosted by a probabilistic automaton
classifier: An application to the Andrews–Curtis conjecture", so one of the two is a
pre-publication variant. I did not read the paper. Automated reasoning is the subject of a
separate direction of this swarm (`survey/automated.md`), and I mention this item only so the
computational table is not missing a recent entry.

## 7. What radius was reached, on which families, with which methods

| source | family | method | published reach | hardware as stated | my verification |
| --- | --- | --- | --- | --- | --- |
| Miasnikov 1999 | series $\langle x,y \mid x^n = y^{n+1}, xyx = yxy\rangle$, $n \ge 2$, and the Miller–Schupp series, total relator length $\le 12$ (273 presentations) | genetic algorithm | all 273 AC-trivial | 500 MHz Alpha processor, two days for exhaustive sequences up to length 7; no hardware given for the genetic algorithm runs | replayed the printed chain for $n = 2$ (21 elementary moves, peak length 25) |
| Miasnikov and Myasnikov 2001 | all two-generator balanced presentations of the trivial group, total relator length $\le 12$ | enumeration plus the genetic algorithm, MAGNUS | all AC-trivial | not stated in the record I read | none directly; the range is independently covered by Havas and Ramsay |
| Havas and Ramsay 2003a | all two-generator balanced presentations, total relator length $\le 13$ | constrained breadth-first search (ACME) plus coset enumeration (ACE) | all trivial ones AC-trivial except $\langle x,y \mid x^3 = y^4, xyx = yxy\rangle$ up to AC-equivalence | 400 MHz Sun Enterprise 450, C with gcc -O3; runs with about 2 GB and about 8 GB of memory | replayed the 11, 14 and 32 move chains; reproduced the level counts and the list sizes 20, 104, 204, 1400 |
| Havas and Ramsay 2003b | two-relator presentations where a Todd–Coxeter proof word has a suitable shape | PEACE proof extraction | case by case | not stated | none; the paper states the method is ad hoc |
| Bowman and McCaul 2006 | ten presentations of relator length 14 and the $m = 3$ Akbulut–Kirby family, total relator length 10 to 17 | breadth-first search on disk with an in-memory hash index | ten solved; the family enumerated without a trivialisation | not verified | none; claims quoted from Swan et al. 2012 |
| Swan, Ochoa, Kendall and Edjvet 2012 | named presentations including the Akbulut–Kirby family | fitness-landscape metrics | no new radius | not stated in the parts I read | none |

## 8. My own computations

All the code is in `survey/computational/`. It is pure Python, deterministic, and uses no
randomness and no wall-clock cutoffs. The files are `census.py` (replays, ball, census),
`enum_check.py` (reconstruction of the published canonical lists), `deep_search.py` (the
bounded search reported in Section 8.7) and `check_certs.py` (an independent certificate
checker that shares no code with the rest).

### 8.1 Words and moves

Words in $F_2$ are tuples of integers with $1 = a$, $-1 = a^{-1}$, $2 = b$ and
$-2 = b^{-1}$, kept freely reduced. A presentation of rank 2 is a pair of words.
The moves are inversion of a relator, multiplication of one relator by another, and
conjugation by a generator or its inverse. `census.py` checks six word identities and
checks that each of the 36 single moves on three sample presentations is undone by an
explicit move sequence; the reverse of multiplying $r_i$ by $r_j$ is
inv $j$, mul $i$ $j$, inv $j$.

### 8.2 Replays of published chains

| chain | source | arrows | elementary moves | peak total length | end point |
| --- | --- | --- | --- | --- | --- |
| length 10 example | Havas and Ramsay 2003, Section 2 | 11 | 11 | 10 | $(b,a)$ |
| Akbulut–Kirby, $m = 2$ | Havas and Ramsay 2003, Section 3 | 14 | 14 | 15 | $(b^{-1},a^{-1})$ |
| Akbulut–Kirby, $m = 2$ | Miasnikov 1999, Section 5 | 19 | 21 | 25 | $(b,a)$ |
| two length-13 representatives | Havas and Ramsay 2003, Section 4 | 32 | 32 | 21 | $a^{-3}bab^{2}$ paired with $aba^{-2}b^{2}$ |

Every arrow is classified by the program as one of inversion, multiplication, or
conjugation by a generator. The peak lengths 15 and 25 agree with statements in the two
papers. The 14-move chain is the certificate that
$\langle a,b \mid a^2 = b^3, aba = bab\rangle$ is AC-trivial, which resolves the $m = 2$
member of the family and leaves $m = 3$ as the smallest unresolved member at length 13.
The status of the family itself is the subject of a separate direction of this swarm
(`survey/ak-status.md`); this file only reports what the computational record establishes.

### 8.3 The unconstrained level counts

My program, started from $(BabAA, AbaBB)$ with no length cap, produces
1, 12, 101, 782, 5906, 44048, 326200 and 2406914 presentations at levels 0 to 7, which
is exactly the sequence printed in Havas and Ramsay 2003, Section 2. This is the strongest
single check of my move model against the published record, because the numbers are
sensitive to every detail of the move set and of the deduplication.

### 8.4 The canonical lists at total length 10 to 13

I reimplemented the enumeration described in Havas and Ramsay 2003, Section 4, steps (A)
to (D): canonical forms under cyclic permutation and inversion of relators, relators
ordered by length then lexicographically, each generator present, distinct relators,
abelianised relators with determinant $\pm 1$, no relator contained in the other, and no
relator of the form $x_i = x_j^m$. The list sizes I obtain are 20, 104, 204 and 1400 for
$l = 10, 11, 12, 13$, which is exactly the published sequence. The intermediate counts in
my run are 6025, 16606, 46321 and 129964 canonical presentations before the filters for
$l = 10, 11, 12, 13$.

I then classified the lists at $l = 10, 11, 12$ using my ball of total length at most 13.

* $l = 10$: all 20 presentations are AC-trivial, each with a certificate.
* $l = 11$: all 104 presentations are AC-trivial, each with a certificate.
* $l = 12$: 184 of the 204 are AC-trivial with a certificate; 4 are proved nontrivial by an
  explicit homomorphism to $A_5$; 16 are not resolved by my ball.

For the four at $l = 12$ I also computed the order of the presented group with an
independent program, `sympy`'s coset enumerator (sympy 1.14.0, `FpGroup.order`). All four
have order 120, which matches the paper's count of four presentations of order 120 in the
$l = 12$ list. The four are $\langle BAABa, BBBBAbA\rangle$, $\langle BABaa, BBBBaba\rangle$,
$\langle BBaba, BABaaaa\rangle$ and $\langle BBAbA, BAAAABa\rangle$ in the letter notation of
the certificates.

### 8.5 A complete census at total relator length at most 11

`census.py` enumerates every canonical two-generator balanced presentation with total relator
length at most $L$, where canonical means: relators freely and cyclically reduced,
order of relators irrelevant, cyclic permutation and inversion of a relator irrelevant.
Both operations preserve AC-triviality and nontriviality, and relator order is notational,
so the enumeration covers every presentation up to these harmless symmetries.

Two exclusions need a word of justification. A presentation with an empty relator, or with
two equal relators, has effective deficiency one, so its abelianisation has rank at least one
and the group is infinite; such a presentation is never a presentation of the trivial group
and can be left out. A relator can always be made cyclically reduced by conjugation, which is
an AC move, so requiring cyclically reduced relators loses no AC class.

For each presentation the program decides one of three things.

1. The exponent-sum matrix has determinant different from $\pm 1$. Then the abelianisation is
   not trivial, so the group is not trivial and the presentation is not AC-trivial. This is a
   complete certificate of nontriviality.
2. A variant of the presentation lies in the breadth-first ball of the standard presentation
   with total relator length capped at 13. Then the presentation is AC-trivial and the program
   constructs an explicit certificate, replays it, and writes it out.
3. Otherwise it searches for a homomorphism to a small finite group ($S_3$, $D_8$, $Q_8$,
   $A_4$, $S_4$, $A_5$) with nontrivial image. Such a homomorphism certifies nontriviality.

The results are as follows.
In every row the breadth-first ball of the standard presentation was capped at a total
relator length somewhat above $L$, because a presentation of total length $L$ may need room
to grow during its proof. The cap is given in its own column.

| $L$ | ball cap | canonical presentations | nontrivial by determinant | AC-trivial with certificate | nontrivial by finite quotient | unresolved |
| --- | --- | --- | --- | --- | --- | --- |
| 5 | 8 | 83 | 66 | 17 | 0 | 0 |
| 7 | 10 | 522 | 433 | 89 | 0 | 0 |
| 8 | 11 | 1349 | 1160 | 189 | 0 | 0 |
| 9 | 12 | 3551 | 3002 | 549 | 0 | 0 |
| 10 | 13 | 9576 | 8419 | 1157 | 0 | 0 |
| 11 | 13 | 26182 | 22485 | 3697 | 0 | 0 |

So at total relator length at most 11 every two-generator balanced presentation is either
AC-trivial with a certificate or has nontrivial abelianisation. At these lengths the finite
quotient branch is never needed, and it agrees with the determinant branch: no presentation is
certified both ways, which is a consistency check on the whole move model, since AC-triviality
implies triviality and therefore forbids any nontrivial finite quotient.

The certificates at $L = 10$ have between 7 and 30 elementary moves, with mean 18.06, and
those at $L = 11$ have between 7 and 37 with mean 19.54. The
longest certificate is longer than the shortest proof because the certificate walks a
breadth-first path in the capped ball and then spends moves realising the cyclic permutations
of the relators.

### 8.6 Independent verification of the certificates

`check_certs.py` is a separate program with its own word arithmetic, its own move
implementation and its own parser. It reads a certificate file and replays every line,
requiring the result to be exactly the standard pair $(a,b)$. On the certificate file for
$L = 8$ it checks 189 certificates with 0 failures and longest 24 moves; on the file for
$L = 10$ it checks 1157 certificates with 0 failures and longest 30 moves.

### 8.7 A failure, recorded exactly

The sixteen $l = 12$ presentations that my length-13 ball does not reach also resist a
bounded depth-first search. `deep_search.py` runs iterative deepening with the total relator
length capped at 16, depth limit 22, and a budget of 1500000 node expansions per
presentation, with moves ordered by the resulting total length. It found no proof for any of
the sixteen, and the whole run took 10 minutes of wall clock. This is the exact point where
my method stops; it does not mean that no proof exists, and the published claim is that they
are reducible once intermediate relator lengths are allowed to grow further.

## 9. Weakest links and what I could not verify

1. **The 1999 claim is weaker than its usual citation.** Miasnikov's own abstract says "all
   known (to us)" presentations of total length at most 12. The universal statement comes
   from the 2001 paper and from Havas and Ramsay's independent enumeration. Anyone citing
   the 1999 paper alone for "all presentations of total length at most 12" is overstating it.
2. **Most genetic-algorithm chains are not published.** The 273 presentations of Miasnikov's
   theorem are reported solved; only one chain is printed. I verified that one.
3. **The pruning steps of the 2003 enumeration are justified in one sentence.** The paper
   writes that "It is straightforward to see that the list after step (A) contains at least
   one copy of each presentation of interest, and that the presentations subsequently
   discarded are either nontrivial, or AC-equivalent to the standard presentation or to a
   presentation from a list for a smaller $l$". My reconstruction of those steps reproduces
   their four list sizes exactly, which is strong evidence that I read the steps as the
   authors intended. It is not a proof that the pruning is sound, and the completeness of the
   length-13 theorem rests on it.
4. **The identification "$L_2(5)$, the unique perfect group of order 120" is inconsistent.**
   $L_2(5) \cong A_5$ has order 60. My independent order computation for the four $l = 12$
   presentations gives order 120. At most one of the two descriptions in the paper can be
   right: either the group has order 60 and is $L_2(5)$, or it has order 120 and is
   $SL_2(5)$, the binary icosahedral group whose quotient by its centre is $A_5$. My
   witnesses for those four presentations are pairs of permutations in $A_5$, which is
   consistent with either reading, and the sympy computation settles the order as 120.
5. **The optimality claims were not reproduced.** The statements that seven essential moves
   is shortest for the length-10 example and that fourteen is shortest for the
   $m = 2$ Akbulut–Kirby presentation come from exhaustive and bidirectional searches that I
   did not rerun.
6. **Bowman and McCaul's quantitative claims are second hand in my account.** I could not
   obtain the paper, and I did not compile or run `ac-mem`.
7. **Hardware statements are as reported by the authors.** I cannot verify the machine
   descriptions, the CPU times or the memory measurements of 2003 and 2006 runs. My own
   measurements are the ones in Section 8, taken on this VM.
8. **"Blacklisting" does not appear in the sources I read.** The direction brief mentions
   blacklisting as one of the computational techniques. I searched the full texts of
   Miasnikov 1999, Havas and Ramsay 2003, its companion paper, and Swan et al. 2012, and the
   term does not occur. The techniques that do occur are deduplication of visited
   presentations (ACME records each presentation when first seen; Bowman and McCaul use a
   disk-based hash table) and pruning by a bound on relator length. I record "blacklisting"
   as a term I could not locate in the primary computational literature, and I flag that the
   brief's use of it may come from automated-reasoning vocabulary rather than from the
   Andrews–Curtis literature.

## 10. References

Only items I checked against a publisher, arXiv or zbMATH record are listed with a DOI or
arXiv identifier. Items marked "record only" were checked for bibliographic metadata, not
read in full.

1. J. J. Andrews and M. L. Curtis, "Free groups and handlebodies", Proceedings of the
   American Mathematical Society 16 (1965), 192–195, DOI 10.1090/S0002-9939-1965-0173241-8.
   Origin of the conjecture.
2. S. Akbulut and R. Kirby, "A potential smooth counterexample in dimension 4 to the Poincaré
   conjecture, the Schoenflies conjecture, and the Andrews–Curtis conjecture", Topology 24
   (1985), no. 4, 375–390, DOI 10.1016/0040-9383(85)90010-2. Source of the family
   $\langle a,b \mid a^m = b^{m+1}, aba = bab\rangle$.
3. A. D. Miasnikov, "Genetic algorithms and the Andrews–Curtis conjecture", International
   Journal of Algebra and Computation 9 (1999), no. 6, 671–686,
   DOI 10.1142/S0218196799000370, arXiv:math/0304306. Genetic algorithm; total length 12 for
   the named series.
4. A. Miasnikov and A. Myasnikov, "Balanced presentations of the trivial group on two
   generators and the Andrews–Curtis conjecture", in Groups and Computation III,
   Ohio State University Mathematical Research Institute Publications 8, Walter de Gruyter,
   2001, 257–263, DOI 10.1515/9783110872743.257, arXiv:math/0304305. All two-generator
   presentations of total length at most 12.
5. G. Havas and C. Ramsay, "Breadth-first search and the Andrews–Curtis conjecture",
   International Journal of Algebra and Computation 13 (2003), no. 1, 61–68,
   DOI 10.1142/S0218196703001365. Constrained breadth-first search; the length-13 theorem.
6. G. Havas and C. Ramsay, "Andrews–Curtis and Todd–Coxeter proof words", in Groups St Andrews
   2001 in Oxford, London Mathematical Society Lecture Note Series 304, Cambridge University
   Press, 2003, 232–237, DOI 10.1017/cbo9780511542770.022. PEACE proof extraction.
7. R. S. Bowman and S. B. McCaul, "Fast searching for Andrews–Curtis trivializations",
   Experimental Mathematics 15 (2006), no. 2, 193–197,
   DOI 10.1080/10586458.2006.10128962, zbMATH Zbl 1112.20027. Secondary-storage search.
   Record only.
8. J. Swan, G. Ochoa, G. Kendall and M. Edjvet, "Fitness landscapes and the Andrews–Curtis
   conjecture", International Journal of Algebra and Computation 22 (2012), no. 2,
   article 1250009, DOI 10.1142/S0218196711006753. Fitness-landscape analysis.
9. M. Fairbank, A. Lisitsa and A. Vernitski, Journal of Automated Reasoning 70 (2026), no. 2,
   DOI 10.1007/s10817-026-09759-8. Probabilistic automaton classifier applied to
   Andrews–Curtis examples. Record only; belongs to the automated-reasoning direction.
10. C. F. Miller III and P. E. Schupp, "Some presentations of the trivial group", in Groups,
    Languages and Geometry (R. H. Gilman, editor), Contemporary Mathematics 250, American
    Mathematical Society, 1999, 113–115. Source of the Miller–Schupp family, cited through
    Havas and Ramsay 2003; I did not open it.

## 11. Exact commands and key output

Run from the repository root.

```
cd survey/computational
python3 census.py 5 8                          # the L = 5 row of the table
python3 census.py 7 10                         # the L = 7 row
python3 census.py 8 11 certs_r8_c11.txt        # about 15 s, 190 MB
python3 check_certs.py certs_r8_c11.txt        # independent verifier
python3 census.py 9 12                         # the L = 9 row
python3 census.py 10 13 certs_r10_c13.txt      # about 3 min, 2.8 GB
python3 census.py 11 13                        # the L = 11 row, same ball cap
python3 check_certs.py certs_r10_c13.txt
python3 enum_check.py 13                       # about 3 min, 2.8 GB
python3 deep_search.py 16 22 1500000           # about 10 min, finds nothing
```

Transcripts of the main runs, produced in this directory, are in `runs.txt`. The smaller
rows of the census table come from the same program with the parameters shown, and each run
takes well under a minute. Re-running `census.py 8 11 certs_r8_c11.txt` reproduces
`certs_r8_c11.txt` byte for byte, which is a check that the computation is deterministic.

Key output of `python3 census.py 8 11 certs_r8_c11.txt`:

```
PART 1  word arithmetic: 6 PASS
PART 2  each move is undone by moves: PASS all 36 single moves
PART 3  replay of chains printed in Havas-Ramsay, IJAC 13 (2003) 61-68
  Sec. 2, 11 moves: PASS all 11 arrows; max total length 10; end (b,a)
  Sec. 3, AK(2), 14 moves: PASS all 14 arrows; max total length 15; end (B,A)
  Sec. 4, 32 moves: PASS all 32 arrows; max total length 21; end (AAAbaBB,abAABB)
  Miasnikov 1999, AK(2), 19 printed steps: 21 elementary moves; max total length 25
PART 4  ball of the standard presentation, total length <= 11: 700712 tuples
  invariant check: tuples with |exponent-sum determinant| != 1: 0
  canonical presentations with total length <= 8: 1349
    nontrivial by determinant 1160; AC-trivial with certificate 189; unresolved 0
    contradictions 0; certificate lengths min 7, max 24, mean 15.04
PART 5  levels 0..6 from (BabAA, AbaBB): [1, 12, 101, 782, 5906, 44048, 326200]
  PASS matches the published level counts exactly
OVERALL PASS
```

Key output of `python3 census.py 10 13 certs_r10_c13.txt`:

```
ball of the standard presentation, total length <= 13: 6476104 tuples
canonical presentations with total length <= 10: 9576
  nontrivial by determinant 8419; AC-trivial with certificate 1157; unresolved 0
  certificate lengths min 7, max 30, mean 18.06
OVERALL PASS
```

Key output of `python3 check_certs.py certs_r10_c13.txt`:

```
checked 1157 certificates from certs_r10_c13.txt: 0 failed, longest 30 moves
RESULT PASS
```

Key output of `python3 enum_check.py 13`:

```
published sizes for l = 10, 11, 12, 13: 20, 104, 204, 1400
l = 10: (A) 5991 | (B) 608 | (C) 44 | (D) 20 MATCH
l = 11: (A) 16596 | (B) 2540 | (C) 204 | (D) 104 MATCH
l = 12: (A) 46245 | (B) 4396 | (C) 320 | (D) 204 MATCH
l = 13: (A) 129952 | (B) 18116 | (C) 1992 | (D) 1400 MATCH
l = 10: 20 presentations | AC-trivial with certificate 20 | quotient 0 | unresolved 0
l = 11: 104 presentations | AC-trivial with certificate 104 | quotient 0 | unresolved 0
l = 12: 204 presentations | AC-trivial with certificate 184 | quotient 4 | unresolved 16
  A5 quotient witnesses for (BAABa,BBBBAbA), (BABaa,BBBBaba), (BBaba,BABaaaa), (BBAbA,BAAAABa)
```

Independent order computation for those four presentations, with sympy 1.14.0:

```
<BAABa, BBBBAbA>  order 120
<BABaa, BBBBaba>  order 120
<BBaba, BABaaaa>  order 120
<BBAbA, BAAAABa>  order 120
```
