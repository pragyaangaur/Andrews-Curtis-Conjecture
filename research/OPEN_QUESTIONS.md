# Open questions on the Andrews-Curtis conjecture

Draft for a three-day research run. Written by member m15 of swarm smw2fzjic in round 1, and updated at the start of round 3 by member m8 of swarm smw2opo0o (direction F8) against the round-1 and round-2 artifacts, with a rerun of every check that was cheap to repeat.

This file collects twenty-seven questions, the original twenty and seven that rounds 1 and 2 raised. Each one is stated precisely together with a reason it matters and with what I could verify about its current status. Each one also carries an honest estimate of what three days of work could achieve. Nothing here is a claim about the truth of the Andrews-Curtis conjecture. Where I state a fact I either verified it in a primary source or checked it by a computation whose command is given.

## 0. This update, and how the labels work

This file was written in round 1 by member m15 of swarm smw2fzjic. Member m8 of swarm smw2opo0o (direction F8) updated it at the start of round 3, after rounds 1 and 2 were complete and refereed. The round-1 text of each question is kept as it stood, and a dated status block follows it. The table of section 3 is new, questions Q21 to Q27 are new, and section 4 records the reruns made during this update.

Every status in this file carries one of the following labels.

- **SETTLED (machine-checked)** means a Lean 4 proof with no `sorry`, no new axiom and no `native_decide`, with the command that prints its axioms. The Lean files named here were compiled again during this update.
- **SETTLED (verified computation)** means an exact deterministic program with replayable certificates, with the command and its key output recorded.
- **VERIFIED-SOURCE** means a textual or bibliographic claim checked against a live identifier during round 3, with the identifier in section 6.
- **ARGUMENT** means a proof written out in a repository artifact and not machine-checked.
- **REPORTED** means a statement taken from a source that this campaign did not replay.
- **OPEN** means that no answer is known.
- **WITHDRAWN** means a published claim that its authors or the record removed.

Three conventions are worth stating before the questions, because round 2 changed them. The group presented by $\mathrm{AK}(n)$ is trivial for every $n$, and this is now machine-checked, so the standing assumption of section 1 is settled rather than checked up to $n=5$. The claim that $\mathrm{AK}(3)$ is stably AC-trivial was withdrawn by its authors, so the stable status is unresolved, and Q27 holds the chronology. The literature uses two different stabilization moves, and Q23 asks whether they generate the same relation.

The changes that the round-3 brief asks the reader to find are the following.

| item | round-1 status | status after round 2 |
| --- | --- | --- |
| Q9, existence half | open | ANSWERED in characteristic 0 (no data), in characteristic 2 (data exist, machine-checked), and, at the level of the fusion category, in characteristic $p\ge5$; $\mathbb{F}_3$ and $\mathbb{Z}[i]$ remain OPEN |
| Q8, case $k=1$ | reported from a printed sketch | SETTLED for $n=2$ to 10 by replayed certificates, and by a uniform argument for all $n$ |
| Q2, length-14 classification | open | SETTLED except for 161 presentations after the replay of section 4.1 item 11 (164 at the round-2 close, of which one is now certified AC-equivalent to AK(3) and two pairs are merged) |
| $\mathrm{AK}(3)$, stable status | claimed trivial, then doubted | UNRESOLVED, and the withdrawal is documented in Q27 |

COORDINATOR UPDATE, 2026-11-04, late (round-3 verdicts that landed while this
update was being written; none of it is m8's work, and every item was checked
by the coordinator before being recorded here).

1. **Q25 is resolved as a reading question, and its conditional deduction is
   withdrawn.** m5's accepted F3 verdict established that Table 1 of
   arXiv:1609.00325 counts pairs of total length EQUAL to $T$, not at most
   $T$ (the $L=10$ column falls from 240 at $T=19$ to 10 at $T=20$), so the
   round-2 comparison crossed two conventions. Under the per-length reading
   their cells are exactly twice our per-length PU-class counts at $T=13$,
   $14$, $15$ ($4, 10, 70$ against $2, 5, 35$), the relator-order convention.
   What survives is a genuine residue: a third length-13 PU class (class C)
   whose eight presentations lie outside the cap-20 box, so any AC path from
   AK(3) to them needs an intermediate of total length at least 21, and a
   residual deficit at $T=16$ to $20$ of $3, 23, 49, 404, 454$ classes. See
   `directions/pu-enumeration/pu.md` (correction note) and
   `directions/pu-gap/pu-gap.md`.
2. **The resisters ledger of Q2, Q15, Q21 and Q24 stands at 157 undecided
   presentations in 155 undecided classes.** m5's six settled length-13
   resisters (now AK(3)-equivalent) and m8's Carreras replay (one more
   AK(3)-equivalent, two merges) combine to: 33 presentations certified
   AK(3)-equivalent, 8 length-13 presentations still undecided (the eight
   cap-17 exhaustions), $c(13) \le 2 + 8 = 10$ and $c(14) \le 2 + 155 =
   157$. The length-14 Miller-Schupp slice of Q7 has at most two undecided
   AC-classes. The certificates are in `directions/pu-gap/run/certs13_settled.txt`
   and `directions/c14/carreras/`, both replayed under independent checkers.
3. **Q20 is answered by m9's accepted F10 verdict** (`directions/hardness/`):
   the measure of Shehper et al. is the persistent $H_0$ barcode plus the
   per-presentation $\ell$-increase; the published finite approximation keeps
   only trivializable-inside-the-cap presentations, so it is undefined
   exactly where difficulty is unknown and excludes the AK(3) and resister
   components by construction; the exact barcode of the AK(3) component is
   computed at caps 13 to 20 (cap 20: 51,411,456 states, 1,751 finite bars);
   as a per-presentation difficulty score the invariant is refuted on our data
   (Spearman $+0.0060$ over 52,744 solved cases, minimum value on the
   91-move hardest case), while inside the component at fixed length it does
   predict move depth ($\rho$ from $0.32$ to $0.92$). AK(2) at most 4 against
   AK(3) at least 8 orders the two families.
4. **Q26(e) is resolved in the affirmative.** The coordinator read the body
   of arXiv:2506.23031v2: Section 1 contains both statements that the
   round-2 ak-ladder draft paraphrased (the AK($n$), $n > 2$ question is open,
   and AK(3) is the shortest potential counterexample in total relator
   length), and Section 2 contains the computability sentence quoted in
   `survey/complexity.md`. m8 was right that the abstract contains none of
   this; the attributions themselves stand.
5. **Q22 is answered (round 4, m10 of swarm smw2woueq, accepted after fresh
   refereeing; see directions/psl27-frontier/): the four PSL(2,7)-frontier
   presentations present INFINITE groups.** Each has a transitive action on
   28 points whose point stabiliser has index 28 and abelianisation
   $\mathbb{Z}^2 \oplus \mathbb{Z}/2$ by Reidemeister-Schreier, so the
   stabiliser is infinite and hence the group is. The length-14 census meets
   its first infinite groups; the 38 nontrivial rows are classified (34 of
   order 120, 4 infinite); the round-3 coset-enumeration overflow is
   explained. Bonus: the family $\langle a,b \mid BAABa, B^{2m}AbA\rangle$
   has order 24 at $m = 1$, order 120 at $m = 2$, and is infinite at
   $m = 3, 4, 5$ (subgroup indices 28, 9, 12).
6. **Q18 is answered in the range computed (round 4, m6 of swarm smw2woueq,
   accepted after fresh refereeing; see directions/ac-graph-diameters/):
   exact diameters, not bounds.** For all eight perfect groups of order at
   most 720 (exactly one at each of the orders 60, 120, 168, 336, 360, 504,
   660, 720, verified in GAP), $\Delta_2(G)$ is connected with diameter 8,
   except PSL(2,8) at 9; $\Delta_3(A_5) = 9$. The same values hold under the
   free-case three-move set; on generating tuples (ordinary generation) the
   diameters are 5 to 7; the product-replacement move set alone gives 44 to
   188 components, merged to one by conjugation. The diameter is always
   attained at a tuple with a trivial entry, and those vertices have no
   free-case counterpart (one-relator groups with a nontrivial relator are
   nontrivial), so the data does not measure free-case difficulty.

## 1. Status, conventions, and standing assumptions

The conjecture is open. The two standard families of candidates are the Akbulut-Kirby presentations and the Miller-Schupp presentations, and both are treated below. I use the convention of Akbulut and Kirby as quoted by Havas and Ramsay [4] and by Miasnikov [5]:

$$\mathrm{AK}(n)=\langle x,y \mid xyx=yxy,\ x^n=y^{n+1}\rangle,\qquad n\ge 1 .$$

The total relator length is $2n+7$, so $\mathrm{AK}(2)$ has length 11 and $\mathrm{AK}(3)=\langle x,y\mid xyx=yxy,\ x^3=y^4\rangle$ has length 13. Two warnings about the literature. First, some papers index the same family by $x^{n+1}=y^n$, which is the same family after exchanging $x$ and $y$; Romary and Zupan use that form [17]. Second, Havas and Ramsay describe the exceptional group in their length-13 theorem as "$L_2(5)$, the unique perfect group of order 120" [4, Section 4], and the group of that order is the binary icosahedral group, since $\mathrm{PSL}(2,5)\cong A_5$ has order 60. Anyone quoting their theorem should keep the order 120 with it.

Miller and Schupp study the family

$$\mathrm{MS}(n,w)=\langle x,y\mid x^{-1}y^{n}x=y^{n+1},\ x=w\rangle,\qquad n>0,$$

where $w$ has exponent sum zero on $x$. Miller and Schupp prove that every such presentation presents the trivial group. Akbulut and Kirby present $\mathrm{AK}(n)$ as a candidate counterexample, so the group it presents must be trivial; I verified that for $n\le 5$ by the computation in Section 4, and I did not find a printed proof for all $n$ in the sources I checked. Round 1 closed the general case: `directions/ak-status/ak_trivial.lean` proves that the group presented by $\mathrm{AK}(n)$ is trivial for every $n$, with no `sorry` and with standard axioms only, and I compiled the file again during this update.

The AC moves I refer to are: replace $r_i$ by $r_i^{-1}$; replace $r_i$ by $r_ir_j$ with $i\ne j$; replace $r_i$ by $wr_iw^{-1}$ for a word $w$. Two tuples are AC-equivalent when one is carried to the other by a finite sequence of these moves. The stable version allows a stabilization move, and the two published formulations of it differ. Miller, Myasnikov and Shpilrain add a new free generator with no relator, which changes the deficiency, while Shehper and coauthors add a generator together with the relator equal to it, which keeps the presentation balanced. Neither paper proves that the two relations coincide, and Q23 is the question.

## 2. The questions

Each entry has the same shape: the question, why it matters, what is known, and a rating. The rating is one of four letters.

- **A**: a definite answer is reachable in three days with a few CPU-days and careful code.
- **B**: a real partial answer is reachable, such as a completed small case or a verified bound.
- **C**: the realistic three-day outcome is a sharper conjecture or a failed test that narrows the search.
- **D**: no realistic chance in three days; listed because a solution would be a major result.

### Theme 1. AK(3) and the search frontier

#### Q1. Is $\mathrm{AK}(3)$ AC-trivial?

**Question.** Is there a finite sequence of AC moves carrying the tuple $(xyxy^{-1}x^{-1}y^{-1},\ x^3y^{-4})$ to $(x,y)$?

**Why it matters.** This is the smallest presentation that no method has trivialised, and it is the only obstruction at total relator length 13. A positive answer removes the standard test case for every search method. A proof that no such sequence exists would disprove the conjecture, so the question is a two-sided target.

**What is known.** The group is trivial, which I checked independently (Section 4) and which follows from the length-13 theorem of Havas and Ramsay [4] together with the exponent-sum computation. Every balanced two-generator presentation of the trivial group with total relator length at most 12 is AC-trivial [6]. Havas and Ramsay prove that every such presentation of length at most 13 is AC-equivalent to the standard presentation or to $\mathrm{AK}(3)$ [4, Theorem, Section 4]. Panteleev and Ushakov enumerate presentations AC-equivalent to $\mathrm{AK}(3)$ with relators of total length up to 20, improving the previous record of 17, and do not reach the standard presentation [14]. They also prove that automorphism moves may be applied to $\mathrm{AK}(n)$ presentations [14].

**Rating.** C. A positive answer would be a major result and no technique in the literature gives a negative certificate, so a definite answer in three days is unlikely. The realistic three-day outcome is B: extend the verified length bound, or verify a claimed enumeration independently.

**Status after round 2, recorded at the round-3 update: OPEN, with bounded negatives that have exact bounds.**
The group presented by $\mathrm{AK}(n)$ is trivial for every $n$ and that is machine-checked (section 1). The computational record is as follows. The census of the AK(3) class inside the total-length box at cap 20 contains 51,411,456 tuples and 79,680 classes, and every tuple in it has both relators of length at least 5, so no AC path from AK(3) to the standard tuple stays within total length 20. The same class contains exactly two Panteleev-Ushakov classes of minimal total length 13, so AK(3) is not alone at its own length (Q21). Panteleev and Ushakov report an enumeration to relator length 20 with no trivialisation, and round 2 did not reproduce their table (Q25). The published claim that AK(3) is stably AC-trivial was withdrawn, and the stable question is open (Q27).
The rating stays at C.

#### Q2. What are the AC-classes of balanced two-generator presentations of the trivial group of total length 14?

**Question.** List the AC-equivalence classes of balanced two-generator presentations of the trivial group with the sum of relator lengths exactly 14, and decide which of them are AC-equivalent to the standard presentation.

**Why it matters.** The verified map currently stops at length 13, where all classes collapse to the standard one or to $\mathrm{AK}(3)$ [4]. Length 14 is the first place where a new obstruction could appear, and a complete classification there would be a concrete deliverable.

**What is known.** The enumeration method is described in [4, Section 4]: put presentations in a canonical form for cyclic permutations and inverses, discard those with nontrivial abelianisation, then decide triviality of the group by coset enumeration, and finally test AC-equivalence. The starting data are finite for each length bound, so the classification is a finite computation once triviality is decidable for each case, and coset enumeration settles triviality on the cases that arise.

**Rating.** B. The enumeration and the triviality tests are routine. The expensive step is deciding AC-equivalence for each surviving class, and for any class that behaves like $\mathrm{AK}(3)$ that decision is out of reach. A realistic outcome is a complete list together with the classes that resist, which is itself the next frontier.

**Status after round 2, recorded at the round-3 update: PARTLY ANSWERED, and the residue is 161 presentations with exact bounds.**
The classification at total relator lengths 12, 13 and 14 was computed for the first time in round 2 (`directions/c14/`). All 54,068 canonical presentations with unimodular abelianisation were classified. Of these, 53,840 are AC-trivial with an explicit certificate, 26 are AC-equivalent to AK(3) with an explicit certificate, 38 present a nontrivial group (34 with a homomorphism onto $A_5$ and 4 with one onto $\mathrm{PSL}(2,7)$), and 164 resist every search that was run. Of the 164, 142 have an exhaustive negative at total length 17, 18 or 19 and 22 were stopped by an explicit budget of 400,000 pairs at cap 19. Every one of the 53,866 certificates replays under an independent checker, and I replayed all of them again during this update: `python3 replay14.py certs_all.txt` prints `replayed 53866 certificates, 0 failed, longest 141 moves`. The length-14 slice of the Miller-Schupp family inside $n\le 7$ and $|w|\le 7$ is classified as well, which is new data for Q7.
During this update I replayed five external certificates under a verifier written here from the format described in section 4.1 item 11. That replay certifies one of the 164 resisters as AC-equivalent to AK(3) and certifies two pairs of resisters as AC-equivalent to each other, so the number of undecided presentations is 161 and the number of presentations certified AC-equivalent to AK(3) is 27. The rating rises to A for the computation as posed, and what remains of it is Q24.

#### Q3. Are $\mathrm{AK}(3)$ and $\mathrm{AK}(4)$ AC-equivalent?

**Question.** Is there a sequence of AC moves taking $\mathrm{AK}(3)$ to $\mathrm{AK}(4)$?

**Why it matters.** If the family members are AC-equivalent to one another then they stand or fall together, and effort spent on one is effort spent on all. If they are pairwise inequivalent then the family supplies many independent candidates, and proving inequivalence for one says nothing about the others.

**What is known.** $\mathrm{AK}(2)$ is AC-trivial [5], [6]. Shehper and coauthors prove that $\mathrm{AK}(n)$ is AC-equivalent to a presentation of total length $n+11$ for every $n\ge 2$, which reduces the length of $\mathrm{AK}(n)$ for $n\ge 5$ [16, Theorem A]. I found no statement in the literature about AC-equivalence between $\mathrm{AK}(n)$ and $\mathrm{AK}(m)$ for $n\ne m$.

**Rating.** C. The question is well posed and a positive answer would be verifiable by exhibiting a move sequence. Nothing in the current toolkit finds move sequences of the length that would presumably be needed, so the realistic outcome is a failed bounded search together with a sharper statement of what was excluded.

**Status after round 2, recorded at the round-3 update: OPEN, and both ends of the comparison now have shorter certified forms.**
Round 2 certified the Shehper length reduction end to end for $n = 2, 3, 4, 5$ with replayable certificates (`directions/ak-ladder/`, 42 certificate files, two independent arithmetics, 0 failures on my rerun). For $n = 3$ the chain reaches a presentation of total length 14, and for $n = 5$ it reaches one of total length 16, which is a certified reduction from length 17. Both $\mathrm{AK}(n)$ and its length-$(n+11)$ form are strict local minima of the total relator length under every single AC move for every $n$ (Theorem 1 of the draft, a proof with no case analysis in $n$). No certificate relates AK(3) to AK(4), and no invariant separates them. A proof of AC-equivalence between two rungs would have to leave the local minimum of each rung, so any certificate has to reach a larger total length on the way.
The rating stays at C.

#### Q4. What is the recalcitrance of $\mathrm{AK}(3)$?

**Question.** What is the least number of elementary M-transformations, in the sense of Burns, Herfort, Kam, Macedonska and Zalesskii [20], that carries $\mathrm{AK}(3)$ to the standard presentation?

**Why it matters.** Recalcitrance measures proof length in a coarser move system. Havas and Ramsay report that $\langle a,b\mid a^2=b^3,\ aba=bab\rangle$, which needs fourteen essential AC moves, has recalcitrance 2 [4, concluding remarks, citing 20]. A coarse system that trivialises $\mathrm{AK}(3)$ in a few moves would point at the structure of a short AC proof.

**What is known.** The definition and the basic examples are in [20]. The move system has infinitely many members at each stage, which is why it has not been attacked computationally. Havas and Ramsay state that it does not seem easily amenable to computer investigation for exactly that reason [4].

**Rating.** C. A bounded version of the question, restricting the M-transformations to a finitely generated subclass, is computable and could give a verified upper bound. The full question needs an idea about which M-transformations matter.

**Status after round 2, recorded at the round-3 update: OPEN, and no progress on the question.**
Recalcitrance was not attacked in rounds 1 or 2, and no bound on it was computed. What exists is a measurement of the opposite kind: AK(3), AK(4) and AK(5) are strict local minima of total relator length, and the certified path for AK(5) reaches total length 28 before descending to 16, so a coarse move system would have to compress a long excursion.
The rating stays at C.

#### Q5. Is the length reduction for $\mathrm{AK}(n)$ asymptotically optimal?

**Question.** Is there a function $f$ with $f(n)=o(n)$ such that $\mathrm{AK}(n)$ is AC-equivalent to a presentation of total relator length at most $f(n)$? In particular, is the bound $n+11$ of [16] the best available linear bound?

**Why it matters.** A uniform length reduction is the only structural statement known about the whole family. If the lengths could be pushed down to a constant, then all $\mathrm{AK}(n)$ would be AC-equivalent to presentations of bounded length, and the family would collapse to finitely many AC-classes.

**What is known.** Shehper and coauthors give a one-parameter family $P(n,k)$ of presentations AC-equivalent to $\mathrm{AK}(n)$, with shortest member of length $n+11$ at $k=n-1$ [16, Theorem A and the discussion before it]. Their result reduces the length for $n\ge 5$, and they state that all but two presentations in the Akbulut-Kirby series are length reducible.

**Rating.** C. Proving a lower bound on the length of a presentation AC-equivalent to a given one is a hard problem. A three-day outcome could be a computational search over the parameter space of the constructions in [16] together with a precise statement of which lengths are achieved.

**Status after round 2, recorded at the round-3 update: PARTLY ANSWERED for the constructive half, and untouched for the lower bound.**
The length-$(n+11)$ presentation is now reached by an explicit certificate for $n = 2, 3, 4, 5$, so the reduction of Shehper and coauthors is certified end to end at those rungs, and for $n = 5$ that is a genuine reduction from total length 17 to 16. The first step and the last step of the chain are uniform templates in $n$, machine-checked for $n$ up to 30 by `python3 patterns.py`, and a formal induction for all $n$ is written out as an argument rather than as a proof. The open link is the middle sequence from $\mathrm{MS}(n,w_1)$ to $\mathrm{MS}(n,w_{n-1})$ for $n\ge 6$. For $n = 6$ the bidirectional search closed its box without finding a certificate (total length cap 28, depth 20, 330 s), so the chain for $n\ge 6$ is not certified. Round 2 also recorded a proof gap in the preprint's Theorem 6, which is the printed proof of that middle step, at the exact point where consequence-level reasoning stands in for AC moves; Q26(b) holds the statement.
The rating stays at C, and the concrete sub-target is a certificate for the middle step at $n = 6$.

### Theme 2. Miller-Schupp presentations

#### Q6. Is $\mathrm{MS}(n,w)$ AC-trivial for every $n$ and every admissible $w$?

**Question.** For every $n>0$ and every word $w$ with exponent sum zero on $x$, is $\mathrm{MS}(n,w)$ AC-equivalent to the standard presentation?

**Why it matters.** This is the second large family of candidates, and it is parametrised by a free word, so it is a natural test bed for any proposed invariant. A single non-trivialisable member would be a counterexample to the conjecture, since the group is trivial by [3].

**What is known.** The group is trivial for every admissible pair $(n,w)$ [3, Corollary 3]. Three infinite subfamilies are known to be AC-trivial, namely $\mathrm{MS}(1,w)$ for all $w$, $\mathrm{MS}(n,w_\star)$ for all $n$ with $w_\star=y^{-1}xyx^{-1}$, and $\mathrm{MS}(2,w_k)$ for all $k$ with $w_k=y^{-k}x^{-1}yxy$ [16, Theorem B]. In addition, for each fixed $n$ the whole family $\mathrm{MS}(n,w_k)$ is AC-equivalent to $\mathrm{AK}(n)$ [16, Theorem B].

**Rating.** D for the general statement. B for a bounded version, which is Q7.

**Status after round 2, recorded at the round-3 update: OPEN, with the case $k=1$ explicit and the triviality of every member known.**
Every $\mathrm{MS}(n,w)$ presents the trivial group by Miller and Schupp, so the only question is AC-triviality. Three infinite subfamilies are AC-trivial in the literature, and round 2 made the case $k=1$ of the subfamily $\mathrm{MS}(n,w_k)$ explicit as a certificate (Q8). No member with $n\ge 3$ is known to be AC-trivial, and no member is known to be AC-nontrivial.
The rating stays at D for the general statement.

#### Q7. Are all $\mathrm{MS}(3,w)$ with $|w|\le 7$ AC-trivial?

**Question.** Decide AC-triviality for the finite set of presentations $\mathrm{MS}(3,w)$ with $w$ of length at most 7 and exponent sum zero on $x$, up to the reductions described in [16].

**Why it matters.** The set is finite, it is large enough to be informative, and it sits just beyond the length-13 frontier of [4] while avoiding $\mathrm{AK}(3)$ itself. The answer would say whether the Miller-Schupp family keeps producing new hard cases or collapses quickly.

**What is known.** Shehper and coauthors assemble 170 presentations for each fixed $n$ after removing cyclic redundancies, and study them with classical search and with a reinforcement learning agent [16]. Lisitsa reports further trivialisations for Miller-Schupp presentations [25], which I could not verify bibliographically (see Section 6).

**Rating.** A. The set is finite and the existing search methods are adequate for many members. A complete answer needs a careful statement of which members remain open, and that statement is itself a useful deliverable.

**Status after round 2, recorded at the round-3 update: OPEN, and the finite set named in the question was not enumerated in round 2.**
The direction that was to attack it was replaced in round 2 by the AK-ladder, so no complete answer exists. What exists is a slice. Round 2 classified the Miller-Schupp presentations of total relator length exactly 14 inside $n\le 7$ and $|w|\le 7$: that slice has 191 canonical presentations, 51 of them with unimodular abelianisation, and the classes at the round-2 close were 45 AC-trivial, 1 AC-equivalent to AK(3) with a 34-move certificate, and 5 resisting, one exhausted at cap 18 and the others at cap 18 or cap 19. The replay recorded in section 4.1 item 11 changes that slice: a second presentation is certified AC-equivalent to AK(3) by 71 moves, and the four remaining resisters pair up, so the length-14 Miller-Schupp frontier has at most two undecided AC-classes and one of them contains Solitar's classical candidate $\langle x,y\mid x^{-1}y^2x=y^3,\ y^{-1}x^2y=x^3\rangle$. The count of 1190 presentations that Shehper and coauthors report for the same parameter box was not reproduced from the definition: with every $w$ allowed the box has 4843 canonical presentations, and with the exponent sum of $w$ on $x$ required to be zero it has 889. Q26(d) records this.
The rating falls to B, because the finite set is not yet pinned down.

#### Q8. For fixed $n$, are all $\mathrm{MS}(n,w)$ AC-equivalent to $\mathrm{AK}(n)$?

**Question.** For fixed $n>0$, is every $\mathrm{MS}(n,w)$ AC-equivalent to $\mathrm{AK}(n)$, or do different words $w$ give different AC-classes?

**Why it matters.** If the answer is yes, the Miller-Schupp family adds no new candidates beyond the Akbulut-Kirby family, and the two families should be studied as one. If the answer is no, then the parameter $w$ produces genuinely new candidates and the search space is much larger than the AK family suggests.

**What is known.** For the specific one-parameter subfamily $w_k=y^{-k}x^{-1}yxy$, all members are AC-equivalent to each other and to $\mathrm{AK}(n)$ [16, Theorem B]. The case $w_1=y^{-1}x^{-1}yxy$ giving $\mathrm{MS}(n,w_1)\sim\mathrm{AK}(n)$ is attributed in [16] to Myasnikov, Myasnikov and Shpilrain [24].

**Rating.** C. A positive answer needs a family of move sequences indexed by $w$, which is a real construction problem. A negative answer needs an invariant, which is harder still.

**Status after round 2, recorded at the round-3 update: SETTLED for $w = w_1$ and every $n$, and OPEN in general.**
Round 2 delivered explicit certificates for $\mathrm{AK}(n)\sim\mathrm{MS}(n,w_1)$ for $n = 2$ to 10, with $4n+3$ moves forward and $7n+3$ moves back. They are replayed by five independent implementations and by a Lean kernel proof whose theorems depend on no axioms at all; `cd directions/ms-ak-certs && bash run_all.sh`, rerun during this update, replays all eighteen certificates and prints eleven lines of the form `does not depend on any axioms`. The construction is described for general $n$ by an induction that is written out and not machine-checked, so the statement for all $n$ is an argument with machine-checked instances. For $k\ne 1$ the round-2 report recorded two exact obstructions to that route: the exponent sums of the second relator do not match those of $D$ or $D^{-1}$, and the word $x^{-1}y^{-1}x$ is not in the normal closure of the first relator.
The rating stays at C.

### Theme 3. Invariants and the topology of 2-complexes

#### Q9. Does Quinn's triangular Hopf algebra exist?

**Question.** Is there a triangular Hopf algebra $H$ with a collection of self-dual irreducible representations $V_i$ such that the product of any two decomposes as a sum of copies of the $V_i$ and $\sum_i (\dim V_i)^2 = 0$?

**Why it matters.** Quinn poses this question as a route to an invariant that is not a function of the fundamental group. Ordinary algebraic invariants of the fundamental group cannot separate balanced presentations of the trivial group, so a counterexample detector has to come from outside that range of invariants.

**What is known.** The question is stated in [11], where Quinn explains that such data would define a topological quantum field theory on 2-complexes which stands a good chance of detecting counterexamples. I did not find a resolution in the sources I checked, and I cannot certify that none exists.

**Rating.** C. The condition is strong, and a search over small semisimple triangular Hopf algebras and small modular tensor categories is a finite computation. Deciding the question in general is well beyond three days, but a systematic negative test on the known small examples would be a real result.

**Status after round 2, recorded at the round-3 update: ANSWERED in part, and the detection question is answered in the negative for Quinn's framework.**
Round 2 settled the existence half characteristic by characteristic. Over any field of characteristic 0 the data cannot exist, because conditions (1) to (3) make the $V_i$ the simples of a symmetric fusion category whose global dimension is the required sum of squares, and Etingof, Nikshych and Ostrik prove that this dimension is positive. Over $\mathbb{F}_2$ the data exist and the example is machine-checked. Over $\mathbb{F}_p$ with $p\ge 5$ the categorical data exist and the invariant form is machine-checked for $p\le 13$. Over $\mathbb{Z}$ the data cannot exist, and the cases $\mathbb{F}_3$ and $\mathbb{Z}[i]$ remain open. The detection question is answered in the negative for the semisimple theories that Quinn's conditions produce, since Khovanov, Krushkal and Nicholson show that such theories cannot distinguish simple homotopy equivalence from 3-deformation. The labels are in `survey/quinn-tqft.md`, and the check is `python3 survey/quinn_check.py`, which I reran.
The rating for the residual questions is B.

#### Q10. Are there simple homotopy equivalent 2-complexes that are not 2-deformation equivalent?

**Question.** Exhibit finite 2-complexes $K$ and $L$ that are simple homotopy equivalent but not related by a 2-deformation, or prove that none exist.

**Why it matters.** Quinn states the generalised conjecture that any simple equivalence of 2-complexes comes from a 2-deformation, and adds that no one expects it to be true [12]. A counterexample in general would locate the difficulty of the Andrews-Curtis problem precisely, and would show that the conjecture fails for reasons that have nothing to do with the contractible case.

**What is known.** Quinn's formulation and the remark that 2-deformations determine simple homotopy equivalences are in [12]. The contractible case is the Andrews-Curtis conjecture itself, by the correspondence between presentations and 2-complexes and Wright's analysis of 3-deformations [10].

**Rating.** D. This is a hard existence problem in simple homotopy theory, and three days will not settle it.

**Status after round 2, recorded at the round-3 update: OPEN, with the search reduced to an exact target.**
Round 2 proved that a separating quantity of the kind the generalised conjecture needs exists on a class of pairwise simple homotopy equivalent 2-complexes exactly when that class contains two complexes that are not 3-deformation equivalent (Theorem 4 of `directions/invariant-ideas/idea.md`, an argument). On the contractible class this is the failure of the stable conjecture (Corollary 5), and at total relator length at most 11 no such pair exists (Corollary 6, from the census). The one published candidate pair, Barmak's pair of presentations of $\mathbb{Z}\times\mathbb{Z}$, is Q**-equivalent by Fernandez's theorem, so it does not realise the gap, and Fernandez's identifier was checked again during this update.
The rating stays at D.

#### Q11. Do elementary M-transformations and AC moves generate the same equivalence relation?

**Question.** Is the equivalence relation generated by elementary M-transformations on balanced presentations the same as AC-equivalence, or strictly coarser?

**Why it matters.** If the two relations coincide, then any complete invariant for one is a complete invariant for the other, and the difference between recalcitrance 2 and fourteen AC moves for $\langle a,b\mid a^2=b^3,\ aba=bab\rangle$ [4], [20] is a pure measure-of-complexity phenomenon. If they differ, then AC-equivalence is strictly finer and a proof of M-equivalence for $\mathrm{AK}(3)$ would not settle Q1.

**What is known.** Elementary M-transformations are introduced in [20], and their number is infinite at each stage. Havas and Ramsay note the enormous difference in move counts and remark that elementary M-transformations do not seem easily amenable to computer investigation, partly because there are infinitely many of them at each stage [4].

**Rating.** C. A negative answer needs a pair of presentations M-equivalent but not AC-equivalent, which needs a separating invariant. A positive answer needs a simulation of each M-transformation by AC moves, which is plausible to attempt for the first few families.

**Status after round 2, recorded at the round-3 update: OPEN, and no progress on it.**
The comparison between elementary M-transformations and AC moves was not attacked in rounds 1 or 2. A neighbouring comparison was raised by round 2 and is well posed: the two published stabilization moves, the deficiency-changing one of Miller, Myasnikov and Shpilrain and the balance-preserving one of Shehper and coauthors, are not proved to give the same relation, and Q23 is that question. The two questions are independent, since Q23 compares two stabilization move sets where this question compares a coarser move set with AC.
The rating stays at C.

### Theme 4. Decidability and complexity

#### Q12. Is the triviality problem for balanced presentations decidable?

**Question.** Is there an algorithm which, given a balanced presentation, decides whether the group it presents is trivial?

**Why it matters.** The Andrews-Curtis conjecture only concerns balanced presentations of the trivial group, so decidability of triviality is the natural algorithmic boundary for the whole subject. A decision procedure would also make the classification of Q2 routine at every length bound.

**What is known.** Triviality is undecidable for finite presentations in general. For balanced presentations, Bridson explains how an iteration of his construction might produce a seed group with unsolvable word problem, and writes that if one could, then it would follow that the triviality problem for balanced presentations was unsolvable [7, Remark 3.3]. He does not achieve it, so as of [7] the balanced case is open.

**Rating.** D. This is a major decidability question and three days will not touch it. It is included because any claimed solution would reframe the field.

**Status after round 2, recorded at the round-3 update: OPEN, and no progress on it.**
Nothing in rounds 1 or 2 touches the decidability of triviality for balanced presentations. The bounded computations now settle large finite boxes instead. Every balanced two-generator presentation of the trivial group with total relator length at most 11 is AC-trivial, every one with total length 12 is AC-trivial or presents a nontrivial group, and the length-13 and length-14 boxes are classified up to 164 presentations (Q2).
The rating stays at D.

#### Q13. Is AC-equivalence in the free group of rank two decidable?

**Question.** Is the set of pairs $(u,v)$ of words in $F_2$ that are AC-equivalent to $(x,y)$ recursive?

**Why it matters.** A decision procedure would settle Q1 immediately. Even a procedure for a restricted class of tuples, such as tuples of total length at most 20, would let the enumeration of [14] be turned into a proof.

**What is known.** The set is recursively enumerable, since one can enumerate move sequences. I found no decidability result in the sources I checked, and I did not find a proof that the problem is undecidable either.

**Rating.** D. The question is at least as hard as Q1 in practice, and nothing in the literature suggests a route.

**Status after round 2, recorded at the round-3 update: OPEN in general, and decided inside explicit boxes.**
Round 2 decided AC-equivalence inside boxes in two families: the class of AK(3) inside total length 20 (51,411,456 tuples and 79,680 classes, with a certificate for every class), and every presentation of the trivial group with total relator length at most 14, up to the 164 resisters. Inside a box the question is finite and was answered by exhaustive search with replayable certificates. No bound carries over to the unbounded question.
The rating stays at D.

#### Q14. Does the superexponential lower bound occur in rank two or three?

**Question.** Is there a sequence of balanced presentations of the trivial group on two generators, with total relator length $L_n$ growing, such that the number of AC moves needed to trivialise the $n$-th presentation grows faster than any fixed tower of exponentials in $L_n$?

**Why it matters.** Bridson's lower bound shows that search failure proves nothing in rank at least four [7]. If the same phenomenon occurs in rank two then the failure to trivialise $\mathrm{AK}(3)$ carries no information at all, and if it does not occur in rank two then rank two is genuinely different from higher rank.

**What is known.** Bridson proves the bound for $k\ge 4$ generators, with total relator length at most $24(n+1)$ and AC-move count at least $\Delta(\lfloor\log_2 n\rfloor)$, where $\Delta(0)=2$ and $\Delta(m+1)=2^{\Delta(m)}$ [7, Theorem A], and he shows the bound can be matched from above [7, Corollary F]. Lishak constructs balanced presentations of the trivial group with two generators and two relators for which the minimal number of relations needed to demonstrate that a generator is trivial grows faster than any fixed-height tower of exponentials in the length of the presentation [8]. Lishak's measure is a diagrammatic area. Bridson's conversion of area bounds into AC-move bounds goes through presentations with an extra generator, so it does not apply to Lishak's two-generator examples as stated.

**Rating.** D. The gap is a genuine technical obstruction, and closing it is a research programme. The useful three-day output is a precise statement of where the conversion fails.

**Status after round 2, recorded at the round-3 update: OPEN, and untouched.**
Round 2 did not attack the tower bounds in rank two or three. The round-2 second referee found three errors in the complexity survey, one of which is a printed bound of Bridson that is false at $m = 1$; the corrected statement is that the conjugate count grows like $\mathrm{fib}_{m+2}$, and Bridson's Theorem A is unaffected. None of this bears on the rank-two question.
The rating stays at D.

#### Q15. How fast does the number of AC-classes grow?

**Question.** Let $c(L)$ be the number of AC-classes of balanced two-generator presentations of the trivial group with total relator length at most $L$. Determine $c(L)$ for $L\le 14$ and estimate its growth.

**Why it matters.** The values of $c(L)$ are the most basic quantitative description of the conjecture at small length. The conjecture in rank two is exactly the statement that $c(L)=1$ for all $L$, so a table of values is a precise record of how far the verified statement extends.

**What is known.** $c(12)=1$ follows from [6]. $c(13)$ is 1 or 2, and it is 1 exactly when $\mathrm{AK}(3)$ is AC-trivial, by [4, Theorem]. Nothing is known for $L\ge 14$.

**Rating.** B. The values up to 13 are re-derivable, and the enumeration to 14 is a substantial but feasible computation. The honest output is a table with the open entries marked.

**Status after round 2, recorded at the round-3 update: SETTLED for $L\le 12$, bounded at 13 and 14, and open above.**
$c(11) = 1$ is verified by the round-1 census, which I reran during this update: `python3 census.py 11 13` prints 26,182 canonical presentations, 3,697 AC-trivial with certificates, 0 unresolved and `OVERALL PASS`, together with the published level counts, and the 3,697 certificates replay with 0 failures. $c(12) = 1$ follows from the round-2 classification, where all 4,392 unimodular length-12 presentations are AC-trivial with a certificate and the other 4 present a nontrivial group. $c(13)$ is 1 or 2 by the published theorem of Havas and Ramsay (REPORTED), and the round-2 computation gives the weaker bound $c(13)\le 16$ without using their search, since 14 length-13 presentations are undecided and every other one is AC-trivial, AK(3)-equivalent or nontrivial. For length 14 the same argument gave $c(14)\le 2+164 = 166$ at the round-2 close, and the replay of section 4.1 item 11 improves it to $c(14)\le 2+161 = 163$, since 147 length-14 presentations and 14 length-13 presentations remain undecided. These bounds are arguments from counts that were verified.
The rating stays at B, with the upper bounds now explicit.

### Theme 5. Topology and finite groups

#### Q16. Are the links $L(3,2;4/d)$ handle-slide equivalent to unlinks?

**Question.** Are the $R$-links $L(3,2;4/d)$ handle-slide equivalent to unlinks, and are the corresponding trisections $\mathcal{T}(4/d)$ standard?

**Why it matters.** These are the questions with which Romary and Zupan close their paper [17]. The same construction produces the Akbulut-Kirby presentations from the family $L(3,2;2n/(2n+1))$, so a criterion for handle-slide triviality of these links would be a geometric criterion for AC-triviality of the associated presentations.

**What is known.** Every presentation $P(3,2;4/d)$ is AC-trivial [17, Theorem 1.2], proved by exhibiting trisections of the closed 4-manifolds $X_{L(3,2;4/d)}$. The family $L(3,2;2n/(2n+1))$ induces the presentation $\langle x,y\mid xyx=yxy,\ x^{n+1}=y^n\rangle$, which is the Akbulut-Kirby family with the letters exchanged [17, introduction]. It remains open whether a nonstandard trisection of $S^4$ exists [17, Section 5].

**Rating.** D for the link-theoretic questions. B for extending the trisection method to further parameter values, which is a computation with a clear success criterion.

**Status after round 2, recorded at the round-3 update: OPEN, and untouched.**
No progress was made on handle-slide triviality of $L(3,2;4/d)$. The 4-manifold method of Romary and Zupan remains the one positive technique in this direction, and Gompf's killing of the 4-sphere built from AK(3) shows that the technique can succeed where the group search has not.
The rating stays at D.

#### Q17. Does a standard trisection imply AC-triviality?

**Question.** Is there a general implication from "the trisection $\mathcal{T}$ of $X_L$ is standard" to "the associated balanced presentation $P$ is AC-trivial"?

**Why it matters.** Romary and Zupan suggest that one route to handle-slide triviality runs through standardness of the trisections, invoking a theorem of Meier and Zupan [17]. If the implication holds in the other direction as well, then a 4-manifold statement would decide an AC statement, which is the kind of bridge the subject needs.

**What is known.** The construction from an $R$-link to a balanced presentation of the trivial group passes through a handle decomposition of the homotopy 4-sphere, and the cases settled in [17] are settled by explicit trisection diagrams. Gompf showed that the particular homotopy 4-sphere built from $\mathrm{AK}(3)$ is standard [13], which shows that the 4-manifold route can succeed where the group-theoretic search has not.

**Rating.** C. The implication is plausible and testable on the examples already in the literature. A three-day outcome would be a precise statement of the implication together with a check on the smallest cases.

**Status after round 2, recorded at the round-3 update: OPEN, and untouched.**
No progress was made on the implication from standardness of a trisection to AC-triviality of the associated presentation. Round 2's topology work went into the Dynnikov preprint, whose reduction of Zeeman's conjecture is REPORTED and rests on one asserted delegation to Matveev 1987.
The rating stays at C.

#### Q18. What is the diameter of the Andrews-Curtis graph of a finite perfect group?

**Question.** For a finite perfect group $G$ and $k\ge 2$, what is the diameter of the graph whose vertices are generating $k$-tuples of $G$ and whose edges are AC moves?

**Why it matters.** Borovik, Lubotzky and Myasnikov proved that the AC graph of a finite group has the components they describe, and concluded that computations in finite groups cannot produce a counterexample to the classical conjecture [9]. A diameter bound would quantify how much a finite quotient can see, and would connect the Andrews-Curtis graph to the product replacement graph, where mixing time bounds are available [26].

**What is known.** For a finite group $G$ the AC graph $\Delta_k(G)$ has vertices the generating $k$-tuples, and the nontrivial AC transformations coincide with Nielsen moves on the abelianisation, so the AC graph sits between the product replacement graph and its enlargement by inversions [9]. The connected components are described completely in [9], and for perfect $G$ the graph is connected for $k\ge 2$ in the setting of their Theorem 2.1.

**Rating.** B. For small groups the diameter is computable exactly by breadth-first search. A general bound is a research problem, and the three-day outcome is a table for the perfect groups of order at most a few hundred together with a conjecture about the growth.

**Status after round 2, recorded at the round-3 update: OPEN, with a component census and no diameter.**
Round 1 computed the components of the Andrews-Curtis graph for 21 group-rank pairs and checked the Borovik, Lubotzky and Myasnikov theorem and its abelian corollary (`python3 survey/nielsen_census.py`). The output includes the Heisenberg group of order 125 at rank 2, where the abelianisation has two components, so the theorem has content beyond connectivity there. No diameter was computed for any group, and the three-day outcome named in the question was not attempted.
The rating stays at B.

### Theme 6. Formalisation and experiment

#### Q19. Can the basic theory be formalised in Lean 4 with Mathlib?

**Question.** Formalise the free group on $n$ letters, the three AC moves on $n$-tuples, and AC-equivalence as the reflexive transitive closure, then prove that AC moves preserve the normal closure of the relators, that they preserve the exponent-sum matrix, and that the set of tuples reachable in at most $k$ moves from a fixed tuple is finite.

**Why it matters.** Every claim in this subject is currently checked by hand or by unaudited code. A small formal kernel for the definitions and the elementary invariants would make future claims checkable, and the three lemmas above are used without proof in every paper on the subject.

**What is known.** Mathlib contains free groups and the normal closure of a subset of a group, so the definitions are available. I found no formalisation of the Andrews-Curtis conjecture in Lean or in another proof assistant in the sources I checked.

**Rating.** A for the three lemmas, which are elementary arguments once the definitions are in place. A fifth and harder target is a Lean 4 proof, with no sorry and no new axiom, that the group presented by $\langle x,y\mid xyx=yxy,\ x^3=y^4\rangle$ is trivial. That target is rated C, since it needs either a verified coset enumeration inside Lean or a hand derivation of $y=1$ from the two relators, and finding such a derivation is an experiment.

**Status after round 2, recorded at the round-3 update: SETTLED for the three named lemmas and for triviality of AK(n), and PARTLY for the rest.**
`toolkit/lean/AC.lean` formalises the three AC moves, AC-equivalence, the exponent-sum invariants and the rank-one non-equivalence of $(x)$ and $(x^2)$, whose theorems use only standard axioms. `toolkit/lean/AC2.lean` adds preservation of the normal closure, so presenting the trivial group is an AC-invariant, together with the rank-two conjugate-to-generator theorem and Lemma 8 of the q-transformations survey in AC form. `directions/ak-status/ak_trivial.lean` proves that the group presented by $\mathrm{AK}(n)$ is trivial for every $n$. `directions/ms-ak-certs/AC_certs.lean` kernel-checks eighteen explicit certificates with no axioms at all. I compiled the first three files again during this update, and each printed only standard axioms. What remains is the permuted-order variant of Lemma 8, a reusable Lean certificate verifier that replays the repository's certificate files, and the formal version of the cocommutativity kill theorem; those are the three targets of round 3's direction F5.
The rating rises to A for the original target.

#### Q20. Is there a computable hardness measure that predicts search difficulty?

**Question.** Is there a function on balanced presentations, computable quickly from the word structure, that correlates with the AC-distance or with the probability that a fixed search method finds a trivialisation?

**Why it matters.** Search methods for the conjecture are compared by anecdote. A validated hardness measure would let effort be directed at the cases that matter, and would give a principled way to report a failed search.

**What is known.** Shehper and coauthors propose a topological hardness measure, report that it correlates with search difficulty on their datasets, and give a difficulty distribution across the Akbulut-Kirby and Miller-Schupp families [16]. Lisitsa uses first-order theorem provers and reports trivialisations of cases that resisted specialised search [18], which suggests that hardness is method-dependent.

**Rating.** B. The datasets and the code of [16] are available, so a replication and an independent test of the proposed measure is feasible. The honest outcome is a correlation table and a statement about which families the measure separates.

**Status after round 2, recorded at the round-3 update: OPEN, and the data now exist.**
The hardness question was not attacked in rounds 1 or 2, and the measure of Shehper and coauthors was not computed on any of our datasets. Three datasets are now available for it: the 79,680 classes of the AK(3) class with their certificate depths (4,640,600 moves in total and a mean of 58.24 moves per class), the 164 resisters with their exact caps, and the complete classification at total lengths 12, 13 and 14. Round 3's direction F10 is the test.
The rating stays at B.

### Theme 7. Questions raised by rounds 1 and 2

The seven questions below did not exist in the round-1 draft. Each one is stated in the same shape as the twenty above, with its own verification status. Rounds 1 and 2 produced them, and round 3 has a direction for four of them.

#### Q21. Which length-13 presentations lie in the AK(3) class?

**Question.** Identify the AC-classes of total relator length 13 that are AC-equivalent to $\mathrm{AK}(3)$, and decide whether the 14 length-13 presentations that the round-2 classification left undecided are among them. Equivalently, decide whether the two Panteleev-Ushakov classes of minimal total length 13 account for every length-13 member of the class.

**Why it matters.** Havas and Ramsay prove that every balanced two-generator presentation of the trivial group with total relator length 13 is AC-trivial or AC-equivalent to $\mathrm{AK}(3)$. That theorem is the boundary of the verified conjecture in rank two, and it is the one place where the published classification rests on a search that this campaign has not replayed. If all 14 undecided presentations turn out to be in the AK(3) class, the published theorem is confirmed inside our own computations. If one of them is not in the class and presents the trivial group, then either the theorem or its reading is wrong.

**What is known.** Round 2 certified 6 length-13 presentations as AC-equivalent to AK(3) with explicit certificates, and left 14 with weaker bounds (8 exhausted at cap 17 and 6 stopped by a budget at cap 19). The census of the AK(3) class inside total length 20 contains exactly two Panteleev-Ushakov classes of minimal total length 13, the second reached in 36 moves, and I reproduced that count. The census also pins the bottleneck of the second class: at cap 16 the box contains one class of minimal total length 13, and at cap 17 it contains two, so the least total length of an intermediate tuple on a path to the second class is exactly 17. `shortest_two.cert` holds the two certificates and replays.

**Rating.** A. The 79,680-class census with certificates is a complete list to test against, and an intersection gives an AK(3)-equivalence certificate for each resister.

**Status.** OPEN. Round 3's direction F4 has the meet-in-the-middle attack.

#### Q22. What group do the four length-14 presentations with a $\mathrm{PSL}(2,7)$ quotient present?

**Question.** Determine the groups presented by the four canonical length-14 presentations `BAABa,BBBBBBAbA`, `BABaa,BBBBBBaba`, `BBAbA,BAAAAAABa` and `BBaba,BABaaaaaa`, where an upper case letter is the inverse of the lower case generator.

**Why it matters.** These are the only presentations at the length-14 frontier that are known to be nontrivial without a finite quotient that decides their order, and they are the reason the length-14 classification does not close. A decision would say whether the length-14 census meets its first infinite group or only another finite one.

**What is known.** Each of the four has exponent-sum determinant $\pm 1$ and a surjective homomorphism onto $\mathrm{PSL}(2,7)$. I checked the latter by brute force over the 168 elements of $\mathrm{GL}(3,2)$: for each presentation there are 337 pairs of images that satisfy both relators. GAP 4.14, asked for the index of the trivial subgroup, exceeded 4,096,000 cosets on the first of the four, so the order is undetermined and a fast Todd-Coxeter run does not close. The round-2 report says that all 38 nontrivial presentations present a group of order 120, which is right for the 34 with an $A_5$ quotient and unsupported for these four; that is a documentation slip found during this update. The package kbmag, which would decide the question through a confluent rewriting system, is not installed on this VM.

**Rating.** B. A coset enumeration with a larger limit, a Knuth-Bendix completion, or a low-index subgroup analysis would settle each case.

**Status.** OPEN.

#### Q23. Do the two published stabilization moves generate the same equivalence relation?

**Question.** Are the following two relations on finite presentations the same? The first is generated by the AC moves together with the move that adds a new free generator, with no relator, and its inverse. The second is generated by the AC moves together with the move that adds a new generator together with the relator equal to it, and its inverse.

**Why it matters.** Both relations are called "stably AC-equivalent" in the literature, and the topological reading depends on which one is meant. The first changes the deficiency, and it is the move that the topological treatments of stabilization use. The second preserves balance, and it is prolongation, which is part of Q**-equivalence and is the relation that corresponds to 3-deformation of standard complexes. A theorem stated for one move set transfers to the other only if the relations coincide.

**What is known.** Neither source proves that the relations coincide. Miller, Myasnikov and Shpilrain define the stable moves as (AC1) to (AC3) together with (AC4), "Y is extended to $\{y_1,\dots,y_m,x_\nu\}$, where $x_\nu$ is a new free generator", and (AC5), the converse. Shehper and coauthors define (AC4) as adding a generator together with the trivial relator, and (AC5) as the inverse move. The quotations and their locations are recorded in `survey/stable-ak3-status.md`, and the second move is prolongation in the sense of Hog-Angeloni and Metzler (28) and of Barmak's (v) and (vi). The first move takes a balanced presentation out of the balanced presentations, while the second keeps it balanced, so the comparison has to be made on all presentations or after a bookkeeping of the deficiency.

**Rating.** A. The question is a simulation problem with explicit moves, and a Lean proof of an implication between the two relations is a realistic target.

**Status.** OPEN. Round 3's direction F2 is the attempt.

#### Q24. Are the 164 resisting length-13 and length-14 presentations AC-trivial?

**Question.** Decide AC-triviality, or AC-equivalence to $\mathrm{AK}(3)$, for the 164 presentations that the round-2 classification left undecided.

**Why it matters.** These are the only undecided presentations at total relator length at most 14, and both Q2 and Q15 reduce to them. A positive answer for all of them finishes the classification to length 14. A negative answer would be a counterexample to the conjecture if the presentation presents the trivial group, which the round-2 Todd-Coxeter runs indicate but do not prove.

**What is known.** Of the 164, 34 are exhausted at cap 17, 40 at cap 18 and 68 at cap 19, and 22 were stopped by a budget of 400,000 pairs at cap 19. The replay recorded in section 4.1 item 11 leaves 161 undecided: one presentation, $\mathrm{MS}(3,yx^2y)$, is certified AC-equivalent to AK(3) by 71 moves, and two pairs are certified AC-equivalent to each other, namely the Solitar candidate with $\mathrm{MS}(2,yx^2y^{-1}x^{-2})$ and $\mathrm{MS}(2,yx^2yx^{-2})$ with $\mathrm{MS}(2,x^{-2}y^{-1}x^2y^{-1})$. Nine of the length-13 resisters carry weaker bounds than the published record, which reduces all but twelve of the 1,400 length-13 presentations once a single relator may grow to length 18. The AK(3) class census gives 79,680 classes with certificates as a meet-in-the-middle target, so an intersection certifies AK(3)-equivalence, and the ball of the standard presentation at cap 14 gives the other target.

**Rating.** A. The certificates exist and only a larger search or an intersection is missing.

**Status.** OPEN, with exact bounds. Round 3's direction F4.

#### Q25. What explains the Panteleev-Ushakov table gap?

**Question.** Are the cumulative class counts of Panteleev and Ushakov at total length 13 to 20 the same quantity as ours under a different normal form, or do their extra members need longer intermediate tuples?

**Why it matters.** If the two relations coincide, their table is a stronger statement about the AK(3) class than our box can give, and the conditional deduction is that at least two of their four length-13 members need intermediates of total length greater than 20. If the relations differ, then the normal form they count is not the AC class, and a comparison of search records between the two implementations has to say so.

**What is known.** Our cumulative counts at caps 13 to 20 are 2, 7, 42, 82, 288, 534, 1,743 and 2,967, and their table reads 4, 10, 70, 86, 458, 590, 3,226 and 3,356. I reproduced our counts at caps 16, 17 and 18 from the shipped enumerator and recomputed the cap-20 quotient from the shipped class list: 79,680 classes into 2,967 classes, with the per-length row 2, 5, 35, 40, 206, 246, 1,209, 1,224. Our own data show that the count at a fixed length depends on the cap, since the number of classes of minimal total length 13 is one at cap 16 and two at cap 17. The three candidate explanations in the round-2 report are a larger intermediate cap in their search (their parameter gives $2L+2 = 36$), the ACM moves they use, and a different normal form.

**Rating.** B. One side can reimplement the other's normal form, and the reimplementation is a finite and well-defined task.

**Status.** OPEN. Round 3's direction F3.

#### Q26. Which verification items do rounds 1 and 2 leave open?

**Question.** Six claims in the repository are relied on without a replayed check. Are they true? They are the general step (D) pruning, the printed proof of the middle ladder step, the Carreras certificates, the 1190 count, the Gilman and Myasnikov sentence, and the Panteleev-Ushakov normal form.

**Why it matters.** Each one is a place where the campaign's record rests on a quotation or on a search it did not replay, and each one has a definite check. A question list that does not say which claims are unchecked invites the reader to treat them as settled.

**What is known.** (a) The step (D) discards are all AC-trivial at length 13 and at length 14, 592 and 648 of them, and the general statement is open. (b) The printed proof of the middle ladder step of Shehper and coauthors reasons at the level of consequences, and the statement is certified for $n = 3, 4, 5$ and open above. (c) Carreras's five certificates of 13, 36, 66, 71 and 85 moves replay under an independent verifier written for this update (section 4.1 item 11), so the certificates are verified; his minimax and Table-2 analyses were not replayed, and the claim of a bottleneck of exactly 19 for $\mathrm{MS}(3,yx^2y)$ is consistent with the round-2 cap-18 exhaustion. (d) The count of 1190 Miller-Schupp presentations was not reproduced. (e) The abstract of arXiv:2506.23031v2 does not contain the sentence that the round-2 draft attributes to Gilman and Myasnikov. (f) The Panteleev-Ushakov normal form is tested in the repository only by its own invariance self-test, which reports 0 failures on a sample of 150 classes.

**Rating.** A for (a), and B for the rest.

**Status.** SETTLED for (c) and OPEN for the other items.

#### Q27. Is $\mathrm{AK}(3)$ stably AC-trivial?

**Question.** Is $\mathrm{AK}(3)$ equivalent to the standard presentation under the AC moves together with stabilization, in either of the two senses of Q23?

**Why it matters.** This is the smallest case of the stable conjecture in rank two, and a positive answer would remove AK(3) from the stable problem. It is also the case where the published record is clearest, so reading it correctly is a test of how the literature is used.

**What is known.** The claim was made in Shehper et al. version 1 of 27 August 2024 and rested on a presentation P of Myasnikov, Myasnikov and Shpilrain 2002. The authors found a misprint in the 2002 paper, one wrong letter in the 13th relator of the 14-generator Wirtinger presentation, and version 2 of 11 February 2025 withdraws the claim. Lisitsa's arXiv version of January 2025 repeats the claim on the same source, and the published version, Journal of Computational Algebra 16 (2025) 100041, says that the status of AK(3) remains unresolved; I verified that identifier live during this update. The leg from P to AK(3) is a 53-move sequence that replays, and the missing leg is the one the misprint destroyed.

**Rating.** C. No technique in the record gives either answer.

**Status.** OPEN, and the status is definitively unresolved: no proof and no disproof exists, and the only published claim was withdrawn by its authors on 11 February 2025.

## 3. Summary

### 3.1 Status table at the round-3 update

The table below replaces the round-1 rating table. The rating column gives the assessment of a three-day effort that the question carried in round 1, updated where rounds 1 and 2 changed it. The status column gives what is known as a matter of record, and the commands behind it are in section 4.

| id | question, shortened | status after rounds 1 and 2 | rating now |
| --- | --- | --- | --- |
| Q1 | is $\mathrm{AK}(3)$ AC-trivial | OPEN, with bounded negatives to total length 20 | C |
| Q2 | classify the length-14 presentations | SETTLED except 161 resisters | A |
| Q3 | is $\mathrm{AK}(3)\sim\mathrm{AK}(4)$ | OPEN, both rungs have shorter certified forms | C |
| Q4 | recalcitrance of $\mathrm{AK}(3)$ | OPEN, untouched | C |
| Q5 | optimality of the length reduction | PARTLY, the constructive half certified for $n\le 5$ | C |
| Q6 | every $\mathrm{MS}(n,w)$ AC-trivial | OPEN, three infinite subfamilies known | D |
| Q7 | $\mathrm{MS}(3,w)$ with $\lvert w\rvert\le 7$ | OPEN, the length-14 slice classified | B |
| Q8 | every $\mathrm{MS}(n,w)\sim\mathrm{AK}(n)$ | $k=1$ SETTLED, general OPEN | C |
| Q9 | Quinn's triangular Hopf algebra | ANSWERED in part, $\mathbb{F}_3$ and $\mathbb{Z}[i]$ open | B |
| Q10 | non-2-deformable simple equivalences | OPEN, reduced to an exact target, no pair known | D |
| Q11 | M-transformations versus AC moves | OPEN, untouched | C |
| Q12 | triviality for balanced presentations | OPEN, untouched | D |
| Q13 | decidability of AC-equivalence in $F_2$ | OPEN, decided inside explicit boxes | D |
| Q14 | superexponential bounds in rank 2 | OPEN, untouched | D |
| Q15 | growth of $c(L)$ | SETTLED to $L=12$, bounded at 13 and 14 | B |
| Q16 | links $L(3,2;4/d)$ | OPEN, untouched | D |
| Q17 | a standard trisection implies AC-triviality | OPEN, untouched | C |
| Q18 | diameter of finite-group AC graphs | OPEN, component census only | B |
| Q19 | Lean formalisation | SETTLED for the named lemmas and for $\mathrm{AK}(n)$ triviality | A |
| Q20 | a validated hardness measure | OPEN, the data now exist | B |
| Q21 | the length-13 members of the AK(3) class | OPEN | A |
| Q22 | the $\mathrm{PSL}(2,7)$ frontier group | OPEN | B |
| Q23 | the two stabilization move sets | OPEN | A |
| Q24 | the 164 resisters | OPEN, 161 remain, with exact bounds | A |
| Q25 | the Panteleev-Ushakov table gap | OPEN | B |
| Q26 | verification items left open | SETTLED for (c), OPEN for the rest | A for (a), B for the rest |
| Q27 | is $\mathrm{AK}(3)$ stably AC-trivial | OPEN, and definitively unresolved | C |

The computations with a definite success criterion and no dependence on the truth of the conjecture are Q2, Q7, Q15, Q18, Q20, Q21, Q22, Q24 and Q25, and the main part of Q2 is already carried to a verified conclusion. Q19's original target is met. Q23 is a simulation problem with explicit moves. The rest are open-ended, and the rating reflects that. The status column of the table distinguishes what was checked from what was reported, and the commands are in section 4.

## 4. What I checked computationally

I wrote a Todd-Coxeter coset enumeration over the subgroup generated by $y$. If the index $[G:\langle y\rangle]$ is 1 then $G$ is cyclic. For $\mathrm{AK}(n)$ the exponent sums of the two relators are $(1,-1)$ and $(n,-(n+1))$, and the determinant of that matrix is $-1$, so the abelianisation is trivial. A cyclic group with trivial abelianisation is trivial.

The enumeration is validated on fourteen cases with independently known orders and subgroup indices: cyclic groups with three subgroup choices, $S_3$ with four subgroup choices, $A_4$ with two, $A_5$ with three, and $Q_8$ with two. It is also tested against the infinite group $\langle x,y\mid xyx=yxy\rangle$, where it must fail to close rather than return a spurious index 1. The results:

```
PASS <x,y|xyx=yxy>: [G:<y>] is infinite, as expected (no spurious collapse)
PASS AK(1): abelianization trivial, [G:<y>]=1, [G:<x>]=1 => G is cyclic, hence trivial
PASS AK(2): abelianization trivial, [G:<y>]=1, [G:<x>]=1 => G is cyclic, hence trivial
PASS AK(3): abelianization trivial, [G:<y>]=1, [G:<x>]=1 => G is cyclic, hence trivial
PASS AK(4): abelianization trivial, [G:<y>]=1, [G:<x>]=1 => G is cyclic, hence trivial
PASS AK(5): abelianization trivial, [G:<y>]=1, [G:<x>]=1 => G is cyclic, hence trivial
PASS MS(1,y): abelianization trivial, [G:<y>]=1 => trivial
PASS MS(1,y^-1x^-1yx): abelianization trivial, [G:<y>]=1 => trivial
PASS MS(2,y^-1x^-1yxy): abelianization trivial, [G:<y>]=1 => trivial
```

The exact command, run from the repository root, is the following.

```
cd checks && python3 todd_coxeter.py && python3 ak_check.py
```

The first command prints the fourteen validation lines. The second prints the nine lines above. Both scripts are in `checks/` at the repository root. They use only the Python standard library and run in under a second.

This is a computation, not a formal proof. The enumeration is my own code, and the argument that its merges are justified is the standard Todd-Coxeter argument together with the validation suite. Anyone reusing the result should treat it as a checked computation and should prefer the citation [4] for the triviality of $\mathrm{AK}(3)$ where a citation will do.

### 4.1 Reruns made during the round-3 update

Every command below was run from the repository root on 2026-11-04, and the key line of output is quoted. These reruns check the round-1 and round-2 artifacts that the status blocks rely on.

1. The Lean files compile, and their theorems use only standard axioms. `lean toolkit/lean/AC.lean` (2.6 s), `lean toolkit/lean/AC2.lean` (3.3 s) and `lean directions/ak-status/ak_trivial.lean` (2.4 s) print only standard axioms. For AC.lean the 41 axiom prints fall into three groups: 6 theorems use `[propext, Classical.choice, Quot.sound]`, 32 use `[propext, Quot.sound]` and 3 use `[propext]`. AC2.lean reports 46 prints, 29 with the three and 17 with two, and ak_trivial.lean reports 11, all with the three.
2. The triviality battery passes. `cd checks && python3 todd_coxeter.py && python3 ak_check.py` prints fourteen PASS validation lines and nine PASS lines for $\mathrm{AK}(1)$ to $\mathrm{AK}(5)$ and three Miller-Schupp presentations.
3. The census at total relator length at most 11 reproduces. `cd survey/computational && python3 census.py 11 13 DIR/certs.txt` writes 3,697 certificates and ends with `PASS every canonical presentation at total length <= 11 is resolved`, and it reproduces the published level counts 1, 12, 101, 782, 5906, 44048 and 326200. `python3 check_certs.py DIR/certs.txt` prints 3,697 certificates, 0 failed, longest 37 moves. The run took 18.5 minutes and 2.8 GB.
4. The AK-ladder draft passes. `cd directions/ak-ladder && python3 test_acx.py` prints `AK(n) strict local minima for n=1..40, conjugators up to length 4: PASS`, and `python3 verify_cert.py` prints `42 certificate files, 0 failed` with both arithmetics passing on every file. `python3 patterns.py` prints `total: PASS` for the two templates over $n = 3$ to 30.
5. The length-14 classification replays. `cd directions/c14 && python3 replay14.py certs_all.txt` prints `replayed 53866 certificates, 0 failed, longest 141 moves` in 1.1 s. The label counts in `final_classes.txt` are 53,840 ac-trivial, 26 ak3-equivalent, 34 nontrivial-quotient-A5, 4 nontrivial-quotient-PSL27, 34 resisting-exhausted-cap17, 40 resisting-exhausted-cap18, 68 resisting-exhausted-cap19 and 22 resisting-budget-cap19, over 54,068 rows.
6. The AK(3) class census reproduces. `gcc -O2 -o rawbox rawbox.c`, then, with `DIR` a writable directory, `./rawbox 16 1 -l DIR/cls16.txt` gives 20,560 states and 80 classes, `./rawbox 17 1 -l DIR/cls17.txt` gives 857,808 states and 2,000 classes, and `./rawbox 18 1 -l DIR/cls18.txt` gives 2,014,992 states and 4,256 classes. `python3 puclass2.py DIR/cls16.txt`, and the same for 17 and 18, give 11, 168 and 299 classes, with the cumulative rows 1, 3, 9, 11 and 2, 7, 37, 69, 168 and 2, 7, 38, 71, 203, 299. The shipped cap-20 class list has 79,680 rows, and `python3 puclass2.py` on it gives 2,967 classes with the per-length row 2, 5, 35, 40, 206, 246, 1,209, 1,224 in 21 minutes. `python3 replay_certs.py cert16all.txt` gives 20,560 certificates, 0 failed, 388,717 moves, and `python3 replay_certs.py shortest_two.cert` gives 2 certificates, 0 failed.
7. The MS to AK certificates replay. `cd directions/ms-ak-certs && bash run_all.sh` replays all eighteen certificates through five implementations, prints `sympy replay: ALL OK`, and prints eleven `does not depend on any axioms` lines from the Lean kernel.
8. The invariant checks pass. `cd directions/invariant-ideas && python3 check_idea.py` prints `ALL CHECKS PASSED` over 34 checks, `python3 survey/q-transformations-check.py` prints `ALL 8 CHECKS PASSED`, `python3 survey/special-classes-check.py` prints `ALL CHECKS PASSED`, `python3 survey/quinn_check.py` prints the list of characteristics in which some listed set satisfies conditions (1) to (4) as `[5, 7, 11, 13]`, and `python3 toolkit/test_toolkit.py` prints `144 passed, 0 failed`.
9. The four length-14 presentations with a $\mathrm{PSL}(2,7)$ quotient have a witness. A brute-force search over the 168 elements of $\mathrm{GL}(3,2)$ finds 337 pairs of images satisfying both relators for each of the four presentations listed in Q22, so each has a surjection onto $\mathrm{PSL}(2,7)$. GAP 4.14, asked through `Index(G, TrivialSubgroup(G))` for the order of the first of the four, exceeded 4,096,000 cosets.
10. The new identifiers were checked live through the arXiv API and through Crossref, as recorded in section 6.
11. Five external certificates were replayed. The five files `certs/cert_ms3_yinvx2yinv_equiv_ak3.json`, `certs/cert_ms3_yx2y_equiv_ak3.json`, `certs/bottleneck_ak_f3_cert.json`, `certs/cert_sym_equiv_orphan1.json` and `certs/cert_idx0_equiv_mirror.json` of the artifact attached to arXiv:2607.23611 were downloaded from the repository named in that paper's comment. The verifier is `work/replay_carreras.py`, written for this update from the JSON format alone and sharing no code with the artifact; it replays the moves with its own free reduction and requires the terminal tuple to equal the declared reached tuple and to lie in the orbit of the target under relator swap, inversion and rotation. `python3 .ultramath/smw2opo0o/m8/work/replay_carreras.py DIR/*.json` prints five PASS lines (13, 71, 66, 36 and 85 moves) and `failed: 0 of 5`, and three deliberately corrupted copies of the 13-move certificate all FAIL, so the verifier rejects bad input. Matching the endpoints against `directions/c14/final_classes.txt` gives these identifications. The 71-move certificate connects `BAABa,BBBBAbbba`, which is $\mathrm{MS}(3,yx^2y)$ and was labelled resisting-exhausted-cap18, to the canonical AK(3) pair `BABaba,BBBBaaa`, so that resister is settled in favour of AK(3). The 36-move certificate starts at Solitar's candidate $\langle x,y\mid x^{-1}y^2x=y^3,\ y^{-1}x^2y=x^3\rangle$, whose relator pair matches the row `BBBAbba,BAAbaaa` up to rotation and inversion, and ends at `BBBAbba,BAAAbaa`, and the 85-move certificate connects `BBBAbba,BAABaaa` to `BBBAbba,BAAABaa`, so two pairs of resisters merge. The 13-move certificate is a shorter certificate for the equivalence of `BABaa,BBBBAbbba` to AK(3), which round 2 already had in 34 moves. The counting consequence is stated in Q2, Q15 and Q24. The artifact also ships a 3.7-million-move reduction ledger, which was not replayed.

## 5. What I could not verify

The four paragraphs below are the round-1 text, and two of them are now out of date. The general triviality of $\mathrm{AK}(n)$ is settled in section 1, and a formalisation exists as recorded in Q19. They are kept as the round-1 record, and section 5.1 gives the limits of this update.

I did not find a printed proof that $\mathrm{AK}(n)$ presents the trivial group for all $n$. I verified the statement for $n\le5$ and every source I checked treats it as known. This should be settled by a citation before anyone relies on the general statement.

I did not verify the current status of Quinn's question (Q9) beyond checking that it is posed in [11]. Absence of a resolution in the sources I read is not evidence that none exists.

I did not verify that the generalised Andrews-Curtis statement in Q10 is still open. Quinn writes in [12] that no one expects it to hold, which suggests that a counterexample may be expected rather than known.

I did not check for formalisations of the conjecture in proof assistants beyond a search of the sources listed in Section 6. The claim in Q19 that no formalisation is known is therefore a statement about the sources I searched.

### 5.1 Limits of this update

1. I did not replay the 79,680 cap-20 certificates. I recomputed the cap-20 class quotient from the shipped class list, which checks the class count and not the individual certificates, and the shipped cap-16 file of 20,560 certificates does replay.
2. I did not rerun the cap-19 or cap-20 enumerations themselves. Caps 16, 17 and 18 were rerun from the shipped C source with exact agreement.
3. I did not verify the Panteleev-Ushakov normal form independently. The count 2,967 is reproducible, and the only test of the normal form in the repository is its own invariance self-test, which reports 0 failures on a sample of 150 classes.
4. I did not decide the order of the four groups in Q22, and I did not verify that they are infinite. The group has $\mathrm{PSL}(2,7)$ as a quotient and its order is undetermined.
5. I did not read the paper of Havas and Ramsay, so their length-13 theorem is REPORTED here, with the round-1 and round-2 records as support.
6. I did not read the proofs of Fernandez, of Etingof, Nikshych and Ostrik, of Khovanov, Krushkal and Nicholson, or of Evans. Their statements are quoted through the repository's surveys, and the identifiers were checked live where section 6 says so.
7. I replayed Carreras's five small certificates (section 4.1 item 11) and I did not replay his minimax or Table-2 analyses, nor Lisitsa's derivations.
8. I did not verify the sentence that round 2 attributed to Gilman and Myasnikov. The abstract of arXiv:2506.23031v2 does not contain it.

## 6. Sources

Bibliographic details below were checked against a publisher page or an arXiv abstract page, as noted in each entry. Where I could not reach the original I say so in the entry.

1. J. J. Andrews and M. L. Curtis, Free groups and handlebodies, Proc. Amer. Math. Soc. 16 (1965), 192-195. DOI 10.1090/S0002-9939-1965-0173241-8.
2. S. Akbulut and R. Kirby, A potential smooth counterexample in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the Andrews-Curtis conjecture, Topology 24 (1985), 375-390. DOI 10.1016/0040-9383(85)90010-2.
3. C. F. Miller III and P. E. Schupp, Some presentations of the trivial group, in Groups, Languages and Geometry (ed. R. H. Gilman), Contemp. Math. 250, Amer. Math. Soc. 1999, 113-115. DOI 10.1090/conm/250/03848.
4. G. Havas and C. Ramsay, Breadth-first search and the Andrews-Curtis conjecture, Internat. J. Algebra Comput. 13 (2003), 61-68. DOI 10.1142/S0218196703001365. The theorem quoted in Q1 and Q2 is in their Section 4; I read the authors' PDF.
5. A. D. Miasnikov, Genetic algorithms and the Andrews-Curtis conjecture, Internat. J. Algebra Comput. 9 (1999), 671-686. DOI 10.1142/S0218196799000370.
6. A. D. Miasnikov and A. G. Myasnikov, Balanced presentations of the trivial group on two generators and the Andrews-Curtis conjecture, in Groups and Computation III (eds. W. M. Kantor and A. Seress), Ohio State Math. Res. Inst. Publ. 8, de Gruyter 2001, 257-263. I take the bibliographic data from the reference list of [4].
7. M. R. Bridson, The complexity of balanced presentations and the Andrews-Curtis conjecture, arXiv:1504.04187 (2015).
8. B. Lishak, Balanced finite presentations of the trivial group, J. Topol. Anal. 9 (2017); arXiv:1504.00418. DOI 10.1142/S1793525317500182.
9. A. V. Borovik, A. Lubotzky and A. Myasnikov, The finitary Andrews-Curtis conjecture, in Progress in Math. 248, Birkhauser 2005, 15-30. DOI 10.1007/3-7643-7447-0_2; arXiv:1103.1295.
10. P. Wright, Group presentations and formal deformations, Trans. Amer. Math. Soc. 208 (1975), 161-169. DOI 10.1090/S0002-9947-1975-0380813-5.
11. F. Quinn, Representation theory, topological field theory, and the Andrews-Curtis conjecture, arXiv:hep-th/9202044 (1992).
12. F. Quinn, Dual decompositions of 4-manifolds, Trans. Amer. Math. Soc. DOI 10.1090/S0002-9947-01-02940-3. I read the publisher's abstract page and the quoted passage on 2-deformations; I did not check volume and page numbers.
13. R. E. Gompf, Killing the Akbulut-Kirby 4-sphere, with relevance to the Andrews-Curtis and Schoenflies problems, Topology 30 (1991), 97-115. DOI 10.1016/0040-9383(91)90036-4.
14. D. Panteleev and A. Ushakov, Conjugacy search problem and the Andrews-Curtis conjecture, Groups Complexity Cryptology 11 (2019), 43-60. DOI 10.1515/gcc-2019-2005.
15. R. S. Bowman and S. B. McCaul, Fast searching for Andrews-Curtis trivializations, Experiment. Math. 15 (2006), 193-197. DOI 10.1080/10586458.2006.10128962.
16. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu, P. Kucharski, Z. Wang and S. Gukov, What makes math problems hard for reinforcement learning: a case study, arXiv:2408.15332 (v1 August 2024, v2 February 2025). Preprint; I did not check whether it has been refereed.
17. E. Romary and A. Zupan, A family of Andrews-Curtis trivializations via 4-manifold trisections, arXiv:2304.03196 (2023); Geometriae Dedicata (2024). I checked the arXiv abstract and the introduction.
18. A. Lisitsa, The Andrews-Curtis conjecture, term rewriting and first-order proofs, ICMS 2018, Lecture Notes in Comput. Sci. 10931, Springer 2018, 343-351. DOI 10.1007/978-3-319-96418-8_41.
19. R. G. Burns and O. Macedonska, Balanced presentations of the trivial group, Bull. London Math. Soc. 25 (1993), 513-526. I take the bibliographic data from the reference list of [4].
20. R. G. Burns, W. N. Herfort, S.-M. Kam, O. Macedonska and P. A. Zalesskii, Recalcitrance in groups, Bull. Austral. Math. Soc. 60 (1999), 245-251. I take the bibliographic data from the reference list of [4]; I did not read the paper.
21. E. C. Zeeman, On the dunce hat, Topology 2 (1963), 341-358. DOI 10.1016/0040-9383(63)90014-4.
22. C. Hog-Angeloni, W. Metzler and A. J. Sieradski (eds.), Two-Dimensional Homotopy and Combinatorial Group Theory, London Math. Soc. Lecture Note Ser. 197, Cambridge Univ. Press 1993. The chapter by Hog-Angeloni and Metzler, The Andrews-Curtis conjecture and its generalizations, is pages 365-380, DOI 10.1017/CBO9780511629358.014.
23. S. Matveev and D. Rolfsen, Zeeman's collapsing conjecture, in [22], pages 335-364.
24. A. Myasnikov, A. Myasnikov and V. Shpilrain, On the Andrews-Curtis equivalence, Contemp. Math. 296 (2002). I take the bibliographic data from the reference list of [16]; I did not read the paper.
25. A. Lisitsa, New Andrews-Curtis trivializations for Miller-Schupp group presentations, Examples and Counterexamples 6 (2024). NOT VERIFIED: I know this only from the bibliography of [16] and could not confirm the volume, pages or DOI.
26. I. Pak, What do we know about the product replacement algorithm?, in Groups and Computation (de Gruyter 2001), DOI 10.1515/9783110872743.301. Cited in Q18 for the comparison with the product replacement graph.

27. J. A. Barmak, *An exotic presentation of $\mathbb{Z}\times\mathbb{Z}$ and the Andrews-Curtis conjecture*, Algebr. Geom. Topol. 25 (2025), no. 1, 345-355, DOI 10.2140/agt.2025.25.345. Identifier checked live through Crossref during this update.
28. X. Fernandez, *Morse theory for group presentations*, Trans. Amer. Math. Soc. 377 (2024), 2495-2523, DOI 10.1090/tran/8958, arXiv:1912.00115v3. Identifier checked live through the arXiv API during this update.
29. P. Etingof, D. Nikshych and V. Ostrik, *On fusion categories*, Ann. of Math. (2) 162 (2005), no. 2, 581-642, DOI 10.4007/annals.2005.162.581, arXiv:math/0203060v11. Identifier checked live during this update; Theorem 2.3 is quoted from `survey/quinn-tqft.md`, where the arXiv text was read.
30. M. Khovanov, V. Krushkal and J. Nicholson, *On the universal pairing for 2-complexes*, Bull. Lond. Math. Soc. 57 (2025), no. 9, 2838-2853, DOI 10.1112/blms.70130, arXiv:2312.07429v2. Identifier and abstract checked live during this update.
31. A. Lisitsa, *Stable Andrews-Curtis trivialization of AK(3) revisited. A case study using automated deduction*, J. Comput. Algebra 16 (2025), article 100041, DOI 10.1016/j.jaca.2025.100041. Checked live through Crossref during this update (online 15 October 2025, issue of December 2025).
32. J. Carreras, *Machine-checkable equivalence certificates at the length-14 Andrews-Curtis frontier*, arXiv:2607.23611v1 (26 July 2026). Identifier and abstract checked live during this update, and five of the certificates were replayed under an independent verifier (section 4.1 item 11).
33. R. H. Gilman and A. G. Myasnikov, *Andrews-Curtis groups*, arXiv:2506.23031v2, journal of Groups, Complexity, Cryptology 16 (2025), DOI 10.46298/jgcc.2025..15972. Identifier and abstract checked live during this update. The abstract does not contain the sentence that the round-2 draft attributes to this paper.
34. V. Ostrik, *On symmetric fusion categories in positive characteristic*, Selecta Math. (N.S.) 26 (2020), no. 3, Paper No. 36, DOI 10.1007/s00029-020-00567-5, arXiv:1503.01492. Quoted from `survey/quinn-tqft.md` and not verified live during this update.

Two entries were flagged as not fully verified in round 1, and both improved during this update. Entry [24] is now verified through Crossref: Contemporary Mathematics 296 (2002), pages 183-198, DOI 10.1090/conm/296/05074, with the three authors recorded there. Entry [25] appears in the Crossref reference list of [31] as Lisitsa, *New Andrews-Curtis trivializations for Miller-Schupp group presentations*, Examples and Counterexamples 6 (2024); the volume agrees, and the pages and DOI were not checked. Entries 27 to 34 were added during this update, and the three marked in their entry were verified live through the arXiv API or through Crossref.

The identifiers of entries 1, 2, 3, 5, 7 to 14, 16 to 18 and 21 to 23 were checked live in round 1 by `python3 survey/check_refs.py`, which reports 33 DOI checks and 13 arXiv checks with 0 unmatched. That run is the round-1 record, and this update did not repeat it.
