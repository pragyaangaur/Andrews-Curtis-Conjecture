# Stable AC-triviality of AK(3): the status after the 2002 misprint

Direction E1 (stable-ak3-referee), member m1 of swarm smw2i9i4j, Round 2. Written 2026-11-04.

This is a referee report. It settles what the misprint in Myasnikov, Myasnikov and Shpilrain (MMS) 2002 is, what it undermines, the chronology of the withdrawal, and the current status of the stable AC-triviality of AK(3). It proves nothing about the Andrews-Curtis conjecture and it attaches no verdict to AK(3) beyond what the sources and my own checks support.

Labels used below. `[V]` marks a statement checked by me with the exact command given, and the output is quoted. `[L]` marks a statement read in the source named. `[A]` marks my own argument, written out so that a reader can check it. `[O]` marks a question on which I found no proof and no disproof. `[U]` marks a statement I could not verify.

## 1. Verdict

The stable AC-triviality of AK(3) is unresolved `[O]`. The claim that AK(3) is stably AC-trivial was made in version 1 of arXiv:2408.15332 (submitted 27 August 2024) and withdrawn in version 2 of the same preprint (11 February 2025), where the authors write that the misprint "undermines the claim" `[L: arXiv:2408.15332v2, sec/introduction.tex, line 91]`. The January 2025 paper arXiv:2501.18601 (Lisitsa) which presents an "alternative proof" of the same statement depends on the same 2002 source, so it is not independent evidence; its published version states that the earlier claim "was based on an incorrect theorem, and thus the status of AK(3) remains unresolved" `[L: Journal of Computational Algebra 16 (2025) 100041, published abstract, DOI 10.1016/j.jaca.2025.100041]`. Neither paper contains a stable AC-trivialization of AK(3), and no later paper or preprint that I found supplies one `[O]`.

[Coordinator note, 6 November 2026, from the round-6 citation audit (.ultramath/smw3ow2dp/m3/audit.md,
C12), confirmed by my own fetches: the quoted concession in the published abstract is NOT reproducible
from open sources as of 5-6 November 2026. The arXiv abstract of 2501.18601 (v1, the only version) still
asserts the stable triviality of AK(3) verbatim; the DOI resolves but the publisher's article page is not
retrievable by automated access (a challenge page), and Crossref returns the record without an abstract.
The round-1 reading of the published abstract stands as recorded but can no longer be checked; the
headline conclusion of this file does not depend on it, resting on the Shehper v2 withdrawal, which the
audit re-verified. Any final report should cite the v2 withdrawal and either attach an archived page
reference for the published abstract or drop the clause.]

The ordinary (non-stable) AC-equivalence of the specific presentation P (total relator length 25) with AK(3) is separately verified. I replayed the 53-move sequence of Shehper et al. and it carries P exactly to the AK(3) relator pair, using only the moves AC1 to AC3 `[V]`. That leg of the withdrawn argument therefore stands. The leg that fails is the stable one.

## 2. The misprint, exactly

### 2.1 Where it is

The source is A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, "On the Andrews-Curtis equivalence", Contemporary Mathematics 296 (2002) 183-198, DOI 10.1090/conm/296/05074. I read the article in two forms: the author's LaTeX source posted as arXiv:math/0302080 (file `ac.tex`, 1157 lines), and Shpilrain's posted PDF of the same article at `https://shpilrain.ccny.cuny.edu/ac.pdf` (16 pages, page numbers 1 to 16 in the article's own pagination, which matches the volume's 16 pages from 183 to 198). Both carry the misprint. The PDF is the author's posted copy of the article, and its page 10 is the page cited by Shehper et al. as `[MMS, p.10]`; in the volume pagination that page is 192 `[L, V by page check]`. The text layer of the PDF drops superscript minus signs, so the LaTeX source is the reliable place to read the exponents.

The authors prove their Theorem 1.4 from a 14-crossing diagram of the unknot, and their proof begins (verbatim from `ac.tex`, lines 778 to 789):

> The corresponding Wirtinger presentation is
> $\langle x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8,$
> $x_9, x_{10}, x_{11}, x_{12}, x_{13}, x_{14} ~| ~x_1 = x_{10}x_{14}x_{10}^{-1},$
> $~x_2=x_{10}^{-1}x_1x_{10}, ~x_3=x_1^{-1}x_2x_1,$
> $x_4=x_6^{-1}x_3 x_6,$
> $~x_5=x_{12}x_4x_{12}^{-1}, ~x_6=x_7^{-1}x_5x_7, ~x_7=x_4^{-1}x_6 x_4,$
> $~x_8=x_1x_7x_1^{-1}, ~x_9=x_{11}^{-1}x_8x_{11}, ~x_{10}=x_{14}x_9x_{14}^{-1},$
> $~x_{11}=x_2^{-1}x_{10}x_2, ~x_{12}=x_1^{-1}x_{11}x_1,$
> $ x_{13}=x_5x_{12}x_5^{-1},$
> $~x_{14}=x_1x_{13}x_1^{-1} \rangle$.

The 13th relator is printed as $x_{13}=x_5x_{12}x_5^{-1}$. According to Shehper et al. it should read $x_{13}=x_4x_{12}x_4^{-1}$, and the difference matters because the two letters name different arcs of the drawn diagram: in a Wirtinger presentation the conjugating letter is the arc that passes over the crossing, and the 13th crossing of the figure has $x_4$ over, not $x_5$ `[L: arXiv:2408.15332v2, app/mms.tex and app/wirtinger.tex]`. I did not reconstruct the figure myself, so the identification of the over-arc rests on Shehper et al. and on the internal consistency check reported in section 2.3 `[U in part]`.

### 2.2 What it breaks in the 2002 paper

MMS obtain their three-generator family by discarding one relator of this presentation and eliminating generators. Their argument then has one sentence that names the group presented by the two surviving relators `[L: ac.tex, lines 395 to 398]`:

> We note that the normal closure of the first two relators contains the commutator subgroup of the ambient free group $F_3$ since the corresponding two-relator group is the fundamental group of the unknot, i.e., is infinite cyclic.

That sentence is the step that converts the abelian computation into a triviality result. It holds only if the input presentation is the Wirtinger presentation of a diagram of the unknot. With the printed 13th relator the input is not that presentation, so the sentence has no support for the printed relation list `[A]`, and Shehper et al. state the consequence as follows `[L: arXiv:2408.15332v2, app/mms.tex]`:

> The theorem statement claimed that every element of this 3-generator family presents the trivial group. However, due to the misprint, $W'$ with the 12th relator eliminated is not a presentation of $\mathbb{Z}$.

The stability claim in MMS lives in a different sentence, in the introduction, about the whole method `[L: ac.tex, lines 379 to 384]`:

> This method can therefore produce numerous potential counterexamples to the Andrews-Curtis conjecture in a free group of any rank $\ge 2$. (Note however that these are {\it not} counterexamples to the {\it weak} Andrews-Curtis conjecture since it is known that Reidemeister moves applied to a knot diagram give stably AC-equivalent Wirtinger presentations of the knot group.)

This sentence is true as a statement about genuine knot diagrams. It does not cover a presentation that is not the Wirtinger presentation of the drawn diagram, which is what the printed relator list gives. The withdrawn claim in Shehper et al. version 1 needs exactly this sentence applied to the printed list, because the presentation P is obtained from it by discarding a relator, adding a word, and eliminating generators. So the misprint removes the only published reason to call P stably AC-trivial `[A]`.

A definitional hazard was recorded here in an earlier version of this paragraph, and it resolves in favour of the sources agreeing. MMS define the stable moves as (AC1) to (AC3) together with (AC4), "Y is extended to {y_1,...,y_m,x_nu}, where x_nu is a new free generator (i.e., y_1,...,y_m do not depend on x_nu)", and (AC5), the converse `[L: ac.tex, lines 142-146]`. Shehper et al. define (AC4) as adding a generator together with the trivial relator, and (AC5) as the inverse move `[L: arXiv:2408.15332v2, sec/stable.tex]`. The two are the same move: in both, a new generator and the relator equal to it enter or leave together, so the deficiency is unchanged by both. That the MMS move deletes the generator is fixed by MMS's own use of it, since the proof of their Theorem 1.4 removes eleven generators from a fourteen-generator presentation "by applying the transformation (AC5)" `[L: ac.tex, lines 793-798, with the generator counts of that proof]`. The earlier reading, which said that the MMS move changes the deficiency, is corrected in survey/stabilization-moves.md section 3, whose four source passages were verified against the arXiv LaTeX by the coordinator. COORDINATOR NOTE, 2026-11-04: this replacement paragraph was applied by the coordinator on the recommendation of the round-3 stabilization-moves direction.

### 2.3 What survives

The items below survive the misprint, and I checked each of them. They are the parts of the 2002 paper that the later argument actually needs.

(a) The exponent-sum computation printed by MMS is correct for the final three-generator presentation they display, and it is the computation that makes their argument plausible. Rebuilding their two final relators from the LaTeX and computing exponent sums gives $(1,0,-1)$ and $(-1,1,0)$, with Smith normal form $(1,1)$, exactly the pair $\{xz^{-1}, x^{-1}y\}$ that they state `[V, section 6, check C2]`.

(b) The particular member of the family with $w=x^{-1}yz$ is the presentation P of total length 25 that Shehper et al. use. I verified the derivation: starting from the three-generator presentation of Theorem 1.4 and substituting $z=y^{-1}x$ from the third relator gives a two-relator presentation of total length 25 whose relators agree with the printed P up to inversion and cyclic shift `[V, section 6, check C3]`. So the printed length count 25 is right and P is the member that the later papers work with.

(c) P presents the trivial group. This follows because P is AC-equivalent to AK(3) `[V, check C1]` and AK(3) presents the trivial group `[L, V elsewhere in this repository: directions/ak-status/ak_trivial.lean proves Subsingleton (PresentedGroup (akRels n)) for every n]`. It is worth keeping the two facts apart: triviality of the presented group is not AC-triviality, and neither is stable AC-triviality.

## 3. The logical chain, and which leg fails

The withdrawn argument has two legs and one conclusion, and the failure of the first leg is what leaves the question open. The list below sets out the two legs and names the evidence offered for each of them.

1. P is stably AC-trivial. The evidence offered was that P is an instance of the family of MMS Theorem 1.4 and that this family comes from a diagram of the unknot, with Reidemeister moves lifting to stable AC moves `[L: arXiv:2408.15332v1, app/stable_ak3.tex]`.
2. P is AC-equivalent to AK(3). The evidence is an explicit sequence of elementary moves from P to the AK(3) relator pair `[L: loc. cit., the 53-move sequence in terms of h_1 to h_12]`.
3. Therefore AK(3) is stably AC-trivial.

Leg 2 is sound and I verified it independently: the 53 moves are legal AC1 to AC3 moves and the final tuple equals $(x^3y^{-4},\,xyxy^{-1}x^{-1}y^{-1})$ exactly, with the total relator length never exceeding 25 `[V, check C1]`. Leg 1 fails with the misprint, and the misprint is in the 2002 source text itself `[A]`. Leg 2 being non-stable is itself acknowledged by the author of the other paper: "in both [Shehper et al.] and this communication, the search conducted to establish the result on stable AC-simplifiability was actually focused on non-stable transformations" `[L: arXiv:2501.18601v1, Conclusion]`.

The second paper's dependence on the first is explicit, and it is the reason its January 2025 statement cannot be counted as independent confirmation `[L: arXiv:2501.18601v1, section 3]`. The paper says so in its own words:

> The presentation $P$ is a particular instance of a family of presentations for which it was shown in [ACE] that they are all stably AC-trivializable. By that stable AC-trivializability of AK(3) followed.

Here `[ACE]` is the MMS 2002 paper, as the bibliography of arXiv:2501.18601v1 records `[L: main_arxiv.bbl, entry ACE]`. Everything that the January 2025 paper adds is a second, independently found reduction from AK(3) to P, which is leg 2 again.

## 4. Chronology

The dates below are from the arXiv abstract pages, the arXiv API, Crossref and OpenAlex, all read on 2026-11-04 `[V]`. Each row gives the event and then the identifier under which it can be checked.

| Date | Event | Identifier |
|---|---|---|
| 2002 | MMS publishes the 14-generator presentation with the misprint, Theorem 1.4, and the weak-conjecture remark | Contemp. Math. 296 (2002) 183-198, DOI 10.1090/conm/296/05074 |
| 2003-02-07 | MMS preprint posted | arXiv:math/0302080 |
| 2024-08-27 18:00:06 UTC | Shehper et al. version 1 posted, with the theorem "AK(3) is stably AC-trivial" | arXiv:2408.15332v1 |
| 2025-01-17 16:35:02 UTC | Lisitsa version 1 posted, calling the result established and offering an "alternative proof" | arXiv:2501.18601v1 |
| 2025-02-11 18:01:40 UTC | Shehper et al. version 2 posted, with the misprint found and the theorem removed | arXiv:2408.15332v2 |
| 2025, 39th conference | NeurIPS proceedings version, revised abstract, no stable section at all | NeurIPS 2025 proceedings, paper `ea8c9cd935dc62e0288bbf33a15e65e9` |
| 2025 (online 2025-10-15, issue December 2025) | Lisitsa's published version, abstract revised to say the status of AK(3) is unresolved | J. Comput. Algebra 16 (2025) 100041, DOI 10.1016/j.jaca.2025.100041 |
| 2025 (Crossref record) | Proceedings volume record for the same paper, pages 177669-177702 | DOI 10.52202/085713-5348 |
| 2026-11-04 | No later proof or disproof found | `[O]` |

Lisitsa's submission of 17 January 2025 precedes the Shehper revision of 11 February 2025 by 25 days `[V]`. The abstract that Lisitsa submitted shows that the correction had not been made public by 17 January 2025. The correction in the published version appeared after, and its wording identifies the 2002 theorem as the failing premise rather than the 2024 reduction `[L]`.

One chronology point needs care, and it corrects a natural reading of the record. The NeurIPS proceedings version of Shehper et al. contains no discussion of the stable conjecture at all. The word "stable" does not occur in the 34-page PDF (the only word beginning with "stab" is "stability", in a reinforcement-learning sentence), the word "misprint" does not occur, and the abstract is the revised one `[V]`. The withdrawn claim therefore exists in the arXiv record of version 1, and the restoration exists in the arXiv record of version 2 and in the two appendices of version 2. The proceedings record neither asserts the withdrawn claim nor withdraws it.

## 5. The statements, verbatim

### 5.1 Shehper et al. version 1, the claim

Abstract `[L: arXiv:2408.15332v1, sec/abstract.tex]`:

> In the process of our study, we demonstrate that one of the potential counterexamples due to Akbulut and Kirby, whose status escaped direct mathematical methods for 39 years, is stably AC-trivial.

Introduction, the theorem `[L: arXiv:2408.15332v1, sec/introduction.tex, Theorem labelled thm:stableAK3]`:

> The following potential counterexample introduced by Akbulut and Kirby is stably AC-trivial:
> AK(3) = <x, y | x^3 = y^4, xyx = yxy>.

Appendix `[L: arXiv:2408.15332v1, app/stable_ak3.tex]`:

> To the best of our knowledge, prior to this work, the shortest potential counterexample to the standard Andrews--Curtis conjecture, namely AK(3), was also a potential counterexample to the stable Andrews--Curtis conjecture. Our proof that AK(3) is stably AC-trivial builds on the following result.

The same appendix attributes to MMS a theorem that includes the stability clause: "Moreover, all such presentations are stably AC-trivial" `[L]`. MMS Theorem 1.4 as printed asserts only that the presentations "determine the trivial group", and the stability is a separate remark in their introduction `[L: ac.tex, Theorem 1.4 and the preceding paragraph]`. So the stability clause in the 2024 paper is the authors' reading of the 2002 remark, and that reading is exactly what the misprint invalidates `[A]`.

### 5.2 Shehper et al. version 2, the withdrawal

Abstract `[L: arXiv:2408.15332v2, sec/abstract.tex]`:

> Notably, we demonstrate the length reducibility of all but two presentations in the Akbulut--Kirby series (1981), and resolve various potential counterexamples in the Miller--Schupp series (1991), including three infinite subfamilies.

The stable claim is absent from this abstract, and the introduction states the correction as follows `[L: sec/introduction.tex, lines 88 to 91]`:

> Motivated by this connection and by the claim in [MMS] that the presentation (ellipsis for a displayed equation) is stably AC-trivial, we apply reinforcement learning to demonstrate its AC equivalence to AK(3). However, after closer inspection, we discovered a subtle misprint in [MMS, p.10] that had gone unnoticed for more than 20 years. This misprint undermines the claim that (eq:MMS3) is stably AC-trivial.

Remark in the stable section `[L: sec/stable.tex, lines 193 to 196]`:

> The unknot diagram of Figure ... was originally presented in [MMS]. Their manuscript contained an unfortunate misprint in the 13th relator, where it is written as x_13 = x_5 x_12 x_5^{-1}. The resultant presentation is not a Wirtinger presentation of any knot diagram, affecting the validity of one of their main theorems ([MMS, Theorem 1.4]).

Appendix on the misprint `[L: app/mms.tex]`:

> In a Wirtinger presentation, any single relator is redundant, meaning that removing any relator still yields a valid presentation of the knot group. In the case of an unknot, this group is the infinite cyclic group Z. However, removing different relators from W' produces different groups. For instance, if the relator x_7 = x_4^{-1} x_6 x_4 is removed, the resulting group is the three-strand braid group, whereas removing x_14 = x_1 x_13 x_1^{-1} yields Z.

The same appendix continues with the following sentence:

> Note, however, that unlike any presentation AC-equivalent to a correct Wirtinger presentation, these presentations are not necessarily stably AC-trivial.

Appendix on Wirtinger presentations `[L: app/wirtinger.tex]`:

> Because of these facts, we cannot use Reidemeister moves to show the stable AC-triviality of MMS3 and therefore AK(3) as well.

The same appendix proves a proposition that is worth recording because it is the one positive technical statement in version 2 about this material `[L]`:

> The balanced presentation MMU(w) of the trivial group is stably AC-equivalent to <x,y | xyx=yxy, w>; in particular, for w_n = x^{-n}y^{n+1}, we have that MMU(w_n) is stably AC-equivalent to AK(n) for each n >= 1.

Here MMU(w) is the printed 14-generator presentation with the relator $x_7=x_4^{-1}x_6x_4$ removed and the word w added. I did not replay this proof, and the proposition says nothing about stable triviality `[U]`.

### 5.3 Lisitsa, preprint and published version

Preprint abstract `[L: arXiv:2501.18601v1]`:

> Recent work by Shehper et al. (2024) demonstrated that the well-known Akbulut-Kirby AK(3) balanced presentation of the trivial group is stably AC-equivalent to the trivial presentation. This result eliminates AK(3) as a potential counterexample to the stable Andrews-Curtis conjecture. In this paper, we present an alternative proof of this result using an automated deduction approach.

Preprint conclusion `[L]`:

> We have presented alternative proofs of the stable AC-trivializability of AK(3), based on the use of automated deduction.

Published abstract `[L: J. Comput. Algebra 16 (2025) 100041, DOI 10.1016/j.jaca.2025.100041, abstract as indexed by OpenAlex; I could not open the publisher's full text. The published abstract sets the clause about P between dashes, and I have replaced each dash by a comma to keep this file free of them]`:

> Subsequent to our initial submission, it has emerged that the earlier theoretical claim about the stable AC-trivializability of P, on which the Shehper et al. result relied, was based on an incorrect theorem, and thus the status of AK(3) remains unresolved. While this paper does not establish the stable AC-triviality of AK(3), it contributes a reproducible and verifiable case study in the use of automated reasoning to analyze deep problems in combinatorial group theory.

The published abstract also describes the contribution as "an independently obtained reduction of AK(3) to P" `[L]`. That matches leg 2 of the withdrawn argument and not leg 1, which is the point I made in section 3 `[A]`.

## 6. What I checked, with commands and output

All files live in `.ultramath/smw2i9i4j/m1/` of this repository. Each script is deterministic, takes no input, and uses only the Python standard library plus sympy.

### C1. Replay of the 53-move sequence from P to AK(3)

Command: `python3 .ultramath/smw2i9i4j/m1/replay53.py`

The sequence is the one printed in arXiv:2408.15332v1, app/stable_ak3.tex, and repeated in v2, app/mms.tex, in terms of the twelve moves h_1 to h_12. Each h_i is a multiplication by the other relator, an inversion, or a conjugation by one generator or its inverse, so each is a legal AC1, AC2 or AC3 move. Output:

```
P relator 1: x^-1y^-1xy^-1x^-1yxy^-1y^-1xyx^-1y  length 13
P relator 2: y^-1x^-1yyx^-1y^-1xyxy^-1y^-1x  length 12
AK(3) relator 1: xxxy^-1y^-1y^-1y^-1  relator 2: xyxy^-1x^-1y^-1
number of moves: 53
total relator length at the start: 25
maximum total length along the 53 moves: 25 at move 0
final total length: 13
  relator 1 (length 7): xxxy^-1y^-1y^-1y^-1
  relator 2 (length 6): xyxy^-1x^-1y^-1
matches AK(3) relator pair up to order, inversion and cyclic shift: True
raw equality with AK(3) in the given order: True  or swapped: False
```

So P and AK(3) are AC-equivalent by 53 explicit moves, and the claim that the total length never exceeds 25 along the path is confirmed `[V]`. None of the 53 moves is a stable move, so this check covers the non-stable leg of the argument and no more.

### C2. Abelian data for the printed and the corrected presentation

Command: `python3 .ultramath/smw2i9i4j/m1/mms_misprint_check.py`

The script builds the 14 relators from the printed words, computes Smith normal forms of the exponent-sum matrices, and reports the final three-generator presentation rebuilt from the printed relators. The full output tabulates every single-relator deletion, and the lines below summarise it:

```
printed:   SNF [1,...,1] (13 ones) -> abelianisation Z
corrected: SNF [1,...,1] (13 ones) -> abelianisation Z
printed, delete rK : Z   for every K in 1..14
corrected, delete rK : Z  for every K in 1..14
```

The consequence is narrow and worth stating because it constrains how the misprint can be detected. The abelianisation is $\mathbb{Z}$ for the printed presentation, for the corrected presentation, and for every single-relator deletion of either. So no abelian computation can separate the printed presentation from the corrected one, and the difference asserted by Shehper et al. has to be non-abelian `[V, A]`.

A separate check on the final three-generator presentation printed in MMS (`python3 .ultramath/smw2i9i4j/m1/mms_final_check.py`) gives:

```
relator 1 (x5 R1^-1): x5x12X7X5x7x5X12X5X7x5x7X12
relator 2 (x7 R2^-1): x7x5x7X5X12X5X7X5x7x5x12X5X7x5
exponent sums relator1: (1, 0, -1)  relator2: (-1, 1, 0)
Smith normal form diag: [1, 1]
surjections onto S3 (order 6): 0
surjections onto S4 (order 24): 0
surjections onto A5 (order 60): 0
presentation with the added relator x5 (w = x): surjections onto S3 0, A5 0, S5 0
```

The exponent sums match the pair printed by MMS. The absence of surjections onto S_3, S_4 and A_5 is consistent with the group being $\mathbb{Z}$, which is what MMS need, and it is not a proof of that `[V, bounded]`.

### C3. P from the three-generator family

Command: `python3 .ultramath/smw2i9i4j/m1/mms3_to_P.py`

The script builds the three relators of MMS Theorem 1.4 from the commutator notation, substitutes $z=y^{-1}x$ from the third relator, and compares with the printed P. Output:

```
MMS3 with z = y^-1 x substituted:
  relator 1 (13): xy^-1xy^-1x^-1yyx^-1y^-1xyx^-1y
  relator 2 (12): yyx^-1y^-1x^-1yxy^-1y^-1xyx^-1
P as printed by MMS (total length 25):
  relator 1 (13): x^-1y^-1xy^-1x^-1yxy^-1y^-1xyx^-1y
  relator 2 (12): y^-1x^-1yyx^-1y^-1xyxy^-1y^-1x
relator 1 equals P relator 1 up to inversion and cyclic shift: True  relator 2: True
total length of the substituted pair: 25
```

So the member of the family named in the 2024 papers is the printed P, and the printed length 25 is correct `[V]`. The comparison is up to inversion and cyclic shift of a relator, and both operations are sequences of AC1 moves on that relator.

### C4. Finite-quotient searches on the deleted-relator presentations

Command: `python3 .ultramath/smw2i9i4j/m1/wwu_quotients.py`

The search is a deterministic backtracking search for surjective homomorphisms onto S_3 and S_4, with a fixed variable order and a fixed value order, and a node budget. It uses no randomness, so a rerun on the same machine reproduces the node counts. Output:

```
PRINTED   delete r12 -> S3: surjections 0 nodes 548
PRINTED   delete r12 -> S4: surjections 0 nodes 19496
PRINTED   delete r7  -> S3: surjections 1 nodes 201
     images: {1: (0,2,1), 2: (1,0,2), 3: (2,1,0), 4: (2,1,0), 5: (1,0,2), 6: (2,1,0), 7: (0,2,1), 8: (0,2,1), 9: (0,2,1), 10: (2,1,0), 11: (0,2,1), 12: (0,2,1), 13: (2,1,0), 14: (1,0,2)}
PRINTED   delete r14 -> S3: surjections 0 nodes 523
PRINTED   delete r14 -> S4: surjections 0 nodes 18775
CORRECTED delete r12 -> S3: surjections 0 nodes 548
CORRECTED delete r12 -> S4: surjections 0 nodes 19496
CORRECTED delete r7  -> S3: surjections 0 nodes 491
CORRECTED delete r7  -> S4: surjections 0 nodes 7757
CORRECTED delete r14 -> S3: surjections 0 nodes 523
CORRECTED delete r14 -> S4: surjections 0 nodes 18775
```

This supports the appendix's contrast between two of its deletions. The printed presentation with $r_7$ deleted has a non-abelian quotient, so it is not $\mathbb{Z}$, and the printed presentation with $r_{14}$ deleted has no such quotient `[V, bounded]`. My search gives no support to the appendix's more important claim, that the printed presentation with $r_{12}$ deleted "is not a presentation of $\mathbb{Z}$". I found no surjection from that group onto S_3 or S_4, and a search for surjections onto A_5 did not finish inside 90 seconds under the machine load of this run, so I record the claim as unverified here `[U]`. The corrected presentation with $r_7$ deleted has no surjection onto S_3 or S_4 either, which is consistent with the genuine Wirtinger property `[V, bounded]`.

The appendix's identification of the $r_7$-deleted group as "the three-strand braid group" is consistent with my quotient, which shows only that the group is non-abelian `[V, bounded]`. The name in the appendix may well be right, and my check does not establish it.

### C5. The Miasnikov AK(2) count

The Round 2 brief asked for the AK(2) chain length to be settled, since two documents gave 19 and 21. The paper settles it and the two counts count different things `[L: A. D. Miasnikov, "Genetic algorithms and the Andrews-Curtis conjecture", Int. J. Algebra Comput. 9 (1999) 671-686, DOI 10.1142/S0218196799000370, arXiv:math/0304306, section "Results"]`. The printed chain is numbered 1 to 19, so there are 19 printed steps. The paper then says: "The transformation 9 requires the elementary transformations of type (AC3') and (AC3''), adding two more transformations to the solution and increasing its length to 21." Step 9 conjugates by the three-letter word $ba^{-1}b$, and conjugating by a word of length three takes three single-letter conjugation steps, so the printed step 9 expands into three elementary moves. The reconciliation is therefore 19 printed steps and 21 elementary moves, with the difference at step 9 `[V by reading and counting the printed chain]`. The sentence in survey/computational.md section 1 that gives 19 printed steps and 21 elementary moves is correct.

## 7. Answers to the four questions of the brief

### 7.1 What the misprint is

It is one wrong letter in the 13th relator of the 14-generator presentation, printed as $x_{13}=x_5x_{12}x_5^{-1}$ where the Wirtinger relator for the drawn crossing is $x_{13}=x_4x_{12}x_4^{-1}$ `[L, V]`. The two letters name different arcs of the diagram, and the conjugating letter at a crossing is the arc that passes over.

### 7.2 What it undermines

It removes the justification for the sentence in MMS that calls the two-relator group the unknot group, and it removes the justification for the remark in the MMS introduction that presentations built from the diagram are stably AC-trivial. The first is the step on which the triviality claim of Theorem 1.4 rests. The second is the step on which the stable triviality of P, and hence of AK(3), rests `[A]`.

### 7.3 The chronology

Version 1 of Shehper et al. is 27 August 2024. Lisitsa's submission is 17 January 2025. Version 2 of Shehper et al. is 11 February 2025, so the correction is 25 days after the submission that relied on the uncorrected claim. Lisitsa's published abstract records the correction and describes the result of the submission as a reduction from AK(3) to P rather than a stable trivialization `[V]`.

### 7.4 The definitive current status

The stable AC-triviality of AK(3) is unresolved `[O]`. Both groups of authors have withdrawn the claim in the published or revised record, with Shehper et al. saying the presentation is "not necessarily stably AC-trivial" and Lisitsa saying "the status of AK(3) remains unresolved". No proof and no disproof is on record. The only verified positive statement about this material that I can add is that P and AK(3) are AC-equivalent by 53 explicit moves `[V]`.

## 8. Corrections to the two survey files

I edited both files with dated notes. Here is what the edits say and why.

For `survey/automated.md` section 3.3: the coordinator's correction is confirmed in substance. The revised abstract does state only the length reducibility and the Miller-Schupp subfamilies, which I checked against the arXiv API record and against the LaTeX of version 2. The sentence attributing the reading of the revised body text to the ak-status survey is now backed by my own reading of version 2 in full. Two details are added. First, the exact sentence in version 2 that names the consequence is "This misprint undermines the claim that (eq:MMS3) is stably AC-trivial", and it cites "[MMS, p.10]". Second, the proceedings version of the paper contains no stable-conjecture material at all, so the withdrawal is visible in the arXiv record and not in the proceedings.

For `survey/ak-status.md` section 2.3: the substance is confirmed and two attributions are made precise. The quotation "undermines the claim" is accurate and is from the introduction of version 2, not from its abstract. The quotation "the status of AK(3) remains unresolved" is from the published abstract in the Journal of Computational Algebra, and it is not in the January 2025 arXiv version, whose abstract says the opposite; the survey's citation "2025" should therefore name the published version. The journal name and volume, which the survey listed as unconfirmed, are Journal of Computational Algebra 16 (2025) 100041, DOI 10.1016/j.jaca.2025.100041. The item's description of the 2025 paper as giving an "alternative proof" of stable triviality should be restricted to the preprint, since the published abstract disclaims exactly that.

## 9. Sources, with what I read

1. A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, "On the Andrews-Curtis equivalence", Contemporary Mathematics 296 (2002) 183-198, DOI 10.1090/conm/296/05074. I read the full LaTeX source of arXiv:math/0302080 and the 16-page PDF posted by Shpilrain. The relator list, Theorem 1.4, its proof, and the weak-conjecture remark were read in the source text.
2. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu, P. Kucharski, Z. Wang and S. Gukov, "What makes math problems hard for reinforcement learning: a case study", arXiv:2408.15332 version 1 of 27 August 2024 and version 2 of 11 February 2025. I read the LaTeX of both versions, including the removed appendix `app/stable_ak3.tex` of version 1 and the added appendices `app/mms.tex` and `app/wirtinger.tex` of version 2.
3. The NeurIPS 2025 proceedings version of the same paper, `https://proceedings.neurips.cc/paper_files/paper/2025/file/ea8c9cd935dc62e0288bbf33a15e65e9-Paper-Conference.pdf`, 34 pages, labelled "39th Conference on Neural Information Processing Systems (NeurIPS 2025)". I searched its full text and found no occurrence of "stable", "misprint" or "Wirtinger"; the only word beginning with "stab" is "stability", in a reinforcement-learning sentence.
4. A. Lisitsa, "Stable Andrews-Curtis trivialization of AK(3) revisited. A case study using automated deduction", arXiv:2501.18601 version 1 of 17 January 2025, and Journal of Computational Algebra 16 (2025) 100041, DOI 10.1016/j.jaca.2025.100041, published online 2025-10-15. I read the full LaTeX of the preprint and the published abstract as indexed by OpenAlex. I could not open the publisher's full text.
5. A. D. Miasnikov, "Genetic algorithms and the Andrews-Curtis conjecture", Int. J. Algebra Comput. 9 (1999) 671-686, DOI 10.1142/S0218196799000370, arXiv:math/0304306. I read the statement of the chain, the printed chain, and the sentence about step 9.
6. The bibliographic records were checked live on 2026-11-04 through the arXiv API and abstract pages, the Crossref API for the three DOIs named above, and the OpenAlex record for the journal article.

One bibliographic discrepancy is worth recording because an earlier survey flagged it and could not resolve it. The DOI 10.52202/085713-5348 has a Crossref record with container title "Advances in Neural Information Processing Systems 38", publication year 2025, and pages 177669-177702. The proceedings site that serves the PDF I read places the paper in the 2025 volume and its first page labels it "39th Conference on Neural Information Processing Systems (NeurIPS 2025)", and the reference list of arXiv:2501.18601v1 gives the year 2024 with the same pages. The page range agrees across the records and the conference number does not. I did not resolve that discrepancy, and no claim in this report depends on it.

## 10. Limits

I could not read the published full text of the Journal of Computational Algebra article, so the published body text is unverified here; only its abstract is. The identification of the over-arc at the 13th crossing rests on Shehper et al. and not on my own reading of the figure. The appendix claim that the printed presentation with the 12th relator deleted is not a presentation of $\mathbb{Z}$ is unverified by me; my searches for non-abelian quotients up to S_4 found none, and the A_5 search did not finish. The identification of the $r_7$-deleted group with the three-strand braid group is likewise unverified; I only show that it is non-abelian. I did not replay the proof of the proposition in `app/wirtinger.tex`. The finite-quotient searches are bounded, and a bounded negative is recorded as bounded.
