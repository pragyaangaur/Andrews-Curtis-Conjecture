# Automated reasoning on the Andrews–Curtis conjecture

Direction D7 of swarm smw2fzjic, written by member m6. Every online source below was read on
2026-11-04. Labels: **Verified** means I read the source or ran the command and quote its
output. **Argument** means my own reasoning, not machine-checked. **Not verified** marks what
I could not check.

## 0. What this note adds

Three items below are checked rather than reported. Each item carries the command that reproduces it.

1. Lisitsa publishes two explicit sequences of AC moves that carry the presentation `P` to
   `AK(3)`. I replayed both with my own code. The long sequence has 160 printed moves; 159 of
   them check exactly as printed, step 81 has a one-letter slip in its conjugator, and with
   that single correction the chain runs from `P` to `AK(3)`. The short sequence has 70 moves
   and checks exactly as printed, every step a standard AC move. Both endpoints match the
   presentations printed in the paper. So `P` and `AK(3)` are AC-equivalent, and this leg of
   Lisitsa's proof of the stable triviality of `AK(3)` is now independently verified.
   The command is `python3 survey/automated_check.py`.
2. Lisitsa's Theorem 1, that adding any of the three automorphism moves of `Aut(F_2)` to the AC
   moves gives a non-equivalent system, rests on two finite algebras printed in his appendix. I
   checked both algebras by brute force: they satisfy the group axioms and every axiom of his
   equational theories `EACT2` and `EACT2~`, and they violate exactly the three equalities he
   claims. That theorem is therefore correct as stated.
   The command is `python3 survey/automated_countermodel_check.py`.
3. The public shared formal statement of the ordinary and the stable conjecture, in the SAIR
   competition repository, compiles here under Lean 4.33.1 and Mathlib, contains no `sorry`,
   and all seven of its theorems depend only on the Lean axioms `propext`, `Classical.choice`
   and `Quot.sound`.

## 1. Lisitsa's method

### 1.1 The move relation at rank 2

The method was introduced by Lisitsa (2013, 2018). At rank 2 a presentation is a pair of words
and an AC move is one of three operations on the pair. His web page states the encoding as a
term rewriting system `ACT_2` on terms `f(x,y)`, with six rules:

```
f(x,y) -> f(x',y)
f(x,y) -> f(x,y')
f(x,y) -> f(x,y*x)
f(x,y) -> f(x*y,x)
f(x,y) -> f((z*x)*z',y)
f(x,y) -> f((z'*x)*z,y)
```

rewriting modulo the equational theory of groups (associativity, two-sided identity, two-sided
inverse). Here `x'` is the inverse of `x`, and `z` is a variable. The first four rules are
inversion of one relator and multiplication of one relator by the other; the last two are
conjugation of one relator by an arbitrary word. The substitution of a variable `z` for the
conjugating word is the technical heart of the approach, because the AC move AC3 quantifies over
all words of the free group while a first-order variable ranges over one term at a time. In a
first-order proof the variable is universally quantified, so a single proof step covers every
conjugator.

Two encodings are used. In the equational encoding the rewrite rules are turned into equations,
which is legitimate because the transitive closure of the AC move relation is symmetric. In the
implicational encoding a predicate symbol `R` replaces the equations and one component of the
pair is held fixed, which cuts the search space. Lisitsa's appendix writes the equational theory
`EACT2` as the group axioms together with

```
f(x,y) = f(r(x),y)
f(x,y) = f(x*y,y)
f(x,y) = f(x,y*x)
f(x,y) = f((a_i*x)*r(a_i),y)      for each generator a_i
```

and `EACT2~` replaces the last line by the non-ground version
`f(x,y) = f((v*x)*r(v),y)` with a variable `v`. His Proposition 1, quoted from his own earlier
paper, says that for ground terms `t1`, `t2` one has `t1 ->*_ACT2/G t2` if and only if
`EACT2 |- t1 = t2` if and only if `EACT2~ |- t1 = t2`. I verified this from the appendix of the extended AITP version, file `AITP.pdf` in Zenodo record 2555481.

### 1.2 The provers

Proofs are produced by Prover9 and countermodels by Mace4, both from the LADR distribution. The
goal handed to Prover9 is an implication between pair-terms, for instance

```
R((group word encoding P)) -> R((group word encoding AK(3)))
```

under the axioms. A successful run yields a first-order proof, from which a sequence of AC moves
is extracted. The extraction step is where the method needs care: the AITP abstract lists
"development of automated extraction of the simplifying move sequences from proofs" as future
work, while the 2025 paper presents extracted sequences and publishes them in a Zenodo record.
The existence of the sequences and of the record is verified, and whether the extraction is fully automatic is not verified.

## 2. The publication record, with identifiers

| Item | Identifier | What it establishes |
|---|---|---|
| A. Lisitsa, "First-order theorem proving in the exploration of Andrews-Curtis conjecture" | TinyToCS 2 (2013) | First statement of the ACT approach. **Verified** only as a bibliographic item: the reference is printed in the AITP 2019 reference list and on Lisitsa's page. I did not fetch the item. |
| A. Lisitsa, "The Andrews-Curtis Conjecture, Term Rewriting and First-Order Proofs" | ICMS 2018, LNCS 10931, pp. 343–351, Springer, DOI 10.1007/978-3-319-96418-8_41 | Introduces `ACT` and its first-order translations; abstract claims "finding required simplifications for several new open cases". **Verified** from the Liverpool repository record (metadata and abstract). Content of the paper itself not read. |
| A. Lisitsa, "Automated Reasoning for the Andrews-Curtis Conjecture" | AITP 2019 abstract, `https://aitp-conference.org/2019/abstract/paper%2024.pdf`; extended version with proofs and countermodels in Zenodo DOI 10.5281/zenodo.2555481 | Claims (i) a negative answer to the Panteleev–Ushakov question on adding automorphisms, (ii) all 12 novel trivialization cases of Panteleev–Ushakov Table 4 reproduced by automated theorem proving, (iii) failure to find the automorphism images of Table 3, and (iv) finite-countermodel proofs of the impossibility of trivializations by subsystems. **Verified**: both PDFs fetched and read; the countermodels of (i) are re-checked in section 4 below. |
| A. Lisitsa, "Towards computer-assisted proofs of parametric Andrews-Curtis simplifications, II" | LPAR 2024 Complementary Volume, Kalpa Publications in Computing 18, pp. 131–136, EasyChair, DOI 10.29007/p2w1 | Claims previously unknown simplifications of the presentations `MS_n(w*)` for n = 3,4,5,6,7,8, and formulates two conjectures on the structure of those simplifications. **Verified** from the EasyChair record (title, author, pages, volume, editors, date 2024-05-26, abstract). Paper body not read. |
| A. Lisitsa, "Stable Andrews-Curtis trivialization of AK(3) revisited. A case study using automated deduction" | arXiv:2501.18601 (2025-01-17) | An alternative proof of the stable AC-trivializability of `AK(3)`, via an explicit AC-equivalence `P -> AK(3)`; five extracted sequences of lengths 252, 160, 70, 57, 110; Prover9 run times 4273.70 s and 927.61 s on an Intel i5-7200U with 16 GB RAM running Windows 10; and an explicit statement that no known computational method searches stable transformations directly. **Verified**: e-print source downloaded, all statements above read in the LaTeX. The sequences S2 and S3 are replayed in section 3. |
| M. Fairbank, A. Lisitsa, A. Vernitski, "Probabilistic Automaton Classifier Applied to Examples Related to the Andrews-Curtis Conjecture" | Journal of Automated Reasoning 70 (2026), DOI 10.1007/s10817-026-09759-8, issued 2026-07-08 | Uses supervised learning to choose which tasks to give an automated reasoner, demonstrated on AC examples. **Verified** from Crossref and OpenAlex metadata including the abstract. The paper body is behind a paywall and was not read. |
| A. Lisitsa, data for the 2018 paper | Zenodo DOI 10.5281/zenodo.1248987, published 2018-05-17 | Prover9 proofs and Mace4 refutations, in folders `AK-2`, `AK-3-Conjugation_is_needed`, `CYCL-OLD`, `DIM-2-NEW`, `DIM-3-NEW`, `DIM-4-NEW`. **Verified** from the Zenodo API and the record's `Read.me.txt`. |
| A. Lisitsa, extended AITP version | Zenodo DOI 10.5281/zenodo.2555481, published 2019-02-02 | Files `AITP.pdf`, `PU-cases.zip`, `countermodels.zip`. **Verified** from the Zenodo API. |
| A. Lisitsa, supplementary data for the 2025 paper | Zenodo record 14567743, published 2024-12-29 | Contains the Prover9 proofs and the extracted sequences of arXiv:2501.18601. **Verified** from the Zenodo API (title "Stable Andrews-Curtis trivialization of AK(3) revisited. Supplementary data."). File contents not inspected. |

Two data files deserve comment. The folder name `AK-3-Conjugation_is_needed` in record 1248987
records the author's finding that the conjugation move is needed for his `AK(3)` rewriting, and
`countermodels.zip` in record 2555481 holds the Mace4 output re-checked in section 4. I did not
open either archive, so the folder name is evidence of the author's label and nothing more.

## 3. Independent replay of the two published sequences

### 3.1 The presentations

Lisitsa's paper states that Shehper, Medina-Mardones, Fagan, Lewandowski, Gruen, Qiu, Kucharski,
Wang and Gukov (arXiv:2408.15332) found a sequence carrying

```
P = < a,b | a^-1 b^-1 a b^-1 a^-1 b a b^-2 a b a^-1 b ,
            b^-1 a^-1 b^2 a^-1 b^-1 a b a b^-2 a >
```

to `AK(3) = < a,b | a b a = b a b, a^3 = b^4 >`, written as the relator pair
`(a^3 b^-4, a b a b^-1 a^-1 b^-1)`. He also states that `P` belongs to a family shown to be
stably AC-trivial in work he cites, so that the AC-equivalence `P -> AK(3)` transfers the stable
triviality to `AK(3)`. The decoding is part of my checker, so the two relator pairs just written are verified to be the ones in the paper.

### 3.2 The replay

`survey/automated_check.py` contains a verbatim copy of the two LaTeX `verbatim` blocks of the
paper, a free-group word implementation, and a checker that decides for each printed line
whether the next printed pair is obtained by the printed move. It prints:

```
S2: parsed 160 printed moves, final state aaaBBBB,abaBAB
S2: printed move numbers are 1..160: True
S2: all printed states are reduced words: True
S2: move kinds: {'INV': 52, 'CONJ': 51, 'MULT-L': 50, 'MULT-R': 7}
S2: multiplications directly by the other relator: 57, by its inverse (three standard moves): 0
S2: first state equals the relator pair of the paper's P: True
S2: last state equals the AK(3) relator pair (a^3 b^-4, a b a b^-1 a^-1 b^-1): True
S2: steps that fail exactly as printed: 1 [(81, 'CONJ ABAbAXaBabA')]
S2: with step 81 conjugator read as aBAbA instead of the printed ABAbA: failing steps = 0
S2: corrected chain runs P -> AK(3) in 160 standard AC moves: True
S3: 67-move S2 prefix plus 3 printed moves = 70 moves, kinds {'INV': 23, 'CONJ': 22, 'MULT-L': 20, 'MULT-R': 3, 'CONJ-R': 1, 'INV-R': 1}
S3: first state equals P: True, last state equals AK(3): True
S3: failing steps: 0 []
RESULT: PASS: both published sequences replay from P to AK(3)
```

The notation of the printed sequence is `wXw'`, with `X` (sometimes printed `x`) standing for
the conjugated word, and `A = a^-1`, `B = b^-1`. So the move on line 81 has conjugator `ABAbA`.
With that conjugator the printed states before and after line 81 are not related by conjugation.
They are related by conjugation with `aBAbA`, which differs in the case of the first letter.
Since steps 1 to 80 and 82 to 160 check exactly, the most economical reading is a one-letter
typographical slip in line 81, and the corrected sequence is a complete certificate.

All 70 moves of the short sequence are standard AC moves. The two composite labels `CONJ-R` and
`INV-R` mean conjugation and inversion of the second relator, which are ordinary AC moves. All
160 moves of S2 are also standard AC moves: 52 inversions, 51 conjugations, and 57
multiplications by the other relator, none of them a multiplication by an inverse relator.

### 3.3 What the replay establishes, and what it does not

What I verified is that the relator pairs `P` and `AK(3)` are related by an explicit 70-step (and, after
the one-letter correction, 160-step) sequence of standard AC moves. No group theory beyond free
reduction is used, and the certificate can be checked in fractions of a second.

Four things remain unverified: that `P` is stably AC-trivial, which is the other leg of the argument and comes from the family argument of Fagan and from Shehper et al.; that `AK(3)` presents the trivial group; that Lisitsa's 53-move count for the original Shehper et al. sequence is correct, since I did not see that sequence; and that any sequence is shortest.

My reading of the paper's logic is as follows. The logical chain of Lisitsa's 2025 paper is: (i) `P` is stably AC-trivial;
(ii) `P` and `AK(3)` are AC-equivalent; therefore (iii) `AK(3)` is stably AC-trivial. My replay
supplies a machine check of (ii) only. A reader who wants (iii) must check the stable-triviality
of `P` in the cited sources. This distinction matters for the campaign because `AK(3)` is
therefore eliminated as a candidate counterexample to the stable conjecture by two independent
arguments, while it remains a candidate for the ordinary conjecture.

COORDINATOR CORRECTION, 2026-11-04. The sentence above is wrong as stated, and I am
recording the correction here rather than leaving it standing. The stable triviality of
AK(3) is not established. Shehper et al. arXiv:2408.15332 version 1 (August 2024) claimed
it, and the abstract of Lisitsa arXiv:2501.18601 (January 2025) repeats the claim, but
version 2 of the Shehper et al. paper (updated 11 February 2025) no longer makes it: the
authors found a misprint in their 2002 source, Myasnikov, Myasnikov and Shpilrain, which
undermines the claim, and the current abstract states only the length reducibility of all
but two Akbulut-Kirby presentations and the resolution of Miller-Schupp subfamilies. I
verified the current abstract myself; the reading of the revised body text is due to the
ak-status survey. The stable status of AK(3) is unresolved. The machine-checked P to
AK(3) certificates of this file transfer stable triviality to AK(3) only if P is itself
stably trivial, and that is exactly what the misprint undermines. A Round 2 referee will
read both papers in full and write the definitive status note.

ROUND 2 REFEREE NOTE ON THE CORRECTION ABOVE, m1, 2026-11-04. I read both papers in full as
promised, together with the 2002 source. The correction above is confirmed in substance, and
three details are added. (1) The exact sentence in version 2 that names the consequence is
"This misprint undermines the claim that the presentation (eq:MMS3) is stably AC-trivial", and it cites
"[MMS, p.10]", which is page 10 of the 16-page article, that is page 192 of the volume.
(2) The revised abstract does state only the length reducibility of all but two Akbulut-Kirby
presentations and the resolution of Miller-Schupp subfamilies; I checked this against the
arXiv API record and against the LaTeX of version 2, so the reading of the revised body text
no longer rests on the ak-status survey alone. (3) The NeurIPS proceedings version of the
paper contains no material on the stable conjecture at all, since the words "stable" and
"misprint" do not occur in the 34-page proceedings PDF (the only word beginning "stab" is
"stability", in a reinforcement-learning sentence), so the withdrawal is visible in the
arXiv record and not in the proceedings record. A further point belongs here because it
qualifies what "unresolved" rests on: my replay of the 53-move sequence in the version 1
appendix carries the length-25 presentation P to the AK(3) relator pair exactly, using moves
AC1 to AC3 only, so the non-stable leg of the withdrawn argument is verified and the stable
leg is the one that fails. The full referee report is survey/stable-ak3-status.md. Check:
python3 .ultramath/smw2i9i4j/m1/replay53.py.


## 4. The countermodels for the automorphism-move theorem

### 4.1 The claim

The question answered here was raised by Panteleev and Ushakov (arXiv:1609.00325, abstract
verified): they extended the AC rules by automorphisms of the free group and showed that this does
not enlarge the reachable sets for `AK(n)` with n at least 3, they left the general case open, and
they report that they could not trivialize any `AK(n)` for n larger than 2. Lisitsa's Theorem 1
concerns the three automorphisms of `F_2` that generate `Aut(F_2)` up to the
AC moves: `phi1: a -> a, b -> b^-1`; `phi2: a -> a, b -> b*a`; `phi3: a -> b, b -> a`. It states
that `g = <a,b | aba, bba>` is not AC-equivalent to either `g1 = <a,b | a b^-1 a, b^-1 b^-1 a>`
or `g2 = <a,b | abaa, babaa>`, and that `g' = <a,b | aaba, bba>` is not AC-equivalent to
`g3 = <a,b | bbab, aab>`. The proof method is to show that `EACT2~` does not derive the
corresponding equality of pair-terms, and to exhibit for each case a finite algebra in which the
axioms hold and the equality fails. Mace4 found a 3-element algebra for the first two cases and
a 5-element algebra for the third, printed in full in the appendix. I verified this by reading the appendix of `AITP.pdf`.

### 4.2 The brute-force check

`survey/automated_countermodel_check.py` hard-codes the two printed algebras and checks by
exhaustive enumeration that the group axioms hold, that all four AC axioms of `EACT2` hold, that
the non-ground conjugation axiom of `EACT2~` holds for every element `v`, and that the three
claimed equalities fail. Output:

```
3-element model: group axioms (associativity, two-sided identity, left and right inverse): True
3-element model: f(x,y)=f(r(x),y): True | f(x,y)=f(x.y,y): True | f(x,y)=f(x,y.x): True
3-element model: ground conjugation axioms: True | non-ground conjugation axiom: True
5-element model: group axioms (associativity, two-sided identity, left and right inverse): True
5-element model: f(x,y)=f(r(x),y): True | f(x,y)=f(x.y,y): True | f(x,y)=f(x,y.x): True
5-element model: ground conjugation axioms: True | non-ground conjugation axiom: True
AT1 (3-element model): f(aba,bba)=1, f(aB a,B B a)=0, inequality holds: True
AT2 (3-element model): f(aba,bba)=1, f(abaa,babaa)=0, inequality holds: True
AT3 (5-element model): f(aaba,bba)=0, f(bbab,aab)=1, inequality holds: True
RESULT: PASS: both printed algebras are models of the AC axioms and refute the three claimed equalities
```

Two points about scope. First, the algebras satisfy the axioms of both equational theories, so by
soundness of equational logic the three equalities are not derivable, which by Proposition 1
means the presentations are not AC-equivalent. Second, the theorem is about presentations of
non-trivial groups. Lisitsa says so explicitly in the appendix: a theorem of this kind for a
balanced presentation of the trivial group would disprove the conjecture, and "it is known
though that it is not possible to do using finite countermodels". This is the sharp boundary of the method. A finite countermodel refutes derivability of an equation from a
subsystem of the AC axioms, and such a refutation can only concern presentations whose group has
a non-trivial finite quotient, because a finite model of the axioms that collapses the group
would also collapse the pair-term.

## 5. Formalization and machine-checkable certificates

### 5.1 The SAIR shared statement

The SAIR Foundation runs a competition on the conjecture whose proof track states both the
ordinary and the stable version and refers to a shared Lean file. I verified the competition record through the JSON metadata embedded in `https://competition.sair.foundation/competitions/acc/proof-track`
(status active, submissions opened 2026-09-11, deadline 2026-12-01T11:59:59Z, 188 participants
at the time of reading), and the repository `https://github.com/SAIRcompetition/Andrews-Curtis`,
which contains `competition/tools/lean/AC.lean`, a Lean verifier with move specifications, and
problem sets under `competition/problems/`.

The file is short and precise. It defines `Word n := FreeGroup (Fin n)`, `Relators n := Fin n ->
Word n`, `standard n := FreeGroup.of`, and

```
def PresentsTrivialGroup (R : Relators n) : Prop := Subsingleton (PresentedGroup (Set.range R))

inductive Step : Relators n -> Relators n -> Prop
  | inv (R) (i) : Step R (Function.update R i (R i)⁻¹)
  | mulRight (R) (i j) (h : i ≠ j) : Step R (Function.update R i (R i * R j))
  | conj (R) (i) (w : Word n) : Step R (Function.update R i (w * R i * w⁻¹))

def Reachable := Relation.ReflTransGen Step
def Conjecture : Prop := ∀ n, 0 < n → ∀ R, PresentsTrivialGroup R → Reachable R (standard n)
```

The stable version adds `StableStep.stabilize` and `StableStep.destabilize`, which insert and
remove a fresh generator with the singleton relator, using `Fin.insertNth` and
`FreeGroup.map g.succAbove`. The file then proves seven theorems, among them
`not_conjecture_iff_counterexample`, `Counterexample.not_conjecture`,
`not_stable_conjecture_iff_counterexample`, `Reachable.stable` and `Conjecture.stable`.

I downloaded the file unchanged, appended seven `#print axioms` commands, and ran `lean` on it
with this VM's toolchain. I verified that it compiles in 1.1 s with no error, that it contains no `sorry`, no `axiom` declaration and no `native_decide`, and that every theorem depends only on
`[propext, Classical.choice, Quot.sound]` (the last one, `Reachable.stable`, only on
`[propext, Quot.sound]`). The file's own `lean-toolchain` asks for `leanprover/lean4:v4.29.1`;
this VM has Lean 4.33.1, and the file compiles there too.

Two comments in the file are mathematical claims that are not proved in the file. One says that
multiplication by an inverse relator and relator permutations are derivable. **Not verified** by
me; I did not search for derivations. The other says that the `i ≠ j` guard excludes squaring a
relator, which need not preserve the presented group. That statement is correct, and it is the
kind of detail that a formal statement has to get right.

### 5.2 A Lean formalization from the reinforcement-learning side

Zhang, Zhao, Joseph George, Gukov and Anandkumar, "Mathematical Discovery and Formalization
Towards the AC Conjecture", NeurIPS 2025 Workshop on Mathematical Reasoning and AI.
I verified the bibliographic item from three independent listings (the LeanDojo project page,
the Caltech publication list of A. Anandkumar, and the first author's blog post), which agree on
title, authors, venue and year. I did not find an archival version or a DOI.

The extended report, "AI-Driven Mathematical Discovery for the Andrews–Curtis Conjecture" by
Zhang, Zhou, Joseph George, Gukov and Anandkumar, is posted at
`https://carolinezhang1.github.io/pdfs/AC_math_discovery.pdf`. I verified from that PDF that the authors formalize the conjecture in Lean, that they build a deterministic autoformalizer called ACC which turns a proposed trivialization path into a Lean-checked proof, and that their reinforcement learning agents "solved 753 presentations belonging to the Miller–Schupp (MS) family". A blog
post by one of the authors describes the formalization as covering free words, presentations, a
rank-two computational move relation, the general rank move relation, and stabilization, with a
proved translation from the rank-two relation into the general one. The 753 figure, the Lean development itself and the proved translation are not verified, because the repository is described as not yet released. The two documents differ in one author's name (Aaron Zhao in the
workshop listing, Aaron Zhou in the extended report); I could not resolve that.

### 5.3 Machine-checkable certificates at length 14

J. Carreras, "Machine-checkable equivalence certificates at the length-14 Andrews-Curtis
frontier", arXiv:2607.23611 (2026-07-26). I verified from the arXiv API record and the abstract that the paper states four explicit AC-equivalences among six hard rank-two presentations at total
relator length 14, with certificates "replayable in under a second by a small dependency-free
verifier", of lengths 36, 85, 66 and 13 moves, and a minimax analysis of a substitution-move
graph. The item is a single-author preprint that I did not find refereed. The certificates, which I did not download or replay, and the minimax distances are not verified.

### 5.4 What exists in the main libraries

Locally I verified that the installed Mathlib (Lean 4.33.1) contains no file that mentions
"Andrews" or "Curtis", so the conjecture is not formalized in Mathlib. Commands:
`grep -ril "andrews" /opt/mathlib/Mathlib --include=*.lean` and the same for "curtis", both with
no output. I did not search the Isabelle Archive of Formal Proofs, the Coq library or Mizar for this note, so I make no claim about them.

An API query on 2026-11-04 verified that a GitHub search for repositories named or described "Andrews-Curtis" returns 27 repositories, of which the official competition repository is one and
at least eleven were created or last pushed in 2026. This is the shape of the field at the moment. Many artifacts now appear quickly and most of them are unreviewed, so the referee's work shifts from finding certificates to replaying them.

## 6. What automated reasoning can and cannot establish here (Argument)

This section is my own assessment and is not machine-checked. A found move sequence is a certificate. It can be replayed independently, as in section 3, and
its correctness does not depend on the prover that found it or on the search heuristics. A failed
search proves nothing, because the search space at rank 2 already contains words of unbounded
length, and no completeness argument is available. I know of no decidability result for AC
reachability at a fixed rank, and the results reported in the literature are all of the form
"this presentation is trivializable", never "this presentation is not".

A finite countermodel is a genuine negative result, but its scope is exactly the equational
theory it models. The countermodels of section 4 refute derivability in the AC axioms extended by
automorphism moves, and they do so only because the presentations involved have non-trivial
groups. Lisitsa states that the same technique cannot work for a balanced presentation of the
trivial group. So automation has produced one clean negative theorem, about a subsystem of the
move set and about presentations of non-trivial groups, and no negative result about the
conjecture itself.

The stable move set is a different matter. Lisitsa writes in the 2025 paper that both the
Shehper et al. search and his own work establish the stable result by searching non-stable
transformations, and that he is "not aware of any computational approach that can directly
search for stable AC-transformations". That is a precise gap, and it is a good target for a
later round of this campaign.

The practical role of automated theorem proving here is to generate certificates that are longer
than the ones specialized searches find. Lisitsa reports that his extracted sequences are longer
than the 53-move sequence of Shehper et al. and that he could not settle whether 53 is optimal,
The value of the method therefore lies in coverage of cases and in independently checkable certificates.

## 7. What I could not verify

- The bodies of the ICMS 2018 paper, the LPAR 2024 paper and the Journal of Automated Reasoning
  2026 paper. For these I verified the bibliographic record and, where available, the abstract.
- The TinyToCS 2013 item itself; I have it only from the author's page and his reference list.
- The stable-triviality of `P`, which is the other leg of the `AK(3)` argument, and hence the
  stable-triviality of `AK(3)`.
- The triviality of the groups presented by `P` and by `AK(3)`.
- The 53-move sequence of Shehper et al., the 753 Miller–Schupp trivializations of Zhang et al.,
  the certificates of Carreras, and the Lean development of Zhang et al.
- The contents of the Zenodo archives `PU-cases.zip`, `countermodels.zip` (beyond the two
  algebras reprinted in the appendix, which I did check) and the 2025 supplementary data.
- Whether Lisitsa's extraction of move sequences from Prover9 proofs is automatic.
- The claim in the SAIR Lean file that relator permutations are derivable by AC moves.
- Any formalization of the conjecture outside Lean. I searched arXiv and GitHub and grepped
  Mathlib, and I did not search the Isabelle Archive of Formal Proofs, Coq or Mizar.

## 8. Reproduction

All commands below run in the repository root on 2026-11-04 with Lean 4.33.1 and Python 3. Both scripts are self-contained and exit with status 0 only when every check passes.

```
python3 survey/automated_check.py                # replay of the two published AC sequences
python3 survey/automated_countermodel_check.py   # brute-force check of the two finite algebras
```

The Lean statement file is checked with the following commands. The `printf` line appends seven axiom queries to the downloaded file.

```
curl -sL https://raw.githubusercontent.com/SAIRcompetition/Andrews-Curtis/main/competition/tools/lean/AC.lean -o ac_sair.lean
printf '\n#print axioms AC.not_conjecture_iff_counterexample\n#print axioms AC.Counterexample.not_conjecture\n#print axioms AC.not_stable_conjecture_iff_counterexample\n#print axioms AC.StableCounterexample.not_stable_conjecture\n#print axioms AC.Reachable.stable\n#print axioms AC.Conjecture.stable\n#print axioms AC.StableCounterexample.counterexample\n' >> ac_sair.lean
lean ac_sair.lean
```

The output consists of one line per theorem, in the form shown below. Each line names the theorem and the axioms it depends on.

```
'AC.Conjecture.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For the arXiv census quoted in section 5.4 and for the metadata above, the arXiv API queries were
`https://export.arxiv.org/api/query?search_query=all:%22Andrews-Curtis%22&max_results=100` (46
items on 2026-11-04) and `id_list=2501.18601,2607.23611,2408.15332,1609.00325,2102.03212,2506.23031`.
Metadata for the DOIs was read from the Crossref and OpenAlex APIs, and the Zenodo records from
the Zenodo API.
