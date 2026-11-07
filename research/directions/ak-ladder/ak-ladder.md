# The AK(n) ladder: local minima, certified length reductions, and a proof gap

Direction: m3, Round 2, swarm smw2i9i4j. Registered direction d10, "the AK(n) ladder".
Date of this note: 2026-11-04.

Nothing in this note proves or disproves the Andrews-Curtis conjecture, and no rung
of the ladder is claimed AC-trivial except the two that were already known. The two
positive results are a theorem about all rungs (Section 3) and explicit AC
certificates for the length-(n+11) equivalences of Shehper et al. for small n
(Section 5). The one negative result about the literature is a proof gap that does
not affect the verified statements (Section 6).

## 1. What was asked, and what the ladder turned out to allow

The direction I registered asked to decide AC-triviality of AK(n) for n = 3, ..., 8
by constructing certificates. That is not decidable with the resources here, and it
is not decided in the literature either. The text of the ladder family is

    AK(n) = < x, y | x y x = y x y,  x^n = y^(n+1) >                (Akbulut, Kirby 1985)

with relator tuple (x y x y^-1 x^-1 y^-1, x^n y^-(n+1)) and total relator length
2n+7. Akbulut and Kirby listed AK(3) as a potential counterexample, AK(1) and AK(2)
are AC-trivial, and triviality of AK(n) for n at least 3 is open. The status of the
family in the current literature is recorded in Section 2 with identifiers.

What the ladder does allow, and what this note delivers, is the following.

1. A theorem with no case analysis in n: for every n at least 1, AK(n) is a strict
   local minimum of total relator length under all single AC moves (Section 3).
2. Explicit AC certificates, replayed by two independent arithmetics, for the
   ladder step of Shehper et al. from AK(n) to their length-(n+11) presentation:
   end to end for n = 2, 3, 4, 5, and step by step for the individual lemmas for
   n up to 12 (Sections 4 and 5).
3. A certified length reduction for AK(5): 77 forward moves take the length-17
   presentation AK(5) to a length-16 presentation. This is an independent certificate
   for the reduction that Shehper et al. found with a 20-million-node greedy search.
4. A proof gap in the printed proof of one of the ladder lemmas. The gap does not
   damage the lemmas I certify, and the lemma in question is certified true for
   n = 3, 4, 5 by my own certificates (Section 6).

## 2. Status of each rung, with sources checked against live records

| n | AK(n) length | status |
|---|---|---|
| 1 | 9 | AC-trivial. A 19-move certificate is replayed independently in this directory (`test_acx.py`), from the certificate of Round 1 `directions/ak-status/ak1_certificate.py`. |
| 2 | 11 | AC-trivial. My own 19-move certificate to the standard tuple is in `certs/ak2_to_standard.json` (total length cap 13, search depth 14, 1.3 s); the literature attribution is Miasnikov, as used in Round 1 `survey/computational.md`. |
| 3 | 13 | Open. AK(3) is the shortest potential counterexample in the family. |
| 4..12 | 15..31 | Open. |

The sources, each checked live on 2026-11-04:

- S. Akbulut and R. Kirby, "A potential smooth counterexample in dimension 4 to the
  Poincare conjecture, the Schoenflies conjecture, and the Andrews-Curtis
  conjecture", Topology 24 (1985) 375-390, DOI 10.1016/0040-9383(85)90010-2. Crossref
  record confirms title, authors, journal, volume, pages and year.
- A. D. Myasnikov, A. G. Myasnikov and V. Shpilrain, "On the Andrews-Curtis
  equivalence", Contemporary Mathematics 296 (2002) 183-198, DOI
  10.1090/conm/296/05074. Crossref record confirms the three authors, the page range
  and the year. This is the source whose misprint is the subject of direction E1.
- R. H. Gilman and A. G. Myasnikov, "Andrews-Curtis groups", arXiv:2506.23031. The
  paper states that the presentations AK(n) with n > 2 are still open, and that
  AK(3) is the shortest potential counterexample in total relator length.
- A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu,
  P. Kucharski, Z. Wang and S. Gukov, "What makes math problems hard for
  reinforcement learning: a case study", arXiv:2408.15332. Version 1 was submitted
  27 August 2024 and version 2 on 11 February 2025 (arXiv abstract page, checked
  live). The version 2 abstract claims "the length reducibility of all but two
  presentations in the Akbulut-Kirby series (1981)", which is a statement about
  length, not about AC-triviality.
- D. Panteleev and A. Ushakov, "Conjugacy search problem and the Andrews-Curtis
  conjecture", Groups Complexity Cryptology 11 (2019) 43-60, DOI
  10.1515/gcc-2019-2005. Crossref record confirms title, authors, pages and year.
  This is the source of the relator-length bound 20 quoted by Shehper et al.

## 3. Theorem: every rung is a strict local minimum of total relator length

Write |w| for the length of a reduced word and |P| = |r_1| + ... + |r_n| for the
total relator length of a presentation P.

**Theorem 1.** For every n at least 1, no single Andrews-Curtis move applied to the
tuple of AK(n) lowers the total relator length. That is, AK(n) is a strict local
minimum of |P| under inversions, right multiplications and conjugations.

**Proof.** Put r_1 = x y x y^-1 x^-1 y^-1 and r_2 = x^n y^-(n+1).

(i) Inversion preserves length, so the first move type cannot lower |P|.

(ii) Both r_1 and r_2 are cyclically reduced: r_1 starts with x and ends with y^-1,
and r_2 starts with x and ends with y^-1, so in neither case is the last letter the
inverse of the first. A cyclic conjugate of a cyclically reduced word is cyclically
reduced, so for every word w the conjugate w r_i w^-1 reduces to a word of length at
least |r_i|, since its cyclic reduction is the cyclic word of r_i, which has length
|r_i|. Hence the third move type cannot lower |P|.

(iii) For the second move type the two possible products are r_1 r_2 and r_2 r_1.
The last letter of r_1 is y^-1 and the first letter of r_2 is x, so the product
r_1 r_2 is reduced and has length |r_1| + |r_2|. The last letter of r_2 is y^-1 and
the first letter of r_1 is x, so r_2 r_1 is reduced and has length |r_1| + |r_2|.
Either product strictly increases the total length.

So every single move increases the total length or leaves it unchanged, which is the
claim. Square.

Two remarks. The conjugation step of the argument applies to any tuple whose relators
are cyclically reduced, and it is the only step that needs the specific shape of
AK(n). For the two length-(n+11) presentations of Section 5 both relators are also
cyclically reduced, and their two products were computed to increase the total length
for every n from 2 to 12, so those tuples are strict local minima in that range as
well (last two columns of `ladder_table.txt`). The argument also shows why local
search fails on every rung: a length-reducing walk has to leave the rung through
longer tuples first, and the certificates of Section 5 do exactly that, with the
largest total length on the path recorded in the certificate files.

The theorem is machine-checked for n = 1, ..., 40 with all conjugators of length at
most 4 by `python3 test_acx.py`, which prints

    AK(n) strict local minima for n=1..40, conjugators up to length 4: PASS

The proof above covers every n and every conjugator, so the finite check is a check
of the code, not of the theorem.

## 4. The certificates: what was computed and how

All searches are exhaustive breadth-first searches over the graph whose vertices are
tuples of two reduced words and whose edges are the three AC moves, with two exact
bounds: a cap on the total relator length of every intermediate tuple, and a bound on
the search depth. Conjugators are the reduced words of length at most 2, which are 16
words. Multiplying by r_j^-1 is generated as the three forward moves inv j, mul i j,
inv j. Nothing is randomised, and every successor is generated in a fixed order.

Two searches are used. The forward ball search (`ball.py`) expands all tuples within
the cap. The bidirectional search (`bidir.py`) expands from the start and from the
target at once, which is sound because every AC move is undone by forward moves:
inv(i) is its own inverse, conj(i,w) is undone by conj(i,w^-1), and mul(i,j) is undone
by inv(j), mul(i,j), inv(j).

Every certificate is stored as a JSON file in `certs/` with the start tuple, the
target tuple and the list of move tags. `verify_cert.py` replays each file twice, once
with the tuple arithmetic of `acx.py` and once with sympy free groups, and demands
that both replays end at the recorded target. The current output is

    job                      moves  start  final    max sympy verdict
    ak2_to_standard             19     11      2     13  True PASS
    chain_ak2_to_P2             21     11     13     15  True PASS
    chain_ak3_to_P3             39     13     14     18  True PASS
    chain_ak4_to_P4             56     15     15     23  True PASS
    chain_ak5_to_P5             77     17     16     28  True PASS
    ... (42 certificate files in the current directory, 0 failed)

The column "max" is the largest total relator length met along the certificate. It
shows the mountain pass: AK(5) has length 17, the target has length 16, and no
certificate can stay below 17 on the way, since both ends are local minima by Theorem 1.
The certificate for AK(5) reaches 28 before descending.

## 5. The length-(n+11) presentation of Shehper et al., certified

Shehper et al., arXiv:2408.15332v2, prove (their Theorem t:n+11, Section "Length
reduction for AK(n)"):

> For every n >= 2, AK(n) is AC-equivalent to the presentation
> < x, y | x^-1 y x = x y x^-1 y ,  x y^(n-1) x = y x y >
> of length n+11. This gives reduction in length of AK(n) for all n >= 5.

The same preprint also displays a different presentation of the same length n+11 in
the file `sec/n+11.tex` of the arXiv source, namely
< x, y | y^-1 x^2 y = x y^-1 x ,  y x y = x y^(n-1) x >. Both displays have total
length n+11. I implemented both (`acx.p_form` for the statement of Theorem t:n+11
and `acx.n11` for the other display) and certified:

| claim | n range | result |
|---|---|---|
| their Proposition (Myasnikov, Myasnikov, Shpilrain): AK(n) to MS(n, w_1) | 4..30 | one uniform template of 2n+9 moves, `patterns.py`, integer-exact for every n in the range |
| the same Proposition by search, as an independent check | 2..5 | certificates of 12, 17, 18, 20 forward moves |
| their Theorem t:ms-short, the last step MS(n, w_(n-1)) to the Theorem t:n+11 presentation | 3..30 | one uniform template of 9 moves, `patterns.py` |
| the same last step to the other display, their Lemma in `sec/n+11.tex` | 3..12 | certificates of 11 or 12 forward moves each, all replayed |
| their Theorem t:mswk_wk1: MS(n, w_k) to MS(n, w_(k+1)) | 3, 4, 5, all k | certificates of 13 to 19 forward moves |
| composed: AK(n) to the Theorem t:n+11 presentation | 2, 3, 4, 5 | 21, 39, 56, 77 forward moves, replay ok |
| AK(2) to the standard tuple (the rung is AC-trivial) | 2 | 19 forward moves, total length cap 13, depth 14, replay ok |

The two templates deserve a comment, because they turn two of the paper's lemmas
from statements into uniform constructions. Template A for the Proposition is 2n+9
moves long. Its prefix of nine moves carries the first relator to
x^-(n-1) y^n x^-1 y^-1 x y and the second relator to a cyclic conjugate of its
target x^-1 y^-1 x^-1 y x y. Each of the n-1 repetitions of the block
[multiply relator 1 by relator 2, then conjugate relator 1 by x] removes one of the
n-1 leading letters x^-1 from the first relator and inserts one more y^-1 after the
internal x^-1, so the y^-exponent at the end of the first relator grows from 1 to
n. The three closing moves rotate the first relator into x^-1 y^n x y^-(n+1), the
relator of AK(n), and return the second relator to its target. Template B for the
last step is the same nine moves for every n and contains n nowhere. Both templates
are machine-checked for n up to 30 by `python3 patterns.py`, and the intermediate
words just described, printed by the same script for n = 5, 6, 7, are what make the
template uniform in n. A formal induction for all n is not written out here.

Here w_k = y^-k x^-1 y x y and MS(n,w) = < x, y | x^-1 y^n x = y^(n+1), x = w >, as in
`survey/ak-status.md` section 3.

What this establishes and what it does not. The chain for n = 5 gives an explicit
certificate that AK(5), of length 17, is AC-equivalent to a presentation of length 16,
so AK(5) is length-reducible. The paper reports this reduction as found by greedy
search over 20 million nodes; the certificate here was found by bidirectional search
and is independent of their search. The chains for n = 2, 3, 4 certify the same
equivalence at those rungs, where n+11 is at least 2n+7, so no length reduction
follows. For n = 6 and larger the two ends of the chain are now covered by the
templates, so the only missing link is the middle sequence MS(n, w_1) to
MS(n, w_(n-1)), which is certified here for n = 3, 4, 5 and not found for n = 6
within the box recorded in Section 7.

One consequence that may be useful to the length-14 question (OPEN_QUESTIONS Q2 and
direction E5): the chain for n = 3 exhibits an explicit length-14 presentation of the
trivial group, namely < x, y | x^-1 y x = x y x^-1 y, x y^2 x = y x y >, which is
AC-equivalent to AK(3) by a 39-move certificate. Any classification of length-14
presentations therefore has at least one member of the AK(3) class to account for, and
this one comes with an explicit certificate.

## 6. A proof gap in the printed proof of Theorem t:mswk_wk1

The paper's proof of Theorem t:mswk_wk1 (quoted verbatim from the arXiv source,
`sec/search.tex`) reads, in its essential steps:

> First, note that the first relation in MS(n, w_k) can be rearranged in the following
> three ways: (i) Multiplying by y^(k-n)x from the left and by y^-1 from the right
> gives y^k x y^-1 = y^(k-n) x y^n. (ii) ... (iii) ...
> Now, we can rearrange the second relation to get y^k x y^-1 = x^-1 y x. Substituting
> (i) gives y^(k-n) x y^n = x^-1 y x, ... Finally, substituting (iii) gives
> y^-(k+1) x^-1 y = x y^-1 x^-1, which is equivalent to x = w_(k+1).

What the argument establishes is that the relation x = w_(k+1) is a consequence of the
two relations of MS(n, w_k). That conclusion has no content at the level of
Andrews-Curtis moves, for the following reason. MS(n, w_k) presents the trivial group
(Todd-Coxeter, index 1, for n = 2, ..., 12 in `ladder_table.txt`), so every word in
F_2 is a consequence of its two relators. A derivation that any chosen word is a
consequence therefore holds for every choice of word and cannot separate an
AC-equivalence class from its complement.

The same point can be made move by move, and this is what the paper's own Definition
(Substitution) asks for. The legal one-step substitution at AC level is the following.

**Lemma 2 (substitution).** Let (r_1, ..., r_n) be a relator tuple, let r_i = u b with
u a prefix of a cyclic conjugate of r_i, and let v be a word such that v u^-1 lies in
the normal closure in F_n of { r_j : j different from i }. Then the tuple obtained
from (r_1, ..., r_n) by replacing r_i with v b is Andrews-Curtis equivalent to it.

**Proof.** Left multiplication of r_i by a product of conjugates of the other relators
is a legal sequence: to replace r_i by t r_i where t = w r_j w^-1, apply conj to
position j by w, conj to position i by t, mul on position i by position j, and conj to
position j by w^-1; the four forward moves restore r_j and replace r_i by t r_i. Give
v u^-1 as a product of conjugates of the r_j with j different from i and insert the
factors in reverse order; the product acts on r_i = u b as (v u^-1)(u b) = v b. Square.

Now test the substitutions of the printed proof against Lemma 2. Their step (i)
rewrites y^k x y^-1 into y^(k-n) x y^n inside the second relator, so u = y^k x y^-1,
v = y^(k-n) x y^n, and the block to be inserted is v u^-1 = y^(k-n) x y^n y x^-1 y^-k,
whose exponent-sum vector is: x-coordinate 1 - 1 = 0; y-coordinate (k-n) + n + 1 - k = 1.
The second relator of MS(n,w_k) is x^-1 y^-k x^-1 y x y, whose exponent-sum vector is
(-1, 2-k), and the first is x^-1 y^n x y^-(n+1), whose vector is (0,-1). Lemma 2 with
i = 2 (the second relator being rewritten) requires the block v u^-1 to lie in the
normal closure of the first relator alone, and every element of that normal closure has
exponent-sum vector (0, m) for an integer m, because conjugation does not change the
exponent-sum vector and products add them. The block has vector (0,1), so it passes this
test. The same test on the first step of the proof of Theorem t:ms-short, where the
block is v u^-1 = x^-1 y x y x^-1 y^-k with vector (-1, 2-k), matches the vector of the
donor relator exactly, and indeed that block is a cyclic conjugate of the donor, which
is why the certificates in Section 5 realize that step in nine moves.

So the exponent-sum test does not by itself refute the individual substitutions of the
printed proof, and I make no claim that the theorem is false. What stands is the first
objection: the printed chain of substitutions is a derivation of consequences, and in a
trivial-group presentation that argument cannot distinguish anything. What is missing
from the preprint is the move-by-move data that Lemma 2 demands, namely, for each
substitution, a factorization of the inserted block into conjugates of the current
relators and the alignment that makes the cancellation happen. My certificates supply
that data for n = 3, 4, 5, and the statement of Theorem t:mswk_wk1 is therefore true at
those rungs.

I record this as a gap in the proof, with the exact point: the proof of Theorem
t:mswk_wk1 in arXiv:2408.15332v2 uses consequence-level reasoning at a place where the
claim is AC-equivalence. The later Lemma on the same page, whose block is a cyclic
conjugate of the donor, does not have this problem, and my nine-move certificates for
n = 2, ..., 12 confirm it.

## 7. Bounded negatives, with the exact bounds

Each entry is an exhaustive statement about a box, not a statement about the whole AC
class. The boxes are: all tuples of total relator length at most the stated cap,
reachable in at most the stated number of moves, with conjugators of length at most 2.

| search | cap | depth | vertices | result |
|---|---|---|---|---|
| AK(3), any shorter tuple | 19 | 20 | 1573202 | none shorter than 13 (`profile_n03.json`) |
| AK(4), any shorter tuple | 19 | 8 | 19914 | none (`profile_n04.json`) |
| AK(5), any shorter tuple | 23 | 18 | 1084907 | none (`anyred.py` run in the log) |
| AK(6), any shorter tuple | 25 | 18 | 1377664 | none |
| MS(n,w_k) to MS(n,w_(k+1)), all n at most 8, k < n-1 | start+2 | 14 | not recorded | no certificate (`run_lemma5.py` log) |
| AK(6) to MS(6,w_1) | 27 | 20 per side | 5 million cap | aborted at the state cap after 589 s |
| MS(6,w_1) to MS(6,w_2) | 28 | 20 per side | box closed | no certificate (330 s; the earlier 5-million-state attempt at cap 25 also found none) |

The AK(6) row is a resource bound: the bidirectional search hit the 5,000,000-state
cap, so nothing is concluded about larger boxes for that step. The MS(6,w_1) row did
close its box, since both frontiers emptied without reaching the state cap. The three
exhaustive "no shorter tuple" rows close their boxes completely as well, since the
frontier emptied and the state count stayed below the cap.

For comparison, the paper reports that the reduction of AK(5) was found by a greedy
search over about 20 million nodes. My lower bound says that no reduction of AK(5) is
visible while every intermediate tuple has total length at most 23, and my certificate
reaches 28 on the way. The gap between 23 and 28 is where the excursion happens.

## 8. Exact commands

    cd directions/ak-ladder
    python3 test_acx.py                       # engine self check and Theorem 1 check
    python3 patterns.py                       # the two move templates, n up to 30
    python3 ladder.py                         # the ladder table, about 0.3 s
    python3 verify_cert.py                    # replays every certificate twice
    python3 compose.py 2 3 4 5                # rebuilds the four composed chains
    python3 run_pattern_chain.py 6 slack=5 depth=20   # the n = 6 attempt of Section 7
    python3 run_lemma5.py 3 4 5 6 7 8         # rebuilds the step certificates (slow)
    python3 anyred.py 5 6                     # the "any shorter tuple" boxes
    python3 profile.py 3 20 2 6 4000000       # the AK(3) box of Section 7

`verify_cert.py` needs sympy. Everything else needs only the Python standard library.
All runs are deterministic.

## 9. What is not established, and what remains uncertain

1. AC-triviality of AK(n) for n at least 3 is not touched. The known status is open,
   and the certificates here do not bear on it.
2. The first step of the chain, their Proposition citing Myasnikov, Myasnikov and
   Shpilrain, and the last step, their Theorem t:ms-short, are both covered by uniform
   templates, verified by machine for n up to 30. Theorem t:n+11 of
   arXiv:2408.15332v2 is certified end to end here for n at most 5 only, because the
   middle sequence is certified for n = 3, 4, 5 and not for n = 6 and beyond. The
   general proof of the middle sequence still rests on the argument of Section 6, and
   the templates for general n rest on the uniformity argument rather than on a formal
   induction written out above.
3. The middle-step searches were run with conjugators of length at most 2. A
   certificate using longer conjugators is not excluded by any row of Section 7.
4. The claim that the printed proof of Theorem t:mswk_wk1 has a gap is an argument
   about the text, supported by a verbatim quotation and by the triviality of the
   presentation computed by Todd-Coxeter. It is not a refutation of the theorem, and
   the theorem is certified true for n = 3, 4, 5.
5. My reading of the source is version 2 of the arXiv e-print, downloaded on
   2026-11-04 from https://arxiv.org/e-print/2408.15332v2. A later version may have
   repaired the proof of Theorem t:mswk_wk1, and any referee should re-read the current
   version before relying on Section 6.

## 10. Files

| file | contents |
|---|---|
| `acx.py` | independent engine: words in F_2, the three moves, verification, AK(n), MS(n,w_k), the two length-(n+11) presentations |
| `test_acx.py` | replays the Round 1 AK(1) certificate and checks Theorem 1 for n at most 40 |
| `ball.py`, `bidir.py` | forward and bidirectional exhaustive searches |
| `jobs.py`, `run_chain.py`, `run_bidir.py`, `run_lemma5.py`, `compose.py` | the searches that produced the certificates |
| `anyred.py`, `profile.py`, `search.py` | the box searches of Section 7 and the earlier beam attempts |
| `patterns.py` | the two uniform move templates and their check for n up to 30 |
| `run_pattern_chain.py` | symbol-free chain assembly for any n, used for the n = 6 attempt |
| `subst.py` | the substitution move of Lemma 2, with the expansion of each substitution into four forward moves |
| `ladder.py`, `ladder_table.txt` | the table of Section 2 and the checks behind it |
| `verify_cert.py` | two-arithmetic replay of every certificate |
| `certs/*.json` | 42 certificates, start tuple, target tuple, move list |
