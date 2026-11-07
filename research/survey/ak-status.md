# The Akbulut-Kirby and Miller-Schupp families: exact status

This file records what is known about two families of balanced presentations of the trivial group, the Akbulut-Kirby family AK(n) and the Miller-Schupp family MS(n,w), and it separates four kinds of statement. The label [V] marks a statement checked by a computation that I ran, with the exact command given in Section 5. The label [L] marks a statement taken from a source whose text I read, with the source in Section 7. The label [A] marks an argument written out here, which a reader can check by hand and which no machine has checked. The label [O] marks a question that the sources state as open. Statements that I could not check are collected in Section 8.

## 1. Summary

| Object | Presents the trivial group? | Andrews-Curtis trivial? |
|---|---|---|
| AK(1) = <x,y \| x = y^2, xyx = yxy> | yes [L], [V] | yes, with an explicit 19-move sequence [V] |
| AK(2) = <x,y \| x^2 = y^3, xyx = yxy> | yes [L], [V] | yes, Miasnikov 1999 found a 21-move sequence [L] |
| AK(3) = <x,y \| x^3 = y^4, xyx = yxy> | yes [L], [V] for all n | open [O], the unique minimal potential counterexample [L] |
| AK(n), n >= 4 | yes [L], [V] for all n | open [O] |
| MS(n,w) with exponent sum of w on x equal to 0 | yes, Miller-Schupp 1999, for every n and w [L], [V] for small instances | open in general [O] |
| MS(1,w) for every w | yes [L] | yes [L] |
| MS(n, y^-1 x y x^-1) for every n | yes [L] | yes, Shehper et al. Theorem B(ii) [L]; automated derivations for n = 3 to 9 are reported [L], see Section 8 |
| MS(2, w_k), w_k = y^-k x^-1 y x y | yes [L] | yes [L] |
| MS(n, w_k) for k in Z and fixed n | yes [L] | AC-equivalent to AK(n) [L], so open for n >= 3 |

The shortest member of the Akbulut-Kirby family, AK(3), has total relator length 13. Every balanced two-generator presentation of the trivial group with total relator length at most 12 is AC-trivial [L], and at total length 13 every such presentation is AC-trivial or AC-equivalent to AK(3) [L]. Nobody has published an AC-trivialization of AK(n) for any n >= 3, and nobody has published a proof that none exists [O].

## 2. The Akbulut-Kirby family

### 2.1 Exact form and the indexing trap

Akbulut and Kirby read off the following presentation from their homotopy 4-sphere X^4 [L, 1985, page 375]: "{x, y | xyx = yxy, x^5 = y^4}". They also remark that their triviality proof "works for the group {x, y | xyx = yxy, x^(n+1) = y^n}". The family used in later work is written with the exponent attached to x as x^n = y^(n+1) [L, Shehper et al. 2024], while Panteleev and Ushakov write the same family as xyx = yxy, x^(n+1) = y^n [L, 2019]. The two writings describe the same presentations after the generators are interchanged, and the index is the same in both, since interchanging x and y turns x^n = y^(n+1) into x^(n+1) = y^n. The presentation actually printed in the 1985 paper is <x,y | xyx = yxy, x^5 = y^4>, which becomes x^4 = y^5 after the generators are interchanged and is therefore AK(4) in the standard indexing, so the example that motivated the family is not its shortest member. In this file AK(n) means

  AK(n) = <x, y | xyx = yxy, x^n = y^(n+1)>,

with relator pair (x^n y^-(n+1), x y x y^-1 x^-1 y^-1) in the free group on x and y.

The total relator length is 2n + 7, because the first relator has length 2n + 1 and the second relator has length 6 [V by arithmetic, and this value is stated in Shehper et al. 2024]. So the family starts at length 9 for n = 1, 11 for n = 2, 13 for n = 3, and 15 for n = 4, the case printed by Akbulut and Kirby.

### 2.2 The presented group is trivial

Akbulut and Kirby give the argument for their case. Their text reads: "xyx = yxy implies that y = (yx)^-1 x (yx) so y^5 = (yx)^-1 x^5 (yx) = (yx)^-1 y^4 (yx) = x^-1 y^4 x = x^5 = y^4 so y = 1 and x = 1" [L, 1985, page 375]. The same computation works for every n, and here is the general form [A].

Write X and Y for the images of x and y in the presented group. From X Y X = Y X Y one gets Y^-1 X Y = X Y X^-1, because multiplying X Y X = Y X Y on the left by Y^-1 gives Y^-1 X Y X = X Y. Hence Y^-1 X^k Y = X Y^k X^-1 for every k, by induction on k. Take k = n and use X^n = Y^(n+1). The left side is Y^-1 Y^(n+1) Y = Y^(n+1), so Y^(n+1) = X Y^n X^-1, which gives Y^n = X^-1 X^n X = X^n after multiplying on the left by X^-1 and on the right by X. Combining Y^n = X^n with X^n = Y^(n+1) gives Y^n = Y^(n+1), so Y = 1. Then X Y X = Y X Y becomes X X = X, so X = 1.

This argument is now a machine-checked theorem for all n at once [V]. The file `ak_trivial.lean` contains a Lean 4 proof, with `import Mathlib` as its only import, of

  theorem AK.ak_trivial (n : Nat) : Subsingleton (PresentedGroup (AK.akRels n)),

where `AK.akRels n` is the set of the two relators above. The command `lean ak_trivial.lean` reports no error and no warning, and `#print axioms` prints `[propext, Classical.choice, Quot.sound]` for every proven lemma, so there is no `sorry` and no new axiom. The proof does not use `native_decide`. This theorem is about triviality of the presented group, and it says nothing about Andrews-Curtis moves.

Two independent computations agree with the theorem on specific members. A Todd-Coxeter enumeration of cosets of the trivial subgroup closes with one coset for AK(1) using sympy, and for AK(2) using my own enumerator [V]. My own enumerator also closes with one coset for the seven Miller-Schupp instances listed in Section 3.2 [V]. For AK(n) with 3 <= n <= 10 my enumerator did not terminate within 200000 cosets, so those instances are undecided by my computation; the Lean theorem covers them in any case. The failure of the enumerator is a limitation of the tool and is recorded in Section 5.

### 2.3 Which members are AC-trivial, and how far the searches went

AK(1) is AC-trivial, and the certificate here is explicit [V]. The file `ak1_certificate.py` writes down 19 elementary AC moves that carry the relator pair (x y^-2, x y x y^-1 x^-1 y^-1) to (x, y), and it checks each move independently: every step is tested against the definitions of AC1, AC2 and AC3, with the conjugating word for AC3 found by an exhaustive search over words of length at most 8. The script prints `CERTIFICATE OK`. The route substitutes x = y^2 into the second relator one letter at a time, which brings the second relator to y, and then removes y^-2 from the first relator. Shehper et al. state that the case n = 1 is easy to solve in a few steps [L]; I know of no published sequence, and the 19 moves here are not claimed to be shortest.

AK(2) is AC-trivial by Miasnikov [L, 1999]. His abstract states that the conjecture holds for the presentation <x,y | xyx = yxy, x^2 = y^3>, and the body of the paper states that he found "a chain of 21 transformations that reduces the presentation (3) to the trivial presentation", where presentation (3) is this one. The method was a genetic algorithm. Miasnikov also proved that all presentations of the trivial group in the two series (3) and (4) of his paper with total relator length at most 12 satisfy the conjecture, a set he counts as 273 presentations [L].

The rank-2 frontier at length 12 and 13 is settled except at one point. Miasnikov and Myasnikov proved that every balanced presentation of the trivial group on two generators with total relator length at most 12 is AC-trivial [L, 2001]. Havas and Ramsay considered total length 13 by breadth-first search and proved "that, up to equivalence, there is a unique minimum potential counterexample" [L, 2003], and the later literature identifies that presentation as AK(3) [L, Shehper et al. 2024; L, Carreras 2026]. Havas and Ramsay also put the software ACME on their page together with the paper [L].

AK(3) and all higher members are open [O]. The computational record on AK(3) is as follows. Panteleev and Ushakov proved that for n > 2 every automorphism of the free group of rank 2 can be realized by AC-moves on the presentations AK(n), and they used this to "enumerate balanced presentations AC-equivalent to AK(3) with relations of lengths up to 20 (previous record was 17)" [L, 2019]. Their abstract states plainly: "despite a lot of effort we were unable to trivialize any of AK(n)-presentations, for n > 2" [L]. They also report that the row lengths of one of their tables stabilise as a parameter grows, and they read that as support for the common opinion that AK(3) is not AC-trivial; this is a heuristic reading of data, and they do not claim a proof [L].

Shehper et al. obtained the first length reduction inside the family [L, 2024]. They prove that for every n, AK(n) is AC-equivalent to each member of a one-parameter family P(n,k), and that AK(n) is AC-equivalent to the presentation <x,y | x^-1 y x = x y x^-1 y, x y^(n-1) x = y x y> of length n + 11 (Theorem A in the arXiv version, Theorem B in the main text of the proceedings version). Since 2n + 7 is larger than n + 11 exactly when n >= 5, this reduces the length of AK(n) for n >= 5 and gives nothing for n = 3 and n = 4. They state that before their work "it was unknown whether this length can even be reduced using AC moves" [L]. No published work trivializes AK(n) for any n >= 3, and no published work proves that AK(3) is not AC-trivial [O].

The stable version of the conjecture had a false alarm here. The NeurIPS paper by Shehper et al. argued that AK(3) is stably AC-trivial, and the argument rests on a claim about a presentation P taken from a paper of Myasnikov, Myasnikov and Shpilrain (2002) that they cite. The authors later found a misprint in that source and recorded that it "undermines the claim" [L, arXiv:2408.15332, revised text]. Lisitsa then restated the position: after the correction, "the status of AK(3) remains unresolved" in the stable sense, and he presents a reduction of AK(3) to P together with a discussion of what is missing [L, 2025]. The stable question is treated in the file on the stable version of the conjecture, and the only point recorded here is that AK(3) is not known to be stably AC-trivial.

ROUND 2 REFEREE NOTE ON SECTION 2.3, m1, 2026-11-04. I read Shehper et al. version 2, Lisitsa's
preprint and the 2002 source in full, and the paragraph above is confirmed with two
attributions made precise. The quotation "undermines the claim" is accurate, and its exact
form is "This misprint undermines the claim that the presentation (eq:MMS3) is stably AC-trivial", in the
introduction of version 2 and not in its abstract. The quotation "the status of AK(3) remains
unresolved" is from the published abstract in the Journal of Computational Algebra, and the
January 2025 arXiv version does not contain it, since that abstract asserts the stable result
instead; the citation "2025" in the paragraph should therefore name the published version,
whose identifiers are Journal of Computational Algebra 16 (2025) 100041, DOI
10.1016/j.jaca.2025.100041; the OpenAlex record gives 2025-10-15 and Crossref gives the December 2025 issue. Item 13 of Section 7 records
that the journal name could not be confirmed; it is confirmed now, and item 13's description
of the paper as giving an "alternative proof" of stable triviality should be restricted to the
preprint, because the published abstract says that the paper does not establish the stable
AC-triviality of AK(3). The misprint itself is one wrong letter in the 13th relator of the
14-generator Wirtinger presentation, printed as x_13 = x_5 x_12 x_5^{-1} where the diagram
requires x_13 = x_4 x_12 x_4^{-1}, and it is on page 10 of the article. Check:
python3 .ultramath/smw2i9i4j/m1/mms_final_check.py. The full referee report is
survey/stable-ak3-status.md.


## 3. The Miller-Schupp family

### 3.1 Exact form

Miller and Schupp study presentations of the form

  MS(n, w) = <a, b | a^-1 b^n a = b^(n+1), a = w>,

where n > 0 and w is a word in a and b whose exponent sum on a is zero [L, 1999]. A necessary condition for such a presentation to present the trivial group is that the group be perfect, and the condition on the exponent sum is what makes the abelianisation vanish [L, 1999, first page]. In the notation x, y used in Section 2 the relator pair is (x^-1 y^n x y^-(n+1), x^-1 w), and its total length is 2n + 3 + 1 + |w|, so it is 2n + 8 when |w| = 4, which gives 14 for n = 3.

The special word that appears in most later work is w_* = y^-1 x y x^-1 [L, Shehper et al. 2024]. With a and b in place of x and y, MS(n, w_*) has relators a^-1 b^n a b^-(n+1) and a^-1 b^-1 a b a^-1, which is exactly the presentation written out in Lisitsa's second paper [L, 2025].

### 3.2 The presented groups are trivial

Miller and Schupp prove the following [L, 1999, Theorem 1]. Let G be a perfect group generated by two elements a and b which satisfy a^-1 b^n a = b^m with n and m relatively prime and positive. Then G is trivial. Their Corollary 3 states that for any word w with exponent sum zero on a, the presentation <a,b | a^-1 b^n a = b^(n+1), a = w> presents the trivial group. Their Lemma 2 is the core step: for m > n > 0 relatively prime and w of exponent sum zero on a, in the group <a,b | a^-1 b^n a = b^m, a = w> one has a = b^q where q is the exponent sum of w on b, the subgroup generated by b is central, and the group is cyclic of order m - n [L].

The computational check here is partial and is offered as such [V]. My coset enumerator closes with a single coset for MS(n, w_*) with n = 1, 2, 3, 4, 5, 6, and it closes with a single coset for the Miller-Schupp illustration <a,b | a^-1 b a = b^2, b^-1 a b = a^2> that they mention on their first page [V]. It did not decide AK(3), so the enumerator is not a general purpose tool for this family; the point of the run is that it confirms the smallest instances of the theorem exactly.

### 3.3 Which members are AC-trivial, and how far the searches went

The two families meet at one point. Shehper et al. cite a result of Myasnikov, Myasnikov and Shpilrain (2002) that AK(n) is AC-equivalent to MS(n, w_1) for all n >= 2, where w_1 = y^-1 x^-1 y x y [L, as reported in their paper]. This is the case k = 1 of their statement that for each fixed n all the presentations MS(n, w_k) are AC-equivalent, so the citation is a check on the indexing and it does not give a separate route to triviality.

Three infinite subfamilies are AC-trivial, by Shehper et al. [L, 2024, Theorem B]. They are MS(1,w) for every w, MS(n, w_*) for every n > 0, and MS(2, w_k) where w_k = y^-k x^-1 y x y with k in Z. They also prove that for each fixed n all members of the family MS(n, w_k) are AC-equivalent to each other and to AK(n) [L]. That last statement puts the whole family MS(n, w_k) with n >= 3 on the same footing as AK(n), so a proof for one member would settle all of them.

Lisitsa's automated derivations cover the subfamily MS(n, w_*) for small n [L, 2024, 2025]. The 2024 paper announces "previously unknown trivializations" for n = 3, 4, 5, 6, 7, 8 and formulates two conjectures about the shape of the simplification sequences. The 2025 paper announces a derivation for n = 9 whose simplification sequence has 8634 elementary moves, produced by Prover9 in about 74 days and more than 56 GB of memory. A Zentralblatt review of the 2024 paper describes the content as deriving a = b = 1 from the relations, and the reviewer remarks that this triviality can be shown by hand [L]. Since Miller and Schupp already proved triviality for the whole family, the interest of these derivations lies in the sequence, and the review and the abstracts do not settle whether the sequences are sequences of AC-moves or sequences of equational steps in first-order logic. The proceedings version of Shehper et al. describes the same work as "AC-trivializations of MS(n, w_*) for n = 3, 4, 5, 6, 7, 8" obtained by Lisitsa, which supports the first reading, while it is a secondary source. Section 8 records the position, and this file does not count these results as a new theorem about AC-equivalence, because the family is already covered by Theorem B(ii).

Shehper et al. also report a search over the family [L, 2024]. Among the MS(n,w) presentations with n <= 7 and |w| <= 7 there are 1190, and with a limit of one million nodes greedy search solved 533 while breadth-first search solved 278. Greedy search solved every MS presentation of length less than 14, and at length 14 six presentations remained. Four of the six were verified to be AC-equivalent to AK(3), and the other two "could be related neither to AK(3) nor to the trivial presentation through any path involving only presentations with both relators having length less than 20" [L]. Two further presentations solved by their reinforcement learning agent have lengths 17 and 19, with paths of 195 and 381 moves after the removal of subsequences that act trivially [L, Theorem 10].

A 2026 preprint by Carreras claims explicit machine-checkable certificates for four of the length-14 equivalences [L, arXiv:2607.23611]. The abstract states that <x,y | x^-1 y^2 x = y^3, y^-1 x^2 y = x^3> is AC-equivalent to MS(2, y x^2 y^-1 x^-2), that MS(2, y x^2 y x^-2) is AC-equivalent to MS(2, x^-2 y^-1 x^2 y^-1), and that MS(3, y x^2 y) and MS(3, y^-1 x^2 y^-1) are each AC-equivalent to AK(3), with move counts 36, 85, 66 and 13. The paper is a preprint, I have not replayed its certificates, and the presentation <x,y | x^-1 y^2 x = y^3, y^-1 x^2 y = x^3> is described there and in the survey of Burns and Macedonska as an old potential counterexample, credited to Solitar. If the certificates hold, the MS(3) branch of the length-14 frontier is closed in favour of AK(3), and two MS(2) presentations remain unlinked to either side.

## 4. What is not known

The sources state the following questions as open [O]. The first question is whether AK(3) is AC-trivial, and the second is whether AK(n) is AC-trivial for some n >= 4. Because MS(n, w_k) is AC-equivalent to AK(n), the question whether MS(3, w_k) is AC-trivial is the same as the first one. The fourth question is whether the two remaining length-14 MS(2) presentations are AC-trivial. The last question is whether AK(n) and AK(m) are AC-equivalent for some pair with n different from m; I did not find a published answer to it in either direction, so I record only that I did not find one.

Two further gaps are worth naming. No published computation decides the stable status of AK(3), and the only claim in that direction was withdrawn by its authors [L, Section 2.3]. I did not find a published invariant that separates AK(3) from the standard presentation, and the file on invariants treats that question.

## 5. Verification log

The Lean file was checked with

  lean ak_trivial.lean

from the directory that contains it, with Mathlib on `LEAN_PATH`. The command exits with status 0, prints nothing except the `#print axioms` lines, and every line reads `[propext, Classical.choice, Quot.sound]`. The elapsed time was about 3 seconds. The file defines the relators of AK(n), derives x^n = y^(n+1) and xyx = yxy in the presented group, proves y = 1 and x = 1 there, and concludes `Subsingleton (PresentedGroup (AK.akRels n))`.

The coset enumeration was run as

  python3 coset2.py

and it prints a validation block followed by blocks for the families. The validation block contains `<x,y | x, y>` with one coset, the Klein four group with 4 cosets, the cyclic group of order 12 with 12 cosets, the symmetric group on three letters with 6 cosets, and the presentation <x,y | x^2, y^3, (xy)^5> with 60 cosets, all matching the known orders. The infinite presentations <x,y | x^2 = y^3> and the Baumslag-Solitar group BS(1,2) are reported as LIMIT, which is the correct outcome for a non-terminating enumeration. The block for AK(n) reads TRIVIAL for n = 2 and LIMIT for n = 1 and for 3 <= n <= 10. The block for MS(n, w_*) reads TRIVIAL for n = 1 to 6. A run of the whole script takes about 40 seconds.

The independent check of AK(1) uses sympy's own Todd-Coxeter implementation and was run as

  python3 ak_sympy_check.py

which prints `AK(1): order of the presented group = 1` and `AK(1) TRIVIAL` in about 0.3 seconds. The same call for AK(2) raised `RecursionError` under sympy's default limit and did not finish within 200 seconds once the limit was raised, so sympy decides nothing about the other members.

The AK(1) certificate was checked as

  python3 ak1_certificate.py

which prints each of the 19 moves with the relator it acts on, then `reached the standard presentation after 19 moves`, then `CERTIFICATE OK`. The checker tests each step against AC1, AC2 and AC3 independently of the way the sequence was produced.

The bounded search was run as

  python3 ak1_search.py

with relator length at most 10, conjugating words of length at most 2, and a cap of three million states. It completed every layer up to depth 6, which is 2504949 states in total, and was stopped by the three million state cap during depth 7 without finding AK(1). This is consistent with the certificate found by hand, because that sequence passes through a relator of length 13, which the search bound excludes.

## 6. Limitations of the computations in this file

The Todd-Coxeter enumerator is my own code and its correctness rests on the validation block above, not on a proof. A completed enumeration with one coset certifies triviality only if the implementation is correct, and the validation checks five known finite groups and two non-terminating cases. The Lean theorem does not depend on that code, and it is the stronger of the two checks on triviality.

The AK(1) certificate is machine-checked as a sequence of legal AC moves from AK(1) to (x, y), and that is enough to prove that AK(1) is AC-trivial. The other direction, that the sequence is shortest or that no shorter one exists, is not claimed.

The bounded search in `ak1_search.py` is deterministic and gives only negative information within its bounds. It does not bear on any statement about AC-distance in general.

## 7. Sources

The entries below were read in the form indicated, and for each one I note what I checked.

1. J. J. Andrews and M. L. Curtis, "Free groups and handlebodies", Proceedings of the American Mathematical Society 16 (1965) 192-195, DOI 10.1090/S0002-9939-1965-0173241-8. I did not open this paper; the reference and DOI appear in the reference list of Lisitsa 2025, and the paper is cited by Akbulut and Kirby.
2. S. Akbulut and R. Kirby, "A potential smooth counterexample in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the Andrews-Curtis conjecture", Topology 24 (1985) 375-390, DOI 10.1016/0040-9383(85)90010-2. I read the text of the paper, including the presentation, the triviality proof, the remark on the family x^(n+1) = y^n, and the sentence "We do not know whether this presentation, let alone the original one with relations (1) and (2), can be trivialized by Andrews-Curtis moves". The copy I read is a scan whose text layer mangles superscripts, so the exponents in the quoted triviality proof are reconstructed from the arithmetic of the computation.
3. C. F. Miller III and P. E. Schupp, "Some presentations of the trivial group", Contemporary Mathematics 250 (1999) 113-115, DOI 10.1090/conm/250/03848, Zbl 0951.20022. I read the text: Theorem 1, Lemma 2, Corollary 3, and their remark that Havas's coset enumeration programs were used on examples of the family.
4. R. G. Burns and O. Macedonska, "Balanced presentations of the trivial group", Bulletin of the London Mathematical Society 25 (1993) 513-526. I saw this citation in the reference lists of Miller-Schupp 1999 and of the open problem list cited below. I did not read the paper and I did not check its DOI.
5. A. D. Miasnikov, "Genetic algorithms and the Andrews-Curtis conjecture", International Journal of Algebra and Computation 9 (1999) 671-686, DOI 10.1142/S0218196799000370, arXiv:math/0304306. I read the abstract, the statement of Theorem 1, the remark on the 21-step chain for <x,y | xyx = yxy, x^2 = y^3>, and the list of presentations (1) to (4).
6. A. D. Miasnikov and A. G. Myasnikov, "Balanced presentations of the trivial group on two generators and the Andrews-Curtis conjecture", in Groups and Computation III, W. Kantor and A. Seress (eds.), de Gruyter (2001) 257-263, arXiv:math/0304305, DOI 10.48550/arXiv.math/0304305. I read the abstract and the arXiv record, which gives the journal reference and the statement that all balanced two-generator presentations of the trivial group with total relator length at most 12 satisfy the conjecture.
7. G. Havas and C. Ramsay, "Breadth-first search and the Andrews-Curtis conjecture", International Journal of Algebra and Computation 13 (2003) 61-68, DOI 10.1142/S0218196703001365. I read the abstract on the authors' page, including the sentence "We prove that, up to equivalence, there is a unique minimum potential counterexample", and I saw the ACME software page.
8. G. Havas and C. Ramsay, "Andrews-Curtis and Todd-Coxeter proof words", in Groups St Andrews 2001 in Oxford, London Mathematical Society Lecture Note Series 304, Cambridge University Press (2003) 232-237, DOI 10.1017/cbo9780511542770.022. I read the abstract on the authors' page and the DOI in the reference list of Lisitsa 2025.
9. D. Panteleev and A. Ushakov, "Conjugacy search problem and the Andrews-Curtis conjecture", Groups, Complexity, Cryptology 11 (2019) 43-60, DOI 10.1515/gcc-2019-2005, arXiv:1609.00325. I read the abstract, the text of Lemmas 3.4 to 3.6 and Proposition 3.7, the sentence on enumeration of presentations AC-equivalent to AK(3) up to length 20, and the heuristic remark about the stabilising table.
10. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu and others, "What makes math problems hard for reinforcement learning: a case study", in the NeurIPS proceedings, DOI 10.52202/085713-5348, arXiv:2408.15332. The proceedings PDF I read names the 39th conference (2025), while the reference list of Lisitsa 2025 gives 2024 and pages 177669-177702; I did not resolve the discrepancy. I read the abstract, Theorems A to D, Theorem 10, Proposition A.5, the passage on the six length-14 presentations, the passage on the misprint, and the footnote on the cases n = 1 and n = 2.
11. A. Lisitsa, "New Andrews-Curtis trivializations for Miller-Schupp group presentations", Examples and Counterexamples 6 (2024) 100168, DOI 10.1016/j.exco.2024.100168. I read the abstract from the publisher and from the Liverpool repository record, and the Zentralblatt review summary on the MaRDI portal.
12. A. Lisitsa, "Automated theorem proving reveals a lengthy Andrews-Curtis trivialization for a Miller-Schupp trivial group presentation", Examples and Counterexamples (2025) 100201, DOI 10.1016/j.exco.2025.100201. I read the abstract, including the explicit presentation MS_9(w_*), the count of 8634 elementary moves, and the cost of about 74 days and 56 GB, and I read its reference list.
13. A. Lisitsa, "Stable Andrews-Curtis trivialization of AK(3) revisited: a case study using automated deduction" (2025), DOI 10.1016/j.jaca.2025.100041. I read the abstract through a search result and the DOI redirect, which resolves to an Elsevier article with pii S2772827725000129. I did not open the full text and I could not confirm the journal name.
14. J. Carreras, "Machine-checkable equivalence certificates at the length-14 Andrews-Curtis frontier", arXiv:2607.23611, submitted 26 July 2026. I read the abstract and the ancillary file list. This is a preprint, and I did not replay the certificates.
15. J. Swan, G. Ochoa, G. Kendall and M. Edjvet, "Fitness landscapes and the Andrews-Curtis conjecture", International Journal of Algebra and Computation 22 (2012) 1250009, DOI 10.1142/S0218196711006753. I saw this citation only in the reference list of Lisitsa 2025 and I did not read the paper.
16. Myasnikov, Myasnikov and Shpilrain (2002), cited by Shehper et al. as the source of the statement that AK(n) is AC-equivalent to MS(n, w_1) and as the source of the misprint behind the stable AK(3) claim. I did not see this paper and I do not know its title or venue, so I give it only as cited.
17. The problem list "Open problems in combinatorial group theory", posted on the publications page of A. Miasnikov, states that all presentations of the trivial group with total relator length up to 12 satisfy the conjecture, checked with the MAGNUS package, and it lists the Akbulut-Kirby and Miller-Schupp families as sources of potential counterexamples. I read the posted PDF; I did not confirm the author list of the document. It is a problem list and not a refereed paper, so I record it as corroboration of items 5 and 6 rather than as an independent proof.
18. "Automated reasoning boosted by a probabilistic automaton classifier: an application to the Andrews-Curtis conjecture", Journal of Automated Reasoning (2026), DOI 10.1007/s10817-026-09759-8. I read the abstract and the surrounding text through a search result. It states that every balanced presentation of the trivial group with two generators and total relator length up to 13 is AC-equivalent to the trivial presentation or to AK(3), and it states that AK(3) remains unsimplified. I use it as corroboration of item 7 and of the open status, and I did not read the paper in full.

## 8. What I could not verify, and what remains uncertain

The largest uncertainty in this file is the nature of the Lisitsa derivations in items 11 and 12. If they are sequences of AC-moves, they give AC-trivializations of MS(n, w_*) for n = 3 to 9, which is a proper subset of the theorem of Shehper et al. that covers all n. If they are first-order derivations of a = b = 1, they establish triviality of the presented group only, which Miller and Schupp already proved for the whole family. The Zentralblatt review points at the second reading and the proceedings version of Shehper et al. points at the first. I did not read the full text, because it is behind a publisher page, so this file records both readings and counts neither as an independent AC result.

The certificates of item 14 are unchecked here. They are the only source I know for explicit move sequences at the length-14 frontier, and their status is that of a preprint.

The AK(1) certificate gives 19 moves, and I do not know the true AC-distance from the standard presentation to AK(1), nor any lower bound for it. My bounded search was cut off by its state cap during the depth 7 layer, and it could not have passed through the long intermediate relators of the certificate in any case.

Two statements in the literature are quoted here from secondary summaries rather than read in full. The claim that at total length 13 every balanced two-generator trivial-group presentation is AC-trivial or AC-equivalent to AK(3) is stated in the abstract of Havas and Ramsay as uniqueness of the minimum potential counterexample, and the identification of that presentation with AK(3) comes from later papers. The claim that AK(3) is the shortest potential counterexample depends on the length calculation 2n + 7 = 13 for n = 3 together with that uniqueness statement.

The indexing of the family is a real hazard in this literature. Akbulut and Kirby print x^5 = y^4, which is AK(4) in the standard indexing, and some papers write the family as xyx = yxy, x^(n+1) = y^n. The two writings agree on the family and on the index after the generators are interchanged, and this file uses x^n = y^(n+1) throughout. A reader comparing quoted presentations across papers should check the exponent attached to the first generator each time.
