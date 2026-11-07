# Round 1 report: map the ground

Started 2026-11-04 18:20 UTC, completed 19:25 UTC. Swarm smw2fzjic, 15 members, all 15 directions accepted after fresh refereeing. One direction (invariants) required one rejection-and-fix cycle. Budget: 2442 of 4500 model calls reserved at close. Full details in REPORT.md; working log in STATE.md.

## What was tried

Eleven surveys (invariants, q-transformations, complexity, computational attacks, Nielsen analogues, topology, automated reasoning, ak-status, special classes, the stable version, bibliography), the Python toolkit, the Lean base file, a bounded annealing experiment, and the open-questions draft. Every deliverable carries a rerunnable check; every citation was verified by the member and spot-checked by the coordinator against live sources.

## What was proved (machine-checked)

1. AK(n) presents the trivial group for every n, in Lean. Check: `lean directions/ak-status/ak_trivial.lean`; axioms propext, Classical.choice, Quot.sound only. Closes the gap that no printed proof for all n was on record.
2. The Lean base file: 42 lemmas, including symmetry of AC-equivalence via a three-move reversal, the exponent-sum span invariant, the AK(3) exponent vectors, and the rank-1 non-equivalence of (x) and (x^2).
3. The Python toolkit: at rank 2 with relators of length at most 4, and at rank 3 with relators of length at most 2, AC-equivalence to the standard presentation is equivalent to unimodularity (2280 and 8112 certificates); all 32040 rank-2 presentations with relators of length at most 5 and unimodular matrix are certified through the length-6 box.
4. A complete census of two-generator balanced presentations at total relator length at most 11: 26182 canonical presentations, 0 unresolved, 1157 certificates at length 10 replayed by an independent checker.
5. Replays of published chains: Miasnikov's AK(2) chain (19 printed steps = 21 elementary moves, peak length 25), Havas-Ramsay's 11, 14 and 32-move chains, Lisitsa's P to AK(3) sequences (70 moves exact; 160 moves after a one-letter correction at step 81), AK(1) in 19 moves, and a deterministic 19-move certificate for a Miller-Schupp presentation.
6. New certified classes: every rank-2 presentation of the trivial group with a relator conjugate to a generator is AC-standard; rank 3 with reduced pair of length at most 13 reduces to the AK(3) frontier.
7. Bounded negatives with exact bounds: AK(3), AK(4) and AK(5) are strict local minima of total length under all single AC moves (proof plus exhaustive check); no improvement in 16 capped annealing runs of 200000 accepted steps; exhaustive to gluing depth 2; a bounded DFS on the sixteen length-12 stragglers.
8. Three independent Todd-Coxeter implementations, GAP and sympy confirm AK-family and Miller-Schupp triviality, superseded by the Lean theorem.

## What was killed

- Every invariant factoring through the normal closure (abelian data, relation module, Fox calculus, Alexander modules, twisted coefficients, finite quotients): constant on the whole class of interest.
- The finite-quotient route, twice over: the invariants survey's Proposition 8 and the BLM Corollary 1.3 census.
- Nielsen and Whitehead subgroup invariants: the conjugation move destroys the generated subgroup (the index-3 dihedral witness, corrected after one rejection).
- Higman and trace invariants: die under conjugation by the commutator identity.
- The BLM abelianisation reduction as a route to the free case: its free case is the classical conjecture itself.
- The unknot-family hope of separating stable from unstable AC: killed in the thesis read by the stable survey, flagged as unrefereed.
- Local and annealing search under total-length caps 20 to 25 on AK(3) to AK(5): no improvement anywhere, with the bounds recorded.

## Corrections to the literature found

1. Lisitsa arXiv:2501.18601, step 81: the printed conjugator ABAbA should be aBAbA.
2. Shehper et al. arXiv:2408.15332 version 2 withdraws the stable-triviality claim for AK(3) after a misprint in MMS 2002; Lisitsa's abstract still asserts it. Coordinator correction recorded in survey/automated.md. Top round-2 priority.
3. BLM Fact 1.2: phi(m)/2 is not an integer at m = 2; the true component count there is 1.
4. Bridson's Fibonacci bound: the sharp value is fib(m+2); his introduction and body print different constants and the proof gives the sharper one.
5. Havas-Ramsay's "L_2(5), the unique perfect group of order 120" is inconsistent: L_2(5) = A_5 has order 60, and the group has order 120, that is SL(2,5).
6. The term "blacklisting" occurs in none of the four primary computational texts.
7. A widely quoted arXiv number for Bridson's lower-bound paper is wrong by two digits.

## Process notes

Replays of published sequences with independent checkers produced the substantive catches. Cross-member consistency (three Todd-Coxeter implementations, the 19-versus-21 step reconciliation) was cheap and strong. The referee caught one arithmetic error and one overstated conclusion; member citation errors were mostly cosmetic. The substantive risks were withdrawn claims and convention mismatches, both caught by verification against live sources.

## Round 2

Ten directions: E1 stable-ak3-referee (top priority), E2 dynnikov-referee, E3 pu-enumeration, E4 ms3-census, E5 c14-frontier, E6 lean-program-2, E7 invariant-ideas, E8 quinn-tqft, E9 certificates-ms-ak, E10 second-referees. Launched 2026-11-04 19:30 UTC.
