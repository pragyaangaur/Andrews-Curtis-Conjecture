# Round 2 report: ideate, test, keep or kill

Started 2026-11-04 19:30 UTC, completed 22:30 UTC. Swarm smw2i9i4j, 10 members, 9 accepted after fresh refereeing, one rejection-and-fix cycle (m7's rank-0 boundary), and one member (m3, the AK-ladder) that stopped without submitting but left a substantial draft whose checks rerun; the draft is carried to Round 3 at directions/ak-ladder/.

## What was tried

Ten directions: the stable-ak3 referee (top priority), the Dynnikov referee, the Panteleev-Ushakov style enumeration, the length-14 frontier, Lean program 2, the invariant ideas, the Quinn TQFT question, the MS-to-AK certificates, the second referees, and a member-proposed variant (the AK-ladder) in place of the untaken MS(3,w) census.

## What was proved or delivered, machine-checked

1. **MS(n, w_1) is AC-equivalent to AK(n) for n = 2 to 10** (m9): explicit replayable certificates (4n+3 moves forward, 7n+3 reverse) making Proposition 1.3 of MMS 2002 explicit for the first time; verified by five implementations plus a Lean kernel proof with `#print axioms` reporting no axioms at all; two exact obstructions for k different from 1.
2. **Lean program 2** (m8): AC moves preserve the normal closure, so presenting the trivial group is an AC-invariant; Corollary 7 of the special-classes survey (rank-2, relator conjugate to a generator) and Lemma 8 of the q-transformations survey in AC form, both formalized with exact statement fidelity, standard axioms only.
3. **The length-14 frontier** (m4): the canonical list at total relator length 14 computed for the first time (2,624 after the published pruning); all 54,068 determinant-passing presentations at lengths 12, 13 and 14 classified; 53,840 AC-trivial and 26 AK(3)-equivalence certificates, all 53,866 replayed with 0 failures; 38 proved nontrivial (34 with A5 quotients, 4 with PSL(2,7) quotients, the latter independently verified by the coordinator's own brute-force search over GL(3,2)); 164 resisters with exact bounds; and the step-(D) pruning audit (592 + 648 discards all AC-trivial), which closes Round 1's weakest-link item 3 at these lengths.
4. **The AK(3)-class enumeration** (m5): a complete census of the AC-class of AK(3) inside the total-length box at every cap from 13 to 20; at cap 20, 51,411,456 tuples, 79,680 conjugation classes, 2,967 Panteleev-Ushakov classes; every certificate replayed by two independent checkers (79,680, 0 failed, 4,640,600 moves); the bounded negative that no tuple in the cap-20 box has a relator shorter than 5; and a second PU-class of minimal total length 13, reached in 36 moves. The total-length-capped census is unpublished data.
5. **The Quinn TQFT question answered per characteristic** (m6): in characteristic 0 the required data cannot exist (Etingof-Nikshych-Ostrik), so Quinn's ground field and his R-matrix strategy are impossible; in F_2 the data exist, machine-checked (a two-dimensional Hopf algebra, showing the conditions alone carry no information); in every odd characteristic p at least 5 the categorical data exist (Ver_p^+, machine-checked to p = 13 with the determinant argument covering all odd p); F_3 and Z[i] open; and the detection question is answered negatively for Quinn's framework, since his conditions force semisimplicity and Khovanov-Krushkal-Nicholson 2025 block semisimple theories from separating contractible 2-complexes from a point.
6. **The m3 draft, unsubmitted, coordinator-verified where checkable**: AK(n) is a strict local minimum of total relator length under all single AC moves for every n (draft theorem extending Round 1's finite check); the Shehper ladder chains from AK(n) to the length-(n+11) presentations certified end to end for n = 2 to 5 (for AK(5), 77 moves reducing length 17 to 16, an independent verification of a reduction the authors found by a 20-million-node search); MS(n, w_k) presents the trivial group for n = 2 to 12; and a claimed proof gap in one printed ladder lemma.

## What was killed or resolved

1. **The stable status of AK(3) is definitively unresolved** (m1, top priority): the misprint is one letter in the 13th relator of the MMS 2002 presentation; the chronology is settled (Shehper v1 claimed, Lisitsa's arXiv abstract repeated citing the same source, Shehper v2 withdrew, Lisitsa's published abstract concedes); the P-to-AK(3) leg is sound and independently machine-replayed by us (53 moves).
2. **The Dynnikov preprint is REPORTED, not proved** (m2): the load-bearing step delegates to Matveev 1987 for non-standard polyhedra in one asserted sentence, plus an unjustified minimality step. Two Round 1 flags resolved: the Matveev equivalence is with the stable conjecture (the zbMATH review settles it), and the topology survey's "tension" was a misreading conflating standard with thickenable (corrected with a dated note).
3. **Both invariant proposals killed at exact points** (m7, after one rejection-fix): the winding invariant is undefined on the class at every positive rank (a stably-trivial class meets the cocommutative tuples only in the empty presentation, which carries no winding data), and its general form degenerates to the exponent-sum matrix; a 3-deformation-preserved, 4-deformation-destroyed quantity exists exactly when a counterexample exists, so the search is the problem itself; none exists at relator length at most 11.

## Corrections found

1. Three errors in the Round 1 complexity survey (m10): Bridson's printed Fibonacci bound is false at m = 1 (machine-checked counterexample); the seed relator has length 9, not 8, so the constant 24 is exactly tight; the recommendation to quote the additive constant 1 is backwards and reverses to the body's 3. Dated coordinator notes added at both sites.
2. REPORT.md's item 4 paired the length-11 census figure with the length-10 command (m7's catch); fixed with a dated note.
3. The seed-relator error had survived the coordinator's own Round 1 hand check; recorded as a process lesson.

## Process notes

Replays and independent reconstructions remain the strongest tools. The second-referee direction found real errors in accepted artifacts, including one that passed the coordinator. One member stopped without submitting after about two hours (steps exhausted mid-computation); its draft was verified where checkable and carried to Round 3, which is the honest treatment of unfinished work. The c14 and pu directions ran multi-hour checkpointed searches to completion inside their rounds.

## Round 3

Launched 2026-11-04 22:45 UTC with ten directions: F1 the ak-ladder completion, F2 the stabilization move sets, F3 the Panteleev-Ushakov table gap, F4 the resisters push, F5 Lean program 3, F6 Zeeman positivity, F7 the Q**-equivalence bounded search, F8 the open-questions refresh, F9 second referees 2, F10 the hardness measure.
