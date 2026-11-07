# Round 6 report: the three AC-19 resisters and the census at cap 25

Started 2026-11-05 15:20 UTC, closed 00:30 UTC on 6 November. Swarm smw3ow2dp, 10 members, 7 accepted after fresh refereeing (zero rejection-fix cycles — the first round with none), and three members (m1, m7, m9) whose runs ended at their step budgets with complete deliverables on disk, coordinator-verified where checkable and recorded in that status.

## What was tried

Ten directions: I1 the three AC-19 undecided resisters, I2 the dimension-three cancellation, I3 the cap-25 census, I4 second referees 5, I5 the remaining 58 resisters (folded by its taker into I1's approach), I6 the Metzler stopping point, I7 AK(3)'s Q**-status at rank 3, I8 Lean program 6, I9 the (5,10)-bucket structure, I10 the AC-19/c14 intersection; plus one member's self-registered variant, the live-source citation audit of rounds 1-5.

## What was proved or delivered, machine-checked

Every entry was rerun by the coordinator.

1. **The live-source citation audit of rounds 1-5** (m3). Eighteen external claims re-checked against live primaries: the AC-19 dataset's existence and the three resisters' membership (rows 83135/82633/69815, matching my round-5 verification independently), the Barmak and Fernandez citations verbatim, the Carreras numbers as printed, the Shehper v2 withdrawal, the PU Table 1 reading, the Bridson m=1 failure (machine-checked witness). TWO CORRECTIONS, both confirmed by my own fetches: survey/dynnikov.md section 6.3 is wrong on both number and form (the live PDF's Proposition 4.3, not 4.2, states the Zeeman-implies-AC direction WITH stabilisations, so the charge against Kupers is backwards — withdrawn with a dated note, also fixing the two shifted numberings); and the Lisitsa published-abstract concession is not reproducible from open sources (the arXiv abstract still asserts; the journal page is challenge-blocked — noted in stable-ak3-status.md, the campaign's conclusion now resting on the Shehper v2 withdrawal alone).
2. **The Metzler stopping point removed** (m6). An explicit 44-move Q**-certificate from <x,y | x^5, y^5, [x,y]> to <x,y | x^5, y^5, [x^2,y]>, replaying under five implementations (including GAP, which also confirms both present Z/5 x Z/5). The recipe: generalised prolongation a = x^2 with the defining relator a x^-2, the closed-form telescoping substitution of Lemma 3 (one conjugate per occurrence of x, never a search), the Nielsen move and the deletion. Lemma 2 (no Q-certificate can hold x^5 and y^5 fixed, by the free-product syllable argument in Z/5 * Z/5) explains why the round-4 heuristic was doomed by a theorem. The family generalises (14 instances). The round-4 draft's order-25 slip corrected (the word-problem group is Z/5), its item 5 answered, and its qverify.py sequential-substitution bug found, fixed and validated (latent: no shipped certificate uses swap).
3. **Lean program 6** (m2). AC6.lean (28,333 lines): AC5.lean + AC3.lean verbatim plus all 53 certificate lines of certs_round5/ in the kernel — the eight falls with their presented groups proved trivial, the two merged blocks as single classes, 1,718 per-lemma axiom audits all standard. The full battery (two independent replays, the transcription audit with doctoring controls, the ledger tie, the negative control) passes on my rerun. The count finding: the four named files hold 43 lines (the direction's 44 was a counting-convention slip), and the eight fall starts are not exact signed-permutation images at tuple level, only at class-key level.
4. **The AC-19/c14 intersection** (m10). The intersection rebuilt from scratch: 3,127 rows all found, 0 missing (a completeness check on the census), 3,083 confirmed by certificate replay, 41 of the 44 resisters decided by round-3 certificates. Proposition 1: a class meeting an exhausted cap-C box needs peak at least C+1, so AC-19 membership can never improve a bound. Eleven explicit depth lower bounds on AC-19 rows inside the trio's cap-25 component. The sigma-transport: AC-19 claims all eight rows of the trio's block. The enrichment measurement (4.9e-18 hypergeometric).
5. **The dimension-three cancellation localized** (m8). Theorem A: in every KS datum the two end cells are free on both sides, so X_1 and Z collapse in one step to the same complex — half of round 5's gap closed. Proposition 5: round 5's sufficient condition sharpened to an exact characterisation; the remaining gap is the punch-cell choice (PTT). The negative result: puncturing is cell-dependent (the fan4 datum: 7 punchable, 4 working), so no general puncturing lemma can close PTT. Conjecture E (Z collapsible implies P0 or P1), tested on 165,457 exhaustive KS data and 900 dunce-hat data (89 collapsible, P0 or P1 in every one).
6. **The (5,10)-bucket structure** (m4). The cap-16 census (129,247,304 states, maximum 34 at the (5,11) bucket): M(cap) = 7,8,9,10,11,12,18,23,34 with the maximum from cap 13 on at total length = cap in the bucket (5, C-5) — the (5,10) peak is a cap-indexed instance. The invariant: the count is constant on class groups (9,752 groups in the (5,10) bucket, no group carrying two counts, 16 extremal groups of size 200). The rho symmetry carrying the family to (10,5). The abelian bound tight on 58 of 84 bucket extremals but 1 against 23 at the peak; the finite-quotient bound sound but reaching only 3. Two self-errors recorded and validated.
7. **The symmetry quotient for the Q** box** (m5). Relator order x signed permutations, with the move-set invariance machine-checked (48 x 72 pairs) and the orbit-enumeration lemma proved — completing the T = 15 box round 5 stopped at (1,662,936 presentations in 246 s and 322 MB against round 5's 93,952,409 states at 4.10 GB; the ordered-tuple count 474,824,896). The cap-20 rank-2 box agrees with round 5's 66,996,960 ordered tuples DIGIT FOR DIGIT (my own orbitcount rerun). The rank-4 box adds nothing at rank 2 or 3 (byte-identical dumps); the mixed box (6,162,232) has its rank-2 part byte-identically the rank-2-only Q* box; no target in any box.

Drafts, unsubmitted, coordinator-verified where checkable:

8. **The three AC-19 resisters are AC-trivial** (m1, at .ultramath/smw3ow2dp/m1/report.md). All three settled by certificates to the standard pair with every intermediate of total length at most 26 (231, 245 and 244 moves), and the other five of the block likewise (252 to 283 moves); my reruns replay all 8 certificates with 0 failures under replay14.py, and the assembly and transport scripts rebuild them. If the claim survives round-7 refereeing it gives c(14) at most 20. The peak-26 minimality rests on the cap-25 exhaustion (referee-certified).
9. **Second referees 5** (m7, at .ultramath/smw3ow2dp/m7/referee.md). All six round-5 targets SOUND, with the strongest check the reproduction of all 52,744 values of cost15.txt and all 22,104 of cost13.txt by its own reverse 0-1 BFS (my diff: the values identical). Three of its own bugs found and fixed on the way.
10. **The cap-25 census continuation** (m9, at .ultramath/smw3ow2dp/m9/report.md). The lower bound pushed from 5,222,573,371 to 9,053,333,421 states (a partial set with its exact stopping point), the two round-5 work directories re-encoded key-for-key identically in a compressed format (11.8 GB and 17 GB against 24.5 GB and 42 GB), and class C absent from the partial sets.

## What was killed or resolved

1. **The round-4 Metzler stopping point**: removed by the 44-move certificate and the closed-form substitution lemma.
2. **The Lisitsa published-abstract concession**: not reproducible from open sources; the campaign's stable-status conclusion now rests on the Shehper v2 withdrawal alone.
3. **The Kupers "loose phrasing" charge**: withdrawn — the survey's own citation was wrong on both number and form.
4. **The qverify.py swap bug**: found, fixed, validated; latent (no shipped certificate affected).
5. **The (5,10) peak as a length-5 phenomenon**: refuted — it is the cap-15 instance of a cap-indexed family.
6. **The round-5 rank-3 wall at T=15**: removed by the symmetry quotient (the wall was the size, not the mathematics).

## Corrections found

1. survey/dynnikov.md section 6.3: the Kupers proposition number and form (dated note, with the two shifted numberings).
2. survey/stable-ak3-status.md: the Lisitsa reproducibility (dated note).
3. directions/qdouble-star/m9/round4-m9.md: the order-5 group correction and the Metzler open item's resolution (dated note).
4. The direction's own "44 certificates" count: a counting-convention slip (the files hold 43; 53 with the cluster file) — found by m2 and verified.
5. The coordinator's STATE.md timestamps slipped four times during the round; all corrected visibly in place.

## Process notes

Zero rejection-fix cycles — the first round with none. Three members ended at their step budgets with complete deliverables; all three were coordinator-verified where checkable, following the round-3/4/5 precedent, and m1's draft (the three AC-19 falls) is the round's biggest single result, to be refereed in round 7. The strongest single check of the round is m5's 66,996,960 ordered-tuple agreement — a different engine, data structure and state convention giving the same number to the digit. The citation audit's two corrections show the value of re-checking even the coordinator's own round-1 verifications: the Lisitsa concession can no longer be reproduced, and the campaign's record now says so.

## Round 7

Launched 00:35 UTC on 6 November with the leads: the three AC-19 falls refereed (m1's draft), the remaining 50 undecided resisters, the cap-25 census, second referees 6 (including the round-6 artifacts), the Metzler family in Lean, the PTT question, and whatever the round-6 drafts leave open.
