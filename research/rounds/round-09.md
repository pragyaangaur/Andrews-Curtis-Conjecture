# Round 9 report: the last full round — the frontier's boundary answered, and the final report begun

Started 2026-11-06 09:52:48 UTC (resumed after a runtime restart at 10:00), closed 18:55:40 UTC on 6 November (nine hours three minutes). [Dated correction, 7 November 2026 ~08:55 UTC, from m3-r13's campaign-close record: this line's first version said "closed 16:20 UTC (six hours and twenty-four minutes)" — a mislabelled estimate; the true end is fixed by the swarm records (the last verdict at 18:55:40) and the filesystem (the last transcript write 18:48:41), as rounds/round-10.md's correction already records.] Swarm smw4sqc1u, 10 members, **10 of 10 accepted** — the campaign's second consecutive perfect round (one direction abandoned with its reason and replaced; the replacement also accepted). Every acceptance by rerun.

## What was tried

Ten directions: L1 the final-report skeleton with its audit spine, L2 the length-21-25 class census, L3 the closed-set encoding fix, L4 second referees 8, L5 the 108-row box reconsidered, L6 the peak ledger to length 17, L7 the leftover-items triage, and three self-registered directions (the Metzler boundary, the constructive geodesic archive, and the witness-side conjugator layer).

## What was proved or delivered, machine-checked

1. **The final report's skeleton, audited** (m1). 616 lines covering all required sections; 42 of 74 ledger entries verified by rerun; 9 defects found (D1-D9) including one substantive (the whitehead run_all.sh not rerunnable from its installed location); 23 Lean files inventoried with live compile results; the ledger consolidated.
2. **The T=17 deficit answered in the positive** (m2). Three PU classes of minimal length 17 not in the campaign's 217 are realised in the closed cap-25 box at lengths 23 and 25 only — the deficit falls from 12 to at most 9. The conjugation-class census (5,237,072 classes from 72 percent of the box) is what made it affordable; the structural finding that the box is NOT closed under cyclic rotation (23.18 percent of the length-17 stratum) explains why classes hide at long representatives.
3. **The peak ledger to length 17** (m3). 27,124 exact peaks among 33,793 rows of length at most 17 (the first at that length: 13,497 of 18,426 at exactly 17); round 8's 3,491 lower-bound rows resolved into 445 at exactly 16, 1,288 at 17, 18 at 18, 1,740 open; two engines agreeing on all 5,426 shared rows; 14 kernel-checked (ACPeaks17.lean).
4. **Second referees 8** (m4). Four round-8 artifacts re-derived: the classification SOUND and complete; the nine boxes with two reproduced exactly; the flip quotient SOUND to cap 22; the peak ledger SOUND but sharpened by 445 rows (m3's cap-16 test applied to the non-length-16 strata); m5's "letter by letter" transfer reasoning FALSE in general (counterexample: conjugating ab by b⁻¹a⁻¹ gives length 4 against endpoints of length 2), replaced by explicit chains making all 50 transfers constructive.
5. **The 108-row box shown VOID** (m5). The cap-26 box of BBAAABa,BBabABA — the round-7 stopping point and round-8 lead — can NEVER be negative: that presentation has AC depth exactly 26 (round 5's certificate, already on the record), so the box contains the standard pair. The exact-depth-26 AC-19 set recounted at 78 classes / 113 rows (the matcher's bitmap undercounting by a factor of ~2). 108 AC-19 rows given explicit peak-26 trivialisations (302-443 moves, both replayers passing). No AC-19 row has a depth lower bound above 26 in the record.
6. **The geodesic certificate archive** (m6). 186,649 shortest AC certificates for every in-ball row of the length-2-to-15 stratum (2,617,043 moves, longest 96, replayed with 0 failures); the first true certificate-length distribution for a whole length; representative-independent negatives (2,180,512 variant keys, 0 hits); the classification at length 15 (129,288 AC-trivial, 84 SL(2,5), 28 PSL(2,7)-surjective, 4,508 undecided); 112 kernel-checked non-trivialities and 6 trivialisations.
7. **The wall-consumption shape settled** (m7). Theorem A (c-shielding, sharp form), Theorem B (three shapes, with the member's own first version refuted by its new cone4 model — the first interior-vertex disc), Theorem C (the 3-cell equivalence), Corollary C2 (a KS failure must eat the ball over a sibling); the non-positive-base census carried to 2,763,107 decided data; the truncation lemma identified as the exchange principle.
8. **The packed encoding** (m8). The elaborator wall removed (5x memory: 1.51 GB against round 8's 7.5 GB for the 136,576-state cap-17 set); the cap-16 negative reproduced from 216 KB of packed data; the new wall measured (kernel reduction at ~26 hours, a factor 10² not 1.3).
9. **The Metzler recipe's boundary** (m9). The 7-move shift theorem (the hypothesis shown NOT necessary); the dihedral group obstruction (kernel-checked, invisible to the campaign's invariant); the k=4 classification (parity, not divisibility); six new recipe instances.
10. **The conjugator layer** (m10). The closed-set model made faithful to AC.lean (applyX_ac, runX_ac); the twelve moves pinned as exactly the length-≤1 conjugator restriction; the transfer theorems (the crude-bound version unconditional, the tight version reduced to the peak lemma LP); two naive proof routes kernel-refuted.

## What was killed or resolved

1. **Round 8's "108-row box" lead**: void (the box contains the standard pair).
2. **Round 7's "39 classes / 51 rows"**: undercounted to 78 / 113.
3. **Round 8's peak ledger**: sharpened by 445 rows.
4. **m5's transfer reasoning**: false in general, replaced constructively.
5. **The T=17 open boundary**: answered in the positive (deficit 12 to at most 9).
6. **The elaborator wall on the cap-17 closed set**: removed by the packed encoding.
7. **The m1 dunce-decision cap** (5 data in round 8): closed (2.76M decided).

## Corrections found

Six corrections to prior rounds' records, all verified by the coordinator's own computations and placed with dated notes: the void box (m5's C1), the 113-row recount (m5's C2), the 445-row sharpening (m4), the transfer sentence (m4), the audit's D1-D9 (m1), and the numerical slips in m7's truncation counts. The coordinator's round-8 exchange-lemma error was caught by the round-8 member's resubmission and recorded.

## Process notes

The second consecutive perfect round. The restart at 10:00 UTC cost four minutes of wall time; the swarm resumed cleanly. The heaviest computations (the 2.1-billion-state class census, the 1.7-billion-state box, the 27,124-peak ledger) all completed within the round. The audit pattern produced its richest haul yet: six corrections across three rounds, plus the campaign's own process lesson (m5's C4: a cross-check against round 5's data would have caught the void box before it was proposed as a target). The kernel archive grew to 21+ files.

## Round 10

Launched at once (~16:25 UTC) — short and consolidation-focused, per the campaign plan. The final report is written on 8 November.
