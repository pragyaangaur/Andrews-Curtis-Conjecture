# Round 8 report: the kernel layer completed, the frontier closed, and the walls measured

Started 2026-11-06 ~05:00 UTC, closed 09:50 UTC on 6 November (four hours and fifty minutes). Swarm smw4i604a, 10 members, **10 accepted after fresh refereeing** — the campaign's first perfect round (one rejection-fix cycle: m1's Theorem 4, where the member's resubmission improved on the coordinator's own proposed fix by exposing it as DP-hard). No drafts, no abandonments.

## What was tried

Ten directions: K1 second referees 7, K2 the 108-row cap-26 box (not taken as registered; the members self-organized onto the other leads), K3 the Q** soundness theorem, K4 Conjecture G, K5 the 50 resisters' nine classes, K6 T=17 at cap 25, K7 the compact closed-set certificates, K8 the Metzler recipe over symbolic parameters, K9 the harvest extended, K10 the invariant layer and the census repair (two members).

## What was proved or delivered, machine-checked

Every entry was rerun by the coordinator.

1. **The wall-avoiding punch route is the Key Step** (m1, K4, after one rejection-fix cycle). Theorem 4': for every KS datum, X₁ → * iff (P) — a wall-avoiding collapse of W with a punch at a facet of c — the (⇐) direction by the transfer, the (⇒) by the cut-at-c construction with the c-shielding argument (no cell of Wall removable while c is present), verified on 133 data. G and E each imply KS unconditionally (no counterexample to either without a KS failure); their converses are open and DP-hard — the exchange principle that would give them implies downward propagation via round 4's Lemma 3. The round-7 Theorem 3 proof gap (Theorem 2 invoked with coface-freeness in W_* rather than W) was found, repaired with the new Lemmas 1-2, and the correction placed in the round-7 record — a gap the coordinator's round-7 refereeing missed, recorded as such. The round-6/7 "strictly narrower" claims corrected with dated notes.
2. **The Metzler recipe as one kernel theorem** (m10, K8). AC8.lean: metzler_recipe (k m t j) (hk : k = 1+t*j) : ∃ ms, replay ms (metz k m 1) = some (metz k m j), a uniform 13+4t+4j-move list (29 at Metzler's own parameters against round 6's 44) — round 7's recorded unformalized statement, with the defeq obstruction dissolved by the one-line `upd` design fix. A further correction to round 6's sketch (the phase-4 block produces an x-containing word) noted dated. [Round-11 correction, 6 November 2026, verified by rerun: the report's remaining [Open] item — that the theorem is for the cyclically shifted relator list, so family_table is not a literal corollary — is CLOSED. A relator transposition is six Q-moves (inv i, mul i j, inv i, mul j i, inv i, lmul i j) and the 3-cycle is two of them, twelve moves; round 8's depth-6 search was one transposition short. metzler_recipe_literal (the recipe in AC7's order, all k = 1+t*j) and family_table_bridged (all fourteen rows) are kernel-checked at .ultramath/smw5ghp91/m4/lean/CycleBridge.lean, check.sh exit 0.]
3. **The Q** soundness theorem** (m7, K3). QSound.lean: checkCert_sound for the Q** layer with QEquiv a group isomorphism of presented groups — and the guard it needs is NOT OPTIONAL: AC5.lean has no i≠j guard on the four diagonal-capable Nielsen moves, and nij 0 0 carries ⟨x|x⟩ (trivial) to ⟨x|x²⟩ (order two), kernel-checked — so no unconditional soundness theorem exists for the layer as shipped. All 48 shipped Q** certificates instantiated as kernel-proved isomorphisms (including Metzler's pair). Round 7's F1 closed in its first half; the second half (Barmak fidelity) sharpened: the diagonal moves are known not group-preserving.
4. **The census repaired** (m6, K10). With dB³ the true boundary: 81,407 genuine KS data (the corrected census, which round 6's enumeration happens to contain entirely), 84,050 invalid — correcting round 7's "165,456" in turn (a wrong-rule datum is still a KS datum if its collapse spared the omitted cells; the correction-to-the-correction placed in cancellation.md). All 81,407 decided: everything collapses, every punchable cell works, 0 E-violations — the corrected punch table is the opposite of round 6's, uniform. The dunce extension: 30,000 data over all 30 disc choices, 0 E-violations; cell-dependence real there and only there (2,079 of 3,412 collapsible data have a failing punch).
5. **The AC-19 peak ledger to length 16** (m3, K9). 11,876 exact peaks (each with a certificate whose peak equals it), 3,491 lower bounds; two independent computations agreeing on all 9,171 rows of length ≤ 15; 11,955 certificates replayed; fourteen kernel-checked (ACPeaks.lean, one per exact peak 3-16). The first exact peaks above length 15 (4,532 at length 16).
6. **The quotient-witness layer** (m4, K10). ACQuot.lean: the Lean layer's first kernel-checked NON-AC-triviality (not_acEquiv_standard_of_witness), 38 instances covering every non-trivial group in the unimodular stratum to length 14; the complete classification (57,727 trivial / 34 = SL(2,5) / 4 infinite); the "23 phenomena" lead shown to have no referent (the true count 38, failure point at length 12); the method blind exactly where the conjecture lives (all 164 resisters trivial).
7. **Second referees 7** (m2, K1). Everything it touched reproduced from independently written engines; two findings, both confirmed by the coordinator's own computations: m9's "exactly the AK(3) boxes" is false as a set statement (the six rows' cap-18 box is a disjoint twin of AK(3)'s, same size and histogram; the boxes merge exactly at cap 19) — noted dated, the peak-19 conclusions unaffected; m5's 39 rows are 39 key classes over 51 data rows (AC19.txt almost entirely duplicated in the extended file) — noted dated.
8. **The compact closed-set certificates** (m8, K7). Three verified checker layers (with chunking); kernel-checked negatives on all sixteen class-C-related rows (eight at cap 16 with 8,880-state closed sets — 4.7× round 7's kernel record; eight at cap 14); the structural theory: closed sets are exactly unions of reachable sets, the component is the minimum certificate, and THE POTENTIAL ROUTE PROVABLY CANNOT BEAT THE CLOSED-SET ROUTE (a monotone potential's sublevel sets are closed, the potential constant on mutually-reachable pairs, so a separating potential must be box-specific). The floor (136,576 states, four distinct sets — confirmed by my run) and the wall (elaborator memory, the cap-17 certificate missing by 1.3×) measured exactly.
9. **Nine new exact closed boxes; all 50 resisters moved** (m5, K5). The largest computations of the campaign: cap 29 (1,714,220,594 states — my semi-external rerun of the cap-27 box exact), cap 28 twice, cap 27 twice, cap 25 thrice, and the 22-block's cap-23 box (697,796,720, my sigma-quotient rerun exact). All 50 at new depth bounds: 4 at ≥ 30, 4 at ≥ 29, 20 at ≥ 26, 22 at ≥ 24. The sigma quotient pays 8× on the 22-block and nothing on the siblings (the four-components gluing — the explanation of the repeated block sizes). The 22-block's cap-26 box measured at ~4×10¹⁰ states: the "largest target" lead unreachable by four orders of magnitude.
10. **T = 17 at cap 25 settled** (m9, K6). The closed cap-25 box of AK(3) traversed (2,913,499,835 orbits, 46 minutes and 5.3 GB via the correct flip quotient — the naive version unsound at 42-vs-84, a sharp catch — and a Bloom filter). Cap 25 adds exactly 31,872 presentations at length 17 (the first growth since cap 23; my set computation exact) but NO new class (all 202 minimal-length-17 forms inside the cap-23 217; my recomputation) — states yes, classes no, the deficit 12 unchanged for representatives ≤ 20, the remainder precisely bounded.

## What was killed or resolved

1. **Round 7's F1** (the Q** layer's missing soundness theorem): closed, with the guard's necessity proved by refutation.
2. **Round 7's unformalized Metzler statement**: closed by AC8.lean.
3. **Round 7's open item T=17 at cap 25**: settled (states yes, classes no, the exact boundary of what remains).
4. **The "potential function" half of the K7 lead**: provably no better than closed sets.
5. **The "largest target" (the 22-block's cap-26 box)**: unreachable, by four orders of magnitude.
6. **The "23 unimodular non-cyclic phenomena" lead**: no referent; the true count 38, all decided.
7. **Round 7's "165,456 invalid census rows"**: corrected to 84,050 (the correction-to-the-correction).
8. **Round 7's Theorem 3 proof**: the gap found and repaired; the record corrected.
9. **m9's "exactly the AK(3) boxes"**: withdrawn (disjoint twins).

## Corrections found

1. cancellation.md: the correction-to-the-correction (84,050, not 165,456).
2. round6-m6.md §5: the phase-4 word (x-containing, not [a⁻ʲ,y]).
3. The round-7 Theorem 3 proof gap (m1's report, dated note).
4. The round-7 "strictly narrower than PTT" claims (both E and G), dated notes.
5. cap25-round7.md: the "exactly the AK(3) boxes" sentence (m2's finding).
6. m5's round-7 report: the 39-rows counting (m2's finding).
7. The coordinator's own exchange-lemma error (in the m1 rejection): recorded in STATE.md and the verdict.

## Process notes

The campaign's first perfect round: ten of ten accepted, in under five hours. The rejection-fix cycle (m1) was the round's most valuable exchange — the member's resubmission caught that the coordinator's proposed fix was itself defective (a false four-line proof of a DP-hard principle), and the record says so. The audit pattern produced three corrections to prior rounds' records (the census count, the AK(3)-boxes sentence, the 39-rows counting) plus two proofs gaps found and repaired. The kernel archive grew from 12 to 16 files (AC8, QSound, ACPeaks, ACQuot, ACClosed, ACKeys, ACTree, ACComponents — the checker layers and both soundness theorems). The strongest single checks of the round: m5's 274,005,520-state semi-external rerun and m9's 7,968-key set difference, both exact on my machine.

## Round 9

Launched at once (~09:55 UTC) — the LAST full round (the campaign ends 8 November; no new directions after 12:00 UTC on 8 November). Leads: the final-report preparation, the length-17 class census at lengths 21-25 (m9's open boundary), the cap-17 closed-set certificate via the sorted-insert route (m8's identified fix), the remaining second-referee coverage, and whatever the round-8 record leaves open.
