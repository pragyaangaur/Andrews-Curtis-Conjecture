# The Andrews-Curtis campaign: final report

**Campaign.** Twelve rounds of a multi-agent research campaign on the
Andrews-Curtis conjecture and its neighbourhood, 4–8 November 2026, on one 4-CPU
/ 16 GB VM — nine research rounds, the round-10 consolidation, the last research
round 11, and the round-12 finalisation this document was finalised in. **97
accepted reports through round 11** (84 through round 9, four in round 10, nine in
round 11), eight rejection-and-fix cycles (all of them in rounds 1–8), two
abandoned directions (rounds 4 and 9), one recorded runtime restart, an installed
kernel archive of 829 Lean 4 files, and a ledger of 94 results, every one of which
carries a rerunnable check, with round 12's entry 95 folded in as dated notes at
three sites. Nothing here is a claim for or against the
Andrews-Curtis conjecture.

**This document.** The campaign's final report. It was **drafted in round 10** by
member m1 (direction M1) from the round-9 skeleton
(`.ultramath/smw4sqc1u/m1/final-report-draft.md`), the round-9 member reports,
`REPORT.md`'s ledger, `rounds/round-01.md` … `rounds/round-09.md`, `STATE.md`, and
the round-10 checks of section 9 and Appendix C; and it was **finalised in round
12** (swarm `smw5n5txi`, member m1, direction M1) by applying the merged patch list
of round 11 — m1-r11's E1–E14, m7's D1–D12, m3's D-1…D-7 with
`PATCH_FOR_SECTION_8.md`, m2's Q28/Q29, m9's D-m9-1/D-m9-2, m10's
`CORRECTIONS_ADDENDA.md` — to a copy of that draft, and folding in the round-11
results (`REPORT.md` entries 90–94), and, at the delivery's final read,
the round-12 result (entry 95) with six fold-in patches (the change log's delivery
section). The copy is a patch, not a re-derivation:
every replacement is listed with its patch id in the change log delivered beside
this report (`.ultramath/smw5n5txi/m1/CHANGE_LOG.md`), and the whole document is
reproducible as `python3 .ultramath/smw5n5txi/m1/patch.py`. It is a consolidation,
not a new set of mathematical claims: every statement carries a label and a
pointer to the artifact that holds it.

**Cut-off and record states.** Round 9 closed 6 November 18:55:40 UTC, round 10
ran 18:57:12–20:31:24 UTC (the round-10 file's own dated correction; the earlier
session's clock-reads were mislabelled estimates about 2.5 hours off), and round 11
ran ~20:58–23:48 UTC. This document's cut-off is the round-12 finalisation on 7
November, for delivery on the campaign's final day, 8 November. Where a round-10,
round-11 or round-12 item (the referees' verdicts, the rebuilt `OPEN_QUESTIONS.md`,
the corrections log and process record, the consolidated archive, the round-12
per-instance compilation) is another member's direction, this report does **not** report
that item as delivered; it reports only what I checked myself, and it says in
section 5.3 and section 9 what I did not.

**Summary in ten lines.**

1. 97 accepted reports in 11 rounds (84 through round 9, four in round 10, nine in
   round 11), 8 rejection-fix cycles, 2 abandoned directions, 18 carried drafts
   through round 11 (22 at the delivery, §10.1), one recorded runtime restart;
   every acceptance by rerun.
2. The conjecture is untouched — no claim for or against it appears anywhere in the
   campaign's record — but its neighbourhood is now measured.
3. The census: every balanced rank-2 presentation of total length ≤ 11 decided;
   c(13) ≤ 2; c(14) ≤ 20 with 50 presentations left in at most 9 classes.
4. The AK(3) box is exhausted at cap 25: no path from AK(3) to the standard pair
   stays inside total length 25, and class C is absent from every box to cap 24, so
   any path from AK(3) to class C needs an intermediate of length at least 25.
5. The T = 17 PU deficit fell from 12 to **at most 9** in round 9, by three
   minimal-length-17 classes realised only above length 20.
6. The AC-19 peak ledger is decided for every row of length ≤ 17 of its own
   universe: 27 124 exact peaks among 33 793 rows, with every certificate replayed
   and twenty-one of the rows kernel-checked; [r11] one cap up, the length-18
   stratum gives 22 653 exact peaks among 23 322 rows, so the campaign's
   length-at-most-18 ledger is 57 115 rows, 51 499 exact (90.2 %); [r12] a cap-25
   push on the open bucket then took the stratum to 22 920 of 23 322 exact
   (98.28 %) and the ledger to 51 766 of 57 115 (90.63 %), 402 rows left open
   with lower bounds.
7. There is a certificate archive with the true shortest lengths along one
   direction for every row of length ≤ 15: 186 649 geodesic **derivations from the
   standard pair to the row**, 2 617 043 moves, longest 96 (read backwards they are
   trivialisations of at most three times those lengths).
8. The kernel archive is now **one installed tree of 829 Lean files** (37 layer
   files, 776 instance files, 16 closed-set rows), every file rebuilt from source in
   round 11; all **3 140** axiom reports name only
   `{propext, Classical.choice, Quot.sound}`, and so does the round-10 recompile of
   22 of the layer files (931 reports).
9. The walls are measured, not hand-waved: one has been removed (the ~26 h
   kernel reduction for the cap-17 closed set, replaced in round 10 by a 26-minute
   slot-array certificate, entry 88) and one stands (the ~4·10¹⁰-state box for the
   22-block).
10. The frontier is Q1 (is AK(3) AC-trivial), Q24 (the 50 resisters) and Q27 (the
    stable status); the peak lemma LP, which the draft listed fourth, is now a
    kernel theorem in its corrected form (round 11, entry 92).

**Contents.** §0 labels and vocabulary · §1 the campaign at a glance · §2 the method
· §3 results by layer · §4 round 9 · §5 rounds 10, 11 and the round-12
finalisation · §6 corrections (including D1–D9 and the round-11 defect lists) · §7
the open questions · §8 the kernel archive and its exact build · §9 honest limits ·
§10 process record · §11 the frontier · Appendices A (build and rerun), B (the
ledger: 94 rows, with round 12's entry 95 folded in as dated notes), C (the
round-10 and round-12 checks), D (file map).

---

## 0. How to read this report

### 0.1 Labels

The campaign's rule is that nothing counts without a check, and that every claim
carries a label saying what kind of check it has. The labels, from
`OPEN_QUESTIONS.md` section 0, with the two additions the round-9 audit introduced:

| label | meaning |
| --- | --- |
| **SETTLED (kernel)** | Lean 4: file elaborates with `lean`, exit 0, no `sorry`, no new `axiom`, no `native_decide`, and `#print axioms` pasted; the command is given |
| **SETTLED (computation)** | an exact deterministic program with a replayable certificate or an exhausted finite search; command and key output given |
| **ARGUMENT** | a written proof in a repository artifact, not machine-checked |
| **REPORTED** | taken from a source the campaign did not replay (a published claim, or a run whose artifact is not in the tree) |
| **OPEN** | not settled |
| **WITHDRAWN** | a claim the campaign made and then withdrew, with the reason |
| **DEAD END** | a route shown not to work, with the exact failure point |
| **AUDITED (r9)** | the round-9 audit (direction L1) reran the printed command; result in `.ultramath/smw4sqc1u/m1/checks.tsv` |
| **AUDITED (r10)** | I reran it for this report in round 10; command and output in Appendix C / `.ultramath/smw5c6gb0/m1/` |
| **AUDITED (r11)** | a round-11 direction re-derived it with independently written code, or recompiled it from source; its command and output are in that direction's directory (`REPORT.md` entries 90–94) |
| **AUDITED (r12)** | I reran it while finalising this report in round 12; command and output in Appendix C.5 and `.ultramath/smw5n5txi/m1/checks/` |

The label names differ from `OPEN_QUESTIONS.md` section 0, which writes `SETTLED
(machine-checked)` and `SETTLED (verified computation)` for what this report calls
**SETTLED (kernel)** and **SETTLED (computation)**, and which also carries
`VERIFIED-SOURCE` for a live-source check. The mapping is one-to-one except that
`VERIFIED-SOURCE` has no row here: this report writes such a claim as **REPORTED**
with the source named, because a live fetch was not repeated in round 12.

A *bounded negative* is always labelled as such: "no path inside the box" is a
statement about paths whose intermediates stay under a stated total length, never
a statement that no path exists.

### 0.2 Three objects the vocabulary depends on

The campaign works on **balanced presentations of the trivial group** in rank two:
pairs `(r₁, r₂)` of words in `F(x,y)` considered up to the twelve move system
invert a relator; multiply one relator by the other on the right; conjugate a
relator by one of the four letters. The standard pair is `(x, y)`. `AK(n)` is
`⟨x,y ∣ x y x y⁻¹ x⁻¹ y⁻¹, x³ y⁻⁴⟩` and `P(n)`, `MS(n,w)` are the classical
families. A **box at cap `T`** is the set of states reachable from a start
presentation through states of total relator length at most `T`. The **AC depth**
of a presentation is the least peak over its twelve-move trivialisations; the
**peak** of a trivialisation is the largest total relator length along it. A
**PU class** is an equivalence class under relator swap, inversion and conjugation.
`punf` is the campaign's canonical form for it (`directions/cap24/punf.py`).

The reason for this apparatus: the conjecture says `AK(3)` is AC-equivalent to the
standard pair, and no invariant is known. The campaign's strategy was therefore
not to attack the conjecture but to map its neighbourhood exactly — every
presentation below a length, every box below a cap, every certificate — so that
whatever is later proved or refuted has a measured floor under it.

---

## 1. The campaign at a glance

### 1.1 Rounds

| round | window (UTC) | swarm | members | accepted | rejection-fix cycles | carried drafts | duration |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 map the ground | 4 Nov 18:20–19:25 | smw2fzjic | 15 | 15 | 1 (invariants) | 0 | 1 h 05 |
| 2 ideate, keep or kill | 4 Nov 19:30–22:30 | smw2i9i4j | 10 | 9 | 1 (m7 rank-0 boundary) | 1 (m3) | 3 h 00 |
| 3 deepen and extend | 4 Nov 22:30 – 5 Nov 02:30 | smw2opo0o | 10 | 8 | 0 | 2 (m7, m10) | 4 h 00 |
| 4 push the frontier | 5 Nov 02:08–07:15 | smw2woueq | 10 | 8 | 2 (m8, m1) | 2 (m7, m9) | 5 h 07 |
| 5 the frontier narrows | 5 Nov 07:26–14:55 | smw38010i | 10 | 8 | 2 (m9, m6) | 2 (m8, m10) | 7 h 29 |
| 6 three AC-19 resisters, census at cap 25 | 5 Nov 15:20 – 6 Nov 00:30 | smw3ow2dp | 10 | 7 | 0 | 3 (m1, m7, m9) | 9 h 10 |
| 7 AC-19 falls certified, class C resolved | 6 Nov 00:35–04:50 | smw48or9f | 10 | 9 | 1 (m1 Theorem 1) | 1 (m6) | 4 h 15 |
| 8 kernel layer completed, frontier closed | 6 Nov ~05:00–09:50 | smw4i604a | 10 | 10 | 1 (m1 Theorem 4) | 0 | 4 h 50 |
| 9 the last full round | 6 Nov 09:52:48–18:55:40 | smw4sqc1u | 10 | 10 | 0 | 0 | 9 h 03 |
| 10 consolidation | 6 Nov 18:57:12–20:31:24 | smw5c6gb0 | 10 | 4 | 0 | 6 | 1 h 34 |
| 11 the last research round | 6 Nov ~20:58–23:48 | smw5ghp91 | 10 | 9 | 0 | 1 | 2 h 50 |
| 12 finalisation | 7 Nov 00:04:39–03:20:10 | smw5n5txi | 8 | 4 | 0 | 4 | 3 h 15 |

Totals through round 9: **84 accepted reports** (74 ledger entries to the round-8
close, ten round-9 reports), **8 rejection-fix cycles**, **11 carried drafts** (each
coordinator-verified where checkable), **2 directions abandoned, each with its
reason posted and replaced by a direction that reached full acceptance** (round 4;
round 9, m6's d9 replaced by d11). [B1, round 12: the first draft of this sentence
counted 1, contradicting lines 9 and 44 and section 10.3, which all say two.]
Round 9 was the campaign's second consecutive perfect round. [REPORTED: round files;
`STATE.md` line 161 (the entry beginning "ROUND 9 CLOSED"), in the 180-line file of
the round-12 open — cited by its text as well as its line, because the file has grown
once per round and every line number in it drifts (PD-5). The line numbers in this
table are the corrected ones of D9.]

Totals through round 11: **97 accepted reports** (84 + 4 + 9), the same 8
rejection-fix cycles (rounds 10 and 11 had none: the second and third consecutive
rounds without one, the run being rounds 9 to 12), **18 carried drafts** (11 through round 9, six in round 10,
one in round 11), and the three-tier kernel archive installed in `toolkit/lean/`.
Round 10's six drafts and round 11's one were each coordinator-verified where
checkable. The round windows are the corrected ones (round 9's close was 18:55:40
UTC, not the 16:20 the earlier session logged; round 10's own file carries the
dated correction). [REPORTED: `rounds/round-09.md`, `rounds/round-10.md` line 1,
`rounds/round-11.md` line 3.]

Five rounds were financed out of an explicit budget: round 1 closed with 2 442 of
its 4 500 model calls reserved, round 2 was launched with a budget of 3 000, round 9
closed at 2 058 of 3 000, round 10 at 1 213 of 2 400, round 11 at 1 523 of 3 000
(`STATE.md`, `rounds/round-09.md`, `rounds/round-10.md`, `rounds/round-11.md`).
[REPORTED]

### 1.2 What the campaign is not

It does not prove or disprove the Andrews-Curtis conjecture, and **no entry in the
ledger bears on its truth in either direction**. Several results are *about* the
conjecture in the sense that they pin an equivalent formulation of a question
(as class C is AK(3)-equivalent iff AK(3) is AC-trivial) or a bound
("no path inside total length 25"), and the report says so in exactly those terms.
The PU-gap prediction, the Keystone questions and the stable version are reported
as readings of the literature, labelled REPORTED where no live source was checked.

### 1.3 The ledger

`REPORT.md` section 2 holds **94 numbered entries** as of the round-11 close: 1–74
(through round 8), 75–84 (round 9), 85–89 (round 10) and 90–94 (round 11), with no
gap and no duplicate. Each has an author, a file, a check and a label. Appendix B
tabulates 1–74 with the round-10 audit column, and the round-9 reports R1–R10; the
round-10 and round-11 entries 85–94 are tabulated in Appendix B.2. Round 12's
entry 95 is not a row of that table: it is carried as dated notes at three sites
(the executive summary, §3.4 and §5.2's table row 93), and `REPORT.md` numbers it
95. The ledger's entries are *results*, not directions: round 1's 15 accepted directions produced 12
entries, and several entries are drafts.

---

## 2. The method, and what it bought

### 2.1 The four rules and how they were enforced

1. **Nothing counts without a check.** Lean 4 with no `sorry`, no new axiom, no
   `native_decide`, `#print axioms` pasted; or a rerunnable computation with the
   exact command. The round-9 audit re-verified 42 of 74 entries by rerunning their
   printed commands and found nine defects (section 6.4) — two substantive (D3, a
   shipped script that does not rerun from its installed location; D7, a stale
   `OPEN_QUESTIONS.md`), the rest documentation, counting, bookkeeping or resource
   statements.
2. **Every claim carries a label** (section 0.1).
3. **Failures are results**, with the exact failure point: the withdrawn
   collapse-image lemma, the void 108-row box, the transfer sentence, the
   non-rerunnable script, and about a dozen bounded negatives are all on the
   record with their failure points.
4. **No claim for or against the conjecture, ever.** Every report restates this;
   the final report restates it.

Enforcement was the coordinator's and it was substantive: **every accepted report
was rerun before its verdict**, and the round files name which checks were rerun
(e.g. round 8: "m5's 274 005 520-state semi-external rerun and m9's 7 968-key set
difference, both exact on my machine"). [REPORTED]

### 2.2 Second referees

A second-referee direction ran in rounds 2–9, always with independently written
engines and, from round 5 on, before reading the target's write-up. The yield
(section 9.4) is the campaign's clearest methodological result:
**independent reimplementation finds what re-running does not.** Re-running a
command reproduces its number; writing a second engine from the definitions finds
the cases where the number was right and the statement was wrong — the disjoint
twins with the same histogram, the twelve-move scope of a claim printed without its
scope, the bitmap that silently drops seven of every eight records (round 9).

### 2.3 Audits

Two full audits were run: round 7's audit of round 6's disc-model census (which
found the campaign's largest single correction: 165 456 of 165 457 census data not
KS data of the stated framework) and round 9's audit of the whole ledger (42 of 74
entries rerun, 9 defects, the kernel inventory measured live). The pattern is that
an audit can be wrong in both directions: round 8's correction-to-the-correction
revised round 7's revision of the same census (84 050 invalid, not 165 456). This
report therefore carries both corrections with their dates rather than the latest
number alone.

---
## 3. Results, by layer

Each subsection states the result, its label, the check, and the audit status.
Round-9 additions are marked **[r9]**, round-10 checks of mine **[r10]**, round-11
results **[r11]** (each with the coordinator's rerun before acceptance), my round-12
recounts **[r12]** (Appendix C.5), and, at the delivery, m7-r12's cap-25 push
**[r12]** (entry 95, coordinator-rerun).

### 3.1 The kernel archive

**Label: SETTLED (kernel).** Every file in the archive elaborates in Lean 4.33.1
with Mathlib on `LEAN_PATH`, exit 0, with no `sorry`, no `native_decide` in code,
no new `axiom` declaration, and every `#print axioms` line a subset of
`{propext, Classical.choice, Quot.sound}`. **As of round 11 the archive is one
installed tree** — `toolkit/lean/`, 829 Lean files in three tiers (37 layer files,
776 instance files, 16 closed-set rows), every one rebuilt from source in round 11
with all 3 140 axiom reports inside the standard three (section 8.6, entry 94). The
inventory and exact build are sections 8 and Appendix A; the round-10 recompile
table is section 8.2, and the single-command verification is section 8.4.

What the archive certifies, by layer:

- **The AC calculus** (`AC.lean`, `AC2.lean`, `AC3.lean`): AC-equivalence is an
  equivalence relation (symmetry by a three-move reversal), the exponent-sum
  invariant, normal-closure preservation (so presenting the trivial group is
  AC-invariant), the rank-2 conjugate-to-generator theorem, a reusable certificate
  verifier `checkCert_sound` with block composition, and the cocommutativity kill
  in stable and unstable form. [SETTLED (kernel); entries 2, 14, 21]
- **The AK(n) theorem** (`directions/ak-status/ak_trivial.lean`): `AK(n)` presents
  the trivial group for **every** n, by the induction from `xyx = yxy` through
  `y⁻¹xⁿy = x yⁿ x⁻¹`. [SETTLED (kernel); entry 1]
- **The certificate layers** (`AC4.lean`, `AC5.lean`, `AC6.lean`, `AC7.lean`,
  `AC19eleven.lean`, `ACPeaks.lean`, `ACPeaks17.lean` [r9]): several hundred
  kernel-checked certificates — the 98 resister certificates, 21 pairwise merges,
  5 Carreras certificates, the MS(n,w₁) family, the eleven depth-26 AC-19 rows,
  14 exact peaks to length 16, and [r9] seven further rows of length 13–17.
  [SETTLED (kernel); entries 29, 46, 50, 56, 57, 69; r9 m3]
- **The soundness layers**: `checkCert_sound` for the AC format (`AC3.lean`,
  `AC4.lean`) and for the Q** format (`QSound.lean`, **with the `CheckWF` guard**,
  which is not optional: `nij 0 0` carries `⟨x|x⟩` to `⟨x|x²⟩`, kernel-checked).
  [SETTLED (kernel); entry 67]
- **The non-triviality layer** (`ACQuot.lean`): `not_acEquiv_standard_of_witness`
  — the first kernel-checked non-AC-triviality — with 38 instances covering every
  non-trivial group in the unimodular stratum to length 14; [r9] `ACQuot15.lean`
  extends it to 112 non-trivial rows of length 15, and `ACTriv15.lean` gives 6
  kernel replay trivialisations at that length. [SETTLED (kernel); entries 70; r9 m6]
- **The closed-set layer** (`ACClosed.lean`, `ACKeys.lean`, `ACTree.lean`,
  `ACComponents.lean`, `ACBounds.lean`): three chunked checkers plus the structural
  theory — closed sets are exactly unions of reachable sets, the component is the
  minimum certificate, and a monotone potential can provably never beat the
  closed-set route. [r9] `ACPack.lean` replaces the state *listing* by packed
  numerals and builds the lookup tree at check time, with `bmem_bld` (no false
  positives, by induction, no ordering hypothesis) and the transfer theorems
  `packCheck_sound`, `not_reach_of_facts`, `runPack_sound`. [SETTLED (kernel);
  entry 72; r9 m8] **[r10]** `ACSlot.lean` carries the closed set as one static slot
  array of packed numerals (no tree built at check time) and the cap-17 negative
  `Row17.row_T_c17` is kernel-checked at 136 576 states in 26 min (entry 88,
  section 3.9). **[r11]** every one of the seventeen kernel-checked closed-set
  negatives is a **full-conjugator** negative at its cap **by computation**: the
  in-box twelve-move component is closed under conjugation by every word whose
  conjugate stays in the box — 33 297 984 conjugate instances over 56 (row, cap)
  pairs, 0 failures, and 22 849 848 more on AK(3) itself at caps 14–17 (entry 91).
  [SETTLED (kernel); SETTLED (computation) for the upgrade; r10 m10, r11 m2]
- **The bridge and the first exact distance** (`ACBounds.lean`, `ACInstances.lean`,
  round 7): the completeness step a hand-written BFS never proves, plus the census
  row `BAAbABa,BAbABa` with cap-14 distance exactly 6, both halves kernel
  computations. [SETTLED (kernel); entry 59] **[r11]** round 9's "only renaming" gap
  between `ACBounds.lean` and `ACConj.lean` is closed as a theorem: the language
  bridge `fW (ACBounds.red l) = FreeGroup.reduce (fW l)` lets the upgraded negative
  be stated directly on the hypotheses a `closedCheck` certificate supplies
  (`no_XTok_path_of_closed_of_corrected_peak_ACBounds`, entry 92).
- **The negative controls** (`aneg.lean`, `qneg.lean`): 16 single-defect tamperings
  kernel-rejected beside positive controls. [SETTLED (kernel); entry 62]
- **[r9] The conjugator layer** (`ACConj.lean`, `ACConjCex.lean`,
  `ACConjPeak.lean`): `applyX_ac` and `runX_ac` make the engine model faithful to
  `AC.lean` in the positive direction, and `g0_singleton`/`g1_singleton` pin the
  twelve moves as *exactly* the length-≤1 conjugator restriction; the transfer
  theorem `full_conj_mem_of_closed` is unconditional under a crude bound, and the
  tight version is reduced to the peak lemma LP (section 3.7). [SETTLED (kernel);
  r9 m10; my round-10 compile and axiom audit in section 8.2]
- **[r9] The Metzler boundary** (`MetzlerShift.lean`, `MetzlerSharp.lean`,
  `MetzlerRecipes.lean`, `MetzlerSharpBridge.lean`): the 7-move shift
  `metz k m j → metz k m (j+k)` for all parameters, the dihedral obstruction
  `¬ Nonempty (G k m 1 ≃* G k m j)` for even m, k ≥ 3, k ∣ 2j, and the
  classification at k = 4 (section 3.7). [SETTLED (kernel); r9 m9] **[r11]** round
  8's last `[Open]` item on this family is closed: a relator transposition is
  exactly six Q-moves, so the 3-cycle is twelve, and `metzler_recipe_literal`
  (AC7's relator order) and `family_table_bridged` (all fourteen conjuncts of
  `family_table`) are kernel-checked — round 8's depth-6 search was one
  transposition short (section 3.7, entry 92's round-11 record).

### 3.2 The census and the resister ledger

**Label: SETTLED (computation) for the certificates, with the bounds as stated.**

- **Total length ≤ 11**: 26 182 canonical balanced two-generator presentations,
  22 485 nontrivial by the exponent-sum determinant, 3 697 AC-trivial with
  certificates, **0 unresolved** (`OVERALL PASS`). Published Havas-Ramsay
  already covers ≤ 12; the campaign's census is its own. [SETTLED (computation);
  entry 4; AUDITED (r9), the ≤ 10 slice rerun, `OVERALL PASS`]
- **Length 13**: all 14 resisters decided (8 AC-trivial, 6 AK(3)-equivalent), so
  **c(13) ≤ 2** — Havas-Ramsay confirmed by computation. [SETTLED (computation);
  entry 26]
- **Length 14**: 164 resisters (round 2) → 66 (round 4, with the 22-block certified
  as one component) → **c(14) ≤ 28** (round 5: eight resisters fall at peak exactly
  26, three blocks merge) → **c(14) ≤ 20** (round 7, referee-certified: the three
  AC-19 resisters are AC-trivial at peak exactly 26, the block of eight is one
  triviality class, 50 undecided presentations in at most 18 classes) → round 8's
  **nine classes** with all 50 moved to depth ≥ 24/26/29/30 (22 at ≥ 24, 20 at
  ≥ 26, 4 at ≥ 29, 4 at ≥ 30). [SETTLED (computation) for c(14) ≤ 20; entries 26,
  44, 55, 73]
- **The unimodular stratum to length 14 is completely classified**: 57 727
  AC-trivial, 34 presenting SL(2,5), 4 infinite — 57 765 rows in all. The bridge
  through quotient witnesses makes the non-triviality kernel-checked. [SETTLED
  (computation) + SETTLED (kernel) for the 38 witnesses; entries 30, 70, 55]
- The four PSL(2,7)-frontier groups are **infinite** (transitive 28-point action,
  index-28 stabiliser with abelianisation `Z² + Z/2`). [SETTLED (computation);
  entry 30; AUDITED (r9), `sh run_all.sh` exits 0]

### 3.3 The AK(3) class boxes, class C, and the T-deficits

**Label: SETTLED (computation) for each exhausted box; a box statement is a
statement about paths inside the cap.**

| object | size | how | entry | audit |
| --- | --- | --- | --- | --- |
| AK(3) class, cap 20 | 51 411 456 tuples, 79 680 classes | `rawbox.c`, 137 s | 16 | AUDITED (r9): rerun 237 s, class list **byte-identical** (79 681 lines) |
| caps 21 / 22 / 23 | 219 042 976 / 419 826 272 / 1 638 542 144 states | disk-backed, resumable | 35 | not rerun (cost) |
| cap 24 | 3 056 896 064 tuples, 1 596 072 conjugation classes, 131 620 PU classes | batched engine + checksum identity | 45 | not rerun (cost) |
| cap 25 (closed box) | 2 913 499 835 orbits | flip quotient, 46 min, 5.3 GB | 74 | not rerun (cost) |

Consequences as recorded:

- **Class C is absent from every box to cap 24**, so any AC path from AK(3) to
  class C needs an intermediate of total relator length at least 25. [SETTLED
  (computation); entries 35, 45]
- **Class C is AK(3)-equivalent iff AK(3) is AC-trivial** — all sixteen states of
  class C's length-13 level set are AC-trivial, at exact peaks 15 and 18 — so the
  pu-gap prediction *is* the conjecture for AK(3), with no cheaper route. [SETTLED
  (computation); entry 58]
- **T = 16** deficit closes exactly at cap 23 (43 = 86/2, the three missing classes
  identified). [SETTLED (computation); entries 35, 45]
- **T = 17**: deficit 12 at caps 23, 24 and 25 for representatives of length ≤ 20;
  cap 25 adds 31 872 presentations at length 17 and **no new class** ("states yes,
  classes no"). [SETTLED (computation); entry 74]
- **[r9] T = 17 answered in the positive.** A conjugation-class census of the
  closed cap-25 box at lengths 21–25 — 2 099 095 069 inserted states, 5 237 072
  classes (72 % of the box by state count) — yields **220** distinct `punf` forms
  with minimal length 17: the campaign's 217 **plus three new ones**, realised at
  total lengths 23, 23 and 25. So the **deficit falls from 12 to at most 9**, and
  a minimal-length-17 class *can* be realised only above length 20. The three forms
  and their explicit witness states are in `.ultramath/smw4sqc1u/m2/CENSUS25.md`
  §6, whose rendering of F1/F2's first relator drops one inverse: the *codes* are
  authoritative and the exponent-sum determinants are 1, −1, −1 — a dated
  correction placed in that section in round 11 (E13). [SETTLED (computation); r9
  m2. **AUDITED (r10): I reran
  `work/check_three.py`, `OVERALL PASS`** — the three forms are `punf` fixed
  points of minlen 17, absent from the 217, each reproduced by its recorded class
  keys (9/9, 7/7, 4/4) all present in `cls25.bin`, and each realised by an explicit
  box state of total length 23/23/25.]
- **[r11] The w24/w25 key counts decoded — round 8's last open data item closed**
  (entry 90): the two files are cumulative dumps of every state of total length at
  most 17, so the 158 320 by which each exceeds its length-17 stratum is exactly the
  length-13…16 part (1 008 + 3 856 + 64 848 + 88 608 orbits = 633 280 presentations,
  matching round 7's cap-24 per-length counts from an independent engine), and the
  two balls coincide at length ≤ 16. There was no discrepancy, and no computed
  number in the record changes. [SETTLED (computation); r11 m6. **AUDITED (r12)**:
  the reported sums are the record's own (`directions/cap24/cap24.md` prints
  4 032/15 424/259 392/354 432 at total lengths 13–16); I did not re-decode the
  binary dumps.]
- **[r9] Why classes hide at long representatives**: the twelve-move box is **not
  closed under cyclic rotation** — 39 408 of 169 968 length-17 states of `B(17)`
  (23.18 %) have a rotation outside the box, and 131 712 of 704 608 (18.69 %) in
  the length-17 stratum of `B(25)`; the control (single-letter conjugation, which
  *is* a move) shows 0 misses in 20 000 sampled states. Hence no
  conjugation-closure argument can close the T = 17 deficit. [SETTLED
  (computation); r9 m2]

**Honest limit.** The round-9 census is partial: 72 % of the box by state count and
about 96.19 % of the cap-23 classes recovered, so **9 is an upper bound on the
deficit, not its value**; a capture-recapture read suggests ~4 % of classes unseen,
so one or two further new classes would not be surprising. [r9 m2 §7]

### 3.4 The AC-19 peak ledger

**Label: SETTLED (computation) per row, plus kernel-checked exact peaks.**

**One convention, used throughout.** A *row* here is a record of the campaign's
data files (one presentation, written once), and where two files hold the same
presentation it counts twice in a file count and once in a presentation count
(E11). The one place this matters is the depth-26 set of section 3.9: 113 records,
78 distinct rows (35 of them recur in `AC19_extended.txt`), 78 classes.

- Round 8: 11 876 exact peaks to length 16, 3 491 lower bounds, two independent
  computations agreeing on all 9 171 rows of length ≤ 15, 11 955 certificates
  replayed, 14 kernel-checked. [entry 69]
- **[r9] Round 9 extends the ledger to length 17 and decides every row of length
  at most 17 *of `AC19.txt`*, together with the 109 further length-17 rows of the
  other two files** (E12): for the **33 793 distinct rows** of total relator length
  ≤ 17 (33 684 in `AC19.txt` plus 109 further length-17 rows from
  `AC19_extended.txt` and `1190MS.txt`), **27 124 rows have their peak determined
  exactly**, each with a twelve-move certificate whose peak equals it, and
  **6 669 rows are open, every one of them with peak at least 18** (182 with an
  explicit upper bound from round 7's harvest, 6 487 without). All new
  certificates replayed: 15 210 of them (`certs_cap17.txt`), 0 failures.
  [SETTLED (computation); r9 m3. **AUDITED (r10)**: `ledger9.tsv` recounts to
  33 793 rows, 27 124 exact, 6 669 open, every open row with lower bound ≥ 18,
  and `certs_cap17.txt` holds 15 210 certificates with 15 210 distinct starts.]
  The universe's edge, stated once: 273 distinct rows of length ≤ 16 that occur
  only in `AC19_extended.txt`/`1190MS.txt` (all of them in `1190MS.txt`) are outside
  this ledger, so "every row of length at most 17" is true of the ledger's own
  33 793 and not of the campaign's whole data set (E12).
- **The length-17 stratum, entered for the first time**: 13 477 of 18 426 rows have
  peak exactly 17 (73.1 %, the same proportion as at length 16: 4 532 of 6 196), 20
  more have peak exactly 18, so 13 497 have their peak determined exactly and 4 929
  have peak at least 18. [SETTLED (computation); r9 m3; E3, re-derived from the
  ledger itself in round 11.]
- **Round 8's 3 491 lower-bound rows resolve into four classes**: **445 at peak
  exactly 16, 1 288 at exactly 17, 18 at exactly 18**, and **1 740 open** with peak
  at least 18. The 445 is the round-9 referee's sharpening (section 6.3). [SETTLED
  (computation); r9 m3 + m4. **AUDITED (r10)**: the ledger's exact-peak histogram
  has 4 977 rows at peak 16 = 4 532 + 445, and 14 765 at peak 17 = 13 477 + 1 288,
  and 6 669 open = 1 740 + 4 929; all three identities hold exactly.]
- **Kernel**: `ACPeaks17.lean` [r9] = `toolkit/lean/AC3.lean` **verbatim** (the
  first 1 996 lines are byte-identical — checked) plus seven certificates, 86
  moves; it elaborates, exit 0, 90 axiom lines, all standard. [SETTLED (kernel);
  r9 m3. **AUDITED (r10)**: re-elaborated in my directory, exit 0, 91 prints,
  90 axiom lines + one "does not depend", all sets `[propext, Quot.sound]` or
  `[propext, Classical.choice, Quot.sound]`.]
- **Two cap-17 engines agreeing where they overlap**: a breadth-first and a
  length-greedy best-first explorer decided 5 426 rows in common with **0
  disagreements** (3 713 HIT, 1 713 EMPTY); an independent Python box reproduces
  the C engines' sizes exactly on 10 rows (1 372 to 136 576 states). [SETTLED
  (computation); r9 m3]
- **Round 8's own global cap-17 transposed box does not fit on this machine**: two
  OOM kills, the second after 18 minutes at 142 148 420 relator-swap orbits with
  the box still growing. The per-row route decides the whole stratum in 384 s of
  wall time; the rows' own boxes total 108 378 692 states (6 718 EMPTY boxes,
  median 4 400, largest 857 808) while the global box is dominated by the standard
  pair's component. [SETTLED (computation) + a DEAD END for the global route; r9 m3]

- **[r11] The ledger to total length 18** (entry 93): **23 322 distinct rows** of
  the length-18 stratum, **22 653 exact peaks** (97.1 %: 18: 19 265, 19: 2 045, 20:
  526, 21: 703, 22: 114 — the last deeper than any exact peak in the length-≤ 17
  ledger), and **669 open at exact stopping points** (lower bounds 21: 143, 22: 92,
  23: 434). Round 9's open rows were decided one cap up: 1 710 newly exact at cap 18
  and 12 at cap 19, out of 6 669. The combined length-at-most-18 ledger is
  **57 115 rows, 51 499 exact (90.2 %), 5 616 open**. `ACPeaks18.lean` (`AC3.lean`
  verbatim + ten certificates) gives the first kernel-checked exact peaks at length
  18: 93 axiom lines, all standard. [SETTLED (computation) + SETTLED (kernel); r11
  m8. **AUDITED (r12)**: I recounted `ledger18.tsv` (23 322 / 22 653 / the five-cell
  histogram above / the three lower bounds) and `ledger_total_ext.tsv`
  (57 115 / 51 499 / 5 616) directly from the shipped files.]

  **[r12] The cap-25 push on the open bucket** (entry 95): of the 669 open rows,
  **267 are now exact** (122 at peak 21, 14 at 22, 107 at 23, 23 at 24, 1 at 25),
  each with a replayed twelve-move certificate at exactly its peak — all 267
  replay under two replayers and a third independent one with identical
  histograms and 0 failures. The remaining **402 carry lower bounds and nothing
  weaker** (69 at least 26, 100 at least 25, 60 at least 24, the rest 21 to 23;
  173 budget-stopped, 56 cap-25 rows unrun and resumable). The stratum moves to
  **22 920 of 23 322 (98.28 %)** and the ledger to **51 766 of 57 115
  (90.63 %)**. [SETTLED (computation); r12 m7, coordinator-rerun. Entry 93's
  round-11 numbers stand as the round-11 close; these supersede them at the
  delivery.]

**Honest limit.** Nothing is claimed about any row above length 18. `AC19.txt` alone has 83 578
rows of length 19 and `AC19_extended.txt` 15 888 rows of length 20–33; none is
touched, and the 24 rows of length 18 that occur only in `1190MS.txt` are all open.
A peak bound is a statement about paths inside a box, never a non-triviality claim;
the 402 rows still open carry exact stopping points (caps 18–25) — 69 with a lower
bound of at least 26, 100 of at least 25 (56 of them never run at cap 25) — which is
a different kind of statement from an exact peak.

### 3.5 Explicit derivations, certificate algebra, and the geodesic archive

- **Certificate algebra** (round 5): 259 755 stored certificates replayed under one
  dependency-free replay layer, 0 failures; the multiplication-form transports
  (left multiplication in five twelve-move steps, inverse multiplication in three,
  every intermediate at most max(start, end)), which together with round 4's
  conjugator-independence theorem makes every resister bound a full-AC bound at its
  cap. [SETTLED (computation); entry 38]
- **The published chains replay**: Miasnikov's AK(2) chain, Havas-Ramsay's 11-, 14-
  and 32-move chains, Lisitsa's 70-move sequence, and his 160-move sequence after a
  one-letter correction at step 81 (section 6.1). [SETTLED (computation); entry 5;
  AUDITED (r9): both sequences replay]
- **[r9] The geodesic certificate archive.** 186 649 explicit **shortest
  twelve-move derivations from the standard pair to each row** — one for every
  in-ball row of the word stratum of total length 2 to 15 — extracted from one exact
  cap-16 breadth-first search by parent pointers and replayed by an independent
  replayer with 0 failures: 2 617 043 moves, longest 96. The length-15 part alone is
  129 288 certificates and 1 879 510 moves. **The direction matters**: the twelve
  moves are not invertible, so a reversed list is not a twelve-move path; read the
  other way these are AC trivialisations of at most three times those lengths and
  are *not* claimed shortest in that direction (E2: round 11 replayed all 186 649
  lists both ways — 186 649 standard-to-row, one row-to-standard). [SETTLED
  (computation); r9 m6. **AUDITED (r10)**: parsing `certs_inball16.txt` gives
  186 649 certificates, 2 617 043 moves, longest 96, and exactly 129 288
  certificates at total length 15. **AUDITED (r11)**: the direction test, full
  population.]
- **[r9] The first true certificate-length distribution for a whole length**: at
  length 15 the distances run 7 to 96, median 14, mean 14.537, 87.8 % at most 16;
  round 4 had measured the *search-generated* archive at mean 25.68 against a true
  12.17 on the rows it could decide. The distances are the **standard-pair-to-row**
  distances of the cap-16 box, not row-to-standard-pair distances. [SETTLED
  (computation); r9 m6; direction as corrected by E2]
- **[r9] Representative-independent negatives**: for every one of the 5 024
  out-of-ball rows of length ≤ 15, all rotations, both inversions and both relator
  orders are *also* outside the ball — 2 180 512 distinct variant keys, 0 hits.
  Group census at length 15: 84 rows of order 120 (SL(2,5)), 28 surjecting onto
  PSL(2,7), 4 508 presenting the trivial group and **undecided**. [SETTLED
  (computation) for the census; r9 m6]

### 3.6 The topology layer: KS, PTT, downward propagation, wall consumption

**Label: ARGUMENT for the topology done by hand; SETTLED (computation) for the
finite model checks; not rerun in the round-9 or round-10 audits.**

- **Theorem 4'** (round 8, entry 65): for every KS datum, `X₁ → *` iff (P), a
  wall-avoiding collapse of W with a punch at a facet of c; Conjectures G and E each
  imply KS, and their converses are DP-hard (the exchange principle that would give
  them implies downward propagation via round 4's Lemma 3). [ARGUMENT]
- **Downward propagation** (entry 28): reduced to its Key Step; Lemma 1 (χ
  preserved), Corollary 2 (the DP hypothesis forces L contractible), Lemma 4
  (Zeeman ⇒ DP for 2-polyhedra), Lemma 5 (the dimension-2 cancellation principle
  fails). [ARGUMENT]
- **The Key Step, honestly bounded** (entry 40): the false collapse-image lemma
  withdrawn after the campaign's own dunce-hat record refuted it; a KS failure
  gives L contractible, X₁ contractible non-collapsible containing B³, K × I
  collapsible, L × I open; the gap is localized to a dimension-three cancellation.
  [ARGUMENT + bounded computation]
- **The census repaired** (entry 68): with `dB³` the true boundary, **81 407
  genuine KS data** and 84 050 invalid (correcting round 7's 165 456 in turn); all
  81 407 decided — everything collapses, every punchable cell works, 0
  E-violations. [SETTLED (computation)]
- **The invariant layer** (entries 61, 70): wall invariance (`dc ⊆ X₁` in every KS
  datum), the punch-cell law, PTT for wall-avoiding routes, Conjecture G; and the
  quotient-witness layer. **[SETTLED (computation) for the wall check; ARGUMENT for
  the punch-cell law, PTT and Conjecture G]** (D10: the label was missing).
- **[r9] The wall-consumption shape settled** (direction L7):
  - **Theorem A** (c-shielding, sharp form) [ARGUMENT];
  - **Theorem B** [ARGUMENT]: every step of a collapse of W that removes a cell of
    `Wall − S` has exactly one of **three** shapes — (i) sibling step
    `(t′_a × (0,1), a × (0,1))`, (ii) wall descent `(a × (0,1), v × (0,1))` with
    a an interior edge of e², (iii) coface descent `(a × (0,1), v × (0,1))` with a
    not an edge of e². The member's **first version of this theorem claimed two
    shapes and is false**: the new `cone4` model — the first in the record with an
    interior vertex of B² — exhibits 2 steps of shape (iii). [Recorded as a
    self-correction; r9 m7]
  - **Theorem C** [ARGUMENT]: under Proposition 5's condition (a), a cell of
    `Wall − S` is removed **iff** a cell of `B3N = {t × (0,1) : t ∈ B², t ≠ e²}`
    is removed. Hence (P1) becomes the purely 3-cell condition (P1′).
  - **Corollary C2** [ARGUMENT]: a KS failure must eat the ball over a **sibling**
    of e², by one of the three explicitly described pairs — sharpening round 8's
    "must consume `Wall − S`".
  - **Computation**: the classification is checked on every state and every
    collapse step of every box enumerated — M2 (2 states), fan4 (66), fan6 B2=3
    (12 696), fan6 B2=2 adj (156 398), cone4 (11), and the dunce hat at choice 0
    (9 000 007 states, 41 935 037 collapse steps), 0 violations. [SETTLED
    (computation) for the checks]
- **[r9] The non-positive-base census** carried to **2 763 107 decided data** on
  disc choice 0 (49× m6's exhaustive sub-box) plus 183 600 data over all 30
  choices, all decided on Conjecture E's conclusion, 0 counterexamples, 0
  undecided. [SETTLED (computation); r9 m7]

### 3.7 The Q** and Metzler layer

- **Metzler's stopping point removed** (entry 49): an explicit 44-move Q**
  certificate `⟨x,y | x⁵, y⁵, [x,y]⟩ → ⟨x,y | x⁵, y⁵, [x²,y]⟩`, replaying under
  five implementations including GAP. [SETTLED (computation)]
- **The recipe as one kernel theorem** (entry 66): `AC8.metzler_recipe (k m t j)
  (hk : k = 1 + t*j)`, uniform `13 + 4t + 4j` moves, 29 at Metzler's own
  parameters. [SETTLED (kernel)]
- **The relator order bridged** [r11]: round 8 recorded as `[Open]` that
  `AC7.family_table` was not a literal corollary of `AC8.metzler_recipe` because the
  two use different relator orders and "it would need one relator 3-cycle, which I
  did not formalize"; a depth-6 search for that 3-cycle (2.59·10⁶ states) had
  failed. **A relator transposition is exactly six Q-moves**
  (`swapMs i j = [inv i, mul i j, inv i, mul j i, inv i, lmul i j]`), so the 3-cycle
  is twelve, and the search stopped one transposition short:
  `cycle3_q2`/`cycle3inv_q2`, `cycle3_metz`/`cycle3inv_metz`,
  `metzler_recipe_literal` (the recipe in AC7's order, every `k = 1 + t·j`) and
  `family_table_bridged` (all fourteen conjuncts of `family_table`, identical to
  `AC7`'s) are kernel-checked, with an independent Python twin. Relator permutation
  is therefore a derived move of the calculus: any statement stated up to relator
  order can be restated literally at a cost of six moves (twelve for a 3-cycle).
  [SETTLED (kernel); r11 m4; I read `RUN_LOG.txt` (`VERDICT: PASS`) and
  `lean/cyclebridge.build.log`, and did not recompile the file in round 12.]
- **The recipe's boundary mapped** (direction d8):
  - **The shift theorem** [SETTLED (kernel)]: for every k, m, j,
    `metz k m j → metz k m (j + k)` in **7** rank-preserving AC moves. So the
    recipe's hypothesis `j ∣ k − 1` is **sufficient but not necessary**; at k = 4,
    j = 5 is reachable although `5 ∤ 3`.
  - **The obstruction** [SETTLED (kernel)]: for even m, k ≥ 3 and k ∣ 2j, the
    presentations `metz k m 1` and `metz k m j` present **non-isomorphic** groups
    (`metz k m 1` is abelian; `metz k m j` has the dihedral group of order 2k as a
    quotient and is non-abelian). This is not a bounded negative: every AC and
    every admissible Q** move preserves the presented group, so no move list of any
    length joins them.
  - **The classification at k = 4** [SETTLED (kernel)]: `metz 4 m j` is
    AC/Q**-equivalent to `metz 4 m 1` **iff j is odd** (even m). Parity, not
    divisibility — and invisible to the campaign's only implemented invariant,
    since the exponent-sum matrix is the same for all j.
  - **New recipe instances** [SETTLED (kernel)]: six further (k,m,t,j), varying m
    (including m = 1) and taking larger t and j > 2.
  - **Honest limit**: only k = 4 is closed. At k = 5 the residue j ≡ 3 (mod 5) is
    open, and there the two groups are isomorphic so no group invariant can decide
    it.
- **The Q** soundness theorem** (entry 67) with the diagonal-Nielsen refutation is
  section 3.1; the Q** status of AK(3) is bounded: no Q**-trivialisation with rank
  ≤ 3 and total length ≤ 16 (12 853 740 presentations, no target), and the rank-2
  cap-20 Q** box is 66 996 960 ordered tuples in 109 072 classes with no target.
  [SETTLED (computation); entry 64]
- **[r9] The conjugator layer** (direction d10): the closed-set model made faithful
  to `AC.lean` (`applyX_ac`, `runX_ac`), the twelve moves pinned as exactly the
  length-≤1 conjugator restriction, `sim`/`run_sim`/`run_sim_totLen_le` giving an
  explicit twelve-move simulation of a conjugator of any length with intermediate
  bound `|u| + 2|w| + |q|`, and `full_conj_mem_of_closed` making every twelve-move
  closed-set negative a full-conjugator negative **whenever the crude bound fits in
  the box**. The tight version needs the **peak lemma LP**: for **reduced** `u` and
  **reduced** `w`, `(conjW s u).length ≤ max u.length (conjW w u).length` for every
  suffix `s` of `w`. As recorded in round 9, without the reducedness hypothesis it
  is **false** — round 10's `ACConj.peakLemma_false` kernel-checks the
  counterexample u = a, w = b·b⁻¹, s = b⁻¹ (3 > max(1,1) = 1) — and the corrected
  form adds `red w = w`, which is harmless in application (E1). What is proved is
  the reduction (`full_conj_mem_of_closed_of_peak`) and two kernel refutations of
  naive routes (prefix-order simulation fails: conjugating `r = a⁻¹b⁻¹` by the
  prefixes of `w = a⁻¹b⁻¹` passes through a length-4 conjugate while both ends have
  length 2; suffix-order monotonicity fails for a non-cyclically-reduced relator).
  The corrected LP holds on every instance tested: 13 807 989 + 27 522 666
  exhaustive checks, 0 violations. **[r11]** the corrected LP is now a **kernel
  theorem** — `peakLemma_corrected` has no hypothesis on `u` at all, only
  `red w = w`, and the path-level negative
  `no_XTok_path_of_closed_of_corrected_peak_ACBounds` is stated directly on the
  hypotheses a `closedCheck` certificate supplies (36 axiom lines, all standard;
  `stepcheck.py` 234 740 instances and `stmtcheck.py` 430 353 pairs, 0 violations;
  entry 92). **[r11]** independently of LP, the seventeen kernel-checked negatives
  are full-conjugator negatives **by computation** (entry 91, section 3.1). What
  remains is not the lemma but its per-instance instantiation: the eighteen
  closed-set certificates on record are not recompiled with the upgrade — a two-line
  term each — and the S-reducedness of the two slot-array closed sets (caps 16, 17)
  was at the round-11 close verified by rerun for the sixteen tree instances only.
  [r12, delivery update: the S-reducedness of BOTH slot arrays is now verified —
  `check_reduced.py` (m2-r12) decodes all 8 880 cap-16 and 136 576 cap-17 states and
  finds 0 non-reduced, 0 round-trip failures, the cap-16 key set inside the cap-17
  one; coordinator-rerun at the m4-r12 verdict. The per-instance compilation,
  which round 12 left open, is done and was rerun at the delivery: round 13's m6
  recompiled all eighteen upgrade terms from source (the sixteen tree terms plus
  `Upgrade16` and `Upgrade17`) — 18/18 exit 0, 51 axiom lines, every set inside
  `{propext, Classical.choice, Quot.sound}`, and the sixteen tree terms'
  statements checked against the instance rows' own tuples and caps, identical
  in 16 of 16 (evidence: `.ultramath/smw645wry/m6/UPG_COMPILATION.md`,
  coordinator-rerun). The terms remain a member artifact
  (`.ultramath/smw5n5txi/m2/`, importing `LP9`-`LP11` from
  `.ultramath/smw5ghp91/m5/`), not part of the installed tree, so the 829-file
  count does not change.] [SETTLED (kernel) for the layer and for the corrected LP;
  the upgrade SETTLED (computation) for the seventeen; r9 m10, r10 m8, r11 m5,
  r11 m2, r12 m2]

### 3.8 The literature layer

**Label: REPORTED where the campaign checked a live identifier;
REPORTED-and-unverified where it did not. Not rerun in rounds 9 or 10 (no network
read); round 11 checked the metadata of the three load-bearing records against the
arXiv API and confirmed them (AUDITED (r11), m7's N9), and did not open the bodies —
so the withdrawal sentence below still rests on the campaign's own quotation of
`sec/introduction.tex` line 91.**

- **The stable status of AK(3) is unresolved**, and the record now rests on the
  Shehper et al. arXiv:2408.15332 **v2 withdrawal alone**: the round-6 audit
  established that the Lisitsa published-abstract concession is **not reproducible
  from open sources** (entry 48), so the campaign's earlier second leg was
  withdrawn. The misprint is one letter in the 13th relator of the 14-generator
  MMS 2002 presentation and is invisible to every abelian computation.
  [AUDITED (r11)]: `arXiv:2408.15332` is Shehper et al., v1 2024-08-27, **v2
  2025-02-11**, 58 pages, and the *revised abstract carries no withdrawal* — the
  withdrawal is in the body, which is exactly what this report says and what
  `survey/stable-ak3-status.md` quotes (`sec/introduction.tex` line 91, "This
  misprint undermines the claim that (eq:MMS3) is stably AC-trivial"). The Lisitsa
  arXiv v1 abstract (`arXiv:2501.18601`, 2025-01-17) **asserts** the stable result
  and does not concede, so the report's choice to rest the status on the v2
  withdrawal alone is forced by the open record, not a hedge. `arXiv:math/0302080`
  is Myasnikov–Myasnikov–Shpilrain with journal reference Contemp. Math. 296 (2002)
  183–198, letter for letter. Not verified in round 11: the body of v2, the
  published Lisitsa abstract, Kupers' PDF and the Havas-Ramsay page.
- **Lisitsa's 160-move P → AK(3) sequence** has a one-letter typo at step 81
  (printed conjugator `ABAbA`, correct `aBAbA`); with the correction P and AK(3)
  are AC-equivalent by explicit certificate (entry 5).
- **The Panteleev-Ushakov Table 1 counts pairs of length exactly T**, not at most
  T; the round-2 conditional deduction was withdrawn (entry 22).
- **Bridson's printed Fibonacci bound is false at m = 1** (machine-checked
  witness), the seed relator has length 9 not 8, and the additive constant
  reverses to 3 (round 2).
- **The order-120 sentence** in `c14.md` is false for the four PSL(2,7) rows, whose
  groups are infinite (entries 30, 39).
- **Dynnikov's reduction of Zeeman's conjecture is REPORTED, not proved**: the
  load-bearing Case K7 delegates to Matveev 1987 in one asserted sentence, and
  **Kupers'** live PDF's Proposition 4.3 (not 4.2) is the one that states the
  Zeeman-implies-AC direction **with stabilisations** (entry 48; D7: the
  Proposition 4.3 at issue is Kupers', and Dynnikov's own section 4 numbers Lemma
  4.3, not a proposition).

### 3.9 Structural results that came out of the audits

These are the results the campaign's own audit pattern produced, and they are the
ones most likely to be useful to someone outside it:

1. **The rotation-closure negative** [r9 m2] (section 3.3): the box is not closed
   under cyclic rotation at constant length, measured exactly. It kills every
   "closure under conjugation" argument for class realisations.
2. **The bitmap undercount** [r9 m5]: a matcher indexed by `record/8` suppresses
   seven of every eight consecutive records, and a lookup that stops at the first
   row of a key undercounts shared keys (157 309 distinct keys over 298 487
   records). The campaign's "39 classes / 51 rows" was really **78 classes / 113
   rows**. [SETTLED (computation); AUDITED (r10): 113 rows, 78 distinct
   presentations]
3. **The void box** [r9 m5]: a box whose root has AC depth exactly 26 can never be
   a negative at cap 26, because it contains the standard pair. Round 7's
   "108-row box" was proposed as a round-8 target without the cross-check against
   round 5's own certificate. [ARGUMENT + SETTLED (computation)]
4. **The relator-swap automorphism** [r9 m5]: `(r₁,r₂) → (r₂,r₁)` is an
   automorphism of the AC move graph, giving an exact factor 2 on the trio's
   cap-25 box (19 143 476 = 38 286 952 / 2). The eight signed-letter-permutation
   images are eight **distinct** components, so the correct quotient group is of
   order 16, not 8. [SETTLED (computation) for the measurements + ARGUMENT]
5. **The transfer repair** [r9 m4]: the "conjugation by a word, letter by letter,
   keeps every intermediate at most the larger endpoint" sentence is **false in
   general** — conjugating `r = ab` by `w = b⁻¹a⁻¹` gives the intermediate
   `b⁻¹abb` of length 4 while both endpoints have length 2. It is true for
   *rotation* conjugators, which is the case the class relation needs; all 50
   transfers were then verified constructively (36 with explicit peak-14 chains,
   14 by a cap-22 component dump). [SETTLED (computation)]
6. **The elaborator wall removed, then re-measured, then removed again** [r9 m8,
   r10 m10]: packed state codes cut the memory to hold the 136 576-state cap-17
   closed set from 7.5 GB to **1.51 GB** (5×) and the olean from 234 MB to 6.4 MB
   (50×), and the cap-16 negative reproduces from 216 KB of data; the cap-17
   certificate was then blocked by the kernel's *reduction* at about **9·10⁴ s
   (~26 h)** — the campaign's clearest statement of where kernel-checking large
   bounds stops *in that form*. **The cap-17 wall was removed in round 10**: the
   closed set is carried as one static slot array of packed numerals (5 464 265 B of
   source, no tree built at check time), the 512 chunk checks and the assembly give
   `Row17.row_T_c17` on `[propext, Classical.choice, Quot.sound]` with **136 576
   states**, and the full run costs **26 min wall** against the ~26 h reduction — a
   factor 60, and the round-9 estimate was 2× conservative in the safe direction.
   Round 11 rebuilt the whole chain from the consolidated tree: 512 of 512 chunks and
   the assembly rc = 0, the same axioms, the same 136 576. [SETTLED (kernel); r9 m8,
   r10 m10, r11 m3 — P-1.]

---
## 4. Round 9: the last full round

Round 9 (swarm smw4sqc1u, 6 November 09:52:48–18:55:40 UTC, 9 h 03 including the
restart; the earlier session logged 09:56–16:20 and 6 h 24, and round 10's own
dated correction fixes it) closed with **ten of ten accepted**, the campaign's
second consecutive perfect round, with one direction abandoned with its reason
(m6's d9, replaced by d11, which was accepted) and no rejection-fix cycle. Every
acceptance was by rerun. [REPORTED: `rounds/round-09.md` (with the dated
correction), `STATE.md` line 161]

The ten directions and what each delivered:

| # | direction | deliverable | label |
| --- | --- | --- | --- |
| m1 | L1: the final report's skeleton with its audit spine | 616-line skeleton; 74 ledger entries consolidated; 42 verified by rerun; 23 Lean files inventoried live; defects D1–D9 | AUDIT |
| m2 | L2: the cap-25 class census beyond length 20 | three new minimal-length-17 classes; **T = 17 deficit 12 → at most 9**; the rotation-closure negative | SETTLED (computation) |
| m3 | L6: the AC-19 peak ledger to length 17 | **27 124 exact peaks among 33 793 rows**; 15 210 new certificates replayed; `ACPeaks17.lean` | SETTLED (computation) + (kernel) |
| m4 | L4: second referees 8 | four round-8 artifacts sound; **the 445-row sharpening**; the transfer-sentence counterexample and constructive repair | AUDIT |
| m5 | L5: the 108-row box and the deeper bounds | **the box is VOID**; the exact-depth-26 set is **78 classes / 113 rows**; 108 explicit peak-26 certificates; no row above 26 | SETTLED (computation) |
| m6 | d11: the geodesic archive | **186 649 shortest derivations (std → row)**, 2 617 043 moves; representative-independent negatives; `ACQuot15.lean`, `ACTriv15.lean` | SETTLED (computation) + (kernel) |
| m7 | L7: the wall-consumption shape | Theorems A, B (three shapes, first version refuted by the new `cone4` model), C; Corollary C2; 2 763 107 decided census data | ARGUMENT + SETTLED (computation) |
| m8 | L3: the cap-17 closed-set certificate by the packed route | `ACPack.lean`; the 136 576-state data at 1.51 GB (5× better); the cap-16 negative reproduced from 216 KB; **the new wall measured at ~26 h** | SETTLED (kernel) + measured limit |
| m9 | d8: the Metzler recipe's parameter boundary | the 7-move shift; the dihedral obstruction; **k = 4 is exactly the odd j**; six new instances | SETTLED (kernel) |
| m10 | d10: the conjugate layer of the closed-set method | `ACConj.lean` faithful to `AC.lean`; the twelve moves = length-≤1 conjugators; the transfer theorems; LP isolated and two naive proofs kernel-refuted | SETTLED (kernel) + OPEN (LP) |

What round 9 changed in the campaign's picture, in one paragraph: the AC-19 peak
ledger closed at length 17; the T = 17 deficit stopped being "12 forever" and
became "at most 9" with three named classes and a structural reason (rotation
non-closure); the 108-row box that round 8 had advertised as its largest target
turned out to be void for a reason already on the record since round 5; the exact
depth-26 set doubled under a correct matcher; the geodesic archive gave the first
true certificate-length distribution for a whole length; the wall-consumption shape
became three explicit step types with a 3-cell equivalence; the elaborator wall on
the closed set was removed and immediately replaced by a measured kernel-reduction
wall; the Metzler recipe's hypothesis was shown not to be necessary and the k = 4
case was closed exactly; and the closed-set model acquired a proof that it is
faithful to `AC.lean` in the positive direction, with the remaining gap isolated to
one sharply stated lemma — which round 10 found false as stated and round 11 proved
in its corrected form (section 3.7).

## 5. Rounds 10 and 11, and the round-12 finalisation

### 5.1 Round 10: consolidation

Round 10 (swarm smw5c6gb0, 18:57:12–20:31:24 UTC, 1 h 34 min) is the campaign's
consolidation round: no frontier work, ten consolidation directions, and this
report's first draft that had to be finished inside it. **4 of 4 submitted reports
were accepted; six members ended at their step budgets with complete deliverables on
disk, each coordinator-verified where checkable.** Every acceptance by rerun; no
rejection-fix cycle. The directions, as launched:

| # | round-10 direction |
| --- | --- |
| M1 | **the final report itself** — this document |
| M2 | the final report's verification: an adversarial referee of this report against its artifacts |
| M3 | `OPEN_QUESTIONS.md` rebuilt to the round-9 state (it is round-3 vintage: audit finding D7) |
| M4 | the corrections log consolidated: all dated notes across all rounds, verified and indexed |
| M5 | the kernel archive's build recipe verified end-to-end, every axiom line, exact commands |
| M6 | the process record: rejection-fix cycles, abandoned directions, the restart, model use, timeline |
| M7 | the data inventory: every `directions/` subdirectory, results file, certificate archive, indexed and sized |
| M8 | the LP lemma's cone4 cascade case split |
| M9 | the three new T = 17 classes' explicit derivations |
| M10 | the cap-17 closed-set certificate via a batched tree build |

**What the draft did not claim.** In round 10 I held direction M1 only, and did not
report M2–M10 as delivered; where their subjects came up (the build recipe, the open
questions, the process record, the data inventory) I reported **my own** verification
and said explicitly what I did not do. `OPEN_QUESTIONS.md` was not rebuilt by me
(that was M3); section 6.4 records how each audit finding is disposed of *in this
report*. Round 12 direction M4 refreshes that file, M5 refreshes the corrections log
and the process record, M3 referees this document, and M2 runs the two pending
checks; **this report does not report those items as delivered** either.

**What round 10 verified, by me, for the draft** (details in section 9.1 and
Appendix C):

1. **22 Lean files re-elaborated** — 13 of the 17 files in `toolkit/lean/` plus 9
   outside it — **931 `#print axioms` prints** (915 of them in the 20 files that are
   archive or round layers), **every axiom set standard**, no `sorryAx`, plus a fresh
   audit file for the round-9 headline theorems. The draft's §5 summary said "20 Lean
   files … 15 of the 17 … 915 prints", whose components sum to 23 and which
   contradicts §8.2 and §9.1; E5 corrects it to the numbers those sections state.
2. **The round-9 headline recomputed**: `check_three.py` `OVERALL PASS` — the three
   new minimal-length-17 classes are what the round-9 report says they are.
3. **The round-9 counts recounted** from the shipped data files: the AC-19 ledger
   (33 793 / 27 124 / 6 669 and the three closure identities), the 15 210 cap-17
   certificates, the 113 rows / 78 presentations / 108 certificates with 302–443
   moves, the 186 649 geodesic certificates / 2 617 043 moves / longest 96.
4. **The audit findings D1–D9 checked statically** and, where a rerun is cheap,
   rerun (D2: `29 checks run / all checks passed`; D1's path resolution confirmed
   in the source; D3's failing line identified; D4's `sys.argv[1]` confirmed;
   D8's two missing attributions **resolved** — entry 8 is round-1 m8, entry 11's
   artifact is `.ultramath/smw2fzjic/m6/work/SAIR_AC.lean`).

### 5.2 Round 11: the last research round

Round 11 (swarm smw5ghp91, ~20:58–23:48 UTC on 6 November, 2 h 50 min) closed with
**9 of 9 submitted reports accepted**, zero rejection-fix cycles (the third
consecutive round without one), and the tenth member — m3, the archive
consolidation — at its step budget with a complete deliverable that was
coordinator-verified and **installed the same night**. `REPORT.md` entries 90–94
carry the results with their checks. Five of them change this report, and one
closes a round-8 open item:

| entry | result | label | where it lands here |
| --- | --- | --- | --- |
| 90 | the w24/w25 key counts decoded: both files are cumulative to length 17, so the 158 320 is the length-13…16 part (633 280 presentations) — no discrepancy, no computed number changes | SETTLED (computation) | §3.3 |
| 91 | the seventeen kernel-checked closed-set negatives are **full-conjugator** negatives at their caps by computation (56 (row, cap) pairs, 33 297 984 conjugate instances, 0 failures; +22 849 848 on AK(3) at caps 14–17) | SETTLED (computation) | §3.1, §3.7, Q28 |
| 92 | the corrected peak lemma **LP is a kernel theorem** (`peakLemma_corrected`, no hypothesis on `u`), with the relator-1 mirror and the `ACBounds`–`ACConj` **language bridge** stated on the hypotheses a `closedCheck` certificate supplies; plus the Metzler relator 3-cycle bridge (twelve Q-moves) closing round 8's last `[Open]` item | SETTLED (kernel) | §3.1, §3.7 |
| 93 | the peak ledger to **total length 18**: 22 653 exact peaks among 23 322 rows; the combined ledger 57 115 rows, 51 499 exact — [r12, entry 95] the cap-25 push takes these to 22 920 of 23 322 and 51 766 of 57 115 | SETTLED (computation) + (kernel) | §3.4 |
| 94 | the kernel archive **consolidated and installed**: 829 files in three tiers, all rebuilt, 3 140 axiom reports all standard | SETTLED (kernel) | §8.6 |

What round 11 killed or resolved, in its own words: round 8's last `[Open]` item on
the Metzler recipe (closed — the 3-cycle is twelve moves, not six); round 8's
w24/w25 open data item (resolved — not a discrepancy); the LP lemma (now a kernel
theorem, so Q28 is no longer open as a mathematical gap); the seventeen
kernel-checked negatives (upgraded); round 9's "only renaming" gap between
`ACBounds` and `ACConj` (closed as a theorem); and **the previous session's
timestamp chain**, exposed by round 11's audit of the process record as mislabelled
estimates about 2.5 hours off — the campaign's fourth and largest such episode, with
dated corrections in three places, and **no idle gap**: round 9 ended at 18:55:40
and round 10 started at 18:57:12, 92 seconds later.

Round 11's audit layer: m10 replayed both round-10 support artifacts against a
67-row ledger (52 CONFIRMED, 7 REFUTED, 5 STALE, 1 PARTIAL, 1 LOCATED, 1
UNCHECKED; the counts are in `AUDIT_TRAIL.tsv` and I recounted them in round 12),
and found the corrections log sound in structure and counts but not reproducible as
shipped (its own verifier now returns FAIL 1 on N06, because the coordinator's
20:54 rewrite of `REPORT.md` added the word "void" at lines 119 and 205), and the
process record accurate in every count it could recompute and wrong in four
sentences. Those addenda are round-12 direction M5's input, not this report's
delivery; §6.6 records what this report takes from them.

### 5.3 The round-12 finalisation: what this document is, and what it does not claim

This document is the round-10 draft with the merged patch list applied and the
round-11 results folded in. The patch list is m1-r11's E1–E14 (a full fresh referee
pass, two defects substantive), m7's D1–D12 (the kernel-archive and citation
layers), m3's D-1…D-7 with `PATCH_FOR_SECTION_8.md` (the consolidated tree), m2's
Q28/Q29, m9's D-m9-1/D-m9-2, and m10's `CORRECTIONS_ADDENDA.md` with the PD-7
sharpening. Every applied item, its source and its verification status is listed in
the change log delivered beside this report
(`.ultramath/smw5n5txi/m1/CHANGE_LOG.md`), which also records the items **not**
applied and why: one patch item is spurious (m7's D3 — the draft already carries the
correct theorem name `packCheckC_flatten`, and the string `packCheck_C_flatten`
occurs nowhere in it), one is moot (m7's D6 — the installed tree carries
`ACPack.lean`), and one pair of patch lists disagrees on a decomposition (E4's 35
versus m3's 37, reconciled in §8.3).

**What I did myself in round 12** (the checks are Appendix C.5; this is not a third
computational layer):

1. **Recounted the round-11 numbers I fold in**: the installed tree (829 files in
   37 + 776 + 16, the three manifests 37/776/16, `ACPack`/`ACSlot`/`audit_r9`
   present); `ledger18.tsv` (23 322 rows, 22 653 exact, the five-cell histogram,
   the three lower bounds) and `ledger_total_ext.tsv` (57 115 / 51 499 / 5 616);
   m2's `results.tsv` (56 (row, cap) pairs whose `checks` column sums to exactly
   33 297 984, 0 failures, and AK(3)'s four rows to 22 849 848);
   m10's `AUDIT_TRAIL.tsv` (67 rows, 52/7/5/1/1/1); m5's `build.log` (36 axiom
   lines, 31 + 3 + 2 = all standard, no `sorryAx` line).
2. **Recounted the draft's own kernel inventory** under the caption's convention:
   the 17 files are 89 365 lines, **9 137 declarations** (`ACTree.lean` has 10, not
   11) and 2 747 prints — E7 and m7's D1, independently confirmed.
3. **Checked the patch list against the file** item by item, and recorded in the
   change log the three items that do not apply as stated.
4. **Not done**: I did not recompile the 829-file tree (round 11's rebuild and the
   coordinator's 4-minute verification are the evidence, and section 8.6 says so); I
   did not rerun any multi-billion-state census, any certificate replay or any
   Lean file; I did not re-decode the w24/w25 binary dumps; I did not touch the
   topology arguments or the literature. Section 9 states this as the report's
   limit, not as a formality. [AUDITED (r12): items 1 and 2; the rest is the
   round-11 record.]

---
## 6. Corrections

The campaign's corrections fall in five classes: to the **literature** (published
errors it found), to its **own artifacts** (dated notes placed at the passage), from
its **round-9 audit** (D1–D9), **corrections to the round-9 inventory itself**
(section 6.5, found while drafting), and the **round-10 and round-11 corrections**
(section 6.6: the defect lists of three referees, the nine dated notes round 11
placed, and the finalisation's own three exceptions). Every item names where it was
recorded.

### 6.1 Corrections to the literature

| # | item | round | where recorded | status |
| --- | --- | --- | --- | --- |
| 1 | Lisitsa, arXiv:2501.18601, step 81: printed conjugator `ABAbA` should be `aBAbA`; with the correction the 160-move sequence replays | 1 | `survey/automated.md` | reproduced (AUDITED r9, and rerun by the round-11 referee: `python3 survey/automated_check.py` → `RESULT: PASS: both published sequences replay from P to AK(3)`; D8 — the draft's "AUDITED r10 by inheritance" was not a label it defines) |
| 2 | Shehper et al., arXiv:2408.15332 **v2 withdraws** the stable AC-triviality of AK(3) after a one-letter misprint in the 13th relator of the MMS 2002 presentation | 1 | `survey/automated.md` 3.3, `survey/ak-status.md` | REPORTED |
| 3 | BLM Fact 1.2: φ(m)/2 is not an integer at m = 2; the true component count there is 1 | 1 | `survey/nielsen.md` | REPORTED |
| 4 | Bridson's Fibonacci bound: the sharp value is fib(m+2); introduction and body disagree and the proof gives the sharper one | 1 | `survey/complexity.md` | REPORTED |
| 5 | Havas-Ramsay's "L₂(5), the unique perfect group of order 120": L₂(5) = A₅ has order 60; the order-120 group is SL(2,5) | 1 | `survey/computational.md` | REPORTED |
| 6 | The term "blacklisting" occurs in none of the four primary computational texts | 1 | `survey/computational.md` (lines 551–556) | REPORTED (E10: the draft named `survey/automated.md`, which does not contain the word) |
| 7 | A widely quoted arXiv number for Bridson's lower-bound paper is wrong by two digits | 1 | `survey/bibliography.md` | REPORTED |
| 8 | Bridson's printed Fibonacci bound is **false at m = 1** (machine-checked witness: `⟨x,y ∣ xy,y⟩` trivialises in one move while area(x) = 2 > fib₁ = 1) | 2 | `survey/complexity.md` | SETTLED (computation) |
| 9 | The seed relator has length 9, not 8, so the constant 24 is exactly tight | 2 | `survey/complexity.md` | SETTLED (computation) |
| 10 | The recommendation to quote the additive constant 1 is backwards; it reverses to the body's 3 | 2 | `survey/complexity.md` | REPORTED |
| 11 | `c14.md`'s order-120 sentence is false for the four PSL(2,7) rows; the four are infinite | 3 | `directions/c14/c14.md` | SETTLED (computation), entry 30 |
| 12 | Panteleev-Ushakov Table 1 counts pairs of length **exactly** T, not at most T; the round-2 conditional deduction is withdrawn | 3 | `directions/pu-enumeration/pu.md` | SETTLED (computation) for the campaign's per-length counts; REPORTED for the identification of Table 1's cells with those counts (D9: "as a reading" was not a label) |
| 13 | The two stabilization move sets generate the same relation; the "deficiency hazard" was a misreading of arXiv:math/0302080 | 3 | `survey/stable-ak3-status.md` | SETTLED (kernel), entry 20 |
| 14 | The attribution of a "Zeeman ⇒ AC" direction to Kupers with a "loose phrasing" charge is withdrawn: the live PDF's **Proposition 4.3** states it **with stabilisations** | 6 | `survey/dynnikov.md` 6.3 | REPORTED |
| 15 | The Lisitsa published-abstract concession is **not reproducible from open sources**; the stable-status conclusion rests on the Shehper v2 withdrawal alone | 6 | `survey/stable-ak3-status.md` | REPORTED |

**The running total is not re-derived here and should not be quoted.** The record's
"twenty-one published corrections" at the round-5 close is a running count that no
single file substantiates — m10's N07 of the round-10 corrections log says the same,
and round 11 confirmed it — and the table above lists the fifteen the round files
name individually (items 1–7 round 1's, 8–10 round 2's, 11–13 round 3's, 14–15 round
6's). This is a real gap in the record, named as item 6 of the round-9 skeleton's
gap list; the honest statement is **fifteen named items, in the table above**.

### 6.2 Corrections to the campaign's own artifacts (dated notes, rounds 2–9; round 11's in section 6.6)

| round | items |
| --- | --- |
| 2 | REPORT.md item 4 paired the length-11 figure with the length-10 command (the seed-relator error had also survived the coordinator's hand check) |
| 3 | `c14.md`: order-120 sentence, the twelve-move scope of the negative bounds (witness r = xy, w = (xy)³), the 57765 total-row cell; `invariant-ideas` Remark 8 example (impossible by Euler characteristic); the `stable-ak3` deficiency hazard; `pu.md`'s Table-1 reading; six OPEN_QUESTIONS statuses |
| 4 | `pu-gap.md` class-C normal form one letter short; the A/B labels flagged INCONCLUSIVE; `hardness.md` l-increase sharpened; two `qdouble-star` tooling defects; `c14.md` extended; one self-contradictory sentence in `downward-propagation` |
| 5 | `cap21.md` three notes (eight conjugation classes; the misprinted 16-letter canonical form; the T = 16 closure inequality); `punf.py`'s 16-map generator list is not the 20 Whitehead automorphisms; a missing sentence in the conjugator theorem; the 744-pair note; two coordinator timestamp slips |
| 6 | `dynnikov.md` 6.3; `stable-ak3-status.md`; the order-5 group slip; the "44 certificates" count (the files hold 43); four coordinator timestamp slips |
| 7 | the `dB³` defect (**the largest correction of the campaign**: 165 456 of 165 457 census data invalid); the inverted stage-2 multiplier; the whitehead class-C caution withdrawn; stale `c14` labels; segment-2 peak 17 not 18; 672 is the Q* box; one table-cell slip; the Lemma A direction remark; coordinator timestamps |
| 8 | the correction-to-the-correction (**84 050 invalid, not 165 456**); the phase-4 word; the round-7 Theorem 3 proof gap; the round-7 "strictly narrower than PTT" claims (both E and G); the "exactly the AK(3) boxes" sentence; the 39-rows counting; the coordinator's own exchange-lemma error |
| 9 | **C1** the 108-row box is void (placement: round 7 §6 and the round-8 lead list); **C2** 78 classes / 113 rows, not 39 / 51 (placement: round 7 headline, REPORT.md item 63); **C3** the 108-row count is a lower bound; **C4** the cross-check against round 5 that would have caught C1; the **445-row sharpening** of the peak ledger; the **transfer-sentence repair** |

Two of these deserve the final report's emphasis. The **`dB³` defect** (round 7)
invalidated a census a whole round had been built on; the
**correction-to-the-correction** (round 8) then revised the revision — a
wrong-rule datum is still a KS datum if its collapse spared the omitted cells.
Together they are the campaign's clearest demonstration that an audit can be wrong
in both directions, and the reason this report carries both dates rather than only
the latest number.

### 6.3 The round-9 corrections in detail

1. **C1 — the 108-row box is void** [SETTLED (computation) + ARGUMENT]. Round 7 §6
   and the round-8 lead advertised the cap-26 box of `BBAAABa,BBabABA` as the target
   that "would put 108 AC-19 rows at depth 27 if it could be exhausted and shown
   negative". It cannot: round 5 had already certified that presentation's AC depth
   as **exactly 26** (a 179-move certificate at peak 26, plus the cap-25 exhaustion
   of 24 781 832 states), so its cap-26 box contains the standard pair. Round 9
   confirmed this three ways and re-derived the depth (cap-25 box closed with least
   total length 14; the cap-26 box printed length-2 states, all eight signed bases
   among them). **The advice "attack it with more memory" must not be followed.**
   [AUDITED (r9): the eight round-5 certificates replay, 179–191 moves, peak 26]
2. **C2 — 78 classes / 113 rows, not 39 / 51** [SETTLED (computation)]. Round 7's
   matcher undercounted twice: a bitmap indexed by `record/8` suppresses seven of
   every eight consecutive records, and the lookup stops at the first row of a key
   that several rows share (157 309 distinct keys over 298 487 records). The
   depth-26 conclusion stands and is strengthened. [AUDITED (r10): the 113-row
   file holds **113 source records and 78 distinct rows** — the 35 `AC19.txt`
   records all recur in `AC19_extended.txt`, so the 78 distinct rows are 78
   classes, one row each — and the 108 certificates have 302–443 moves each (E11)]
3. **C3 — the 108 is a lower bound** [SETTLED (computation)]. The box meets at
   least 108 AC-19 rows; all 108 now have explicit peak-26 trivialisations, 97 of
   them outside the campaign's harvest archive.
4. **C4 — a process correction** [ARGUMENT]. Round 5 had already recorded the
   standard pair at layer 173 of that very box; a cross-check of a new direction
   against the previous rounds' own data would have caught C1 before it was
   proposed.
5. **The 445-row sharpening** [SETTLED (computation)]. Round 8's ledger applied its
   cap-16 test only to the length-16 stratum; the same test on the rows left with a
   lower bound decides **445 more at peak exactly 16** (15 of length 13, 34 of
   length 14, 396 of length 15). Exact peaks 11 876 → 12 321; lower-bound-only
   3 491 → 3 046. Nothing in the ledger was false; it was not maximal.
6. **The transfer sentence** [SETTLED (computation) + ARGUMENT]. "Per-relator
   conjugation by a word, done letter by letter, keeps every intermediate at most
   the larger endpoint" is **false in general**: conjugating `r = ab` by
   `w = b⁻¹a⁻¹` gives the intermediate `b⁻¹abb` of length 4 against endpoints of
   length 2. It is true for rotation conjugators, which is all the class relation
   needs; all 50 transfers were re-verified constructively (36 with explicit
   peak-14 chains, the 14 others by a cap-22 component dump). [AUDITED (r9)]

### 6.4 The audit findings D1–D9, and how this report disposes of them

The round-9 audit of the ledger (`audit-findings.md`, 8.3 kB) found nine defects.
Each is listed with the fix this report applies.

| id | finding | disposition in this report |
| --- | --- | --- |
| **D1** | **entry 7**'s printed command fails from the repository root (`AssertionError: results/havas_ramsay_ak2.cert.txt`); the script resolves `results/` relative to its own directory | **fixed**: the command quoted for entry 7 is `cd directions/experiment-01 && python3 test_ac_experiment.py`, which prints `ALL 34 CHECKS PASSED`. [AUDITED (r9); the path resolution confirmed statically in round 10] |
| **D2** | **entry 20**: `survey/stabilization-check.py` **does not exist**; the shipped file is `survey/stabilization-moves-check.py`, and it prints **29** checks, not 27 | **fixed**: the file name and the count are corrected. [AUDITED (r10): `29 checks run / all checks passed`] |
| **D3** | **entry 39**: `directions/whitehead/run_all.sh` **does not exist**; the shipped copy is `directions/whitehead/work/run_all.sh` and **fails at its own step 7** — `cd: ../../../../directions/cap21: No such file or directory` — because the relative path is hardcoded to the author's directory depth. Steps 1–6 run (231 s) | **recorded as a resource/rerunnability defect, not repaired in the tree**: the report says the working location is `.ultramath/smw38010i/m4/work/` and that the installed copy is not rerunnable from its installed location. [AUDITED (r9); round 10 confirmed line 49 of the installed copy carries the hardcoded `../../../../directions/cap21`] |
| **D4** | **entry 41**: `python3 verify_path.py` raises `IndexError` — the script needs its path JSON | **fixed**: the command quoted is `python3 verify_path.py path_19.json` (266 elementary moves packaged). [AUDITED (r9); `sys.argv[1]` confirmed in the source in round 10] |
| **D5** | **entry 72's sixteen instance files** are resource-bound: the author's record is **84–609 s and 1.7–7.7 GB per file**, about 40 minutes of kernel time in total; of the sixteen, one reran in full (273 s, 1.8 GB, axioms exactly as recorded), four attempts died at a 600 s timeout (rc 124) or by SIGKILL (rc 137) under round-9 load | **stated in the entry as a resource requirement, and in section 9.3 here**. This is a resource statement, not a refutation: the format's negative controls and the completed instance reproduce |
| **D6** | **count conventions**: AC6 carries 1 835 live `#print axioms`; the ledger's "1 718 per-lemma axiom audits" is not that count. AC4 has 318 live prints; AC3's "83 theorems" matches its prints | **fixed**: the report quotes the file's own live print count and says what the other number counts. Round 10 adds the per-file print/axiom-line table of section 8.2, with the convention stated. **The 1 718 is the `Round5` namespace's share of the prints** (1 718 of 1 834; the other 116 are 83 `AndrewsCurtis` and 33 `AC5`), as m7's D11 established by reading the printed names — the draft's explanation ("the per-lemma audits excluding the `_checked` certificate theorems") is wrong, since `AC6.lean` has 33 `_checked` declarations and all of them are among the 1 834, so excluding them would give 1 801. The file's own count is 1 835 live prints (1 834 axiom lines + 1 "does not depend", all standard) |
| **D7** | **`OPEN_QUESTIONS.md` is stale**: its status table is at round-3 vintage and rounds 4–8 moved at least ten of its twenty-seven questions | **fixed in this report**: section 7 carries the table refreshed to the round-11 close. The **repository file** is still round-3 vintage (mtime 5 November 03:34); round 10's direction M3 rebuilt it as a member deliverable (`.ultramath/smw5c6gb0/m9/OPEN_QUESTIONS.md`), and round 12's direction M4 is refreshing the repository file — this report does not report that as delivered, and section 7 is its authoritative table |
| **D8** | **entry 8** names no author; **entry 11** names no file path, so its artifact cannot be located from the ledger | **both resolved in round 10**: entry 8's author is **round-1 m8** — its directory holds `triviality_check.py`, whose own report reads `python3 triviality_check.py -> 17 PASS, "ALL TODD-COXETER CHECKS PASSED"`, matching the entry's 17 PASS; entry 11's artifact is **`.ultramath/smw2fzjic/m6/work/SAIR_AC.lean`** (with `sair_competition_tools_lean_AC.lean` beside it) |
| **D9** | two shipped check scripts **write into the repository** when rerun: `survey/check_refs.py` rewrites `survey/check_refs.out`, and `directions/carreras-minimax/verify_path.py` writes `gs19_elementary_cert.json` | **recorded in the rerun instructions (Appendix A.3)**: every campaign check is rerunnable on a writable copy; on a read-only checkout these two fail at the write |

**What the round-9 audit did not find**: no Lean file with `sorry`, `native_decide`
or a new axiom; no certificate replay with a failure; no arithmetic in the
ledger's headline counts that contradicted a rerun. The two boxes it recomputed
(the cap-20 class list and the length-≤ 10 census) reproduce exactly, the class list
byte-identically.

### 6.5 Corrections to the round-9 inventory itself (found in round 10)

These are mine, and they are counting defects in the round-9 skeleton, not in any
artifact:

1. **The "axiom lines" column is one low for five files.** For AC3, AC4, AC6,
   AC19eleven and ACPeaks the round-9 table gives 82, 316, 1 833, 93 and 96 axiom
   lines; the correct numbers (round-9's own logs, and my round-10 recompiles for
   four of them) are **83, 317, 1 834, 94 and 97**. In each case *prints = axiom
   lines + "does not depend"* then holds exactly (84, 318, 1 835, 95, 98). The
   property that matters — every axiom set inside `{propext, Classical.choice,
   Quot.sound}` — is unaffected, and the round-9 print counts were right; the
   derived column was wrong. Section 8.2 states the convention and the verified
   numbers.
2. **The file count in the round-9 prose is wrong.** The prose says "sixteen files
   in `toolkit/lean/`, plus five supporting files kept outside it … all 23 files";
   16 + 5 is 21. The table itself has 23 rows: **16 in `toolkit/lean/` and 7
   outside** (`audit.lean`, `ACBounds.lean`, `ACInstances.lean`, `aneg.lean`,
   `qneg.lean`, `ak_trivial.lean`, `stabilization-moves.lean`). With
   `ACPeaks17.lean` it is **17 in `toolkit/lean/`** as of round 9's close.
3. **Two retained round-9 logs are the failed attempts.** `leanlogs/ACClosed.lean.log`
   and `leanlogs/ACQuot.lean.log` in the round-9 audit directory record the
   repository-root run, which fails on `unknown module prefix`; the successful runs
   (with the dependency's olean on `LEAN_PATH`) are the ones the draft's §3.2
   recipe describes. Round 10 re-elaborated the whole closed-set chain from the
   shipped sources and confirms it (section 8.2).
4. **Three counting conventions are in play and the report names which it uses.**
   "lines" is `wc -l`; "declarations" is `theorem`/`lemma` at the start of a line
   with no attribute or visibility prefix (so `private theorem` and `@[simp]
   theorem` are excluded — m5's column counts attribute-prefixed ones too, so
   `AC.lean` reads 37 here and 42 there); "prints" is `#print axioms` at the start
   of a line (excludes occurrences in comments). Under the looser conventions the
   numbers are larger.

### 6.6 The round-11 corrections, and this finalisation's own list

Round 11 placed nine dated correction notes, and its two referees and its own
directions produced the defect lists that this finalisation applies. The notes, all
verified present at their passages:

| where | what | source |
| --- | --- | --- |
| `CENSUS25.md` §6 | F1/F2's first relator rendered without its inverse; the determinants are 1, −1, −1 | m2's D4 = E13 |
| `ACConj.md` §4 | LP needs reduced `u`, reduced `w`; the uncorrected form is kernel-false | r10 m8, entry 85 |
| `LP-PROOF.md` §3 | D-LP1: the "transfer" step is **false** (u = b·a·b⁻¹, q = [b], w = [b⁻¹], s = [] gives red(s++q) = [b] against red(w++q) = []); D-LP2: MONO/BAD assume cyclic reducedness | r11 m5, entry 92 |
| `DERIVATIONS.md` §4 | D-m9-1: the length-25 novelty claim is false — round 9's own `trap20stdout.txt` held 264 and 298 `HIT L 25` lines in two of the three classes and 0 in the third | r11 m9 |
| `BUILD_RECIPE.md` §7 | D-m9-2: the copy counts are convention-dependent; 25/24 reproduce, "97" and "2 to 6" do not | r11 m9 |
| `rounds/round-08.md`, `.ultramath/smw48or9f/m4/REPORT.md` | the 3-cycle bridge, closing the `[Open]` item | r11 m4 |
| `PROCESS_RECORD.md` §3.2 | the idle-interval note, replaced by the enlarged timestamp-discipline finding (PD-7 sharpening: round 9 ended 18:55:40, round 10 started 18:57:12, 92 seconds apart — no idle gap) | r11 m10 + coordinator |
| `REPORT.md` entry 85 | two notes, updated as m2's and m5's results landed | coordinator |
| `rounds/round-10.md` line 1 | the round's own start/close times, corrected from ~16:25/4 h 06 to 18:57:12–20:31:24 | coordinator |

**What this finalisation found in the patch list itself.** Three items do not apply
as stated, and the change log records each with its evidence: m7's **D3** (the
theorem name `packCheck_C_flatten`) does not exist in the draft — it already reads
`packCheckC_flatten`, and `packCheck_C` occurs zero times in the file; m7's **D6**
(the `MANIFEST.tsv` omits `ACPack.lean`) is moot because the installed tree's
manifest has 37 rows including it; and **E4 vs m3's P-4** disagree on the layer-file
decomposition (35 versus 37), which §8.3 resolves by dating both counts. **E14** is
superseded by the round-11 close and by round 12: `REPORT.md` now holds 95 entries
(94 at the round-11 close plus round 12's entry 95), not the 90 the round-11
referee could see; §1.3 and Appendix B state the round-11-close count, 94, and
say so.

[The change log is the authority on the mapping patch → passage; this section only
records the three exceptions.]

---

## 7. The open questions at the round-11 close

`OPEN_QUESTIONS.md` at the repository root carries twenty-seven questions with a
status table — but that table is at **round-3 vintage** (D7): the file's mtime is 5
November 03:34 and rounds 4 to 11 settled or moved at least fifteen of its
twenty-seven questions. Round 10's direction M3 did rebuild it to the round-9 state,
but as a member deliverable (`.ultramath/smw5c6gb0/m9/OPEN_QUESTIONS.md`, 124 531
bytes, 6 November 19:09), not in the repository file; round 12's direction M4
(another member) is refreshing the repository file to the round-11 state, and this
report does not report that as delivered. The table below is the status at this
report's cut-off, reconstructed from the ledger entries named in the "basis"
column, and it is the table the report carries. Questions Q28–Q33 are new in round
9 and were not on the round-3 list.

| id | question (short) | status at the round-11 close | basis | label |
| --- | --- | --- | --- | --- |
| Q1 | is AK(3) AC-trivial | **OPEN**; no AC path to the standard tuple inside total length 25 (the cap-25 closed box is exhausted), and class C is AK(3)-equivalent iff AK(3) is AC-trivial, so the pu-gap prediction is this question | 58, 74, 45 | OPEN (bounded) |
| Q2 | classify the length-14 presentations | **SETTLED except 50 presentations in at most 9 classes**, each at depth ≥ 24/26/29/30; 57 727 trivial, 34 = SL(2,5), 4 infinite, and c(14) ≤ 20 | 15, 55, 70, 73 | SETTLED (computation) in part |
| Q3 | is AK(3) ~ AK(4) | **OPEN**, untouched after round 1 | — | OPEN |
| Q4 | recalcitrance of AK(3) | **OPEN**; exact distances known only inside boxes (P(3) at 24, AK(4) ~ P(4) at 43) | 32 | OPEN |
| Q5 | optimality of the length reduction | **PARTLY**: AK(n) ~ P(n) in exactly 12n−2 moves for n ≤ 20 (verified to 30); no lower bound | 19 | SETTLED (computation) one side |
| Q6 | every MS(n,w) AC-trivial | **OPEN**; three infinite subfamilies known (`⟨a,b ∣ BAABa, B^{2m}AbA⟩` infinite from m = 3) | 30 | OPEN |
| Q7 | MS(3,w) with \|w\| ≤ 7 | **OPEN**; the length-14 slice is classified | 15 | OPEN |
| Q8 | every MS(n,w) ~ AK(n) | **k = 1 SETTLED for n = 2 … 10**, and the uniform ladder step holds for every n and k on w_k; general w OPEN | 13, 19 | SETTLED (kernel) for k = 1 |
| Q9 | Quinn's triangular Hopf algebra | **ANSWERED in characteristic 0** (impossible), **F₂** (exists, machine-checked), **p ≥ 5** (exists at fusion-category level); **F₃ and Z[i] OPEN**; the detection question answered negatively | 17 | SETTLED (computation) in part |
| Q10 | non-2-deformable simple equivalences | **OPEN**, reduced to an exact target; no pair known | 28, 61 | OPEN |
| Q11 | M-transformations versus AC moves | **OPEN**, untouched | — | OPEN |
| Q12 | triviality for balanced presentations | **OPEN**, untouched (decidable inside every exhausted box) | 74 | OPEN |
| Q13 | decidability of AC-equivalence in F₂ | **OPEN**; decided inside explicit boxes to total length 25 | 74 | OPEN |
| Q14 | superexponential lower bound in rank 2 or 3 | **OPEN**, untouched | — | OPEN |
| Q15 | growth of c(L) | **SETTLED to L = 12**; c(13) ≤ 2 (Havas-Ramsay confirmed by computation), c(14) ≤ 20 | 4, 26, 55 | SETTLED (computation) |
| Q16 | links L(3,2;4/d) | **OPEN**, untouched | — | OPEN |
| Q17 | trisection ⇒ AC-triviality | **OPEN**, untouched | — | OPEN |
| Q18 | AC-graph diameters of finite perfect groups | **ANSWERED**: diameter 8 for seven of the eight perfect groups of order ≤ 720, 9 for PSL(2,8); the product-replacement graph is disconnected (44–188 components) | 33 | SETTLED (computation) |
| Q19 | Lean formalisation | **SETTLED** for the named lemmas, the AK(n) theorem, both soundness theorems, the non-triviality layer, the closed-set logic (round 10: the cap-17 negative), the conjugator layer and the Metzler boundary (round 9), and (round 11) the corrected peak lemma with the language bridge — the archive is one installed tree of 829 files with 3 140 axiom reports, all standard | section 8, section 8.6 | SETTLED (kernel) |
| Q20 | a computable hardness measure | **ANSWERED negatively** for the per-presentation score (Spearman +0.0060 over 52 744 solved cases; the 91-move case has l-increase exactly 0); the published finite approximation is undefined exactly where difficulty is unknown | 23, 31 | SETTLED (computation) |
| Q21 | the length-13 members of the AK(3) class | **ANSWERED**: the A/B split is 4 and 8, each by one explicit automorphism, minimality 13 by peak reduction; class C's length-13 level set has 16 states (8 resisting, 8 AC-trivial) and is AK(3)-equivalent iff AK(3) is trivial | 39, 58 | SETTLED (computation) |
| Q22 | the four PSL(2,7)-quotient groups | **ANSWERED: all four are infinite** (index-28 stabiliser with abelianisation Z² + Z/2) | 30 | SETTLED (computation) |
| Q23 | the two stabilization move sets | **SETTLED: they coincide** (Lean, five theorems on `[propext, Quot.sound]`) | 20 | SETTLED (kernel) |
| Q24 | the 164 resisters | **50 undecided in at most 9 classes**; every bound moved in round 8: 22 at depth ≥ 24, 20 at ≥ 26, 4 at ≥ 29, 4 at ≥ 30; c(14) ≤ 20 | 26, 44, 55, 60, 73 | OPEN (bounded) |
| Q25 | the Panteleev-Ushakov table gap | **RESOLVED as a reading** (Table 1 counts pairs of length exactly T; the cells are the halved ours); T = 16 closes exactly at cap 23; **T = 17 deficit 12 → at most 9** in round 9 (three new classes above length 20) | 22, 35, 45, 74, [r9 m2] | SETTLED (computation) as a reading; the exact deficit OPEN |
| Q26 | verification items left open by rounds 1–2 | **mostly closed** by the second-referee programme (rounds 2–9), with named residues (the A/B labels needed the Whitehead minimisation, done in round 5; the Lisitsa concession cannot be reproduced) | 25, 36, 39, 47, 48, 64, 71, [r9 m4] | SETTLED in part |
| Q27 | is AK(3) stably AC-trivial | **UNRESOLVED**, and the record rests on the Shehper et al. v2 withdrawal **alone** | 18, 48 | OPEN, claim WITHDRAWN in the literature |
| **Q28** | **the peak lemma LP** (conjugator length bound) | **SETTLED (kernel) in its corrected form, round 11**: LP as the draft states it — with no reducedness hypothesis — is **false** (round 10's `ACConj.peakLemma_false`: u = a, w = b·b⁻¹, s = b⁻¹, 3 > max(1,1) = 1); with `red w = w` (and reduced `u`) it is `peakLemma_corrected`, proved in the kernel with no hypothesis on `u`, together with the relator-1 mirror and the `ACBounds`–`ACConj` language bridge, so the upgraded negative is stated on the hypotheses a `closedCheck` certificate supplies (36 axiom lines, all standard). **The upgrade of the seventeen kernel-checked negatives is delivered by computation independently of LP** (33 297 984 conjugate instances, 0 failures), so no closed-set negative on record depends on the lemma. What is left is not the lemma but its instantiation: the eighteen certificates are not recompiled with the upgrade (a two-line term each), and the two slot-array closed sets' S-reducedness, open at the round-11 close, is verified at the delivery (`check_reduced.py`, 0 non-reduced over 8 880 + 136 576 states, coordinator-rerun, §3.7) — the per-instance compilation alone remains open | [r9 m10, r10 m8, r11 m5, r11 m2] | SETTLED (kernel) for the corrected lemma; the per-instance instantiation OPEN (round-12 M2) |
| **Q29** | **the cap-17 closed-set certificate** | **SETTLED (kernel), round 10**: the static slot array removes the tree build, and `Row17.row_T_c17` (`Asm17.lean`) is `¬ ∃ ts, (∀ i, i ≤ ts.length → totLen (run startSt (ts.take i)) ≤ 17) ∧ run startSt ts = stdSt` on `[propext, Classical.choice, Quot.sound]`, 136 576 states, 512 chunk checks, 26 min at 4-way; round 11 rebuilt it end to end from the consolidated tree with the same axioms and the same count (512/512 chunks, assembly rc = 0) | [r9 m8, r10 m10, r11 m3] | SETTLED (kernel) |
| **Q30** | **the 22-block's cap-26 box** | **OPEN (measured)**: ~4·10¹⁰ states, four orders of magnitude beyond reach; without a cheaper certificate or a symmetry argument, 108 AC-19 rows stay at depth ≥ 27 rather than exact | 73, [r9 m5] | OPEN (with a measured wall) |
| **Q31** | **the full cap-25 class census at lengths 21–25** | **OPEN**: round 9 reached 72 % of the box by state count and ~96 % of the classes; the three new minimal-length-17 classes may not be all, so the deficit is "at most 9", not "9" | [r9 m2] | OPEN (bounded) |
| **Q32** | **the Metzler boundary for k ≠ 4** | **OPEN**: only k = 4 is closed (odd j). At k = 5 the residue j ≡ 3 (mod 5) is open and both groups are isomorphic there, so no group invariant can decide it | [r9 m9] | OPEN |
| **Q33** | **the exact depth-26 set's true size** | **OPEN (bounded)**: 113 rows are decided; the count of AC-19 rows meeting the partially explored cap-26 box is a lower bound, and the exact value needs one more run with the exact matcher | [r9 m5] | OPEN |

**Two structural remarks for whoever continues.**

1. Q1, Q12 and Q13 are the same question at three levels of ambition, and the
   campaign's own result pins them together: the pu-gap prediction *is* the AK(3)
   question (entry 58), and no invariant factoring through the normal closure can
   separate the class (round-1 survey, Corollary 3). They should be read as one
   question, not three.
2. Q24's nine classes are the campaign's live frontier and its numbers are all
   *lower* bounds. "Depth ≥ 30" is a statement about exhausted boxes at caps 29
   and 28, not about distance; the exact distances are unknown and the 22-block's
   cap-26 box is measured at ~4·10¹⁰ states, i.e. unreachable by four orders of
   magnitude.
3. Q28 and Q29 were the campaign's two named kernel gaps at the round-9 close, and
   round 10–11 closed both — Q29 by the slot array, Q28 by proving the corrected
   lemma and, independently, by the finite check that removes the negatives'
   dependence on it. The open items they leave are instantiation and verification
   labour, not mathematics; the report says so rather than carrying the round-9
   status forward (m2's Q29 staleness note and m3's P-2, both verified).

---
## 8. The kernel archive: inventory and exact build

### 8.1 Inventory of the 17 core layer files (measured in round 10)

These are the files `toolkit/lean/` held at the round-9 close, and they are the
archive's core; since round 11 the directory is a three-tier tree of **829** Lean
files (section 8.6), and these 17 are its top tier's core. "lines" is `wc -l`;
"decls" counts declarations at the start of a line with no attribute or visibility
prefix (`private theorem` and `@[simp] theorem` are excluded, comments excluded —
m5's column counts attribute-prefixed ones too, so `AC.lean` reads 37 here and 42
there, and `AC8.lean` 108 and 109); "prints" counts `#print axioms` at the start of
a line. Every file was elaborated in round 10 unless the last column says
otherwise.

| file | lines | decls | prints | round-10 recompile |
| --- | ---: | ---: | ---: | --- |
| `AC.lean` | 600 | 37 | 42 | yes — exit 0, 42 prints (41+1), sets `P`, `PS`, `PCS` |
| `AC2.lean` | 1 256 | 58 | 47 | yes — exit 0, 47 prints (46+1) |
| `AC3.lean` | 1 996 | 100 | 84 | yes — exit 0, 84 prints (83+1) |
| `AC4.lean` | 30 418 | 2 841 | 318 | yes — exit 0, 318 prints (317+1), 1 m 34 s |
| `AC5.lean` | 5 916 | 1 200 | 33 | **not run in round 10** (needs ~7 GB; round 9: exit 0, 33 axiom lines) |
| `AC6.lean` | 28 333 | 3 032 | 1 835 | **not run in round 10** (round 9: 791 s, 1 834 axiom lines + 1 "none", all standard) |
| `AC7.lean` | 5 021 | 846 | 40 | yes — exit 0, 40 prints |
| `AC8.lean` | 1 041 | 108 | 16 | yes — exit 0, 16 prints |
| `AC19eleven.lean` | 7 551 | 458 | 95 | yes — exit 0, 95 prints (94+1) |
| `ACPeaks.lean` | 2 364 | 156 | 98 | yes — exit 0, 98 prints (97+1) |
| `ACPeaks17.lean` [r9] | 2 232 | 128 | 91 | yes — exit 0, 91 prints (90+1); byte-identical to m3's copy |
| `ACQuot.lean` | 730 | 88 | 48 | **not run in round 10** (needs `AC2.olean` and ~6.6 GB; round 9: 411 s, 48 axiom lines) |
| `QSound.lean` | 1 199 | 45 | 0 | **not run in round 10** (needs `AC5.olean`; audited by `QSoundAudit.lean`, 51 axiom lines) |
| `ACClosed.lean` | 232 | 11 | 0 | yes — exit 0 (with `ACBounds.olean` on `LEAN_PATH`) |
| `ACKeys.lean` | 182 | 10 | 0 | yes — exit 0 |
| `ACTree.lean` | 147 | 10 | 0 | yes — exit 0 |
| `ACComponents.lean` | 147 | 9 | 0 | yes — exit 0 |
| **total** | **89 365** | **9 137** | **2 747** | 13 of 17 re-elaborated in round 10; 4 by round 9 |

`P` = `[propext]`, `PS` = `[propext, Quot.sound]`, `PCS` = `[propext,
Classical.choice, Quot.sound]`. No file contains `sorry`, `native_decide` in code,
or an `axiom` declaration (static scan of all 17 in round 10; of all 829 in round
11). `ACTree.lean`'s cell is **10**, not the draft's 11: the eleventh match is line
17, a docstring line beginning `  theorem (\`Nat.pair_unpair\`) rather than a
computation on the data;` (E7 = m7's D1 = m3's D-4, and I recounted all 17 rows in
round 12: 89 365 / 9 137 / 2 747).

### 8.2 Round-10 recompile: the axiom audit, file by file

Every entry below is a `lean` run I performed for this report, in
`.ultramath/smw5c6gb0/m1/kernel/`, with the sources copied from the archive (and
`ACBounds.lean` from `.ultramath/smw4sqc1u/m8/`, where it lives — see 8.4).
`prints` is the number of `#print axioms` statements executed; `axiom lines` the
number that reported a non-empty set; `none` the number that reported "does not
depend on any axioms". **No axiom set outside the standard three appeared.**

| file | exit | prints | axiom lines | none | axiom sets |
| --- | --- | ---: | ---: | ---: | --- |
| `AC.lean` | 0 | 42 | 41 | 1 | 6×PCS, 32×PS, 3×P |
| `AC2.lean` | 0 | 47 | 46 | 1 | 29×PCS, 17×PS |
| `AC3.lean` | 0 | 84 | 83 | 1 | 51×PCS, 32×PS |
| `AC4.lean` | 0 | 318 | 317 | 1 | 285×PCS, 32×PS |
| `AC7.lean` | 0 | 40 | 40 | 0 | 32×PCS, 6×PS, 2×P |
| `AC8.lean` | 0 | 16 | 16 | 0 | 14×PCS, 2×PS |
| `AC19eleven.lean` | 0 | 95 | 94 | 1 | 62×PCS, 32×PS |
| `ACPeaks.lean` | 0 | 98 | 97 | 1 | 65×PCS, 32×PS |
| `ACPeaks17.lean` | 0 | 91 | 90 | 1 | 58×PCS, 32×PS |
| `ACBounds.lean` | 0 | 0 | 0 | 0 | — (audited inside `ACInstances.lean`) |
| `ACClosed.lean` | 0 | 0 | 0 | 0 | — (audited by `audit.lean`) |
| `ACKeys.lean` | 0 | 0 | 0 | 0 | — |
| `ACTree.lean` | 0 | 0 | 0 | 0 | — |
| `ACComponents.lean` | 0 | 0 | 0 | 0 | — |
| `audit.lean` (round 8) | 0 | 28 | 26 | 2 | 12×P, 10×PCS, 4×PS |
| `ACPack.lean` [r9] | 0 | 0 | 0 | 0 | — (theorems audited in `audit_r9.lean`) |
| `ACConj.lean` [r9] | 0 | 15 | 15 | 0 | 14×PCS, 1×PS |
| `ACConjCex.lean` [r9] | 0 | 6 | 6 | 0 | 6×P |
| `MetzlerSharp.lean` [r9] | 0 | 17 | 17 | 0 | 14×PCS, 3×PS |
| `audit_r9.lean` (mine, round 10) | 0 | 18 | 18 | 0 | 15×PCS, 1×PS, 2×P |
| `ak_trivial.lean` (entry 1) | 0 | 11 | 11 | 0 | 11×PCS |
| `stabilization-moves.lean` (entry 20) | 0 | 5 | 5 | 0 | 5×PS |
| **total (22 files)** | **0** | **931** | **922** | **9** | all standard |

`audit_r9.lean` is the file I wrote for this report; it prints the axiom sets of
eighteen headline theorems of the three round-9 layers — the Metzler obstruction
(`abelian_metz_one`, `coprime_of_recipe_hypothesis`, `abelian_of_coprime`,
`not_mulEquiv_four_even`, `not_mulEquiv_four_two_two`), the conjugator layer
(`applyX_ac`, `runX_ac`, `conjL_length_ge`, `conjW_length_le`, `run_sim`,
`run_sim_totLen_le`, `run_mem_of_closed`, `full_conj_mem_of_closed`) and the packed
closed-set layer (`bmem_bld`, `packCheck_sound`, `packCheckC_flatten`,
`not_reach_of_facts`, `runPack_sound`). It is in
`.ultramath/smw5c6gb0/m1/kernel/audit_r9.lean`, is **37** lines (a 13-line header
comment, three imports, eighteen `#print axioms`), and prints 18 axiom sets (E8 =
m7's D2).

### 8.3 The kernel files outside the 17 core files

At the round-9 close the archive was not all in one directory; since round 11 it is
(section 8.6). Beyond the 17 core files of section 8.1:

| file | where | what |
| --- | --- | --- |
| `ACBounds.lean` | only `.ultramath/smw48or9f/m8/` (round 7) and `.ultramath/smw4i604a/m8/`, `.ultramath/smw4sqc1u/m8/` | the completeness bridge; **imported by** `ACClosed` and `ACComponents` |
| `ACInstances.lean` | `.ultramath/smw48or9f/m8/` (round 7) | the first kernel-checked exact distance (entry 59) |
| `aneg.lean`, `qneg.lean` | `.ultramath/smw48or9f/m7/` (round 7) | 16 tamperings, kernel-rejected (entry 62) |
| `QSoundAudit.lean` | `.ultramath/smw4i604a/m7/` | the 51-axiom-line audit of `QSound.lean` |
| `audit.lean` | `.ultramath/smw4i604a/m8/` | the 28-print audit of the four closed-set files |
| `ak_trivial.lean` | `directions/ak-status/` (and `.ultramath/smw2fzjic/m5/`) | the AK(n) theorem (entry 1) |
| `stabilization-moves.lean` | `survey/` | the two move sets coincide (entry 20) |
| `ACPeaks17.lean` | `toolkit/lean/` **and** `.ultramath/smw4sqc1u/m3/` (byte-identical) | seven round-9 certificates |
| `ACPack.lean` | `.ultramath/smw4sqc1u/m8/` | the packed closed-set layer [r9] |
| `ACQuot15.lean`, `ACTriv15.lean` | `.ultramath/smw4sqc1u/m6/` | 112 non-trivialities and 6 trivialisations at length 15 [r9] |
| `MetzlerShift.lean`, `MetzlerSharp.lean`, `MetzlerRecipes.lean`, `MetzlerSharpBridge.lean` | `.ultramath/smw4sqc1u/m9/` | the Metzler boundary [r9] |
| `ACConj.lean`, `ACConjCex.lean`, `ACConjPeak.lean` | `.ultramath/smw4sqc1u/m10/` | the conjugator layer [r9] |
| `ACQ16b.lean` + `ACQ16b_data.lean` + 70 `ACQ16b_g*.lean` | `.ultramath/smw4sqc1u/m8/` | the complete cap-16 packed certificate (8 880 states, 70 group checks) [r9] |
| `C17data.lean` | `.ultramath/smw4sqc1u/m8/` | the cap-17 packed data, **data only** (no certificate) [r9] |

Counting the *layer* files only (definitions and theorems, not instance data), as
of the round-9 close: **17 in `toolkit/lean/` + 8 support files outside it + 10
round-9 layer files = 35 named layer files** — the eight support files being
`ACBounds`, `ACInstances`, `aneg`, `qneg`, `QSoundAudit`, `audit`, `ak_trivial` and
`stabilization-moves`. (m3's P-4 counts seven support files and reaches 37 by adding
three round-9/10 layer files, `ACPack.lean`, `ACSlot.lean` and `audit_r9.lean`; the
two statements are reconciled by dating them: **35 at the round-9 close**, and
**37 = 35 + `ACSlot.lean` + `audit_r9.lean` in the installed tree's tier 1**, where
`QSoundAudit.lean` is counted as a layer file because it sits in the same tier. E4
and P-4 are therefore both right about their own date, and this paragraph states
both counts.) The round-10 `MANIFEST.tsv` listed **34** of them: it omitted
`ACPack.lean` (m7's D6), which is load-bearing for the cap-17 chain. Beyond the
layer files the archive now holds the 776-file instance chain and the 16 closed-set
rows of entry 72, and the round-9 member directories alone already held 170 `.lean`
files (21.7 MB), most of them experimental variants.

### 8.4 Exact build, and the two facts a reader needs

1. **Inter-file imports need the directory on `LEAN_PATH`.** `ACQuot.lean` (imports
   `AC2`), `QSound.lean` (imports `AC5`), `ACKeys.lean` (imports `ACClosed`),
   `ACTree.lean` (imports `ACKeys`), `ACComponents.lean` (imports `ACBounds`) and
   `ACPack.lean` (imports `ACKeys`) do not elaborate from the repository root as
   shipped: `lean toolkit/lean/ACQuot.lean` fails with
   `error: unknown module prefix 'AC2'`. The working recipe, which I used for every
   file I ran in round 10, is to run in the file's own directory with that directory
   first on the path, after building the dependency's olean:
   ```sh
   cd <dir> && export LEAN_PATH=.:$LEAN_PATH
   lean -o AC2.olean AC2.lean && lean ACQuot.lean
   lean -o AC5.olean AC5.lean && lean QSound.lean
   lean -o ACBounds.olean ACBounds.lean && lean -o ACClosed.olean ACClosed.lean \
        && lean -o ACKeys.olean ACKeys.lean && lean -o ACTree.olean ACTree.lean \
        && lean -o ACComponents.olean ACComponents.lean && lean audit.lean
   lean -o ACPack.olean ACPack.lean
   ```
2. **`ACBounds.lean` was not in `toolkit/lean/` at the round-9 close.** The four
   closed-set layers import it; it lived only in the round-7/8/9 member directories.
   A reader of the round-9 `toolkit/lean/ACClosed.lean` alone therefore saw
   `unknown module prefix 'ACBounds'` — I hit exactly this in round 10 and fixed it
   by copying the file from `.ultramath/smw4sqc1u/m8/`. **Since round 11 it is in
   the tree**, which is one of the consolidation's points: the archive builds in
   place.

**The whole archive now builds with one command.** `bash
.ultramath/smw5ghp91/m3/scripts/verify_archive.sh` orders, builds and audits all
three tiers and prints `VERDICT: PASS` (rc = 0; **3 min 50 s** measured by its
author, **4 min 0 s** by the coordinator on the same night). To install the tree into
`toolkit/lean/`, `bash .ultramath/smw5ghp91/m3/scripts/consolidate.sh` prints the
plan and `--apply` writes it; it compares with `cmp -s` and **refuses** to overwrite
any file that differs from the archive copy (m3's D-5). `toolkit/lean/README_BUILD.md`
travels with it and carries the build order, the `LEAN_PATH` requirement (`. ` must
be on it — Lean does not search the working directory for `import AC2`), and the
three tiers. The tree was installed on 6 November; the source tree is
`.ultramath/smw5ghp91/m3/archive/` and is byte-identical to it.

**Axiom-audit provenance.** Seventeen of the toolkit files carry their own `#print
axioms` blocks. Six do not, and their audit lives beside them: `QSound.lean` is
audited by `.ultramath/smw4i604a/m7/QSoundAudit.lean` (51 axiom lines), the four
closed-set files by `.ultramath/smw4i604a/m8/audit.lean` (28 prints → 26 axiom
lines + 2 none; I ran it: sets `P`, `PS`, `PCS` only), `ACBounds.lean` inside
`ACInstances.lean`, and `ACPack.lean` by my `audit_r9.lean` (round 10).

**Resource facts** (round 9's measurements on a VM shared with nine other members;
my round-10 runs were on a much quieter machine and are not comparable): the
heaviest files are `AC6.lean` (791 s, 4.9 GB peak), `ACQuot.lean` (411 s, 6.6 GB),
`ACInstances.lean` (107 s, 2.9 GB) and `AC5.lean` (100 s as an olean build, ~7 GB).
The sixteen large closed-set instance files are the other heavy item: their author's
round-9 record is 84–609 s and 1.7–7.7 GB **per file**; of the sixteen, one reran in
full in round 9 (273 s, 1.8 GB, axioms exactly as recorded) and four attempts under
round-9 load died at a 600 s timeout or by SIGKILL. **Round 11 measured them again:
all sixteen build sequentially in 34–142 s each** (eight cap-16 rows at 136–142 s,
eight cap-14/15 rows at 34–35 s), no kill, no OOM, on the same 4-core box — so the
round-9 range is round-9's loaded box, not a property of the files (m3's D-7). My
round-10 recompiles: `AC4.lean` 94 s, `ACPeaks17.lean` 36 s, `MetzlerSharp.lean`
1.2 s, the closed-set chain 7 s in total, `ACConj.lean` 20 s. That is a resource
statement, not a refutation.

### 8.5 What the kernel layer does and does not certify

It certifies: the AC move calculus and its invariants; the triviality of the whole
AK(n) family; several thousand explicit certificates as kernel computations; the
**logic** of the certificate formats (soundness) for AC and for Q** (with the
guard); non-AC-triviality through the quotient layer (38 rows at length ≤ 14, 112
at length 15); exact distances in one census row; the closed-set certificate logic
and its instances at caps 14, 16 and 17 (the installed tree's three instance
chains); the conjugator layer's faithfulness and transfer; and the Metzler shift
and obstruction. [H3a, round 12: the first draft said caps 14 and 16, the round-9
extent; the installed tree added the cap-17 chain.]

**One limit of that audit, stated** (m7's N1): the axiom audit of the closed-set
layer (`audit.lean`) prints 28 theorems, while `ACClosed`, `ACKeys`, `ACTree` and
`ACComponents` declare 40; the other twelve are covered by the absence of `sorry`
warnings in the recompiles, not by a printed axiom set. A `sorry` in one of the
twelve would not show up in any `#print axioms` line — and none does, because Lean
emits `declaration uses 'sorry'` and no round-10, round-11 or round-12 transcript
contains that warning. [SETTLED (kernel), with this scope note.]

It does not certify: any of the campaign's large negative bounds **other than the
closed sets the tree carries** — the census boxes, the resister bounds and the
AC-19 search bounds are computations, and the kernel-reduction wall of the *single
reduction* form is measured at ~0.1–0.2 s per state at cap 17 (section 3.9);
the topology (Theorem 4', KS, DP, Conjecture G/E are hand proofs, ARGUMENT); the
general peak lemma in any form other than `peakLemma_corrected`; and nothing about
the truth of the conjecture.

### 8.6 The consolidated archive (round 11)

The kernel archive is **one tree of 829 Lean files**, installed in `toolkit/lean/`
(entry 94). Its source tree is `.ultramath/smw5ghp91/m3/archive/`, byte-identical to
the installed copy. Three tiers, each with a measured `MANIFEST.tsv` (sha256, bytes,
lines, declarations, `#print axioms` count, imports, intra-archive edges, a
comment-stripped forbidden-token scan):

| tier | files | source bytes | `#print axioms` | round-11 rebuild |
| --- | ---: | ---: | ---: | --- |
| layer | 37 | 6 420 880 | 3 084 | 37/37 rc = 0 |
| instances (cap-17, cap-16, cap-14) | 776 | 6 760 707 | 8 | 776/776 |
| closed-set rows (entry 72) | 16 | 23 555 466 | 48 | 16/16 |
| **total** | **829** | **36 737 053** | **3 140** | **829/829** |

**Every one of the 3 140 reports names only `propext`, `Classical.choice`,
`Quot.sound`**, and no file contains `sorry`, `axiom`, `constant`, `opaque`,
`native_decide`, `admit`, `unsafe`, `@[extern]`, `implemented_by` or `ofReduceBool`
once comments are stripped. The two headline theorems reprint as
`'Row17.row_T_c17'` and `'Row16.row_T_c16'` on those three axioms, with the state
counts **136 576** and **8 880** from each certificate's own slot array. The 512
cap-17 chunks are `chunkCheck 17 T stdSt (j*512) 512` for `j < 512`, tiling
`[0, 8⁶) = [0, 262 144)` exactly; the 256 cap-16 chunks tile it the same way at
`j*1024`. [SETTLED (kernel); r11 m3, coordinator-verified and installed.
**AUDITED (r12)**: I counted the installed tree — 829 `.lean` files, 37 at the top
level, 776 under `instances/`, 16 under `instances/rows/`, and the three manifests
with exactly 37/776/16 data rows; `ACPack.lean`, `ACSlot.lean`, `audit_r9.lean` and
`README_BUILD.md` are present. I did **not** rebuild it.]

Ninety-seven files remain outside the tree: two earlier cap-16 packed routes, the
single-reduction forms that document the memory wall and do not complete, and the
cap-17 data in its two containers. Each is listed with its size, status and exact
build command in `.ultramath/smw5ghp91/m3/CORPUS.md`; the cap-16 statements among
them are the same statements `Asm16.lean` proves at the same 8 880 states.

**The honest residue:** the round-11 rebuild is a rebuild of the *sources*; it does
not re-audit the mathematics inside them (that is rounds 4, 7, 8, 9 and 10), it
trusts Mathlib (which is not rebuilt), and its axiom audit is transitive through
proof terms rather than per declaration — 3 140 reports over about 11 600
`theorem`/`lemma` declarations, so a helper that nothing uses is covered by nothing.
The 768 chunk files are independent `decide +kernel` computations over shared
definitions: the *statement* coverage is verified arithmetically, the packed
placement only in the safe direction (a bad placement makes a check fail, never
pass). `ACPeaks18.lean` (round 11's ledger to length 18, §3.4) is **not** in the
tree: it is at `.ultramath/smw5ghp91/m8/ACPeaks18.lean`, 2 446 lines, 93 standard
axiom lines, and would be a tier-1 addition.

---

## 9. Honest limits

### 9.1 What I verified myself in round 10

All of it is in `.ultramath/smw5c6gb0/m1/` and re-runnable from the repository root;
the exact commands and outputs are Appendix C.

1. **22 Lean files re-elaborated**, exit 0, 931 `#print axioms` prints, 922 axiom
   lines plus 9 "does not depend", **every set inside
   `{propext, Classical.choice, Quot.sound}`**. This includes 13 of the 17 files in
   `toolkit/lean/`, the whole closed-set dependency chain, and four round-9 layer
   files, plus two outside-the-toolkit files (`ak_trivial.lean`,
   `stabilization-moves.lean`). I did **not** run `AC5.lean`, `AC6.lean`,
   `ACQuot.lean` (resource-heavy), and I did **not** run any of the sixteen large
   closed-set instance files.
2. **The round-9 headline recomputed**: `work/check_three.py` under
   `.ultramath/smw4sqc1u/m2` prints `OVERALL: PASS` — three `punf` fixed points of
   minlen 17, absent from the campaign's 217, each reproduced by its recorded class
   keys (9/9, 7/7, 4/4) all present in the 5 237 072-class census file, and each
   realised by an explicit box state of total length 23, 23, 25.
3. **Recounts of the round-9 data files**: the AC-19 ledger (33 793 rows, 27 124
   exact, 6 669 open, all open ≥ 18, and the three closure identities 4 532+445,
   13 477+1 288, 1 740+4 929); `certs_cap17.txt` (15 210 certificates, 15 210
   distinct starts); the depth-26 set (113 rows, 78 distinct presentations, 108
   certificates of 302–443 moves); the geodesic archive (186 649 certificates,
   2 617 043 moves, longest 96, 129 288 at length 15); `ACPeaks17.lean`'s first
   1 996 lines byte-identical to `AC3.lean`; the toolkit inventory (17 files,
   89 365 lines, **9 137** declarations, 2 747 prints — the draft said 9 138;
   E7 / m7's D1, recounted in round 12).
4. **D1–D9**: nine findings checked, two resolved (D8's missing author and path),
   one rerun (D2: `29 checks run / all checks passed`), the rest confirmed
   statically or carried as stated.
5. **One correction to the round-9 skeleton of my own** (section 6.5): the
   axiom-lines column for five files, the 16 + 5 = 23 file-count slip, and the two
   retained failed logs.

### 9.2 What I did not verify (inherited, and extended to rounds 11–12)

**Round 12 (the finalisation).** I applied a patch list and recounted the round-11
numbers it folds in (section 5.3, Appendix C.5). I did **not** recompile any Lean
file, rerun any certificate replay or any census, or re-derive any round-11 result
myself: the evidence for those is the round-11 directions' own runs, which the
coordinator reran before acceptance (`REPORT.md` entries 90–94), and the labels on
each say so. Where I state a round-11 number as AUDITED (r12) it is because I
recounted it from the shipped data file, not because I recomputed it. Entry 95,
folded in by the coordinator at the delivery's final read, I did not recount; its
evidence is m7-r12's run (`verify_extension.py` A–F, `crossreplay.py`),
coordinator-rerun.

**Rounds 10 and earlier, inherited.**

- The multi-billion-state boxes: caps 21–25 of the AK(3) class (219 M to 2.9 G
  states/orbits), the cap-24 census (3 056 896 064 tuples), the round-9 cap-25
  class census (2 099 095 069 inserted states, 2 741 s + 2 927 s of `punf`), the
  22-block's cap-25/26 boxes (38 286 952 and beyond), and every cap-26/27/28/29 box
  of round 8. I read their reports and their counts; I did not rerun them.
- The 108 peak-26 certificates, the 186 649 geodesic certificates, the 259 755
  certificate-algebra replays, the 15 210 cap-17 certificates: I counted the files,
  I did not replay them. (Round 9 replayed the cap-17 ones and the geodesic ones
  with independent replayers, 0 failures, and that is the evidence I rely on.)
- The topology (Theorem 4', the Key Step, Theorems A/B/C, Conjectures G/E): read,
  not line-by-line re-checked. They are ARGUMENT, and the report says so.
- The literature: no live source was read in round 10, and none in round 12. Every
  literature statement here is the campaign's, labelled REPORTED; round 11 checked
  the *metadata* of the three load-bearing records against the arXiv API and left
  the bodies unopened (§3.8).
- `OPEN_QUESTIONS.md` as a file: not rewritten (direction M3). The kernel build
  recipe as an end-to-end script (direction M5): I ran the pieces, not one script.
  The process record (M6) and the data inventory (M7): I did not duplicate them.

### 9.3 Resource facts, stated as limits

The VM is 4 CPUs and 16 GB, shared by ten members during a round. Round-9 and
round-10 wall times are therefore not benchmarks. The campaign's own recorded
figures: the cap-23 census 1 638 542 144 states at 541 MB peak (round 4); the
cap-25 closed box 2 913 499 835 orbits in 46 min at 5.3 GB (round 8); the round-9
cap-25 class census 2 741 s to its last checkpoint at 72 % of the box; `AC6.lean`
791 s at 4.9 GB; `ACQuot.lean` 411 s at 6.6 GB; the sixteen closed-set instance
files 84–609 s under round-9 load and **34–142 s** measured sequentially in round
11; the whole 829-file tree rebuilt in round 11 and verified in one command in
3 min 50 s (4 min 0 s on the coordinator's run). The ~9·10⁴ s (~26 h)
kernel-reduction wall on the cap-17 closed set belongs to the *single-reduction*
form and is recorded as such; the slot-array form closed the same statement in
26 min (section 3.9). Any timing in this report is labelled with the machine state
it was taken on.

### 9.4 What the reruns do not establish

A rerun of a campaign engine is a rerun of the campaign's own engine, not an
independent reimplementation: the byte-identical class list shows determinism, not
correctness. The independent evidence for those numbers is the second-referee
programme (section 10.4), not this report's audit. The same holds for every
"reproduced" in Appendix B: it means "the command returns the recorded output",
not "the method is right".

### 9.5 What this document is not

It is not a proof of anything about the conjecture, and it is not a referee's
verdict on itself: it was refereed in round 10 (m2, five defects), round 11 (m1's
E1–E14 and m7's D1–D12, 26 defects — m1's pass calls two of its own fourteen
substantive, and the coordinator's merged list also flags m7's D11) and round 12
(direction M3,
whose verdict is delivered separately). It is the campaign's consolidated record,
with its labels, its checks, its failures and its limits — and, after this round,
with its referees' fixes applied and listed in the change log.

---
## 10. Process record

### 10.1 The rules and how they were enforced

Section 2.1 states the four rules. Three enforcement mechanisms are worth naming
here because they are what produced the record's quality:

- **Every accepted report was rerun by the coordinator before its verdict**, with
  the exact command from the report; the round files say which checks were rerun.
- **Second referees** ran as a standing direction in rounds 2–9, with independently
  written engines and, from round 5 on, before reading the target's write-up.
- **Drafts were carried, not discarded**: twenty-two runs ended at their step budgets
  with complete deliverables on disk (11 through round 9, six in round 10, one in
  round 11, four in round 12); each was coordinator-verified where checkable,
  labelled a draft, and carried forward. [r13 correction: an earlier draft said
  eighteen, the rounds-1-to-11 count.]

### 10.2 The rejection-fix cycles (eight)

| round | member | what was wrong | what the fix produced |
| --- | --- | --- | --- |
| 1 | m8 (invariants) | Section 8 conjugation arithmetic wrong; the displayed tuple had determinant 2, so not even AC-equivalent to standard | the correct index-3 dihedral witness, machine-checked |
| 2 | m7 (invariant ideas) | the stable clause false as stated: the empty presentation at rank 0 is vacuously cocommutative and stably equivalent to every stably-trivial presentation | the theorem restricted to rank ≥ 1 with the rank-0 exception as a remark, plus a check that destabilises the standard rank-2 tuple |
| 4 | m8 (downward propagation) | the Lemma 6 complement cell | Lemma 4 (Zeeman ⇒ DP) and the reduction to the Key Step |
| 4 | m1 (resisters) | Section 5 argument and table labels | the K-family conjugator-independence theorem |
| 5 | m9 (Key Step) | the false collapse-image lemma ("a collapse image of a collapsible complex is collapsible"), refuted by the campaign's own dunce hat | the honest bounded Key Step with the gap localized to a dimension-three cancellation |
| 5 | m6 (Q** status) | the raw-versus-reduced length comparison in Lemma 2, and Proposition 3's scope | Lemma 2 proved in the correct form (intermediates at most max of the two ends), which dissolved the round-4 conjugator caution for box censuses |
| 7 | m1 (PTT) | a missing removal mode in Theorem 1's Case B | wall invariance, the punch-cell law, PTT for wall-avoiding routes |
| 8 | m1 (Theorem 4) | Theorem 2 invoked with coface-freeness in W_* rather than W | Theorem 4' with the cut-at-c construction and the c-shielding argument; the coordinator's own proposed fix exposed as DP-hard |

**In four of the eight, the fix upgraded the result** (round 4's Lemma 6→4, round
4's resister Section 5→the conjugator-independence theorem, round 7's Theorem 1→wall
invariance and PTT, round 8's Theorem 4→Theorem 4′). Rounds 3, 6, 9, 10, 11 and 12
had no rejection-fix cycle; rounds 9–12 are four consecutive rounds without one at
the close.

### 10.3 Abandoned directions (two)

1. **Round 4**: the group-invariant separation of the 66 undecided resisters,
   abandoned with its reason posted — vacuous, because all 66 present the trivial
   group (GAP order 1, re-verified). Replaced by a direction that reached full
   acceptance. [The vacuity itself became a recorded result, and the direction is
   entry 4.17 of the failed-ideas list.]
2. **Round 9**: m6's d9, abandoned with its reason and replaced by d11 (the geodesic
   archive), which was accepted. [REPORTED: `STATE.md` line 159]

The board convention is that a dead end is posted, not quietly dropped; that is why
the campaign's failed-ideas list (25 entries) is as informative as its ledger.

### 10.4 The referee programme, round by round

| round | referee direction | artifacts audited | verdicts | what it found |
| --- | --- | --- | --- | --- |
| 2 | m10, "second referees" | round 1 (3 targets) | all SOUND | 3 errors in the complexity survey, one of which had passed the coordinator |
| 3 | m4, "second referees 2" | round 2 (4 targets) | all SOUND | 3 documentation defects in `c14.md` |
| 4 | m7, "second referees 3" | round 3 (5 targets) | sound where checkable, 1 INCONCLUSIVE | the A/B label caution (later resolved as the audit's own input typo); 2 Q** tooling defects |
| 5 | m10, "second referees 4" | round 4 (6 targets) | all SOUND | five defect-list items |
| 6 | m7, "second referees 5" | round 5 (6 targets) | all SOUND | its own three bugs found and fixed; all 52 744 cost values reproduced |
| 7 | m6, "second referees 6" | round 6 (3 targets) | all SOUND | the 672/168 slip; the (5,10) invariant survives cap 16; a new T = 16 box |
| 8 | m2, "second referees 7" | round 7 (4 targets) | everything reproduced | m9's "exactly the AK(3) boxes" (disjoint twins); m5's 39-rows counting |
| 9 | m4, "second referees 8" | round 8 (4 artifacts + the Q** guard) | (a) SOUND complete; (b) SOUND, 2 of 9 boxes reproduced; (c) SOUND to cap 22; (d) SOUND but **445 rows short of maximal**; Q** SOUND | the 445-row sharpening; the transfer sentence false in general; a label pointing at a sibling block |
| 10 | m2, "M2" | the draft final report (claim reproduction) | 24 claims re-derived, 19 agree, 5 out of scope | five defects (the geodesic wording, 113 records / 78 rows, the ledger universe, two mis-rendered forms in `CENSUS25.md` §6, two counting wordings) |
| 11 | m1, "M1" (full fresh pass) and m7, "M7" (kernel and citation layers) | the draft final report, end to end / all 36 named kernel files and the literature metadata | 14 defects (2 substantive) and 12 defects; nothing load-bearing failed | E1 LP without reducedness; E2 the archive's direction; the `Round5` namespace answer to "1 718"; the three wrong paths |
| 12 | m3, "M3" | this finalised report, end to end | delivered separately | whether every patch landed and whether the editing introduced a defect |

The pattern: **independent reimplementation finds what re-running does not.**
Re-running a command reproduces its number; writing a second engine from the
definitions finds the cases where the number was right and the statement was wrong.

### 10.5 The coordinator's own recorded failure modes

Kept in the record deliberately, because they are the campaign's most transferable
process lessons:

- **Timestamp bookkeeping** slipped in rounds 4, 5, 6, 7 and 8 (entries estimated
  but labelled clock-read; each corrected visibly in `STATE.md`), and then again
  across the round-9/round-10 session boundary, where the estimate was 2.5 hours
  off and was caught only by round 11's audit of the process record (PD-7,
  corrected in three places).
- **Path-depth arithmetic** produced three file-not-found errors in round 5.
- A **mkdir race** hit twice on background jobs in round 7.
- A **stale status snapshot** differed from a member's own final table in round 3.
- The **round-6 close** updated the round file and `STATE.md` but not `REPORT.md`'s
  ledger, so the round-6 entries were only added at the round-7 close.
- **Two substantive checks of his own were wrong**: the round-2 endorsement of the
  invariant-ideas Remark 8 example (impossible by Euler characteristic) and the
  round-8 exchange-lemma error inside a rejection (caught by the member's
  resubmission; recorded as such).

### 10.6 The strongest single checks of the campaign

1. **The checksum identity** (round 5): an order-independent XOR over all
   1 638 542 144 cap-23 states, implemented independently by the coordinator,
   matching across two engines that share no traversal code.
2. **The 66 996 960 ordered-tuple agreement** (round 6): a different engine, data
   structure and state convention giving the same Q** box count to the digit.
3. **The 53 866-certificate replays** across independent checkers (rounds 2–4), and
   the **259 755 certificates** replayed under one dependency-free replay layer
   (round 5).
4. **m5's 274 005 520-state semi-external rerun** and **m9's 7 968-key set
   difference** (round 8), both exact on the coordinator's machine.
5. **The transcription audits with doctoring controls** (rounds 6, 7): the
   generator reproduces the shipped certificate section byte-identically, and
   deliberate single-defect tamperings are kernel-rejected (16 of them, entry 62).
6. **[r9] The peak ledger's three independent closures**: two cap-17 engines
   agreeing on all 5 426 shared rows with 0 disagreements, an independent Python box
   reproducing 10 box sizes exactly, and the round-8 closure arithmetic
   (4 532 + 445, 13 477 + 1 288, 1 740 + 4 929) holding exactly on the shipped
   ledger — rechecked in round 10.

### 10.7 Timeline and model use

| date/time (UTC) | event |
| --- | --- |
| 4 Nov 18:20 | campaign starts; round 1 launched |
| 4 Nov 19:25 | round 1 closes, 15 of 15 accepted; 2 442 of 4 500 calls reserved |
| 4–5 Nov | rounds 2–5 (3 h 00, 4 h 00, 5 h 07, 7 h 29) |
| 5 Nov 15:20 – 6 Nov 00:30 | round 6 (9 h 10), 7 of 10 accepted, 3 drafts |
| 6 Nov 00:35–04:50 | round 7 (4 h 15), 9 of 10 |
| 6 Nov ~05:00–09:50 | round 8 (4 h 50), 10 of 10 — the first perfect round |
| 6 Nov 09:52:48 | round 9 launched; a runtime restart at ~10:00 cost four minutes of wall time and the swarm resumed cleanly |
| 6 Nov 18:55:40 | round 9 closes, 10 of 10 — the second consecutive perfect round; 2 058 of 3 000 calls reserved |
| 6 Nov 18:57:12–20:31:24 | round 10 (consolidation), 4 of 4 submitted accepted, six drafts; the draft of this report written in it |
| 6 Nov ~20:58–23:48 | round 11 (the last research round), 9 of 9 accepted plus the archive draft, zero rejection-fix cycles; the archive installed |
| 7 Nov 00:04:39 | round 12 (finalisation) launched (the swarm record and the directory birth time agree to the second; an earlier draft of this row said ~00:11, an estimate) |
| 7 Nov 03:20:10 | round 12 closed with m7's accepted cap-25 push (the round's last transcript write; an earlier draft of this row said 02:10, an estimate — the round ran 3 h 15 m): 4 of 4 accepted plus four step-budget deliverables verified; this document finalised and twice-checked |
| 7 Nov ~08:00 | the coordinator's final read: the numbers against the ledger, entry 95's extension folded in (this delivery) |
| 8 Nov 12:00 | boundary: no new directions after this time |
| 8 Nov | the final-report-only day: the report is delivered from the repository root |

The times before round 9's close were the campaign's worst bookkeeping. Round 9's
close, round 10's launch and round 10's length were **logged as estimates labelled
clock-reads**: 16:20, ~16:25 and four hours six minutes. Round 11's audit of the
process record, prompted by m10's PD-7, fixed them from the swarm records' own
`at_ms` values and the filesystem: round 9's last verdict at 18:55:40, round 10's
first at 18:57:12 — **92 seconds apart, so "launched at once" was true and there
was no idle gap** — and round 10 closed at 20:31:24 after 1 h 34 min. This is the episode
round 11's record calls the campaign's fourth (after the round-4, round-5 and
round-6 corrections that stand at the head of `STATE.md`; rounds 7 and 8 have
further, smaller ones) and by far the largest, about 2.5 hours; the dated
corrections are in `rounds/round-10.md`
line 1, `rounds/round-09.md` and `STATE.md`. The lesson the campaign records is the
one its own rules imply: a clock-read is a check, an estimate is not, and the label
must not say otherwise.

Model use: the campaign's recorded budgets are round 1's 4 500 calls (2 442
reserved), round 2's 3 000, round 9's 3 000 (2 058 reserved at its close), round
10's 2 400 (1 213 reserved) and round 11's 3 000 (1 523 reserved); rounds 10 and 11
ran ten-member swarms at ≤ 120 and 150 model calls per member. Round 12 runs eight
members at ≤ 150 calls each, budget 2 400. The process record's own independent
recount (m6's, audited in round 11) gives 10 652 model calls and 10 929 tool calls
over rounds 1–9. Every other figure in this table is a round-file or `STATE.md`
record; none is estimated here.

---

## 11. Where the campaign stops: the frontier, ranked

Nothing in this list is a claim for or against the conjecture. It is the map as the
campaign leaves it, ordered by what a successor would most usefully do first.

1. **AK(3) itself (Q1/Q12/Q13).** Everything the campaign proved is a bound inside a
   box or a statement about a finite object. The conjecture for AK(3) is untouched,
   and the campaign's own result says why there is no cheap route: class C is
   AK(3)-equivalent iff AK(3) is AC-trivial, and no invariant factoring through the
   normal closure can separate it.
2. **The 50 resisters in nine classes (Q24).** The live frontier: c(14) ≤ 20, every
   presentation moved to depth ≥ 24/26/29/30, and the exact distances unknown. The
   wall is measured: the 22-block's cap-26 box is ~4·10¹⁰ states.
3. **The stable status of AK(3) (Q27).** The record rests on one withdrawal; a
   literature pass with live sources would either restore a second leg or close the
   question to the campaign's satisfaction.
4. **The peak lemma LP (Q28).** No longer a gap in the form the draft carried: LP
   without reducedness is kernel-false (round 10), the corrected lemma is a kernel
   theorem with the language bridge (round 11, entry 92), and the seventeen
   kernel-checked negatives are full-conjugator negatives by computation, without
   LP (entry 91). What a successor inherits is the instantiation — the eighteen
   certificates' upgrade terms, written as m2-r12's `Upg_*` files but not
   compiled — and the general statement's remaining hypotheses, stated in Q28.
5. **One measured wall (Q30) and one removed (Q29).** The 22-block's
   ~4·10¹⁰-state box stands, stated with its number; the cap-17 kernel reduction at
   ~9·10⁴ s was removed in round 10 by the slot array (26 min, 136 576 states,
   standard axioms, entry 88) and rebuilt from source in round 11.
6. **The two partial censuses (Q31, Q33).** Round 9 reached 72 % of the cap-25 box
   by state count (~96 % of the classes) and a lower bound on the depth-26 set;
   finishing either would turn "at most 9" and "at least 113" into values.
7. **The Metzler residues (Q32).** k = 4 is closed; the coprime residues at k ≠ 4
   are open and no group invariant can decide them.
8. **Untouched after round 1 (Q3, Q4, Q11, Q14, Q16, Q17).** AK(3) ~ AK(4), the
   recalcitrance of AK(3), M-transformations, superexponential lower bounds, the
   links L(3,2;4/d), and trisection ⇒ AC-triviality. They should be read as
   untouched, not as live leads.

**What the campaign would say to a successor, in one sentence.** The neighbourhood
is now measured — the census to length 14, the AK(3) box to total length 25, the
AC-19 ledger to length 17, the certificate archive for every row of length ≤ 15 —
and the conjecture is exactly where it was; what has changed is that every claim
about the neighbourhood now has a check, a label, and a measured wall behind it.

---
## Appendix A. Exact build and rerun

All commands are run from the repository root unless the command says otherwise.
Lean is 4.33.1 with Mathlib prebuilt at `/opt/mathlib` and on `LEAN_PATH`.

### A.1 The kernel archive

**As of round 11 the whole archive is in `toolkit/lean/` and builds with one
command** (section 8.6):

```sh
bash .ultramath/smw5ghp91/m3/scripts/verify_archive.sh   # VERDICT: PASS, 3 min 50 s
# or, from inside the tree, tier by tier:
cd toolkit/lean && export LEAN_PATH=".:$LEAN_PATH"
python3 ../scripts/arch.py order MANIFEST.tsv   # 29 intra-archive edges, 0 violations
python3 ../scripts/arch.py build MANIFEST.tsv   # lean -o M.olean M.lean, topological
python3 ../scripts/arch.py check MANIFEST.tsv   # every axiom report parsed and checked
```

The individual commands below are the round-10 ones and remain correct for a
single file or a single chain; the `ACBounds is NOT in toolkit/lean` note is
historical (it is in the tree now).

```sh
# a file that imports only Mathlib (AC, AC2, AC3, AC4, AC5, AC6, AC7, AC8,
# AC19eleven, ACPeaks, ACPeaks17, ak_trivial, stabilization-moves):
lean toolkit/lean/AC.lean                 # exit 0, 42 axiom prints

# the closed-set chain as it stood in round 10 (ACBounds was NOT in toolkit/lean then):
cd .ultramath/smw4sqc1u/m8 && export LEAN_PATH=.:$LEAN_PATH
lean -o ACBounds.olean ACBounds.lean
lean -o ACClosed.olean ACClosed.lean
lean -o ACKeys.olean ACKeys.lean
lean -o ACTree.olean ACTree.lean
lean -o ACComponents.olean ACComponents.lean
lean -o ACPack.olean ACPack.lean
lean audit.lean                           # 28 prints, 26 axiom lines + 2 none

# ACQuot (needs AC2.olean) and QSound (needs AC5.olean), in their own directory:
cd <dir> && export LEAN_PATH=.:$LEAN_PATH
lean -o AC2.olean AC2.lean && lean ACQuot.lean
lean -o AC5.olean AC5.lean && lean QSound.lean
```

The round-10 verification runs are in `.ultramath/smw5c6gb0/m1/kernel/` with
`sources copied in and all logs kept; `python3 kernel_summary.py` regenerates the
table of section 8.2 from the logs.

### A.2 The main computations (one command per layer)

```sh
# census at total length <= 11 (entry 4; ~7 min)
cd survey/computational && python3 census.py 11 13 certs_r11_c13.txt && \
  python3 check_certs.py certs_r11_c13.txt

# the bounded negatives (entry 7; corrected command, D1)
cd directions/experiment-01 && python3 test_ac_experiment.py    # ALL 34 CHECKS PASSED

# the length-14 classification (entry 15)
cd directions/c14 && python3 enum14.py && python3 replay14.py certs_all.txt

# the AK(3) cap-20 class census (entry 16; 137 s)
cd directions/pu-enumeration && gcc -O2 -o rawbox rawbox.c && \
  ./rawbox 20 1 -l cls20k1.txt -c cert20k1.txt

# the two PSL(2,7) / stabilization spot checks (entries 20, 30; corrected name, D2)
python3 survey/stabilization-moves-check.py        # 29 checks run / all checks passed
cd directions/psl27-frontier && sh run_all.sh

# the Carreras minimax certificate (entry 41; corrected command, D4)
cd directions/carreras-minimax && python3 sublevel.py && \
  python3 verify_path.py path_19.json

# round 9: the T = 17 three-class certificate (~20 s)
cd .ultramath/smw4sqc1u/m2 && python3 check_three.py        # OVERALL: PASS

# round 9: the AC-19 ledger recount (instant)
cd <repo> && python3 .ultramath/smw5c6gb0/m1/checks/recount.py
```

### A.3 Read-only warning (D9)

Two shipped checks write into the repository when rerun:
`python3 survey/check_refs.py` rewrites `survey/check_refs.out`, and
`python3 directions/carreras-minimax/verify_path.py path_19.json` writes
`directions/carreras-minimax/gs19_elementary_cert.json`. Both are correct; on a
read-only checkout they fail at the write. Run them on a writable copy.

### A.4 The one command that does not work as printed (D3)

`cd directions/whitehead && bash run_all.sh` names no existing file: the directory
holds `whitehead.md` and `work/`. The shipped copy `directions/whitehead/work/run_all.sh`
runs steps 1–6 (231 s) and then fails at its own step 7 with
`cd: ../../../../directions/cap21: No such file or directory`, because the relative
path is hardcoded to the author's directory depth. The working location is
`.ultramath/smw38010i/m4/work/`. Nothing in the entry's mathematical claim depends
on it; the claim was rerun there.

---

## Appendix B. The ledger: entries 1–74 and the round-9 reports

> What an `AUDITED r9` cell means (round 12, from the round-9 audit's own record):
> 42 entries rerun, 5 partial, 1 failed at an exact point, 24 examined but not
> rerun (cost), 2 read as documents. Entries 47 and 63 are on the not-rerun list —
> their cells record examination, not a rerun. [B3]

`REPORT.md` section 2 holds **94** numbered entries as of the round-11 close: 1–74
(through round 8), 75–84 (round 9), 85–89 (round 10), 90–94 (round 11). This
appendix tabulates **1–74** (the draft's 84-row table) plus the ten round-9 reports
R1–R10 below it; the round-10 and round-11 entries 85–94 are tabulated in
**Appendix B.2**, and round 12's entry 95 is carried as dated notes at three sites
(the executive summary, §3.4 and §5.2's row 93), not as a row of that table. "Audit" is the round-9 audit's result (AUDITED r9 = the printed
command rerun; "not rerun" = cost) and, where I checked it in round 10, AUDITED
r10; the round-11 and round-12 notes are added where they apply. R1–R10 are the
round-9 reports.

| # | result | label | check (short) | audit |
| --- | --- | --- | --- | --- |
| 1 | AK(n) presents the trivial group for every n | SETTLED (kernel) | `lean directions/ak-status/ak_trivial.lean` | AUDITED r9; **r10: exit 0, 11 axiom lines** |
| 2 | Toolkit Lean base: AC-equivalence, exponent sums, rank-1 non-equivalence | SETTLED (kernel) | `lean toolkit/lean/AC.lean` | AUDITED r9; **r10** |
| 3 | Toolkit Python propositions at rank 2 (≤ 4) and rank 3 (≤ 2) | SETTLED (computation) | `python3 toolkit/test_toolkit.py` (144 PASS) | AUDITED r9 |
| 4 | Complete census at total length ≤ 11: 26 182 / 22 485 / 3 697 / 0 | SETTLED (computation) | `census.py 11 13` + `check_certs.py` | AUDITED r9 (≤ 10 slice) |
| 5 | Replays of published chains (Miasnikov, Havas-Ramsay, Lisitsa 70 and 160 moves, AK(1), MS) | SETTLED (computation) | `python3 survey/automated_check.py` | AUDITED r9 |
| 6 | New certified classes (relator conjugate to a generator) | SETTLED (computation) | `python3 survey/special-classes-check.py` | AUDITED r9 |
| 7 | Bounded negatives with exact bounds for AK(3)–AK(5) | SETTLED (computation) | `cd directions/experiment-01 && python3 test_ac_experiment.py` (D1) | AUDITED r9 |
| 8 | Triviality battery: three Todd-Coxeter implementations, 17 PASS (author: round-1 m8 — D8) | SETTLED (computation) | `cd survey/invariants_checks && python3 triviality_check.py` | AUDITED r9 |
| 9 | Finite-analogue census (BLM 1.1, 1.3, φ(m) counts) | SETTLED (computation) | `python3 survey/nielsen_census.py` | AUDITED r9 (SHA reproduced) |
| 10 | Lisitsa countermodels validated | SETTLED (computation) | `python3 survey/automated_countermodel_check.py` | AUDITED r9 |
| 11 | The SAIR competition statement compiles (artifact: `.ultramath/smw2fzjic/m6/work/SAIR_AC.lean` — D8) | SETTLED (kernel) | `lean` on that file | not rerun r9 |
| 12 | Bibliography registry: 33 DOI + 13 arXiv checks, 0 without MATCH | SETTLED (computation, live) | `python3 survey/check_refs.py` | AUDITED r9 |
| 13 | MS(n,w₁) ~ AK(n) for n = 2…10 (18 certificates, five implementations) | SETTLED (kernel) | `cd directions/ms-ak-certs && bash run_all.sh` | AUDITED r9 |
| 14 | Lean program 2: normal closure, conjugate-to-generator | SETTLED (kernel) | `lean toolkit/lean/AC2.lean` | AUDITED r9; **r10** |
| 15 | The length-14 frontier: 54 068 classified, 53 866 certificates | SETTLED (computation) | `cd directions/c14 && python3 enum14.py` + `replay14.py` | AUDITED r9 |
| 16 | AK(3) class census, cap 20: 51 411 456 tuples / 79 680 classes | SETTLED (computation) | `rawbox 20 1 -l cls20k1.txt -c cert20k1.txt` | AUDITED r9 (byte-identical class list) |
| 17 | Quinn's TQFT question per characteristic | SETTLED (computation) + REPORTED | `python3 survey/quinn_check.py` | AUDITED r9 |
| 18 | The stable status of AK(3): unresolved | REPORTED | three replay scripts | not rerun r9 |
| 19 | The uniform ladder step MS(n,w_k) ~ MS(n,w_{k+1}); AK(n) ~ P(n) in 12n−2 | SETTLED (computation) | `cd .ultramath/smw2opo0o/m1/ak-ladder && python3 round3/check_all.py` (1 711 certificates; the `cd` is required, P2) | AUDITED r9 |
| 20 | The two stabilization move sets coincide | SETTLED (kernel) + (computation) | `python3 survey/stabilization-moves-check.py` (**29** checks, D2) + `lean survey/stabilization-moves.lean` | AUDITED r9; **r10: 29 checks passed; Lean 5 axiom lines** |
| 21 | Lean program 3: cocommutativity kill, certificate verifier | SETTLED (kernel) | `lean toolkit/lean/AC3.lean` | AUDITED r9; **r10** |
| 22 | The PU table gap resolved as a reading (length exactly T) | SETTLED (computation) | `cd directions/pu-gap && python3 checks13.py` | AUDITED r9 |
| 23 | The hardness measure tested and mostly refuted | SETTLED (computation) | `cd directions/hardness && bash run_all.sh` | not rerun r9 (12 min, 3 GB) |
| 24 | OPEN_QUESTIONS rebuilt; Carreras certificates replayed | SETTLED (computation) | `cd directions/c14/carreras && python3 replay_carreras.py …` | AUDITED r9 |
| 25 | Second referees 2: four round-2 targets SOUND | AUDIT | `directions/second-referees-2/referee.md` §7 | document (not rerun) |
| 26 | The resisters push: c(13) ≤ 2, 98 certificates | SETTLED (computation) | `cd directions/resisters && python3 replay_own.py …` | AUDITED r9 |
| 27 | The Q** bounded search: 68 resisters Q*-trivial | SETTLED (computation) | `cd directions/qdouble-star && python3 check_qstar.py out/*.cert` | AUDITED r9 |
| 28 | Downward propagation reduced to its Key Step | ARGUMENT + (computation) | `cd directions/downward-propagation && python3 certify_dunce.py` | AUDITED r9 |
| 29 | Lean program 4: 124 certificates, 98 triviality corollaries | SETTLED (kernel) | `lean toolkit/lean/AC4.lean` | AUDITED r9; **r10: 318 prints** |
| 30 | The four PSL(2,7)-frontier groups are infinite | SETTLED (computation) | `cd directions/psl27-frontier && sh run_all.sh` | AUDITED r9 |
| 31 | The exact minimum of the 91-move worst case (44 in cap 15) | SETTLED (computation) | `cd directions/worst-case && python3 wcase.py …` | AUDITED r9 (105 488 certificates, 0 failed) |
| 32 | P(3) ~ AK(3) in 24 moves, AK(4) ~ P(4) in 43 | SETTLED (computation) | `cd directions/p-trivial && bash run_all.sh full` | not rerun r9 |
| 33 | AC-graph diameters: Q18 answered (8, and 9 for PSL(2,8)) | SETTLED (computation) | `cd directions/ac-graph-diameters && python3 verify.py census` | AUDITED r9 |
| 34 | The resisters final push and the conjugator-independence theorem | SETTLED (computation) + ARGUMENT | `cd directions/resisters/round4 && ./acx search …` | not rerun r9 |
| 35 | The disk-backed census at caps 21–23; class C absent | SETTLED (computation) | `python3 verify.py && verify22.py && verify23.py` | not rerun r9 |
| 36 | Second referees 3: five round-3 targets sound, one INCONCLUSIVE | AUDIT | `directions/second-referees-3/referee.md` | document (not rerun) |
| 37 | First explicit Q** certificates for the quoted pairs | SETTLED (computation) | `bash directions/qdouble-star/m9/checkall.sh` | AUDITED r9 |
| 38 | Certificate algebra: 259 755 certificates under one replay layer | SETTLED (computation) | `cd directions/certificate-algebra && bash run_all.sh` | AUDITED r9 |
| 39 | The Whitehead minimisation and the A/B split (4 and 8) | SETTLED (computation) | `.ultramath/smw38010i/m4/work/run_all.sh` (D3: not the installed copy) | AUDITED r9 — **the installed copy fails at step 7** |
| 40 | The Key Step, honestly bounded | ARGUMENT + (computation) | `python3 ks_engine.py` | AUDITED r9 |
| 41 | The Carreras minimax audit (d_GS = 19) | SETTLED (computation) | `python3 sublevel.py`; `python3 verify_path.py path_19.json` (D4) | AUDITED r9 |
| 42 | The length-5-relator family; exact multiplication count ≤ 17 | SETTLED (computation) | `bash run_h8.sh` | not rerun r9 |
| 43 | AK(3)'s Q** status bounded; the conjugator question settled | SETTLED (computation) | rebuild of `qbox.c`; 66 996 960 states / 109 072 classes | not rerun r9 |
| 44 | Eight resisters fall; c(14) ≤ 28 | SETTLED (computation) | 44 certificates under two replayers | not rerun r9 |
| 45 | The cap-24 census; class C excluded to length 25; T = 17 deficit 12 | SETTLED (computation) | `verify24.py`; 3 056 896 064 states | not rerun r9 |
| 46 | Lean program 5: the Q** move set, 33 certificates | SETTLED (kernel) | `lean toolkit/lean/AC5.lean` | AUDITED r9 |
| 47 | Second referees 4: five defect-list items | AUDIT | `bash directions/second-referees-4/code/rerun.sh` | AUDITED r9 |
| 48 | The live-source citation audit of rounds 1–5 (two corrections) | REPORTED | 18 external claims against live primaries | not rerun r9 |
| 49 | The Metzler stopping point removed (44-move certificate) | SETTLED (computation) | five implementations including GAP | not rerun r9 |
| 50 | Lean program 6: AC6, 1 835 live prints (the "1 718" is the `Round5` namespace's share of them — D6/D11) | SETTLED (kernel) | `lean toolkit/lean/AC6.lean` | AUDITED r9 (1 834 axiom lines + 1 none, all standard) |
| 51 | The AC-19/c14 intersection rebuilt (3 127 rows) | SETTLED (computation) | intersection recomputed | not rerun r9 |
| 52 | The dimension-three cancellation localized | ARGUMENT | Theorem A, Proposition 5, Conjecture E on 900 data | not rerun r9 |
| 53 | The (5,10)-bucket structure | SETTLED (computation) | cap-16 census (129 247 304 states) | not rerun r9 |
| 54 | The symmetry quotient for the Q** box | SETTLED (computation) | orbit-enumeration lemma + box counts | not rerun r9 |
| 55 | The AC-19 falls referee-certified; c(14) ≤ 20 | SETTLED (computation) | 417 replays + the coordinator's cap-25 exhaustion | AUDITED r9 (cap-25 box 38 286 952) |
| 56 | The eleven depth-26 AC-19 rows, kernel-checked; the harvest | SETTLED (kernel) | `lean toolkit/lean/AC19eleven.lean` | AUDITED r9; **r10: 95 prints, exit 0** |
| 57 | The Metzler family in the kernel (AC7) | SETTLED (kernel) | `lean toolkit/lean/AC7.lean` | AUDITED r9; **r10: 40 prints** |
| 58 | Class C resolved; the pu-gap prediction is exactly the AK(3) question | SETTLED (computation) | cap-17 exhaustion at 136 576 + cap-18 find | not rerun r9 |
| 59 | The bridge and the first exact distance (cap-14 distance 6) | SETTLED (kernel) | `lean ACBounds.lean` + `lean ACInstances.lean` | AUDITED r9 (**r10: ACBounds exit 0**) |
| 60 | The 50 resisters: nine classes, the exact wall | SETTLED (computation) | 393 certificates under an independent checker | not rerun r9 |
| 61 | Three PTT theorems; PTT reduced to Conjecture G | ARGUMENT + (computation) | `gprime`, the wallstep mechanism | not rerun r9 |
| 62 | The Lean layer negative-tested (16 tamperings rejected) | SETTLED (kernel) | `lean aneg.lean`, `lean qneg.lean` | AUDITED r9 |
| 63 | Thirty-nine AC-19 rows at depth exactly 26 → **78 classes / 113 rows** (C2) | SETTLED (computation) | ordered-key membership + certificates | AUDITED r9 |
| 64 | Second referees 6; the T = 16 Q** box closes with no target | AUDIT + SETTLED (computation) | `.ultramath/smw48or9f/m6/` (E6: `directions/second-referees-6/` does not exist) | not rerun r9 |
| 65 | Theorem 4′: the wall-avoiding punch route is the Key Step | ARGUMENT | `gprime` (133 data), the c-shielding argument | not rerun r9 |
| 66 | The Metzler recipe as one kernel theorem (AC8) | SETTLED (kernel) | `./check_ac8.sh` | AUDITED r9; **r10: 16 prints** |
| 67 | The Q** soundness theorem, with the non-optional guard | SETTLED (kernel) | `lean -o QSound.olean QSound.lean` + `QSoundAudit.lean` (51 lines) | AUDITED r9 |
| 68 | The census repaired: 81 407 genuine KS data, 84 050 invalid | SETTLED (computation) | `run_all.sh` (17 m 44 s) | not rerun r9 |
| 69 | The AC-19 peak ledger to length 16: 11 876 exact, 3 491 bounds | SETTLED (computation) + (kernel) | transpose box + `ACPeaks.lean` | AUDITED r9; **r10: ACPeaks 98 prints** |
| 70 | The quotient-witness layer: the first kernel non-triviality | SETTLED (kernel) | `lean toolkit/lean/ACQuot.lean` (411 s, 6.6 GB) | AUDITED r9 |
| 71 | Second referees 7: everything reproduced; two findings | AUDIT | `.ultramath/smw4i604a/m2/` | not rerun r9 |
| 72 | The compact closed-set certificates (16 rows) | SETTLED (kernel) | `check.sh` + **all sixteen rebuilt in round 11** (34–142 s each, 48 axiom reports, all standard); the whole tier is in the consolidated archive | AUDITED r9; rebuild r11 |
| 73 | Nine new exact closed boxes; all 50 resisters moved | SETTLED (computation) | five campaign counts + the cap-27 rerun (274 005 520) | not rerun r9 |
| 74 | T = 17 at cap 25 settled (states yes, classes no) | SETTLED (computation) | 2 913 499 835 orbits, 46 min | not rerun r9 |
| **R1** | **The final report's skeleton and the ledger's audit (D1–D9)** | AUDIT | 42 of 74 entries rerun; 23 Lean files compiled | the basis of this report |
| **R2** | **Three new minimal-length-17 classes; T = 17 deficit ≤ 9; rotation non-closure** | SETTLED (computation) | `check_three.py` | **AUDITED r10: `OVERALL: PASS`** |
| **R3** | **The AC-19 peak ledger to length 17: 27 124 exact among 33 793** | SETTLED (computation) + (kernel) | `ledger9.py`, `rcheck.py`, `ACPeaks17.lean` | **AUDITED r10: recounted; ACPeaks17 exit 0, 91 prints** |
| **R4** | **Second referees 8; the 445-row sharpening; the transfer repair** | AUDIT | independent engines; `transfer50.py` | **AUDITED r10 (the closure arithmetic)** |
| **R5** | **The 108-row box is VOID; 78 classes / 113 rows; 108 peak-26 certificates** | SETTLED (computation) | `bx`, `cert108.py`, two replayers | **AUDITED r10: 113 rows, 78 presentations, 108 certificates** |
| **R6** | **The geodesic archive: 186 649 shortest derivations (std → row); representative-independent negatives** | SETTLED (computation) + (kernel) | `acx` + independent replayer; `ACQuot15.lean`, `ACTriv15.lean` | **AUDITED r10: 186 649 / 2 617 043 / longest 96; AUDITED r11: the direction, full population (E2)** |
| **R7** | **The wall-consumption shape: Theorems A, B (three shapes), C, Corollary C2** | ARGUMENT + (computation) | `box.c` on six models, 41 935 037 steps | read, not rechecked |
| **R8** | **The packed encoding: 1.51 GB for the 136 576-state set; the ~26 h wall** | SETTLED (kernel) + measured | `ACPack.lean`, `ACQ16b*`, `C17data.lean` | **AUDITED r10: `ACPack.lean` exit 0 and its import chain (`ACBounds → ACClosed → ACKeys`) exit 0; 5 headline theorems on the standard axioms. `ACQ16b*` / `C17data.lean` not recompiled in round 10 (D12); r11 m3 rebuilt the whole chain, 512/512 chunks + assembly** |
| **R9** | **The Metzler boundary: the 7-move shift; the dihedral obstruction; k = 4 exactly odd j** | SETTLED (kernel) | `bash m9/check.sh` (four files, 46 axiom lines) | **AUDITED r10: MetzlerSharp exit 0, 17 axiom lines** |
| **R10** | **The conjugator layer: faithfulness, the length-≤1 restriction, the transfer theorems, LP isolated** | SETTLED (kernel) + OPEN (LP) | `ACConj.lean`, `ACConjCex.lean`, `ACConjPeak.lean` | **AUDITED r10: ACConj 15 prints, ACConjCex 6 prints, all standard** |

---

## Appendix B.2 The round-10 and round-11 entries (85–94)

One line each, as `REPORT.md` carries them; the labels and checks are `REPORT.md`'s,
and the round-11 entries were accepted after the coordinator reran their checks.

| # | result | label | where |
| --- | --- | --- | --- |
| 85 | LP as recorded was **false**; the corrected lemma (`red w = w`) has all its cascade ingredients kernel-checked (15 axiom lines, all standard) | SETTLED (kernel) | `.ultramath/smw5c6gb0/m8/` |
| 86 | the kernel archive's build recipe, end to end: 34 files, 3 066 axiom reports, all standard, `VERDICT: PASS` in 13 min 36 s | SETTLED (kernel) + build | `.ultramath/smw5c6gb0/m5/` |
| 87 | the three T = 17 derivations: explicit twelve-move paths from AK(3) to length-25 states in all three classes (F1 2 320 moves, F2 7 069, F3 2 145) | SETTLED (computation) | `.ultramath/smw5c6gb0/m3/` |
| 88 | the cap-17 closed-set certificate `Row17.row_T_c17`, 136 576 states, standard axioms, 26 min by the static slot array; cap-16 reproduced the same way | SETTLED (kernel) | `.ultramath/smw5c6gb0/m10/` |
| 89 | the final report drafted (1 640 lines) and first-refereed: five defects with exact fixes | AUDIT | `.ultramath/smw5c6gb0/m1/`, `m2/` |
| 90 | the w24/w25 key counts decoded: cumulative dumps to length 17, the 158 320 identified (633 280 presentations), no discrepancy | SETTLED (computation) | `.ultramath/smw5ghp91/m6/` |
| 91 | the seventeen kernel-checked negatives are **full-conjugator** negatives: 56 (row, cap) pairs, 33 297 984 conjugate instances, 0 failures; +22 849 848 on AK(3) | SETTLED (computation) | `.ultramath/smw5ghp91/m2/` |
| 92 | the corrected peak lemma **LP in the kernel** with the relator-1 mirror and the `ACBounds`–`ACConj` language bridge (36 axiom lines, all standard); D-LP1/D-LP2 recorded; the Metzler 3-cycle bridge in the same round's entry | SETTLED (kernel) | `.ultramath/smw5ghp91/m5/` |
| 93 | the peak ledger to total length 18: 22 653 exact among 23 322 rows; the combined ledger 57 115 rows, 51 499 exact — [r12, entry 95] the cap-25 push takes these to 22 920 of 23 322 and 51 766 of 57 115; `ACPeaks18.lean` | SETTLED (computation) + (kernel) | `.ultramath/smw5ghp91/m8/` |
| 94 | the kernel archive consolidated and installed: 829 files, three tiers, all rebuilt, 3 140 axiom reports all standard | SETTLED (kernel) | `.ultramath/smw5ghp91/m3/`, `toolkit/lean/` |

Round 12's entry 95 — the cap-25 push on the length-18 open bucket, `REPORT.md`'s
last numbered entry — is the [r12, entry 95] note in row 93 above and §3.4's dated
paragraph; it is not a row of this table.

## Appendix C. The round-10 and round-12 checks, with commands and outputs

Everything in C.1–C.4 was run for this report, from the repository root, in round
10; C.5 is round 12's recount.
The artifacts are in `.ultramath/smw5c6gb0/m1/`.

### C.1 `checks/recount.py` — the round-9 counts, recomputed

```
$ python3 .ultramath/smw5c6gb0/m1/checks/recount.py
== m3, ledger9.tsv (AC-19 peak ledger to length 17) ==
  rows                : 33793
  exact peaks         : 27124
  open (no exact peak): 6669
  exact-peak histogram: {3: 4, 4: 4, 5: 8, 6: 12, 7: 54, 8: 50, 9: 139, 10: 149,
                         11: 352, 12: 277, 13: 1043, 14: 1092, 15: 4160, 16: 4977,
                         17: 14765, 18: 38}
  open rows lower bnd : {18: 6669}
  rows by length      : {3: 4, ..., 15: 5248, 16: 6196, 17: 18426}
  open rows by length : {13: 13, 14: 62, 15: 673, 16: 992, 17: 4929}
  length-17 rows      : 18426 exact 13497 open 4929
  cross-check 4,532 + 445 = 4,977 at peak 16 : True (file says 4977)
  cross-check 13,477 + 1,288 = 14,765 at 17  : True (file says 14765)
  cross-check open   = 1,740 + 4,929 = 6,669 : True
  every open row has a lower bound >= 18    : True
== m3, certs_cap17.txt ==
  comment lines       : 3
  certificate lines   : 15210
  distinct starts     : 15210
== m5, the 113-row depth-26 set ==
  data rows           : 113
  distinct presentations: 78
  distinct AC19 refs  : 113
  cap-26 certificates : 108
  moves per certificate: min 302 max 443
  distinct starts     : 108
== m6, certs_inball16.txt (geodesic archive) ==
  certificates        : 186649
  moves in total      : 2617043
  longest certificate : 96
  length-15 part      : 129288
== toolkit/lean (static inventory) ==
  17 files, 89382 lines, 9138 theorem/lemma declarations, 2749 #print axioms
```

(The last line uses the looser "any occurrence" convention throughout: 2 749
occurrences of `#print axioms`, of which 2 747 are at the start of a line, and
9 138 theorem/lemma occurrences, of which 9 137 are declarations at the start of a
line — section 8.1 and E7. The script counts a file's lines as newlines + 1, hence
89 382 = 89 365 + 17 for the 17 files; section 8.1's 89 365 is the `wc -l` number.
Round 12's recount in C.5 uses the caption's convention and prints 9 137.)

### C.2 If I had only one check to leave behind

It is this one, because it touches the campaign's headline round-9 result:

```
$ cd .ultramath/smw4sqc1u/m2 && python3 check_three.py
campaign cap-23 census, minimal-length-17 forms: 217
F1: ... minlen 17  fixed point: True  in the campaign's 217: False  keys 9/9 (23, 25)
F2: ... minlen 17  fixed point: True  in the campaign's 217: False  keys 7/7 (23, 25)
F3: ... minlen 17  fixed point: True  in the campaign's 217: False  keys 4/4 (25)
   F1/F2/F3: explicit states of total length 23/23/25 punf to the form: True
class file .../work/cls25.bin holds 5237072 classes
   recorded keys present in the census: 9/9, 7/7, 4/4
OVERALL: PASS
```

### C.3 The kernel audit

```
$ cd .ultramath/smw5c6gb0/m1/kernel && python3 kernel_summary.py
file    rc errors prints axiom_lines none axiom_sets
AC      0  0      42     41          1    6xPCS; 32xPS; 3xP
AC2     0  0      47     46          1    29xPCS; 17xPS
AC3     0  0      84     83          1    51xPCS; 32xPS
AC4     0  0      318    317         1    285xPCS; 32xPS
AC7     0  0      40     40          0    32xPCS; 6xPS; 2xP
AC8     0  0      16     16          0    14xPCS; 2xPS
AC19eleven 0 0    95     94          1    62xPCS; 32xPS
ACPeaks 0  0      98     97          1    65xPCS; 32xPS
ACPeaks17 0 0     91     90          1    58xPCS; 32xPS
ACBounds/ACClosed/ACKeys/ACTree/ACComponents/ACPack  0  0  0  0  0  -
audit   0  0      28     26          2    12xP; 10xPCS; 4xPS
ACConj  0  0      15     15          0    14xPCS; 1xPS
ACConjCex 0 0     6      6           0    6xP
MetzlerSharp 0 0  17     17          0    14xPCS; 3xPS
audit_r9 0 0      18     18          0    15xPCS; 1xPS; 2xP
```

plus `ak_trivial.lean` (11 prints, 11×PCS) and `stabilization-moves.lean` (5 prints,
5×PS). No `sorryAx`, no set outside the standard three.

```
$ cd .ultramath/smw5c6gb0/m1/kernel && lean audit_r9.lean
'MetzlerSharp.abelian_metz_one' depends on axioms: [propext, Classical.choice, Quot.sound]
... (18 lines, all standard)
```

### C.4 The static checks behind D1–D9

```
$ ls survey/stabilization-moves-check.py            # D2: the cited file does not exist
$ python3 survey/stabilization-moves-check.py       # 29 checks run / all checks passed
$ sed -n '49p' directions/whitehead/work/run_all.sh # D3: cd ../../../../directions/cap21
$ sed -n '101p' directions/carreras-minimax/verify_path.py  # D4: sys.argv[1]
$ grep -n 'results/' directions/experiment-01/test_ac_experiment.py | head  # D1: relative
$ ls .ultramath/smw2fzjic/m8/triviality_check.py    # D8: entry 8's author
$ ls .ultramath/smw2fzjic/m6/work/SAIR_AC.lean      # D8: entry 11's artifact
```

### C.5 The round-12 checks (this finalisation)

Everything here was run from the repository root on 7 November 2026, in round 12,
by `python3 .ultramath/smw5n5txi/m1/checks/r11_recount.py`; the script is the
deliverable and the output below is its whole output, verbatim (the file
`checks/r11_recount.out` holds the same bytes). It is a **recount**, not a
recomputation: every line reads a shipped data file and counts. The last block is
round 9's, included because those counts are the report's headlines and the draft's
round-10 recount had already verified them.

```
$ python3 .ultramath/smw5n5txi/m1/checks/r11_recount.py
== toolkit/lean tree (installed round 11) ==
  .lean files total      : 829
  tier1 (top level)      : 37
  tier2 (instances/)     : 776
  tier3 (instances/rows) : 16
  manifest rows toolkit/lean/MANIFEST.tsv                  37
  manifest rows toolkit/lean/instances/MANIFEST.tsv        776
  manifest rows toolkit/lean/instances/rows/MANIFEST.tsv   16
  present ACPack.lean        True
  present ACSlot.lean        True
  present audit_r9.lean      True
  present README_BUILD.md    True
  present ACPeaks18.lean     False
== m8, the peak ledger to total length 18 (entry 93) ==
  length-18 rows: 23322 exact: 22653 open: 669
  exact-peak histogram: {'18': 19265, '19': 2045, '20': 526, '21': 703, '22': 114}
  lower bounds of open: {'21': 143, '22': 92, '23': 434}
  combined ledger rows: 57115 exact: 51499 open: 5616
== m2, the full-conjugator upgrade (entry 91) ==
  (row, cap) pairs: 56  conjugate instances: 33297984  rows with fails: 0
  AK(3) caps 14-17 : 22849848 instances, 0 fails: True
== m10, the audit trail (section 5.2) ==
  rows: 67  status: {'CONFIRMED': 52, 'LOCATED': 1, 'PARTIAL': 1, 'REFUTED': 7, 'STALE': 5, 'UNCHECKED': 1}
== m5, the LP build log (entry 92) ==
  'depends on axioms' lines: 36  sets: {'[propext, Classical.choice, Quot.sound]': 31, '[propext]': 2, '[propext, Quot.sound]': 3}
  sorryAx lines: 1  error lines: 0
== the 17 core kernel files, section 8.1's convention (E7) ==
  AC.lean          lines    600 decls    37 prints    42
  QSound.lean      lines   1199 decls    45 prints     0
  ACTree.lean      lines    147 decls    10 prints     0
  TOTAL lines 89365 decls 9137 prints 2747
== round-9 counts the report headlines ==
  ledger9.tsv rows: 33793  exact: 27124  open: 6669
  certs_cap17.txt certificates: 15210
  geodesic archive certificates: 186649  moves: 2617043  longest: 96  length-15 part: 129288
  depth-26 rows file: 113
```

The counts that matter, and where they land: **829 = 37 + 776 + 16** (§8.6);
**23 322 / 22 653 / 669** and **57 115 / 51 499 / 5 616** (§3.4, entry 93);
**33 297 984** and **22 849 848** conjugate instances with 0 failures (§3.1, entry
91); **67 = 52 + 7 + 5 + 1 + 1 + 1** (m10's audit trail, §5.2); **36** LP axiom
lines, none outside the standard three and no error line (§3.7, entry 92); the
inventory at **89 365 lines / 9 137 declarations / 2 747 prints**, which is E7 /
m7's D1 (`ACTree.lean` = 10) independently confirmed; and round 9's **33 793 /
27 124 / 6 669**, **15 210**, **186 649 / 2 617 043 / 96 / 129 288** and **113**,
which are the numbers §3.1, §3.4 and §3.5 print.

One line of the output needs its gloss: `sorryAx lines: 1` is the scan's own header
line (`---- sorryAx / native_decide / standalone sorry in sources (want 0 0 0):`),
and the per-file counts under it are 0 for each of LP9, LP10 and LP11 (three scans
each). There is no `sorryAx` in any LP source.


---

## Appendix D. The file map

```
REPORT.md                the ledger: 95 entries, sections 2–5
STATE.md                 the coordinator's log and bookkeeping corrections
OPEN_QUESTIONS.md        the 27 questions (round-3 vintage at the repository root;
                         round 10's rebuild is .ultramath/smw5c6gb0/m9/; section 7
                         here is the report's authority)
charter.md               the original task document
rounds/round-01..12.md   the round reports
survey/                  the literature and method surveys, with their check scripts
toolkit/                 the Python toolkit and lean/ — since round 11 the installed
                         three-tier kernel archive: 829 .lean files, three
                         MANIFEST.tsv, README_BUILD.md
directions/              34 named directions: certificates, censuses, Lean programs
results/                 (empty: every result lives with the direction that made it)
checks/                  two shared checkers (ak_check.py, todd_coxeter.py)
.ultramath/smw*/         per-round member directories, by swarm id:
   smw2fzjic  round 1       smw4sqc1u  round 9
   smw2i9i4j  round 2       smw5c6gb0  round 10  (this report's draft: m1/)
   smw2opo0o  round 3       smw5ghp91  round 11  (the archive: m3/, the LP: m5/,
   smw2woueq  round 4                                the ledger to 18: m8/)
   smw38010i  round 5       smw5n5txi  round 12  (this finalisation: m1/)
   smw3ow2dp  round 6
   smw48or9f  round 7       .ultramath/smw4sqc1u/m1/  the round-9 audit
                             checks.tsv, kernel_inventory.tsv, ledger.tsv, leanlogs/,
                             audit-findings.md, final-report-draft.md
```

The results a reader is most likely to want, by path:

| what | where |
| --- | --- |
| the kernel archive | `toolkit/lean/` — 829 Lean files in three tiers as of round 11 (section 8.6), with the individual files' provenance in section 8.3 |
| the census and the length-14 classification | `directions/c14/`, `directions/pu-enumeration/`, `directions/resisters/` |
| the AK(3) boxes | `directions/cap21/`, `cap24/`, `cap25/`, `.ultramath/smw4i604a/m9/` |
| the AC-19 data and certificates | `directions/carreras-minimax/sources/ac19/`, `directions/ac19/`, `.ultramath/smw4sqc1u/m3/` |
| the round-9 geodesic archive | `.ultramath/smw4sqc1u/m6/certs_inball16.txt` |
| the round-9 T = 17 census | `.ultramath/smw4sqc1u/m2/CENSUS25.md`, `work/cls25.bin` |
| the round-9 depth-26 set | `.ultramath/smw4sqc1u/m5/rows_depth26_113.txt`, `certs_cap26_108.txt` |
| the round-9 packed certificate | `.ultramath/smw4sqc1u/m8/ACPack.lean`, `ACQ16b*`, `C17data.lean` |
| the round-9 Metzler layer | `.ultramath/smw4sqc1u/m9/` |
| the round-9 conjugator layer | `.ultramath/smw4sqc1u/m10/ACConj*.lean`, `ACConj.md` |
| this report's round-10 checks | `.ultramath/smw5c6gb0/m1/checks/`, `kernel/` |
| this report's round-11 and round-12 inputs | `.ultramath/smw5ghp91/m1/referee-verdict.md` (E1–E14), `m7/FINAL.md` (D1–D12), `m3/PATCH_FOR_SECTION_8.md` and `ARCHIVE_REPORT.md` (D-1…D-7), `m2/REPORT.md` (Q28/Q29), `m10/AUDIT_TRAIL.tsv` and `CORRECTIONS_ADDENDA.md`, `m5/LP9-11.lean`, `m8/ledger18.tsv` |
| this finalisation's checks and change log | `.ultramath/smw5n5txi/m1/checks/r11_recount.py`, `patch.py`, `CHANGE_LOG.md` |

---

*End of report. Drafted in round 10 (swarm smw5c6gb0, member m1, direction M1),
finalised in round 12 (swarm smw5n5txi, member m1, direction M1) by applying the
merged round-11 patch list to a copy of the draft and folding in the round-11
results. The labels, the checks and the limits are the campaign's; the round-10
recount and kernel audit are mine, the round-11 results are their directions' (each
with the coordinator's rerun), and the round-12 recount and the change log are mine.
Nothing here is a claim for or against the Andrews-Curtis conjecture.*
