# directions/ — an index

**What this directory is.** The campaign's per-direction working artifacts: one
subdirectory per research direction, each holding its report (a `.md` file whose
every claim is labelled and carries a rerunnable check), its code, and its data.
32 subdirectories, 618 MB, 1,300-odd files, spanning rounds 1 to 9 of the
campaign (4–8 November 2026). The bulk of the size is enumerated state data and
downloaded primary sources, not prose: the six largest subdirectories hold 569 of
the 618 MB, and most of that is binary state dumps and class lists.

**How to read it.** Each subdirectory's main report is the entry point (named
below). The authoritative summary of what each direction established is
`REPORT.md`'s ledger at the repository root (95 numbered entries, each citing its
file and its check); the round-by-round narrative is `rounds/round-01.md` through
`round-13.md`; the delivered campaign summary is `FINAL_REPORT.md`. This index
tells you what is in each subdirectory and which ledger entries rest on it.
Nothing in this directory is a claim for or against the Andrews-Curtis
conjecture.

**What is not here.** The kernel archive (829 Lean files) is installed at
`toolkit/lean/`. The members' full working directories (including the search
engines' raw outputs, the transcripts and the later rounds' artifacts) are under
`.ultramath/<swarm-id>/m<N>/`. The per-round referee verdicts are in
`STATE.md` and the round files.

---

## The map, one line per subdirectory

| subdirectory | size | rounds | what it established | main report | ledger entries |
| --- | ---: | --- | --- | --- | --- |
| `ak-status/` | 48 K | 1 | AK(n) presents the trivial group for every n, in Lean | — (`ak_trivial.lean` is the artifact) | 1, 8 |
| `experiment-01/` | 236 K | 1 | AK(3)/AK(4)/AK(5) are strict local minima under every single AC move; bounded negatives with exact bounds | `experiment.md` | 3, 7 |
| `ms-ak-certs/` | 352 K | 2 | MS(n, w₁) is AC-equivalent to AK(n) for n = 2–10; the obstruction at k ≠ 1 | `ms-ak-certs.md` | 13 |
| `ak-ladder/` | 3.6 M | 2–3 | the uniform ladder step MS(n, w_k) ~ MS(n, w_{k+1}); the ≤11 frontier | `ak-ladder-final.md` | 19 |
| `pu-enumeration/` | 6.9 M | 2–3 | the Panteleev–Ushakov table reading corrected (exactly-T cells); the punf canonical form machinery | `pu.md` | 18–22 |
| `pu-gap/` | 2.7 M | 3–4 | class C's printed normal form corrected; the cap-23 census of the AK(3) class | `pu-gap.md` | 22, 30 |
| `c14/` | 16 M | 1–3 | the complete length-14 classification: 57,765 rows, 53,866 certificates, 164 resisters, the four PSL(2,7) rows | `c14.md` | 15, 19–24 |
| `resisters/` | 332 M | 3–8 | the resisters push: 98 of 164 decided (r3); the conjugator-independence theorem (r4); the falls, c(14) ≤ 20 (r7); the nine exact closed boxes (r8) | `resisters.md`, `resisters-round4.md` | 30–34, 59, 71, 73 |
| `cap21/` | 56 M | 4–5 | the cap-21 census: class C excluded to length 25; the T = 17 deficit first measured; the PU-class counts 39,840 / 144,292 | `cap21.md` | 32–35 |
| `cap24/` | 31 M | 5 | the cap-24 census: the T = 17 deficit 12 at caps 23 and 24, no length-17 class entering | `cap24.md` | 41 |
| `cap25/` | 1.5 M | 7–9 | class C resolved (exact peaks 15/18/19, the whole length-13 slice decided); T = 17 at cap 25 settled (r8); the cap-25 box tools | `cap25-round7.md`, `README.md` | 57, 74 |
| `worst-case/` | 73 M | 4–5 | the 91-move worst case; H8: the length-5-relator family, the exact multiplication count, the (5,10) bucket | `H8-report.md` | 38–42 |
| `hardness/` | 30 M | 3 | the Shehper et al. difficulty score tested and refuted (Spearman +0.0060); the finite-barcode census; the l-increase bounds | `hardness.md` | 12, 38 |
| `certificate-algebra/` | 160 K | 5 | the certificate algebra: composition, transports, the 259,755-replay engine | `report.md` | 38 |
| `whitehead/` | 284 K | 4–5 | the Whitehead minimisation and the A/B split (4 and 8, resolved r5); the 16-vs-20 generator gap | `whitehead.md` | 39 |
| `invariant-ideas/` | 116 K | 1–3 | the winding invariant's degeneracy; the rank-0 boundary; what no invariant factoring through the normal closure can see | `idea.md` | (failed ideas 9–10) |
| `downward-propagation/` | 220 K | 4–8 | the Key Step; Theorem 4′ (the wall-avoiding punch route ~ X₁ → *); PTT reduced to Conjecture G; the cone4 and dunce models | `report.md`, `keystep.md` | 50, 65, 71 |
| `zeeman-positivity/` | 60 K | 3 | Zeeman positivity: the backward direction's elementary-3-collapse question | `zeeman-positivity.md` | (round-3 record) |
| `qdouble-star/` | 8.5 M | 2–8 | the Q\*\* layer: the Metzler certificate and family (r6); the tooling defects found and fixed; the round-4/5 Q\*\*-status work | `qdouble-star.md` | 34–37, 44–49 |
| `psl27-frontier/` | 144 K | 4 | the four PSL(2,7)-surjective length-14 rows present infinite groups | `answer.md` | 24 |
| `p-trivial/` | 4.5 M | 2–7 | the p-trivial certifier; `replay12.py`, the campaign's standing independent twelve-move replayer (the third replayer of rounds 12–13) | `p-trivial.md` | (tooling) |
| `ac-graph-diameters/` | 6.8 M | 4 | exact diameters of the AC graphs of finite perfect groups (A₅: 3,599 vertices, degree 126, diameter 8) | `README.md` | (round-4 record) |
| `carreras-minimax/` | 47 M | 5–7 | the independent audit of arXiv:2607.23611 (all nine state counts and the certificate table reproduced to the digit); **holds the AC-19 primary sources** (`sources/ac19/`: AC19.txt, AC19_extended.txt, 1190MS.txt — the peak ledger's universe) | `README.md` | 9, 41, 52–56 |
| `ac19/` | 312 K | 7 | the AC-19 eleven: explicit certificates at peak exactly 26, kernel-checked; the 1,237-row harvest | `README.md` | 55, 63 |
| `lean-program-3/` | 20 K | 3 | the Lean program 3 report (the Q\*\* layer's first formalisation steps) | `lean-program-3.md` | (round-3 record) |
| `lean-program-5/` | 4 K | 5 | empty (the direction's deliverable landed in `toolkit/lean/` and the member directory; nothing was installed here) | — | — |
| `lean-program-6/` | 104 K | 6 | AC6.lean's build and audit scripts (the transcription audit with doctoring controls; the file itself is in `toolkit/lean/`) | `report.md` | 50 |
| `lean-program-7/` | 32 K | 7 | AC7.lean's README, the Metzler family's build record and the stage-2 defeq obstruction note | `README.md` | 54 |
| `second-referees/` | 32 K | 2 | the round-1 artifacts' second referee (the complexity survey's three substantive errors) | `referee.md` | (round-2 record) |
| `second-referees-2/` | 36 K | 3 | the round-2 artifacts' second referee | `referee.md` | (round-3 record) |
| `second-referees-3/` | 192 K | 3 | the round-3 targets audited with code written from the definitions | `referee.md` | 33–36 |
| `second-referees-4/` | 232 K | 4 | the round-4 audit: all six targets SOUND, the cap-24 documentation defect, the transfer-sentence repair | `referee.md` | 44–47, 64 |

---

## The subdirectories in detail

### The censuses and the boxes (the six largest)

**`resisters/` — 332 M, the campaign's largest directory.** The push against the
164 length-13/14 presentations that resisted classification. Round 3 decided 98
of them (`resisters.md`); round 4 built the standard-pair balls and the conjugator
machinery (`resisters-round4.md`, `round4/` — the bulk of the size is the ball
key dumps `target.u64`, `std16keys.u64`, `std15keys.u64`, `ak3keys.u64` and the
`push/` engine's outputs); rounds 6–7 certified the falls (c(14) ≤ 20, the 50
undecided in nine ~-classes); round 8 built the nine exact closed boxes. The
final ledger: 50 undecided presentations in at most 9 classes, depth ≥ 24/26/29/30.
Entry point: `resisters.md`, then `resisters-round4.md`.

**`worst-case/` — 73 M.** The worst-case direction: the 91-move certificate, and
H8, the length-5-relator family study (`H8-report.md`) — the exact multiplication
count, the (5,10) bucket structure, M(cap) = 7,8,9,10,11,12,18,23,34. The bulk is
`h8/` (35 M of census dumps) and `data/` (7.3 M). Entry point: `H8-report.md`.

**`cap21/` — 56 M.** The cap-21 census of the AK(3) class (`cap21.md`): the
disk-backed enumeration, class C excluded to length 25, the T = 17 deficit first
measured, the PU-class counts 39,840 (cap 20) and 144,292 (cap 21). The bulk is
`results/` — the per-cap class lists (`classes20.txt` … `classes23.txt.gz`) that
every later census re-reads. This directory also holds `punf.py`, the PU normal
form used across the campaign. Entry point: `cap21.md`.

**`carreras-minimax/` — 47 M, and load-bearing beyond its audit.** The
independent audit of arXiv:2607.23611 (`README.md`): all nine published state
counts, the classification table and the certificate table reproduced to the
digit. But the directory also holds **the AC-19 primary sources** under
`sources/ac19/` — `AC19.txt` (140,535 rows), `AC19_extended.txt` (156,762) and
`1190MS.txt` (1,190) — which are the peak ledger's universe (REPORT.md entries
77, 79, 93, 95: 57,115 rows of length ≤ 18, 51,766 exact). Any rerun of the
ledger starts here. Entry point: `README.md`.

**`cap24/` — 31 M.** The cap-24 census (`cap24.md`): the T = 17 deficit answered
with a negative at caps 23 and 24 (exactly 12, no length-17 class entering), the
class-C exclusion extended to length 25, the per-length histograms the later
rounds re-derive (13:4032 14:15424 15:259392 16:354432 …). Entry point:
`cap24.md`.

**`hardness/` — 30 M.** The Shehper et al. difficulty measure tested on the
campaign's own data (`hardness.md`): the l-increase score refuted (Spearman
+0.0060 over 52,744 solved cases), the finite-barcode approximation shown
undefined exactly on the hard components, the full cap-20 barcode census. The
bulk is the state and edge dumps (`states_17.txt`, `states_18.txt`,
`edges_16.txt`). Entry point: `hardness.md`.

### The classifications and frontiers

**`c14/` — 16 M.** The complete classification of the length-14 stratum
(`c14.md`): 57,765 canonical rows, 53,866 replayed certificates (26 to AK(3),
the rest to the standard pair), 34 of order 120, 4 infinite, 164 resisters.
Holds the meet-in-the-middle searches (`certs_mitm*.txt`), the census stages and
`replay14.py` — the certificate replayer several later rounds borrow. Entry
point: `c14.md`.

**`ak-ladder/`, `pu-enumeration/`, `pu-gap/`, `cap25/`, `p-trivial/`,
`ac-graph-diameters/`** — the frontier and machinery directions, each summarised
in the table above. `cap25/` is the smallest of the census directories but the
one that settled class C; `p-trivial/`'s `replay12.py` became the campaign's
standing third replayer; `ac-graph-diameters/` holds the exact finite-group
diameter tables.

### The Lean programs

The Lean artifacts themselves live in `toolkit/lean/` (AC.lean through AC8.lean,
AC19eleven, the closed-set layers, and the 829-file consolidated tree). What
lives here is each program's build and audit machinery: `lean-program-6/`'s
transcription audit with its doctoring controls, `lean-program-7/`'s stage-2
obstruction note, `ak-status/`'s `ak_trivial.lean` (the campaign's first theorem),
and `ms-ak-certs/`' certificate generator. `lean-program-5/` is empty — its
deliverable landed elsewhere and nothing was installed here.

### The theory directions

`downward-propagation/` (the Key Step, Theorem 4′, PTT → Conjecture G, the cone4
and dunce models), `zeeman-positivity/`, `invariant-ideas/` (what no invariant
of this kind can see), `whitehead/` (the A/B split), `certificate-algebra/`
(composition and transport of certificates), `qdouble-star/` (the Q\*\* layer:
the Metzler certificate and family, the tooling fixes), `psl27-frontier/` (the
four infinite rows). Each is small (60 K – 8.5 M) and self-contained; each
report is the entry point.

### The second referees

`second-referees/` through `second-referees-4/`: the adversarial audits of
rounds 1–4's accepted artifacts, each with code written from the definitions
rather than the authors' scripts — the campaign's standing verification pattern,
later formalised into rounds 11–13's referee passes. The later audits (rounds
5–13) live in the member directories under `.ultramath/`, not here.

---

## Sizes, and what to do about them

The 618 MB is dominated by six directories (resisters 332 M, worst-case 73 M,
cap21 56 M, carreras-minimax 47 M, cap24 31 M, hardness 30 M = 569 M). Of that,
the bulk is regenerable data: binary state-dump and key files (`*.u64`, `*.bin`),
per-cap class lists, and census dumps — all produced by the engines whose source
sits beside them, with the exact commands in each report's rerun section. The
47 M of `carreras-minimax/sources/` is the exception: it is downloaded primary
data (the published AC-19 files), not regenerable, and the peak ledger depends
on it — do not delete it. Nothing else in the tree needs the bulk to survive:
the reports, the code and the certificate files together come to well under
40 M.

*Index written 7 November 2026, at the campaign's close. Sizes are `du -sh`
measurements taken today; the ledger citations are REPORT.md's entry numbers.*
