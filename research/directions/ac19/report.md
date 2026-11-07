# Round 7, direction J7: the eleven AC-19 rows at peak exactly 26, kernel-checked, and 1,237 harvested certificates

Member m3, swarm smw48or9f. Every statement below carries one of the campaign's
labels: **[Verified]** a machine check with the command given, **[Computed]** a
number from a stated run, **[Argument]** a proof written out, **[Quoted]** taken
from another artifact, **[Open]** not settled. Nothing here is a claim for or
against the Andrews-Curtis conjecture, and nothing here says that any
presentation is nontrivial.

All files are in `.ultramath/smw48or9f/m3/`. Paths are relative to the
repository root unless stated. The heavy input this direction consumes is round
6's: the eleven rows and their paths to the resister are
`.ultramath/smw3ow2dp/m10/` (direction I10, table_11.tsv / hits.json), and the
resister's own 231-move certificate is `.ultramath/smw3ow2dp/m1/cert_fall.txt`
(direction I1).

## 0. Summary

1. **The eleven rows now have explicit certificates at peak exactly 26.**
   Round 6 proved that each of eleven rows of the AC-19 dataset that sit inside
   the exhausted cap-25 component of `BBAAbaa,BBabABA` needs peak at least 26
   for any Andrews-Curtis trivialisation, and never exhibited a certificate for
   any of them. This direction writes one certificate per row down and replays
   it: 245, 250, 254, 260, 408, 407, 419, 417, 415, 424, 422 moves, every
   intermediate of total relator length at most 26. Together with the cap-25
   lower bound (**reproduced here**, 38,286,952 states, no hit) the peak of each
   of the eleven is **exactly 26**. `certs_11.txt`,
   `check_certs11.py`. **[Verified]**
2. **The eleven certificates are in the Lean kernel.** `AC19eleven.lean` is
   `toolkit/lean/AC3.lean` verbatim followed by the eleven certificates,
   checked by `decide` in blocks of 24 moves and glued with `checkCert_append`;
   `lean AC19eleven.lean` exits 0 and prints
   `'AndrewsCurtis.c11_i' depends on axioms: [propext, Classical.choice, Quot.sound]`
   for `i = 0..10`, which is Lean's standard set (the same three axioms the
   campaign's AC3/AC4/AC6 print). Because the 231-move resister certificate is
   the common tail of all eleven chains, the kernel also validates **m1's
   round-6 resister certificate** as part of the run. **[Verified]**
3. **All eleven are rows of the AC-19 dataset**, checked with my own parser:
   `AC19.txt` 0-based lines 54524, 14965, 35322, 52847, 112516, 113759, 95275,
   30388, 38969, 78175, 48340; total relator lengths 17, 17, 16, 17, 17, 17, 19,
   19, 19, 19, 19; every one with `|det| = 1`. `a19membership.py`. **[Verified]**
4. **A harvest of 1,237 further certificates.** Every state on a
   standard-ending certificate chain is itself AC-trivial, at the peak of the
   rest of the chain. Matching the class key of a state against the 140,535
   rows of `AC19.txt` turns that into certificates: **1,237 rows of total length
   15 to 19** now carry an explicit twelve-move certificate to the standard
   pair (633 at length 15, 159 at 16, 262 at 17, 67 at 18, 116 at 19; 23 to 424
   moves; peaks 15 to 30), each replayed move by move with 0 failures; 1,226 of
   them are outside the eleven of item 1 (the eleven are among the 1,237
   because their own chains are part of the harvest's input).
   `harvest2.py`, `certs_harvest.txt`, `check_certs11.py`. **[Verified]** The
   campaign's earlier certificate archives start at presentations of total
   length at most 14 (Section 4), and AC-19 ships no move sequence at all (round
   6's finding), so these rows had no certificate anywhere before.
   **[Computed]**
5. **The transport lemma, rechecked here.** The five Andrews-Curtis relator
   moves that are not among the twelve are realised by twelve-move sequences
   whose peak never exceeds the larger of the two end lengths: 3,200 random
   instances, 0 failures. `transports_check.py`. **[Verified]** This is what
   upgrades the cap-25 exhaustion (a twelve-move computation) to a bound for
   the full Andrews-Curtis move set.

**What depends on whom.** The eleven certificates are (row → resister) followed
by (resister → standard). The second part is m1's round-6 certificate; I did not
construct an independent one (Section 6). So items 1 and 2 are **conditional on
m1's certificate being correct**, and the kernel check in item 2 is an
independent validation of it, not a replacement for it. The lower bound of item
1 uses the round-4 engine `directions/resisters/round4/acx`, which I ran myself
but did not write.

## 1. The eleven rows, their certificates, and their exact peak

### 1.1 What the eleven are

Round 6 (m10, direction I10, `.ultramath/smw3ow2dp/m10/`) exhausted the
total-length-25 component of the resister `P0 = BBAAbaa,BBabABA`
(38,286,952 states, no state in the class of the standard pair or of AK(3)) and
found inside it exactly eleven rows of the AC-19 dataset, each with a
twelve-move path from `P0` of peak at most 25. By round 6's Proposition 1, each
of the eleven therefore needs peak at least 26 for any AC trivialisation.

They are, with the distance from `P0` recorded by m10:

| row | length | moves from `P0` | peak of that path |
| --- | --- | --- | --- |
| `BBAAbaa,BAAABaaabA` | 17 | 2 | 21 |
| `BBAAABBaba,BBabABA` | 17 | 5 | 23 |
| `BBBBaBAAA,BBabABA` | 16 | 7 | 20 |
| `BBBBBABBAA,BBabABA` | 17 | 9 | 21 |
| `BABAAbaa,BABabABAA` | 17 | 108 | 25 |
| `BBABabbAA,BABAAbaa` | 17 | 113 | 25 |
| `BBABABABAbA,BABAAbaa` | 19 | 113 | 25 |
| `BBABAAABabA,BABAAbaa` | 19 | 114 | 25 |
| `BBAAAbaabaa,BABAAbaa` | 19 | 116 | 25 |
| `BBAAABaBAbA,BABAAbaa` | 19 | 117 | 25 |
| `BBAAAbbaaBa,BABAAbaa` | 19 | 119 | 25 |

### 1.2 The head of each certificate: row to the resister, peak at most 25

m10's paths end at a state whose class key (per relator: cyclically reduced,
minimal over rotations and inversion; the two relators sorted) equals the row's.
A class key is an AC-equivalence by per-relator conjugation, inversion and, if
needed, the exchange of the two relators, and each of those can be realised
explicitly. `ac12.py` builds the moves: conjugate the relator to its cyclic
core, optionally invert, rotate, then conjugate out to the target word, each
step a single-letter conjugation (`align_word`). The relator exchange, when the
two relators arrive in the crossed order, is the six-move sequence
`0 11 5 10 0 11`, verified on 2,000 random word pairs (`ac12.swap_moves_found`).

Two refinements were needed to keep every peak at 26 and not higher:

* exchanging the relators is expensive (`|u| + 2|v|` or `2|u| + |v|` on the
  pair `(u,v)`); doing it at the row costs up to 30 when the row has length 19.
  Instead the **whole path is mirrored** through the exchange (the move indices
  map `0↔5`, `1..4↔6..9`, `10↔11`), so the exchange is paid at the resister,
  where both relators have length 7 and the peak is 21.
* among the alternative joining points on the recorded path, the one with the
  smallest replayed peak is chosen.

The result (`segment_peaks.out`): the heads have 14, 19, 23, 29, 177, 176, 188,
186, 184, 193, 191 moves, peaks 21, 23, 20, 21, 25, 25, 25, 25, 25, 25, 25, and
each head ends **exactly** at `BBAAbaa,BBabABA` (not merely in its class).

### 1.3 The certificates

Appending m1's 231-move certificate from the resister to `a,b` gives
`certs_11.txt`: eleven lines `start|moves|std`, with 245, 250, 254, 260, 408,
407, 419, 417, 415, 424, 422 moves and peak 26 in every case.

### 1.4 The lower bound, reproduced

The round-4 engine, run by me in this session, from the resister with a
class-key target holding only the classes of the standard pair and of AK(3):

```
$ directions/resisters/round4/acx search 25 45000000 \
    .ultramath/smw48or9f/m3/res_cap25_mine.txt none \
    .ultramath/smw3ow2dp/m10/stdak.u64 .ultramath/smw3ow2dp/m10/start1.txt 1 \
    .ultramath/smw3ow2dp/m10/members.txt
...
EXHAUSTED | 25 | trio | 38286952 | 351.4s
```
38,286,952 states, no hit — the round-4 and round-6 count to the digit. Peak
RSS about 750 MB, 351 s of wall time. **[Computed]**

### 1.5 Exactness

Let `R` be one of the eleven and suppose `R` had an AC trivialisation with every
intermediate of total length at most 25. The head of Section 1.2 is an AC path
from `R` to `P0` with every intermediate of length at most 25, so concatenating
gives one for `P0` at peak at most 25, contradicting Section 1.4. Hence the peak
of `R` is at least 26; Section 1.3 gives at most 26. **The peak of each of the
eleven is exactly 26.** **[Argument]** on **[Verified]** facts, the only input
not verified in this session being the transport lemma, which Section 5
rechecks on random instances.

For the *full* Andrews-Curtis move set (which allows left multiplication and
conjugation by an arbitrary word), the same conclusion needs the transport
lemma: every AC path of peak `p` becomes a twelve-move path of peak at most `p`.
Section 5 verifies the five non-twelve relator moves on 3,200 random instances,
with the peak never above `max(start, end)`.

## 2. The Lean file

`AC19eleven.lean` (7,547 lines, 361 KB) is `toolkit/lean/AC3.lean` verbatim,
then `namespace AndrewsCurtis`, then per certificate: the start and finish
presentations as `mkPres` lists, the moves in blocks of 24, one
`theorem c11_i_bk : checkCert ... = true := by decide` per block (with
`set_option maxRecDepth 100000`), the gluing `c11_i_k1 ... c11_i_kN` through
`checkCert_append`, and

```
theorem c11_i : ACEquiv c11_i_s c11_i_t := checkCert_sound c11_i_check
#print axioms c11_i
```

`c11_i_t` is the tuple `((a),(b))`, i.e. the standard pair written out. The file
is generated from `certs_11.txt` by `gen_lean.py`, so the kernel and the Python
checker check the same move lists.

Run: `lean AC19eleven.lean` — exit 0 after 16 min 18 s of wall time on a loaded
4-CPU VM; eleven `#print axioms` lines, all
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no
new axiom. Log: `lean_run.log`. **[Verified]**

Why this matters beyond the eleven: the last 231 moves of every chain are m1's
round-6 resister certificate, so the kernel proves the resister's AC-triviality
as well, from cert_fall.txt's move list, under AC3's independent definitions of
`invertAt`, `conjAt`, `mulAt` and `replay`. That is a third, independent check of
the round-6 draft's central certificate (the other two are m1's own replay and
the coordinator's round-6 replay with `replay14.py`).

## 3. Dataset membership

`a19membership.py` parses `AC19.txt` itself (48 integers per line, two
zero-padded blocks of 24, letters `1=a -1=A 2=b -2=B`), converts each row to
the campaign's letter notation, and looks for the eleven. All eleven are found,
at the line numbers and lengths of Section 0 item 3, and all have `|det| = 1`.
Nothing about membership is taken from round 6 on trust here.

## 4. The harvest: 1,237 further certificates

**Idea.** A state `s` on a certificate chain that ends at the standard pair is
itself AC-trivial, with a certificate of peak equal to the peak of the rest of
the chain. Any presentation whose class key equals the key of `s` is
AC-equivalent to `s` by per-relator conjugation and inversion (Section 1.2), so
it is AC-trivial at peak `max(peak of the alignment, peak of the rest)`.

**Chains used.** `directions/c14/certs_all.txt` (53,866 lines, 53,840 of which
end at the standard pair; the other 26 end at AK(3) and were skipped — a
reproduction of the census's 26 AK(3)-equivalent rows), `directions/resisters/std_certs.txt`
(72), `certs_fall8_idx.txt` (m1's eight, 8), `certs_11.txt` (11). Together
53,931 chains and 1,487,313 states. **[Computed]**

**Filter.** AC-19 rows are cyclically reduced, so a match requires the multiset
of cyclic-core lengths of the state to be one of the 25 multisets occurring
among the rows of length at least 15; only states passing that filter get a full
class key. This is what keeps the run under half a minute.

**Result.** 1,237 rows of `AC19.txt` of total length 15 to 19 have an explicit
certificate: by length 633, 159, 262, 67, 116 at lengths 15, 16, 17, 18, 19; by
peak 214, 21, 165, 133, 107, 51, 136, 75, 105, 42, 71, 53, 34, 12, 8, 10 at peaks
15 to 30; 23 to 424 moves. All 1,237 replay with 0 failures under
`check_certs11.py`. The eleven rows of Section 1 are among the 1,237 — their own
chains are part of the input, so each matches its own first state — and the
harvest therefore adds **1,226 rows** that had no certificate before.

**No completeness claim.** The harvest certifies the rows whose class key happens
to lie on one of 53,931 chains. Nothing is said about the remaining ~135,000
rows of length at least 15: they are neither certified nor bounded here. A row
that is not in the harvest is simply not reached by this method.

**Novelty.** The certificate archives of rounds 1 to 6 start at presentations of
total length at most 14, with two exceptions found by a scan of 331,230
certificate-like lines in 36 files of `directions/`: 63 hit-path fragments in
`directions/resisters/results/allhit_paths.txt` (17 starting at length 15, 45 at
16, 1 at 14) which end at a search hit rather than at the standard pair, and
`directions/c14/ms_family_7_7.txt`, which is a Miller-Schupp family listing and
not a certificate file. AC-19 itself ships no move sequence at all (round 6's
finding, re-read there against the live repository). So none of these 1,226 rows
had a certificate before. **[Computed]**

## 5. The transport check

`transports_check.py`, seed 20261106, 400 random pairs and all five non-twelve
relator moves:

| move | twelve-move realisation | moves |
| --- | --- | --- |
| `r_i → r_i r_j^{-1}` | `inv_j, mul_i, inv_j` | 3 |
| `r_i → r_j^{-1} r_i` | `inv_i, mul_i, inv_i` | 3 |
| `r_i → r_j r_i` | `inv_i, inv_j, mul_i, inv_i, inv_j` | 5 |
| `r_i → w r_i w^{-1}` | conjugate through the cyclic core (Section 1.2) | at most `2|w| + 4` |
| `r_i → r_i^{-1}` | `inv_i` | 1 |

3,200 checks, 0 failures, and in every case the peak of the realisation is at
most the larger of the two end lengths. (A first version of the
left-multiplication row above was wrong — it dropped the final `inv_j` — and the
check caught it; the failing run is the reason the row is stated with five
moves.)

## 6. What I did not do, and what remains uncertain

1. **I did not build an independent certificate for the resister.** A cap-26
   search from `BBAAbaa,BBabABA` with the standard class keys as target costs
   about 10^9 states (m1's round-6 run: 1,019,686,852 states and 3,386 s before
   its own time budget stopped it, on this same VM). I judged that too expensive
   to repeat under round 7's load, so the eleven certificates inherit m1's. If
   the fresh audit of the AC-19 falls (round 7, direction J1) finds an error in
   that certificate, items 1 and 2 of Section 0 fail with it — my kernel run
   would have failed too, since the kernel replays the same moves. What can be
   said in its favour: the same 231-move list has now been replayed at least
   four times independently (m1's own assembly, the coordinator's round-6 replay
   with `replay14.py` and `assemble.py` reporting 0 failures and peak 26, my
   `ac12.py`, and the Lean kernel), and the four agree on the endpoint `a,b` and
   on the peak 26.
2. **The lower bound is not my engine.** I ran `acx` (round 4, m1) and
   reproduced 38,286,952 states; I did not write an independent twelve-move
   enumerator for this session. The number agrees with two earlier independent
   runs (round 4's and round 6's), which is the reason to trust it.
3. **The harvest's certificates are not claimed minimal.** Their peaks (15 to
   30) are the peaks of the chains they came from plus the alignment; nothing
   here says a shorter or shallower certificate does not exist.
4. **No lower bounds for the harvest rows.** A row of length 15 to 19 whose
   certificate here has peak 27 might well have one at peak 20; I did not run
   any exhaustion for them.
5. **`lean` timing is machine-dependent.** The 16 min 18 s is wall time on a
   4-CPU VM with a load average of about 25 from other members' runs; the file's
   own user time was about 40 s.
6. **Two cosmetic points.** The Lean theorems are stated for the explicit
   finish tuple `mkPres (n := 2) [[(0,true)],[(1,true)]]` rather than for
   `standard 2`; the two are the same presentation (`standard n` is
   `fun i => FreeGroup.of i` and `FreeGroup.of a` is `mk [(a,true)]`), and a
   bridge lemma would need another 16-minute compile, which I did not spend.
   The files `certs_more.txt` (487 rows, an earlier and smaller harvest before
   the census chains were added) and `certs_fall8_idx.txt` (m1's eight
   certificates in index form) are inputs or superseded stages, not
   deliverables.

## 7. Exact rerun commands and key output

From `REPO/.ultramath/smw48or9f/m3/` (Python 3, no extra packages):

```
$ PYTHONPATH=. python3 assemble11c.py
resister: 231 moves from m1 certificate, peak 26, end a,b
BBAAbaa,BAAABaaabA       join P002  245 moves  peak 26
... (eleven lines) ...
peaks: [26]
$ PYTHONPATH=. python3 check_certs11.py certs_11.txt
OK     BBAAbaa,BAAABaaabA       245 moves  peak 26  end a,b
... (eleven OK lines) ...
certificates checked = 11, failures = 0
move counts 245..424, peaks [26]
$ PYTHONPATH=. python3 segment_peaks.py
BBAAbaa,BAAABaaabA       head  14 moves, peak 21, ends at the resister; total 245, peak 26
... (eleven lines, heads at peak 20 to 25) ...
$ PYTHONPATH=. python3 a19membership.py
rows parsed: 140535
BBAAbaa,BAAABaaabA       AC19.txt line  54524  total length 17  det -1
... (eleven lines) ...
rows of the eleven not found in AC19.txt: 0
$ PYTHONPATH=. python3 transports_check.py
transport realisations checked = 3200, failures = 0
$ PYTHONPATH=. python3 harvest2.py        # writes certs_harvest.txt
AC19 rows 140535; rows of length >= 15: 136612 (by length {15: 5248, 16: 6196, 17: 18317, 18: 23273, 19: 83578})
chains 53931, states 1487313, matched 1237, certificates written 1237
by length {15: 633, 16: 159, 17: 262, 18: 67, 19: 116}
by peak {15: 214, ..., 30: 10}
$ PYTHONPATH=. python3 check_certs11.py certs_harvest.txt | tail -2
certificates checked = 1237, failures = 0
move counts 23..424, peaks [15, ..., 30]
$ PYTHONPATH=. python3 replay_fall8.py     # m1's eight certificates, index form
... eight lines, all peak 26, all ending a,b ...
wrote .../certs_fall8_idx.txt (8 certificates)
$ PYTHONPATH=. python3 gen_lean.py --out AC19eleven.lean --block 24
written .../AC19eleven.lean
$ lean AC19eleven.lean                     # 16 min 18 s wall, exit 0
'AndrewsCurtis.c11_0' depends on axioms: [propext, Classical.choice, Quot.sound]
... (eleven lines) ...
```

From `REPO/`:

```
$ directions/resisters/round4/acx search 25 45000000 \
    .ultramath/smw48or9f/m3/res_cap25_mine.txt none \
    .ultramath/smw3ow2dp/m10/stdak.u64 .ultramath/smw3ow2dp/m10/start1.txt 1 \
    .ultramath/smw3ow2dp/m10/members.txt
EXHAUSTED | 25 | trio | 38286952 | 351.4s
```

## 8. Files

| file | what it is |
| --- | --- |
| `ac12.py` | the engine: rank-2 words, the twelve moves, canonical keys, alignment, the six-move relator exchange |
| `assemble11c.py` | builds `certs_11.txt` from m10's paths and m1's certificate |
| `certs_11.txt` | the eleven certificates, `start|moves|std`, sha256 `9f658b9c02982ddb...` (regenerated byte-identically) |
| `check_certs11.py` | the independent replayer used for every certificate file here |
| `segment_peaks.py` | splits each certificate into head (row to resister) and tail (m1's), reports the head peak |
| `a19membership.py` | own parser of `AC19.txt`; membership and lengths of the eleven |
| `transports_check.py` | the five non-twelve relator moves, 3,200 random instances |
| `harvest2.py` | the harvest: 1,237 certificates from 53,931 standard-ending chains |
| `certs_harvest.txt` | the 1,237 harvested certificates |
| `certs_more.txt` | superseded smaller harvest (487 rows), kept for the record |
| `replay_fall8.py`, `certs_fall8_idx.txt` | m1's eight round-6 certificates in twelve-move index form, replayed |
| `gen_lean.py` | generates the Lean file from `AC3.lean` and `certs_11.txt` |
| `AC19eleven.lean` | the kernel file, 11 theorems, standard axioms only |
| `lean_run.log` | the Lean run: exit 0, 11 axiom lines |
| `*.out` | the recorded output of each command above |
| `res_cap25_mine.txt` | the cap-25 exhaustion log |
