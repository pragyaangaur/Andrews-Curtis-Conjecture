# The AC-19 eleven: explicit certificates at peak exactly 26 (Round 7, direction J7)

Accepted 2026-11-06 01:34 UTC (coordinator verdict on swarm smw48or9f, member m3).
The member's full working directory, with all scripts and recorded outputs, is
`.ultramath/smw48or9f/m3/` (the scripts resolve their inputs relative to their
own location, so run them from there). This folder holds the citable data:
`report.md` (the report, verbatim), `certs_11.txt` (the eleven certificates,
`start|moves|std` in twelve-move index form), `certs_harvest.txt` (the 1,237
harvested certificates, same format).

## What is established

1. The eleven round-6 depth-26 AC-19 rows (m10's intersection, round 6) each
   have an explicit twelve-move Andrews-Curtis certificate to the standard
   pair `a,b`, of 245 to 424 moves, with every intermediate of total relator
   length at most 26, and no such certificate at peak 25 or less: **the peak of
   each of the eleven is exactly 26**. The eleven are rows of AC19.txt
   (0-based lines 54524, 14965, 35322, 52847, 112516, 113759, 95275, 30388,
   38969, 78175, 48340), all with |det| = 1.
2. The eleven certificates are kernel-checked: `toolkit/lean/AC19eleven.lean`
   is `toolkit/lean/AC3.lean` verbatim plus the eleven certificates in `decide`
   blocks glued by `checkCert_append`; `lean toolkit/lean/AC19eleven.lean`
   exits 0 with all eleven `c11_i` theorems depending only on
   `[propext, Classical.choice, Quot.sound]`. Since m1's round-6 231-move
   resister certificate is the common tail of all eleven chains, the kernel
   run validates it as well.
3. A harvest of 1,237 AC-19 rows of total length 15 to 19 (1,226 beyond the
   eleven) now carry explicit certificates to the standard pair (23 to 424
   moves, peaks 15 to 30), replayed move by move with 0 failures. No
   completeness claim: only rows whose class key lies on one of the 53,931
   standard-ending certificate chains of the repository are reached.

The lower bound (peak at least 26) is the cap-25 exhaustion of the resister
`BBAAbaa,BBabABA`'s component: 38,286,952 states, no hit against the classes
of the standard pair or AK(3) — reproduced four times independently (round 4,
round 6, m3, and the coordinator's round-7 rerun). The head of each chain is a
twelve-move path from the row to the resister with peak at most 25, so a row
trivialisation at peak at most 25 would concatenate to a resister
trivialisation at peak at most 25, which the exhaustion excludes. The
twelve-move to full-AC upgrade is the transport lemma (round 5's accepted
certificate algebra, rechecked here on 3,200 random instances, 0 failures).

## Exact rerun commands (from the repository root)

```
cd .ultramath/smw48or9f/m3
PYTHONPATH=. python3 check_certs11.py certs_11.txt        # 11, failures = 0, peaks [26]
PYTHONPATH=. python3 check_certs11.py certs_harvest.txt   # 1237, failures = 0
PYTHONPATH=. python3 a19membership.py                     # rows parsed 140535, 0 not found
PYTHONPATH=. python3 transports_check.py                  # 3200, failures = 0
PYTHONPATH=. python3 assemble11c.py                       # regenerates certs_11.txt byte-identically
PYTHONPATH=. python3 harvest2.py                          # regenerates certs_harvest.txt byte-identically
PYTHONPATH=. python3 gen_lean.py --out AC19eleven.lean --block 24
lean AC19eleven.lean                                      # exit 0; eleven standard axiom lines
# from the repository root:
directions/resisters/round4/acx search 25 45000000 <out> none \
    .ultramath/smw3ow2dp/m10/stdak.u64 .ultramath/smw3ow2dp/m10/start1.txt 1 \
    .ultramath/smw3ow2dp/m10/members.txt
# EXHAUSTED | 25 | trio | 38286952
```

## Coordinator verification record (2026-11-06, 01:26-01:34 UTC)

All of the above rerun and matched: the eleven replays (peak 26, 245-424
moves), the 1,237 harvest replays, the membership check, the 3,200 transport
checks, the byte-identical regenerations of `certs_11.txt`,
`certs_harvest.txt` and `AC19eleven.lean` (from `certs_11.txt` and AC3.lean),
the AC3.lean prefix diff, the eleven starts against m10's `table_11.tsv`, the
token-exact index translation of m1's `cert_fall.txt` as the common 231-move
tail (replayed to `a,b` at peak 26 through the same conversion), the novelty
scan (63 hit-path fragments at start lengths 14-16, `ms_family_7_7.txt` a
family listing), the eleven-among-1,237 count, the Lean run (exit 0, 6m36s
wall on a loaded VM, no errors, all eleven axiom lines standard), and the
cap-25 exhaustion (EXHAUSTED, 38,286,952, no hit, 6m02s).
