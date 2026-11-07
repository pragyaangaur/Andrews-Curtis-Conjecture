# The kernel archive: consolidated tree, build order, axiom audit

Round 11, member m3. **Nothing here says anything for or against the Andrews–Curtis
conjecture.** Every statement below is about which Lean files exist, where, in what order
they elaborate, and which axioms their `#print axioms` reports name.

Three tiers. `toolkit/lean/` after `scripts/consolidate.sh --apply` is exactly this tree.

| tier | directory | files | source bytes | `#print axioms` | round-11 status |
| --- | --- | ---: | ---: | ---: | --- |
| **1. layer files** | `.` | 37 | 6 420 880 | 3 084 | **all rebuilt**, exit 0, empty stderr |
| **2. instance chain** | `instances/` | 776 | 6 760 707 | 8 | **all rebuilt** (768 chunk `decide`s + 2 assemblies + 4 instance files) |
| **3. closed-set rows** | `instances/rows/` | 16 | 23 555 466 | 48 | **all rebuilt**, exit 0, empty stderr |
| | **total** | **829** | **36 737 053** | **3 140** | |

Each tier has a `MANIFEST.tsv` whose every column is measured from the staged source:
`sha256`, `bytes`, `lines_wc`, `decls` (lines beginning `theorem`/`lemma`, allowing
`private`/`protected`/`noncomputable`/`@[...]` prefixes), `prints` (lines beginning
`#print axioms`), `imports` (every module on an `import` line, comments stripped), `intra`
(the subset that are other archive files), `forbidden` (comment-stripped `sorry`/`axiom`/
`constant`/`opaque`/`native_decide`/`admit`/`unsafe`/`@[extern]`/`implemented_by`/
`ofReduceBool`).

## Tier 1 — the 37 layer files

The 34 files of m5's round-10 `MANIFEST.tsv` **plus three the round-10 recipe left out**:

| file | why it is here | round |
| --- | --- | --- |
| `ACPack.lean` | the packed closed-set layer; `ACSlot` imports it and the final report cites five of its theorems as SETTLED (kernel) — it was in **no** manifest and in no recipe | r9 (m8) |
| `ACSlot.lean` | the static slot-array apparatus behind the cap-17 certificate | r10 (m10) |
| `audit_r9.lean` | the 18-theorem axiom audit of the round-9 layers (`MetzlerSharp`, `ACConj`, `ACPack`) — without it `ACPack` has no audit of its own | r10 (m1) |

```sh
cd <this dir>
export LEAN_PATH=".:$LEAN_PATH"          # load-bearing: lean does not search '.' for `import AC2`
python3 ../scripts/arch.py order MANIFEST.tsv     # topological check (29 intra-archive edges, 0 violations)
python3 ../scripts/arch.py build MANIFEST.tsv     # lean -o M.olean M.lean, one file at a time
python3 ../scripts/arch.py check MANIFEST.tsv     # parse every log, verify every axiom report
```

Measured in round 11: 37 files, 3 084 reports (3 074 non-empty, 10 "does not depend on any
axioms"), **every reported set inside `{propext, Classical.choice, Quot.sound}`**, every
file's report count equal to its manifest `prints`, zero `sorryAx`/`ofReduceBool` in any
log, zero forbidden tokens in any comment-stripped source.

## Tier 2 — the instance chain (776 files)

| group | files | what it certifies |
| --- | --- | --- |
| `SlotData_17.lean`, `RowBase.lean`, `D17_0..511.lean`, `Asm17.lean` | 515 | `Row17.row_T_c17`: no path from `BABaba,BBBaBaa` to `a,b` with every intermediate of total length at most 17; **136 576 states** (r10, m10) |
| `SlotData_16.lean`, `RowBase_16.lean`, `C16_0..255.lean`, `Asm16.lean` | 259 | the same at cap 16; **8 880 states** |
| `ACInstP_c14.lean`, `ACInstQ_c14.lean` | 2 | the two cap-14 closed-set certificates, 168 states (r9, m8) |

```sh
cd instances
export LEAN_PATH=".:..:$LEAN_PATH"       # '..' carries the tier-1 oleans, '.' the instances
lean -o SlotData_17.olean SlotData_17.lean      # 291 s, 1.7 GB  (measured r11)
lean -o RowBase.olean RowBase.lean              # 1 s
for j in $(seq 0 511); do lean -o D17_$j.olean D17_$j.lean; done   # 512 chunks, ~10 s each
lean -o Asm17.olean Asm17.lean                  # 3 s
# cap 16: SlotData_16 (151 s), RowBase_16, C16_0..255 (~2 s each), Asm16
# cap 14: ACInstP_c14 (9 s), ACInstQ_c14 (7 s)
```

`Asm17.lean` prints `'Row17.row_T_c17' depends on axioms: [propext, Classical.choice,
Quot.sound]` and `#eval`s the certificate's own state count, `136576`; `Asm16.lean` prints
`'Row16.row_T_c16'` on the same three axioms. `../audit_inst.lean` (beside the archive, not in
it) imports both assemblies and reprints the two axiom sets and both state counts, 8880 and
136576 — run it with `LEAN_PATH=".:..:$LEAN_PATH" lean ../../audit_inst.lean` from
`instances/`. **Chunk coverage is exact**: the 512 cap-17
chunks are `chunkCheck 17 T stdSt (j*512) 512` for `j < 512`, i.e. offsets `0, 512, …,
261632` with length 512, tiling `[0, 262144)` = `[0, NSLOT)` with `NSLOT = 8^6`; the 256
cap-16 chunks are `(j*1024) 1024`, the same tiling. No gap, no overlap (checked from the
sources, not from the report).

## Tier 3 — the closed-set rows (16 files)

Entry 72 of the final report: sixteen compact closed-set certificates, eight at cap 16 and
eight at cap 14/15, importing only `ACClosed`. They were in **no** manifest and no recipe;
they are here because the report calls them SETTLED (kernel).

```sh
cd instances/rows
export LEAN_PATH=".:../..:..:$LEAN_PATH"
for f in *.lean; do lean -o "${f%.lean}.olean" "$f"; done     # 34–142 s each, measured r11
```

Measured: 48 reports (32 non-empty, 16 "none"), all inside the standard set; for example
`ACInst_p15_BBAAbA_BBabAba` gives `closed_T` on `[propext]`, `keys_T` on no axioms, and
`row_0` on `[propext, Classical.choice, Quot.sound]`.

## One command

```sh
bash ../scripts/verify_archive.sh            # the whole tree, every tier, prints PASS
```

## What else is in this directory (and is *not* part of the tree)

Beside the 829 `.lean` files and the three `MANIFEST.tsv`, this directory also holds, from
round 11, copies of the round-1…10 checker scripts (`check_all_certs.sh`, `check_ms_certs.sh`,
`check_ac5.sh`, `check_cert_lean.sh`, `check_c14_batch.sh`, `certs_replay.py`,
`cert_to_lean.py`, the `certs/` spot-check lists) — copied here so that each could be re-run
against the consolidated tree without writing anywhere else (§5 of `../ARCHIVE_REPORT.md`) —
plus three read-only symlinks (`.scratch`, `directions`, `.ultramath`) that those scripts
need to find their inputs, and the disposable `.olean`s (637 MB; `find . -name '*.olean'
-delete` leaves a 36.7 MB source tree). `scripts/consolidate.sh` copies only the `.lean`
files, the three manifests and this file, so none of that reaches `toolkit/lean/`.

## What is *not* in this tree, and where its build is recorded

97 `.lean` files under `.ultramath/smw4sqc1u/m8/` — two earlier cap-16 packed routes, the
single-reduction forms that do not complete, and the cap-17 data in its two containers.
`../CORPUS.md` §2 lists them with sizes, status and the exact build command, and says which
were rerun.

## What this tree does not certify

* Mathlib itself is trusted and not rebuilt.
* The audit is transitive through proof terms, not per declaration: 3 140 reports over
  ~11 600 `theorem`/`lemma` declarations. A helper nothing uses is covered by nothing.
* The 768 chunk files are independent `decide +kernel` computations over shared definitions;
  the *statement* coverage is verified arithmetically, the *cuckoo placement* of the packed
  data only in the safe direction (a bad placement makes a check fail, never pass).
* Round 11 rebuilt every file of all three tiers on a 4-core box shared with nine other
  members; the times above are wall clock under variable load and vary by up to 8×.
