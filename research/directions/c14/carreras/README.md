# Carreras's length-14 certificates, replayed

Round 3, direction F8 (member m8, swarm smw2opo0o), accepted 2026-11-04 after
fresh refereeing by the coordinator, who reran everything below.

Source: J. Carreras, *Machine-checkable equivalence certificates at the
length-14 Andrews-Curtis frontier*, arXiv:2607.23611v1 (26 July 2026). The
artifact is at https://github.com/joe-carr-data/ac-certificates (named in the
paper's arXiv comment); `provenance.json` records the upstream URLs and blob
SHAs of the five certificate files. Two of the five were re-downloaded by the
coordinator and are byte-identical to these copies.

The five certificates, replayed by `replay_carreras.py` (an independent
verifier written from the JSON format alone, sharing no code with the
artifact; three deliberately corrupted controls FAIL):

| file | moves | identifies |
|---|---:|---|
| `cert_ms3_yx2y_equiv_ak3.json` | 71 | `BAABa,BBBBAbbba` = MS(3, yx^2 y), a resisting-exhausted-cap18 row of `final_classes.txt`, is AC-equivalent to AK(3) |
| `bottleneck_ak_f3_cert.json` | 66 | the same equivalence (AK(3) to a rotation of MS(3, yx^2 y)) |
| `cert_ms3_yinvx2yinv_equiv_ak3.json` | 13 | `BABaa,BBBBAbbba` = MS(3, y^-1 x^2 y^-1) to AK(3); round 2 had this in 34 moves |
| `cert_sym_equiv_orphan1.json` | 36 | `BBBAbba,BAAbaaa` (Solitar's candidate) is AC-equivalent to `BBBAbba,BAAAbaa` |
| `cert_idx0_equiv_mirror.json` | 85 | `BBBAbba,BAABaaa` is AC-equivalent to `BBBAbba,BAAABaa` |

Exact command, from this directory:

    python3 replay_carreras.py cert_*.json bottleneck_*.json

Consequences for the round-2 ledger of `directions/c14/final_classes.txt`
(164 resisting presentations): one resister is settled as AK(3)-equivalent
(27 presentations now certified AK(3)-equivalent) and two pairs of resisters
merge, leaving 163 undecided presentations in 161 undecided classes and
c(14) at most 2 + 161 = 163. Combined with m5's six settled length-13
resisters (`directions/pu-gap/run/certs13_settled.txt`), the round-3 ledger
stands at 157 undecided presentations in 155 classes, 33 certified
AK(3)-equivalent, c(14) at most 157 and c(13) at most 10; see the dated
coordinator notes in `../c14.md` and in the repository's OPEN_QUESTIONS.md.

Note on the family: w = yx^2 y has exponent sum 2 on x, so MS(3, yx^2 y) lies
outside the exponent-sum-zero subfamily covered by the Miller-Schupp
triviality theorem; its triviality follows from this certificate together
with the Lean theorem that AK(3) presents the trivial group.
