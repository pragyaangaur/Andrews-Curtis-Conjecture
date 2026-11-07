# Lean program 7 (Round 7, direction J5): the Metzler certificate and the family of 14 in the kernel

Accepted 2026-11-06 ~01:56 UTC (coordinator verdict on swarm smw48or9f, member m10).

**The artifact:** `toolkit/lean/AC7.lean` (5,021 lines, sha256
`14e0d037fa8e8fd71b1769153fe897e049cd22ae138ae99ec1bbaefef7a6e17c`,
byte-identical to the member's). It is AC5.lean's Q\*\* machinery (lines
31-287, namespace renamed `AC7`) plus:

- the 15 Q\*\*-certificates of round 6 (Metzler's 44-move pair certificate and
  the 14 family certificates, 788 moves, 394 block decisions), each with its
  replay theorem, its endpoint identification against
  `metz k m j = <x,y | x^k, y^m, [x^j,y]>` (decide), and the Q\*\*-equivalence
  as an existential over move lists;
- `family_table`, round 6's 14 rows as conjoined existentials;
- the algebra of the recipe for ALL parameters: `conjProd_of_subst` /
  `conjProd_of_lift` (round 6's Lemma 3), `powerProd_spec` /
  `powerProd_cert` / `powerProd_factor_is_conj` (the stage-2 closed form,
  stating the CORRECTED identity `x^(1+tj) · x^(-tj) a^j = x a^j`), and
  `subst_defining` (the stage-3 substitution).

The file imports four Mathlib modules instead of all of Mathlib, so the check
costs about 1.9 GB and 1.5 minutes instead of 5.1 GB and 4-8 minutes.

**The correction:** round 6's proof sketch
(`directions/qdouble-star/m9/round6-m6.md` section 5) printed the stage-2
multiplier as `(x^(-tj) a^j)^(-1)`; the identity that holds is
`x^(1+tj) · x^(-tj) a^j = x a^j`. Verified by exact free-group arithmetic
(36/36 cases for the corrected form, 0/36 for the printed one) by the member
and independently by the coordinator; dated note placed at the passage. The
certificate files are unaffected (five Python implementations and the kernel
agree on all 15).

**What is NOT formalized** (see `stage2_attempt.md`, copied here): the recipe
as one theorem over symbolic `k, t, j, m` — the obstruction is a defeq issue
with `setRel`'s projections, recorded exactly with the clean route identified.
Round 6's Lemmas 1 and 2 remain `[Argument]`; Q\*-inequivalence is quoted only.

## Rerunning

The end-to-end check and the negative controls live in the member's directory
(the scripts resolve two repo-relative inputs from their own location, so run
them there):

```
cd .ultramath/smw48or9f/m10
./check_ac7.sh        # lean exit 0, 40 standard axiom lines; replay7 15/15;
                      # verify_claims (peak table, identity 36/36 vs 0/36,
                      # round-6 table 13/13, move census); qverify and
                      # check_qstar 15/15. ALL CHECKS PASS.
./tamper_test.sh      # both one-letter tamperings rejected: BOTH TAMPERINGS CAUGHT
gap -q -b groupcheck.g # all 14 rows: same abelian group at both ends
```

The certificate inputs are byte copies of
`directions/qdouble-star/m9/certs/metzler_pair_qstar_gap.cert` (sha256
`10566d02f2dec919...`) and `directions/qdouble-star/m9/fam_certs/fam_*.cert`.

## Coordinator verification record (2026-11-06, 01:41-01:56 UTC)

All of the above rerun and matched, including: the byte-identical
regeneration of AC7.lean from `gen_ac7.py` (with the machinery slice AC5.lean
lines 31-287 verified verbatim by direct comparison); the certificate file
provenance (sha256 and cmp); `fam_k5_t2_m5` being move-for-move Metzler's own;
the theorem shapes read in the source; the correction verified by the
coordinator's own free-group implementation (after catching and fixing a bug
in that implementation's cancellation rule); the GAP group check; and the two
tamperings both caught by the kernel.
