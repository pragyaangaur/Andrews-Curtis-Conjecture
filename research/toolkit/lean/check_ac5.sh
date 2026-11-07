#!/usr/bin/env bash
# Rerun the AC5 checks.
#
#   (1) lean AC5.lean        the 33 Q**-certificates of directions/qdouble-star/m9/certs/
#                            replayed in the Lean 4 kernel, 582 block decisions, plus the
#                            axiom audit (#print axioms on every certificate)
#   (2) qverify.py           the independent Python replayer of round 4, same 33 files
#   (3) check_qstar.py       the independent Python replayer of round 3, same 33 files
#
# The Lean run takes about 80 s and 7 GB of resident memory (Mathlib import included).
# Exit status 0 means every certificate checked and every axiom line is Lean's standard set.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
certs=$(ls "$repo"/directions/qdouble-star/m9/certs/*.cert)
fail=0

echo "== 1. lean AC5.lean (33 kernel certificate checks)"
log="$here/ac5.run.log"
lean "$here/AC5.lean" > "$log" 2>&1
rc=$?
echo "lean exit status: $rc   (log: $log)"
if [ $rc -ne 0 ]; then
  echo "FAIL: lean reported errors"
  grep -i error "$log" | head -20
  fail=1
fi
nok=$(grep -c "depends on axioms" "$log")
echo "certificates with an axiom line: $nok (expected 33)"
[ "$nok" -eq 33 ] || { echo "FAIL: expected 33 axiom lines"; fail=1; }
bad=$(grep "depends on axioms" "$log" | grep -vc "propext, Classical.choice, Quot.sound")
echo "axiom lines outside Lean's standard set: $bad (expected 0)"
[ "$bad" -eq 0 ] || { echo "FAIL: non-standard axioms"; fail=1; }

echo "== 2. python3 qverify.py (round-4 replayer)"
python3 "$repo/directions/qdouble-star/m9/qverify.py" $certs | tail -1
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "FAIL: qverify"; fail=1; }

echo "== 3. python3 check_qstar.py (round-3 replayer)"
python3 "$repo/directions/qdouble-star/check_qstar.py" $certs | tail -1
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "FAIL: check_qstar"; fail=1; }

if [ $fail -eq 0 ]; then echo "ALL CHECKS PASS"; else echo "FAILURES PRESENT"; fi
exit $fail
