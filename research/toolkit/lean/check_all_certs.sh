#!/usr/bin/env bash
# check_all_certs.sh -- run both checkers on the 124 round-4 certificates.
#
#   bash check_all_certs.sh              # replay in Python, then check the shipped AC4.lean
#   bash check_all_certs.sh --rebuild    # regenerate AC4.lean from the certificate files first
#
# Checker 1 (certs_replay.py): an independent Python replay of every move list, written from
# the file formats and the documented move tables, sharing no code with the generators.
# Checker 2 (the Lean kernel): `lean AC4.lean`, which replays every certificate with `decide` in
# blocks of at most twelve moves and glues the blocks with `checkCert_append`.  No `sorry`, no
# new axiom and no `native_decide` is used; the script fails unless
#   * lean exits 0,
#   * the log has no `error` and no `sorryAx`,
#   * all 124 `*_sound` theorems and all 98 `*_trivial` theorems are reported by `#print axioms`,
#   * every reported axiom list is Lean's standard one.
#
# Expected: 72 + 26 + 21 + 5 = 124 certificates, 13568 moves, 98 triviality corollaries,
# about 90 seconds of Lean.  The log is kept at ac4.log next to this script.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"

echo "== checker 1: independent Python replay"
python3 certs_replay.py all --quiet || { echo "PYTHON REPLAY FAILED"; exit 1; }

if [ "${1:-}" = "--rebuild" ]; then
  echo "== rebuilding AC4.lean from the certificate files"
  python3 build_ac4.py || { echo "BUILD FAILED"; exit 1; }
fi

echo "== checker 2: the Lean kernel"
start=$(date +%s)
lean AC4.lean > ac4.log 2>&1
rc=$?
end=$(date +%s)
echo "lean exit $rc after $((end - start)) s, log ac4.log ($(wc -l < ac4.log) lines)"
[ $rc -eq 0 ] || { echo "LEAN REJECTED THE FILE"; tail -40 ac4.log; exit 1; }

echo "== log audit"
python3 - <<'PY' || exit 1
import re
import sys

txt = open('ac4.log').read()
txt = re.sub(r'\n ', ' ', txt)          # join axiom lists wrapped by the printer
lines = [l for l in txt.splitlines() if 'depends on axioms' in l or 'does not depend' in l]
if re.search(r'\berror\b', txt) or 'sorryAx' in txt:
    sys.exit('error or sorryAx in the log')
standard = 'depends on axioms: [propext, Classical.choice, Quot.sound]'
weak = 'depends on axioms: [propext, Quot.sound]'
bad = [l for l in lines if standard not in l and weak not in l and 'does not depend' not in l]
counted = {}
for l in lines:
    m = re.match(r"'([^']+)'", l)
    counted[m.group(1).split('.')[-1]] = l
want = ['std_%02d' % i for i in range(72)] + ['ak3_%02d' % i for i in range(26)]
want += ['merge_%02d' % i for i in range(21)] + ['carr_%d' % i for i in range(5)]
missing_sound = [n + '_sound' for n in want if n + '_sound' not in counted]
missing_triv = [n + '_trivial' for n in want[:98] if n + '_trivial' not in counted]
nonstd_triv = [n for n in want[:98] if n + '_trivial' in counted
               and standard not in counted[n + '_trivial']
               and weak not in counted[n + '_trivial']]
print('axiom lines total: %d' % len(lines))
print('certificates with a soundness theorem: %d of 124' % (124 - len(missing_sound)))
print('triviality theorems: %d of 98' % (98 - len(missing_triv)))
print("axiom lines outside Lean's standard set: %d" % len(bad))
for l in bad[:5]:
    print('  ' + l)
for name, lst in (('missing soundness', missing_sound), ('missing triviality', missing_triv),
                  ('non-standard triviality', nonstd_triv)):
    if lst:
        print('%s: %s' % (name, ' '.join(lst[:10])))
if bad or missing_sound or missing_triv or nonstd_triv:
    sys.exit(1)
print('== PASS: 124 certificates and 98 triviality corollaries accepted by the kernel, '
      'standard axioms only')
PY
