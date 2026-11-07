#!/usr/bin/env bash
# Check every certificate in directions/ms-ak-certs/ in Lean, in the kernel.
#
#   bash toolkit/lean/check_ms_certs.sh
#
# Each JSON certificate is converted by cert_to_lean.py into blocks of twelve moves; the blocks
# are checked with `decide` and glued with `checkCert_append`.  The generated file is
# .scratch/AllMsCerts.lean, which is AC3.lean followed by the certificate blocks, and the run
# ends with one `#print axioms` per certificate.  lean exits 0 exactly when every certificate was
# accepted by the kernel.  Expected output: 18 lines, each `... _sound depends on axioms:
# [propext, Classical.choice, Quot.sound]`.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
mkdir -p "$root/.scratch"
dir="$root/directions/ms-ak-certs"
revs=$(ls "$dir"/cert_n*_rev.json | sort -V)
fwd=$(ls "$dir"/cert_n*.json | grep -v '_rev\.json$' | sort -V)
out="$root/.scratch/AllMsCerts.lean"
python3 - "$here" "$root" "$out" $revs $fwd <<'PY'
import os, subprocess, sys
here, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
files = sys.argv[4:]
blocks = ['open AndrewsCurtis']
names = []
for f in files:
    name = 'c_' + os.path.basename(f).replace('.json', '').replace('-', '_')
    names.append(name)
    r = subprocess.run([sys.executable, os.path.join(here, 'cert_to_lean.py'), '--ms', f,
                        '--name', name, '--chunk', '12'], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('conversion failed for %s: %s' % (f, r.stderr))
    if r.stderr.strip():
        sys.stderr.write('warning for %s: %s\n' % (f, r.stderr.strip()))
    blocks.append(r.stdout)
ac3 = open(os.path.join(here, 'AC3.lean')).read()
tail = '\n'.join('#print axioms %s_sound' % n for n in names) + '\n'
open(out, 'w').write(ac3 + '\n'.join(blocks) + tail)
print('wrote %s with %d certificates' % (out, len(files)))
PY
cd "$root"
lean "$out"
