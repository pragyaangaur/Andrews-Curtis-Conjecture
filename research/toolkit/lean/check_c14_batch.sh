#!/usr/bin/env bash
# Check a batch of directions/c14 certificates in Lean, in the kernel.
#
#   bash toolkit/lean/check_c14_batch.sh 0 90 5000 53850
#
# The arguments are line numbers of directions/c14/certs_all.txt (counting from 0, blank lines
# skipped, the same convention as `cert_to_lean.py --line`).  Each certificate is converted into
# blocks of twelve moves, checked with `decide`, and the blocks are glued with `checkCert_append`.
# The generated file is .scratch/C14Batch.lean; the run ends with one `#print axioms` per
# certificate, and lean exits 0 exactly when every certificate was accepted by the kernel.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
mkdir -p "$root/.scratch"
out="$root/.scratch/C14Batch.lean"
python3 - "$here" "$root" "$out" "$@" <<'PY'
import os, subprocess, sys
here, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
lines = sys.argv[4:]
blocks = ['open AndrewsCurtis']
names = []
for ln in lines:
    name = 'c14_%s' % ln
    names.append(name)
    r = subprocess.run([sys.executable, os.path.join(here, 'cert_to_lean.py'),
                        '--c14-file', os.path.join(root, 'directions/c14/certs_all.txt'),
                        '--line', ln, '--name', name, '--chunk', '12'],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('conversion failed for line %s: %s' % (ln, r.stderr))
    if r.stderr.strip():
        sys.stderr.write('warning for line %s: %s\n' % (ln, r.stderr.strip()))
    blocks.append(r.stdout)
ac3 = open(os.path.join(here, 'AC3.lean')).read()
tail = '\n'.join('#print axioms %s_sound' % n for n in names) + '\n'
open(out, 'w').write(ac3 + '\n'.join(blocks) + tail)
print('wrote %s with %d certificates' % (out, len(lines)))
PY
cd "$root"
lean "$out"
