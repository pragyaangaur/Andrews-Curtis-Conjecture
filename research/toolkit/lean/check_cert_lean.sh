#!/usr/bin/env bash
# Check one explicit AC certificate in Lean, in the kernel, without native_decide.
#
#   bash toolkit/lean/check_cert_lean.sh --ms directions/ms-ak-certs/cert_n2.json
#   bash toolkit/lean/check_cert_lean.sh --c14 'aB,b|i0 c0a m0|std'
#   bash toolkit/lean/check_cert_lean.sh --c14-file directions/c14/certs_all.txt --line 0
#
# The script writes .scratch/CertCheck.lean, which is AC3.lean followed by the certificate
# block produced by cert_to_lean.py, and runs lean on it.  The relevant output is the final
# `#print axioms` style report of the generated theorems: lean exits 0 exactly when the
# kernel accepted the `decide` proof of the certificate.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
mkdir -p "$root/.scratch"
snippet="$root/.scratch/CertSnippet.lean"
out="$root/.scratch/CertCheck.lean"
python3 "$here/cert_to_lean.py" "$@" > "$snippet"
cat "$here/AC3.lean" > "$out"
printf '\nopen AndrewsCurtis\n' >> "$out"
cat "$snippet" >> "$out"
printf '\n#print axioms cert_check\n#print axioms cert_sound\n' >> "$out"
cd "$root"
lean "$out"
