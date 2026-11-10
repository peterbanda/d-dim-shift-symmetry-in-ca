#!/usr/bin/env bash
# Re-export the info trees of every Lean file the audit can show
# (Paper statements and proofs, core Lemmas, Definitions, Statement).
# Usage: tools/export_lean.sh [-j N]
set -euo pipefail
J=6; [[ "${1:-}" == "-j" ]] && J="$2"
cd "$(dirname "$0")/../../shiftsym"
OUT=../correspondence_audit/data/lean
mkdir -p "$OUT"
ls Shiftsym/Paper/*.lean Shiftsym/Paper/Proofs/*.lean Shiftsym/Lemmas/*.lean \
   Shiftsym/Definitions.lean Shiftsym/Statement.lean |
  xargs -P "$J" -I{} sh -c 'out='"$OUT"'/$(echo {} | sed "s#/#__#g; s#\.lean\$#.json#");
    lake env lean --run ../correspondence_audit/tools/ExportInfo.lean {} "$out" 2>&1 | tail -2' \
  | tee "$OUT/_export.log"
if grep -qv " 0 errors" "$OUT/_export.log"; then echo "EXPORT HAD ERRORS"; exit 1; fi
