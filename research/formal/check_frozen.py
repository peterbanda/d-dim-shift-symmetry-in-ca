#!/usr/bin/env python3
"""Frozen-statement gate (Phase H).

Every frozen statement file of the paper-wide layer (Shiftsym/Paper/S??_*.lean,
Paper/Common.lean) and of the extension layer (Shiftsym/Ext/SX*.lean) was
fingerprinted when it passed its triple fidelity review, before any proof was
written. Since 2026-10-19 the record also holds every other file whose
definitions a frozen statement unfolds to (Definitions.lean, Statement*.lean and
six lemma files; ../frozen_deps.lean computes that closure and fails if a file in
it is not recorded) and the toolchain/mathlib pins. This script checks that
  * every fingerprinted file still exists and is byte-identical, and
  * no statement file exists without a fingerprint
so that a statement can be neither weakened, nor deleted, nor added unnoticed.
(The build audits AuditPaper.lean / AuditExt.lean check that each frozen
statement has a proof of exactly its type; this script checks that the
statements themselves are the reviewed ones.) Exit code 1 on any finding.
"""
import glob, hashlib, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.join(HERE, "shiftsym")
rec = {}
for line in open(os.path.join(HERE, "frozen_statements.sha256")):
    if line.strip() and not line.startswith("#"):
        h, p = line.split()
        rec[p] = h
bad = 0
for p, h in sorted(rec.items()):
    f = os.path.join(BASE, p)
    if not os.path.exists(f):
        print("MISSING  ", p); bad += 1; continue
    cur = hashlib.sha256(open(f, "rb").read()).hexdigest()
    if cur != h:
        print("CHANGED  ", p, cur[:12], "!=", h[:12]); bad += 1
present = [os.path.relpath(f, BASE) for pat in ("Shiftsym/Paper/S*.lean", "Shiftsym/Paper/Common.lean",
                                                "Shiftsym/Ext/SX*.lean", "Shiftsym/Statement*.lean",
                                                "Shiftsym/Definitions.lean") for f in glob.glob(os.path.join(BASE, pat))]
for p in sorted(set(present) - set(rec)):
    print("UNRECORDED", p); bad += 1
print(f"frozen statements and their dependencies: {len(rec)} files fingerprinted;",
      "OK (all unchanged, none missing, none unrecorded)" if not bad else f"{bad} finding(s)")
sys.exit(1 if bad else 0)
