#!/usr/bin/env python3
"""Placeholder gate for the Lean development (replaces the bare grep).

Scans every .lean file under research/formal/shiftsym/Shiftsym (or the
directories given as arguments) with comments, docstrings and string
literals removed (Lean block comments nest), and reports any occurrence of
the tokens `sorry`, `admit`, `native_decide` or a kernel-bypass option.
The authoritative check is still the axiom audit (`lake env lean
Shiftsym/Audit.lean` and the build-failing `Shiftsym/AuditPaper.lean`):
a `sorry` would show up there as `sorryAx`. Exit code 1 on any finding.
"""
import os, re, sys

def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)

PAT = re.compile(r"\b(sorry|admit|native_decide|skipKernelTC)\b")
roots = sys.argv[1:] or [os.path.join(os.path.dirname(os.path.abspath(__file__)), "shiftsym", "Shiftsym")]
found = 0
for root in roots:
    for dp, _, fs in os.walk(root):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            code = strip(open(p, encoding="utf-8").read())
            for k, line in enumerate(code.split("\n"), 1):
                if PAT.search(line):
                    print(f"{p}:{k}: {line.strip()}"); found += 1
print("placeholder check:", "CLEAN" if not found else f"{found} finding(s)")
sys.exit(1 if found else 0)
