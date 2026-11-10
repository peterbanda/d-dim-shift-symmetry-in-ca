#!/usr/bin/env python3
"""Carry verdicts forward across a bundle rebuild when only positions changed.

A verdict is stale when its item_hash differs from the item's hash in
data/audit_data.json. The hash covers the item's TeX, the Lean source of its
declarations and its correspondence block, and that block contains TeX line
numbers (`scope.lines`). A paper edit elsewhere therefore makes verdicts stale
even when nothing the auditor judged has changed.

For every stale verdict this script finds the committed bundle whose item hash
equals the verdict's hash, then compares that bundle's state with the current one:
  - the item's TeX (exact),
  - the Lean declarations (names, files) and their source text (exact),
  - the correspondence block with every `lines` entry removed (exact),
  - every current mapping carries a mapping mark equal to the verdict.
Only if all four hold is the verdict re-issued, under the current hash, in a
session labelled `carry-forward-...` (tool `claude-code:carry-forward-positional`).
The other stale items are listed and left alone, for the auditor to judge again.

  carry_forward.py            dry run: print what would be carried forward
  carry_forward.py --apply    append the carry-forward session to logs/events.jsonl
"""
from __future__ import annotations

import datetime as dt
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import auditlog  # noqa: E402

AUDIT_REL = "research/formal/correspondence_audit"
TOOL = "claude-code:carry-forward-positional"
LEAN_REL = "research/formal/shiftsym"


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(auditlog.REPO), *args], stderr=subprocess.DEVNULL)


def show(rev: str, path: str) -> str | None:
    try:
        return git("show", f"{rev}:{path}").decode()
    except subprocess.CalledProcessError:
        return None


def strip_lines(x):
    if isinstance(x, dict):
        return {k: strip_lines(v) for k, v in x.items() if k != "lines"}
    if isinstance(x, list):
        return [strip_lines(v) for v in x]
    return x


def lean_src(decls: list[dict], read) -> str | None:
    parts = []
    for d in decls:
        text = read(d["file"])
        if text is None:
            return None
        parts.append("\n".join(text.splitlines()[d["sl"] - 1:d["el"]]))
    return "\n".join(parts)


def corr_block(corr_text: str | None, iid: str):
    if corr_text is None:
        return None
    c = json.loads(corr_text)
    if isinstance(c, dict) and "items" in c:
        c = {b.get("id"): b for b in c["items"]}.get(iid, c)
    return c


def main(apply: bool) -> int:
    data = json.loads(auditlog.DATA.read_text())
    cur = {i["id"]: i for i in data["items"]}
    st = auditlog.replay(auditlog.read_events())
    stale = {k: v for k, v in st["verdicts"].items()
             if k in cur and v.get("value") and v.get("hash") not in (None, cur[k]["hash"])}
    revs = git("log", "--format=%h", "--", f"{AUDIT_REL}/data/audit_data.json").decode().split()
    bundles: dict[str, dict] = {}

    def bundle(rev):
        if rev not in bundles:
            bundles[rev] = {i["id"]: i for i in json.loads(show(rev, f"{AUDIT_REL}/data/audit_data.json"))["items"]}
        return bundles[rev]

    corr_files = {p.stem.replace("_", ":", 1): p for p in (auditlog.AUDIT / "data" / "corr").glob("*.json")}
    carry, keep = [], []
    for iid, v in stale.items():
        rev = next((r for r in revs if bundle(r).get(iid, {}).get("hash") == v["hash"]), None)
        if rev is None:
            keep.append((iid, "no committed bundle has the verdict's hash"))
            continue
        old, new = bundle(rev)[iid], cur[iid]
        reasons = []
        if old["tex"] != new["tex"]:
            reasons.append("TeX changed")
        if [(d["decl"], d["file"]) for d in old["lean_decls"]] != [(d["decl"], d["file"]) for d in new["lean_decls"]]:
            reasons.append("Lean declarations changed")
        elif lean_src(old["lean_decls"], lambda f: show(rev, f"{LEAN_REL}/{f}")) != \
                lean_src(new["lean_decls"], lambda f: (auditlog.REPO / LEAN_REL / f).read_text()):
            reasons.append("Lean source changed")
        cf = corr_files.get(iid)
        if cf is None:
            reasons.append("no correspondence file")
        else:
            ob = corr_block(show(rev, f"{AUDIT_REL}/data/corr/{cf.name}"), iid)
            nb = corr_block(cf.read_text(), iid)
            if ob is None or strip_lines(ob) != strip_lines(nb):
                reasons.append("correspondence changed beyond line numbers")
        unmarked = [m["id"] for m in new["maps"]
                    if st["marks"].get(f"{iid}::{m['id']}", {}).get("value") != v["value"]]
        if unmarked:
            reasons.append(f"mappings not marked {v['value']}: {', '.join(unmarked)}")
        (keep if reasons else carry).append((iid, "; ".join(reasons) or f"judged against bundle {rev}", rev, v))

    for iid, why, *_ in carry:
        print(f"CARRY  {iid:22s} {why}")
    for iid, why, *_ in keep:
        print(f"KEEP   {iid:22s} {why}")
    unjudged = [i for i in cur if i not in st["verdicts"] or not st["verdicts"][i].get("value")]
    print(f"\n{len(carry)} to carry forward, {len(keep)} stale left for re-judging, unjudged: {', '.join(unjudged) or 'none'}")
    if not apply or not carry:
        if not apply:
            print("dry run; rerun with --apply to append the session")
        return 0

    ms = int(time.time() * 1000)
    t = dt.datetime.fromtimestamp(ms / 1000, dt.timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")
    session = f"carry-forward-{t.replace(':', '-')}"
    meta = {"t": t, "ms": ms, "session": session, "tool": TOOL,
            "reason": "item changed only in TeX line numbers/positions since the verdict"}
    events = [{"type": "session_start", "item": None, "ua": "claude-code carry forward (not a browser session)",
               "bundle_git": data.get("git") or data.get("built_git")}]
    for iid, _, rev, v in carry:
        events.append({"type": "verdict", "item": iid, "value": v["value"], "previous": v["value"], "auto": False,
                       "item_hash": cur[iid]["hash"], "carried_from_hash": v["hash"], "carried_from_bundle": rev,
                       "carried_from_t": v["t"], "active_ms": 0})
    n = auditlog.append(events, meta)
    print(f"appended {n} events to {auditlog.rel(auditlog.EVENTS)} (session {session})")
    return 0


if __name__ == "__main__":
    sys.exit(main("--apply" in sys.argv[1:]))
