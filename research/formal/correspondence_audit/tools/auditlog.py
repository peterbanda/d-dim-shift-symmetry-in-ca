#!/usr/bin/env python3
"""Audit log: event store, state replay, and the end-of-audit report.

Every interaction of the audit UI is appended as one JSON line to
`logs/events.jsonl` (never rewritten). The current state (verdicts, notes,
mapping marks) and the report are pure functions of that file.

  auditlog.py report      write logs/audit_report_<UTC stamp>.{md,json} from the events
  auditlog.py state       print the replayed state as JSON
  auditlog.py --instance DIR report|state    the same for another paper (tools/instance.py)
"""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent
REPO = AUDIT.parents[2]
LOGS = AUDIT / "logs"
EVENTS = LOGS / "events.jsonl"
DATA = AUDIT / "data" / "audit_data.json"


def set_log_dir(d: Path):
    global LOGS, EVENTS
    LOGS = d
    EVENTS = d / "events.jsonl"


def set_instance(inst):
    """Use the data and the log of an audit instance (tools/instance.py)."""
    global DATA
    DATA = inst.data / "audit_data.json"
    set_log_dir(inst.logs)


def lean_file(data: dict, f: str) -> Path:
    """A Lean file of the bundle: in the package of its top-level module (instances with several
    packages record them in `lean_roots`), else under `lean_root`."""
    roots = data.get("lean_roots") or {}
    return REPO / roots.get(f.split("/")[0], data["lean_root"]) / f


def rel(p: Path) -> str:
    try:
        return str(p.relative_to(REPO))
    except ValueError:
        return str(p)


def now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).astimezone().isoformat(timespec="milliseconds")


def append(events: list[dict], meta: dict) -> int:
    LOGS.mkdir(exist_ok=True)
    with EVENTS.open("a") as f:
        for e in events:
            e = dict(e)
            e["received"] = now_iso()
            e.update({k: v for k, v in meta.items() if k not in e})
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    return len(events)


def read_events() -> list[dict]:
    if not EVENTS.exists():
        return []
    out = []
    for line in EVENTS.read_text().splitlines():
        line = line.strip()
        if line:
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return out


def replay(events: list[dict]) -> dict:
    verdicts: dict[str, dict] = {}
    notes: dict[str, dict] = {}
    marks: dict[str, dict] = {}
    for e in events:
        t = e.get("type")
        if t == "verdict":
            verdicts[e["item"]] = {"value": e.get("value"), "t": e.get("t"), "hash": e.get("item_hash"),
                                   "auto": e.get("auto", False)}
        elif t == "note":
            notes[e["item"]] = {"text": e.get("text", ""), "t": e.get("t")}
        elif t == "mapping_mark":
            marks[f"{e['item']}::{e['mapping']}"] = {"value": e.get("value"), "t": e.get("t")}
    return {"verdicts": verdicts, "notes": notes, "marks": marks}


def fmt_ms(ms: float) -> str:
    s = int(round(ms / 1000))
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    return f"{h}h {m:02d}m {s:02d}s" if h else f"{m}m {s:02d}s"


def sha256(p: Path) -> str | None:
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()
    except OSError:
        return None


def report() -> tuple[Path, Path, str]:
    events = read_events()
    data = json.loads(DATA.read_text())
    items = data["items"]
    st = replay(events)

    # active time per item: each item_close carries cumulative per-session counters
    active: dict[str, float] = {}
    wall: dict[str, float] = {}
    per_session: dict[str, dict[str, float]] = {}
    per_session_wall: dict[str, dict[str, float]] = {}
    sessions: dict[str, dict] = {}
    opens: dict[str, int] = {}
    map_views: dict[str, set] = {}
    node_views: dict[str, int] = {}
    defs: dict[str, int] = {}
    changes: dict[str, int] = {}
    first_verdict: dict[str, str] = {}
    for e in events:
        sid = e.get("session", "?")
        s = sessions.setdefault(sid, {"first": e.get("t"), "last": e.get("t"), "n": 0, "active_ms": 0,
                                      "start": None, "finish": [], "ua": None})
        s["last"] = e.get("t") or s["last"]
        s["n"] += 1
        t = e.get("type")
        it = e.get("item")
        if t == "session_start":
            s["start"] = e
            s["ua"] = e.get("ua")
        if t == "finish":
            s["finish"].append(e.get("t"))
        if t == "item_close" and it:
            per_session.setdefault(sid, {})[it] = max(per_session.get(sid, {}).get(it, 0), e.get("active_ms", 0))
            per_session_wall.setdefault(sid, {})[it] = max(per_session_wall.get(sid, {}).get(it, 0), e.get("wall_ms", 0))
        if t == "item_open" and it:
            opens[it] = opens.get(it, 0) + 1
        if t == "mapping_select" and it:
            map_views.setdefault(it, set()).add(e.get("mapping"))
        if t == "node_inspect" and it:
            node_views[it] = node_views.get(it, 0) + 1
        if t == "goto_def" and it:
            defs[it] = defs.get(it, 0) + 1
        if t == "verdict" and it:
            changes[it] = changes.get(it, 0) + 1
            first_verdict.setdefault(it, e.get("t"))
    for sid, m in per_session.items():
        for it, ms in m.items():
            active[it] = active.get(it, 0) + ms
        sessions[sid]["active_ms"] = sum(m.values())
    for sid, m in per_session_wall.items():
        for it, ms in m.items():
            wall[it] = wall.get(it, 0) + ms

    rows = []
    for it in items:
        iid = it["id"]
        v = st["verdicts"].get(iid, {})
        value = v.get("value")
        stale = bool(value) and v.get("hash") not in (None, it["hash"])
        rows.append({
            "item": iid, "display": it["display"], "tex_lines": it["tex_lines"],
            "lean": [f"{d['file']}:{d['sl']}-{d['el']} ({d['decl']})" for d in it["lean_decls"]],
            "verdict": value, "verdict_time": v.get("t"), "first_verdict_time": first_verdict.get(iid),
            "verdict_changes": changes.get(iid, 0),
            "stale": stale, "note": st["notes"].get(iid, {}).get("text", ""),
            "active_ms": round(active.get(iid, 0)), "open_ms": round(wall.get(iid, 0)),
            "opens": opens.get(iid, 0),
            "mappings_total": len(it["maps"]), "mappings_viewed": len(map_views.get(iid, set()) & {m["id"] for m in it["maps"]}),
            "nodes_inspected": node_views.get(iid, 0), "definitions_opened": defs.get(iid, 0),
            "mapping_marks": {m["id"]: st["marks"][f"{iid}::{m['id']}"]["value"]
                              for m in it["maps"] if f"{iid}::{m['id']}" in st["marks"]},
            "item_hash": it["hash"],
        })

    up = sum(1 for r in rows if r["verdict"] == "up")
    down = sum(1 for r in rows if r["verdict"] == "down")
    open_ = len(rows) - up - down
    fp_now = {
        "paper_pdf": sha256(REPO / data["fingerprints"]["paper_pdf"]["path"]),
        "paper_tex": sha256(REPO / data["fingerprints"]["paper_tex"]["path"]),
    }
    lean_changed = [f for f, h in data["fingerprints"]["lean"].items()
                    if sha256(lean_file(data, f)) != h]
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    summary = {
        "generated": now_iso(), "git_head_at_build": data["git_head"], "data_built": data["built"],
        "items": len(rows), "up": up, "down": down, "unjudged": open_,
        "total_active_ms": round(sum(r["active_ms"] for r in rows)),
        "sessions": [{"session": sid, "first_event": s["first"], "last_event": s["last"], "events": s["n"],
                      "active_ms": round(s["active_ms"]), "finished_at": s["finish"], "user_agent": s["ua"]}
                     for sid, s in sessions.items()],
        "sources_unchanged_since_build": {
            "paper_pdf": fp_now["paper_pdf"] == data["fingerprints"]["paper_pdf"]["sha256"],
            "paper_tex": fp_now["paper_tex"] == data["fingerprints"]["paper_tex"]["sha256"],
            "lean_files_changed": lean_changed,
        },
        "fingerprints_at_build": data["fingerprints"],
        "events_file": rel(EVENTS), "events_sha256": sha256(EVENTS), "event_count": len(events),
        "rows": rows,
    }
    LOGS.mkdir(exist_ok=True)
    jpath = LOGS / f"audit_report_{stamp}.json"
    mpath = LOGS / f"audit_report_{stamp}.md"
    jpath.write_text(json.dumps(summary, indent=1, ensure_ascii=False))

    sym = {"up": "👍 up", "down": "👎 down", None: "— not judged"}
    L = []
    L.append("# Paper ↔ Lean correspondence audit — report")
    L.append("")
    L.append(f"Generated {summary['generated']} from `{summary['events_file']}` "
             f"({len(events)} events, sha256 `{(summary['events_sha256'] or '')[:16]}…`).")
    L.append(f"Audit data built {data['built']} at git `{data['git_head'][:10]}`.")
    L.append("")
    L.append(f"**{up} up · {down} down · {open_} not judged** (of {len(rows)} items); "
             f"active audit time {fmt_ms(summary['total_active_ms'])}.")
    src = summary["sources_unchanged_since_build"]
    if src["paper_pdf"] and src["paper_tex"] and not src["lean_files_changed"]:
        L.append("")
        L.append("Sources unchanged since the data build (PDF, TeX and every Lean file match their recorded SHA-256).")
    else:
        L.append("")
        L.append(f"**Sources changed since the data build** — PDF ok: {src['paper_pdf']}, TeX ok: {src['paper_tex']}, "
                 f"changed Lean files: {', '.join(src['lean_files_changed']) or 'none'}.")
    stale = [r for r in rows if r["stale"]]
    if stale:
        L.append("")
        L.append(f"**Stale verdicts** (item content changed after the verdict): {', '.join(r['item'] for r in stale)}.")
    L.append("")
    L.append("## Items")
    L.append("")
    L.append("| Item | Verdict | When | Active time | Mappings viewed | Lean nodes inspected | Definitions opened | Note |")
    L.append("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in rows:
        note = (r["note"] or "").replace("|", "\\|").replace("\n", " ")
        L.append(f"| {r['display']} | {sym.get(r['verdict'], r['verdict'])}{' (stale)' if r['stale'] else ''} | "
                 f"{r['verdict_time'] or ''} | {fmt_ms(r['active_ms'])} | {r['mappings_viewed']}/{r['mappings_total']} | "
                 f"{r['nodes_inspected']} | {r['definitions_opened']} | {note} |")
    downs = [r for r in rows if r["verdict"] == "down" or "down" in r["mapping_marks"].values()]
    if downs:
        L.append("")
        L.append("## Rejected correspondences")
        for r in downs:
            L.append("")
            L.append(f"### {r['display']}")
            L.append(f"- verdict: {sym.get(r['verdict'], r['verdict'])}")
            L.append(f"- TeX lines {r['tex_lines'][0]}–{r['tex_lines'][1]}; Lean: " + "; ".join(r["lean"]))
            bad = [k for k, v in r["mapping_marks"].items() if v == "down"]
            if bad:
                L.append(f"- mappings marked wrong: {', '.join(bad)}")
            if r["note"]:
                L.append(f"- note: {r['note']}")
    L.append("")
    L.append("## Sessions")
    L.append("")
    for s in summary["sessions"]:
        L.append(f"- `{s['session']}`: {s['first_event']} → {s['last_event']}, {s['events']} events, "
                 f"active {fmt_ms(s['active_ms'])}" + (f", finished {', '.join(s['finished_at'])}" if s["finished_at"] else ""))
    L.append("")
    L.append("## Fingerprints (at data build)")
    L.append("")
    L.append(f"- PDF `{data['fingerprints']['paper_pdf']['path']}`: `{data['fingerprints']['paper_pdf']['sha256']}`")
    L.append(f"- TeX `{data['fingerprints']['paper_tex']['path']}`: `{data['fingerprints']['paper_tex']['sha256']}`")
    L.append(f"- {len(data['fingerprints']['lean'])} Lean files, {len(data['fingerprints']['corr'])} correspondence files "
             f"(full list in `{jpath.name}`)")
    L.append("")
    L.append(f"Full per-event log: `{summary['events_file']}`; machine-readable report: `{jpath.name}`.")
    md = "\n".join(L) + "\n"
    mpath.write_text(md)
    return mpath, jpath, md


if __name__ == "__main__":
    sys.path.insert(0, str(HERE))
    from instance import from_argv
    _inst = from_argv()
    if not _inst.is_default():
        set_instance(_inst)
    cmd = sys.argv[1] if len(sys.argv) > 1 else "report"
    if cmd == "state":
        print(json.dumps(replay(read_events()), indent=1, ensure_ascii=False))
    else:
        m, j, _ = report()
        print(m)
        print(j)
