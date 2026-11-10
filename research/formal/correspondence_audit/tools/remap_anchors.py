"""Carry the TeX anchors of the correspondence data from one paper version to the next.

Usage (from the repository root):
    git show <old commit>:shift_symmetry_d_dimensions.tex > /tmp/old.tex
    python3 research/formal/correspondence_audit/tools/remap_anchors.py /tmp/old.tex shift_symmetry_d_dimensions.tex [--apply]

Run it before build.py --check, while data/corr still validates against OLD (first used for paper v7 -> v8, Run 029).

For each anchor: find its match in OLD within its scope (must exist: v7 validated clean), then
  - env scope: check NEW's item env;
  - lines scope: map the scope's line range through build.line_map(OLD, NEW) and check there.
Status: OK (unchanged), REMAP (lines scope needs new numbers; found in mapped range with the same
count), MOVED (lines scope: not in the mapped range, but exactly once in NEW, scope set to that line range),
TEXT (wording changed: needs a hand edit, and the mapping must be re-read against the new wording).
With --apply, REMAP and MOVED scopes are written back to the JSON files (only "lines" values change).
"""
import json, sys
from pathlib import Path

AUDIT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(AUDIT / "tools"))
import build  # noqa: E402

old_text, new_text = Path(sys.argv[1]).read_text(), Path(sys.argv[2]).read_text()
apply = "--apply" in sys.argv
old, new = build.Tex(old_text), build.Tex(new_text)
aux = json.loads((AUDIT / "data/paper.aux.json").read_text())
items_old = {it["id"]: it for it in build.find_items(old, aux)}
items_new = {it["id"]: it for it in build.find_items(new, aux)}
lm, st = build.line_map(old_text.split("\n"), new_text.split("\n"))


def count(tex, text, lo, hi):
    return [m for m in build.ws_regex(text).finditer(tex.text, lo, hi)]


summary = {"OK": 0, "REMAP": 0, "MOVED": 0, "TEXT": 0}
for f in sorted((AUDIT / "data/corr").glob("*.json")):
    d = json.loads(f.read_text())
    label, changed = d["label"], False
    for mp in d["statement"]["maps"]:
        for ta in mp.get("tex") or []:
            scope = ta.get("scope", "env")
            occ = ta.get("occ", 1)
            if scope == "env":
                o_lo, o_hi = items_old[label]["body"], items_old[label]["end_tag"]
                n_lo, n_hi = items_new[label]["body"], items_new[label]["end_tag"]
                new_scope = scope
            else:
                a, b = scope["lines"]
                o_lo, o_hi = old.offset(a), old.line_end(b)
                na, nb = lm[a], lm[b]
                new_scope = {"lines": [na, nb]}
                n_lo, n_hi = new.offset(na), new.line_end(nb)
            mo = count(old, ta["text"], o_lo, o_hi)
            mn = count(new, ta["text"], n_lo, n_hi)
            if len(mo) < occ:
                print(f"OLD-MISSING {f.name}:{mp['id']}: {ta['text'][:70]!r}")
                continue
            if len(mn) >= occ and (len(mn) == len(mo) or "occ" in ta):
                if new_scope != scope:
                    status = "REMAP"
                    if apply:
                        ta["scope"] = new_scope
                        changed = True
                else:
                    status = "OK"
            elif scope != "env" and len(count(new, ta["text"], 0, len(new.text))) == 1:
                g = count(new, ta["text"], 0, len(new.text))[0]
                status = "MOVED"
                ns = {"lines": [new.line_of(g.start()), new.line_of(g.end())]}
                print(f"MOVED {f.name}:{mp['id']} {scope['lines']} -> {ns['lines']}: {ta['text'][:70]!r}")
                if apply:
                    ta["scope"] = ns
                    changed = True
            else:
                status = "TEXT"
                m = mo[occ - 1]
                l0 = old.line_of(m.start())
                print(f"TEXT {f.name}:{mp['id']} [{scope if scope == 'env' else scope['lines']}]"
                      f" old line {l0} -> new ~{lm[l0]} ({st[l0]}), found {len(mn)}x in new scope: {ta['text'][:90]!r}")
            summary[status] += 1
    if changed:
        f.write_text(json.dumps(d, ensure_ascii=False, indent=1))
print(summary)
