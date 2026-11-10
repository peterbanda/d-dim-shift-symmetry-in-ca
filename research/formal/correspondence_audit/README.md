# Paper ↔ Lean correspondence audit

A local tool for auditing, item by item, whether the frozen Lean statements in
`../shiftsym/` correspond to the statements of
`shift_symmetry_d_dimensions.tex/.pdf`. It covers every theorem, lemma,
proposition and corollary of the paper: 27 audit items. Proofs are not
audited. The mappings go only to Lean definitions and frozen statement
`Prop`s, never to `theorem`s; once a statement is shown to correspond, the
Lean kernel's check of its `_proved` theorem carries the proof (see the
axiom and placeholder gates in `../../../README.md`). `tools/build.py`
rejects correspondence files with a `proof` block or a Lean theorem anchor.

```
python3 research/formal/correspondence_audit/serve.py      # from the repo root
# open http://127.0.0.1:8765/
```

## What you see

- **Left: the official PDF** (PDF.js). The current item is highlighted in
  yellow. Every paper sub-expression that has a mapping gets a dashed box;
  clicking one selects the innermost mapping under the cursor.
- **Right: the item.** Verdict buttons (👍 holds / 👎 fails), a notes field,
  the summary, the deltas (representation choices), the list of mappings
  (each with ✓/✗ marks; once every mapping is judged the item is marked
  automatically, 👍 if all are ✓ and 👎 if any is ✗, with a short animation;
  an automatic verdict is withdrawn if a mark is taken back, and a manual
  verdict is never overridden), the project definitions the statement uses, and one card per Lean
  declaration. Each card shows the source with real line numbers
  and `file:first–last` (a `vscode://` link).
- **Mapping kinds** (colour of the boxes and arrow): *same*;
  *representation* (same content, different encoding, e.g. ℝ for ℕ or
  0-indexing); *definition*; *hypothesis* (incl. standing hypotheses the
  paper leaves implicit); *generalization* (the Lean statement covers more);
  *weaker* (the Lean statement says less: this part of the paper is not
  certified by a frozen statement); *paper-only* (no Lean counterpart, e.g.
  names); *lean-only* (no paper counterpart); *citation*.
- **SVG arrow** from the PDF to the Lean side. With no mapping selected it
  points from the item to its header. With a mapping selected it points from
  the paper sub-expression to the Lean sub-expression. It is dashed when one
  end is scrolled out of view.
- **Inspector (bottom right).** Clicking any Lean token selects the innermost
  info-tree node there and shows its type, its elaborated form, and the
  constant it names, with signature, docstring and *Open definition*. Click
  again to widen to the enclosing expression, or use the breadcrumb. Tactic
  nodes show the goals before and after. A selected mapping shows its note,
  the exact TeX source with line numbers, and what the Lean anchor elaborates
  to.
- **Paper line numbers in Lean comments.** The Lean files cite paper lines of
  the version they were written against (groups 01–11: v3.1, group 12: v4,
  the window-20 supplement: v5: the paper just before the commit that added
  the file), and the frozen files are never renumbered. `tools/build.py` maps
  each cited version onto the current paper with a line diff, and a badge
  after a citation gives the line in the current paper wherever it differs
  (`line 1213` →1366). Amber: that line's text has changed since; red: the
  line is gone (the badge gives the nearest line). Hover a badge for both
  texts; click it to show them in the inspector. The build warns if a file's
  quotations match another version of the paper better than its own.

Keys: `j`/`k` next/previous item · `n`/`p` next/previous mapping · `N` next
mapping not yet judged · `u`/`d`
mark the selected mapping ✓/✗, or with no mapping selected set the item
verdict 👍/👎 · `Esc` clear · `+`/`−` zoom (click the % to fit) · `?` help.

## The audit log

Every action is appended to `logs/events.jsonl` (append-only, one JSON
object per line, with client and server timestamps). The events are:
session start (with the data build's git commit and the PDF/TeX SHA-256), item
open/close, active and wall time per item (sent on item close; idle after
2 min without input is not counted), mapping selections (and whether they came
from the PDF, the list, the keyboard or Lean), Lean nodes inspected,
definitions opened, verdicts (with the item's content hash), notes, mapping
marks, zoom, visibility and idle.

History of the committed log (the log is kept under version control; "append-only" describes the
viewer, not every change to the file): commit `b83a7fb` (2026-10-22) removed the heartbeat events
from it; and on 2026-11-02 a script appended the session `bulk-clear-v6-to-v8-…` (68 events, tool
`claude-code:clear-changed-mapping-marks`), which withdrew the marks and verdicts of the mappings
that changed between the v6 and v8 bundles, so that they were judged again (all 25 items were
approved afterwards; five verdicts, given against the bundle of 2026-10-22/23, were flagged stale
at v8 only because line numbers had moved). Two later sessions were appended by
`tools/carry_forward.py` (tool `claude-code:carry-forward-positional`): `carry-forward-2026-11-08T00-33-44.837Z`
(25 events, Run 045) re-issued 24 verdicts for paper v10, and `carry-forward-2026-11-08T22-36-22.311Z`
(13 events, Run 047) re-issued 12 for paper v11, whose edits (Sections 4.5, 11–12, the new Appendix B)
moved their line numbers. The script re-issues a
verdict under the item's current hash only if the item's TeX, the Lean source of its declarations and
its links are unchanged apart from line numbers and positions, and every link carries a mark equal to
the verdict; each event records the hash, bundle and time of the verdict it carries. Anything else is
left stale for the auditor (Theorem 4.7 since Run 046, whose links `Gp`, `Fp`, `dp` now point to the new
frozen statement `pTorsionVectorSpaceStatement`). Corollary 4.8 became Corollary B.1 in v11 without any
change to its text or links, so its verdict stayed current. Opening the viewer appends your own session to the log
(`git checkout research/formal/correspondence_audit/logs` discards it); `serve.py --log-dir DIR`
writes to another directory instead, but then starts from an empty log.

**Finish audit** (or `python3 tools/auditlog.py report`) writes
`logs/audit_report_<UTC>.md` and `.json`. They contain, per item: verdict,
when it was set, how often it changed, active time, mappings viewed/total,
nodes inspected, definitions opened, the note, and per-mapping marks. They also
contain per-session times, the rejected items in detail, and the fingerprints.
A verdict is flagged **stale** if the item's TeX, Lean source, or mapping has
changed since the verdict was given. The report also states whether the PDF,
TeX, and every Lean file still match the SHA-256 recorded at build time.
Verdicts persist across sessions (the state is replayed from the event log),
and you can finish as often as you like.

`serve.py --log-dir DIR` writes the log elsewhere, e.g. for a dry run.

## How the data is built (and why the highlights can be trusted)

```
tools/export_lean.sh          # info trees of every Paper/, Proofs/, Lemmas/ file (lake env lean --run)
python3 tools/build.py        # needs docker image shiftsym-tex:jammy (see below)
```

1. `tools/ExportInfo.lean` re-elaborates each Lean file and dumps what the
   editor's infoview would show: every term node (range, type, elaborated
   term, constant), every tactic node (goals before/after), the declarations
   with their ranges, and the signature, docstring and location of every
   referenced constant. The output goes to `data/lean/`. It is read-only on the
   Lean development.
2. `data/corr/*.json` is the correspondence data, one file per paper
   environment (schema in `tools/build.py`'s validator, worked example
   `data/corr/lem_fix.json`). Every TeX anchor is a substring of the
   environment (or of a stated line range). Every Lean anchor is a substring
   of a named declaration. The validator rejects anchors that do not resolve,
   are ambiguous, or would disturb typesetting.
3. Positions: a copy of the paper with zero-width `\pdfsavepos` markers
   around every anchor and at every item boundary is compiled with the same
   pdfTeX 1.40.22 / TeX Live 2022-dev that produced the official PDF (Ubuntu
   22.04 in Docker). **The build fails unless every word of that copy sits at
   exactly the coordinates of the official PDF** (`pdftotext -bbox`, every
   page). The marker coordinates are therefore coordinates in the official
   PDF. The boxes are fitted to the official PDF's glyph boxes
   (`tools/pdf_chars.py`, PyMuPDF via `uv`).
4. `data/audit_data.json` holds the items, resolved mappings, rectangles, and
   SHA-256 of every input.

Docker image (once). It must have the same fonts as the machine that built the
official PDF: `cm-super` supplies the scalable T1 text fonts (SFRM, SFBX, …).
Without it pdfTeX falls back to bitmap fonts. A layout check against an
official PDF built with `cm-super` then fails from the first word. Run
`pdffonts` on the official PDF to see which fonts were used.

```
docker build -t shiftsym-tex:jammy - <<'EOF'
FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended cm-super poppler-utils && rm -rf /var/lib/apt/lists/*
WORKDIR /work
EOF
```

To validate correspondence files without TeX, run `tools/build.py --check
[files]`. Add `--layout` to also verify the typesetting.

`--check` does not refresh `data/audit_data.json`. After any change to the
paper, the correspondence files or the Lean exports, rerun the full build.
The viewer always shows the current PDF but takes item numbers, highlights and
item hashes from `audit_data.json`. A verdict is shown as stale only when it
differs from an item hash in that file, so an outdated bundle hides changes.
Before relying on the viewer, check that the `fingerprints` in
`audit_data.json` match the current PDF and TeX. The audit report
(`tools/auditlog.py report`) states whether they match.

## Caveat

The correspondence data was drafted by Claude sessions reading the paper
and the Lean sources. It is the claim being audited, not evidence. A 👍
should rest on your own reading of the highlighted paper text against the
Lean code and its elaborated types, not on the mapping notes.
