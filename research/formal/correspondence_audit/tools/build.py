#!/usr/bin/env python3
"""Build the data file of the paper <-> Lean correspondence audit.

Pipeline (all read-only on the paper and the Lean development):

1. Items: every theorem / lemma / proposition / corollary environment of
   `shift_symmetry_d_dimensions.tex`, with its TeX line range and its number
   (from the LaTeX .aux). Proofs are not audited: the audit checks that each
   paper statement corresponds to its frozen Lean statement, and the Lean
   kernel checks the proofs.
2. Correspondences: `data/corr/*.json` (hand-written, one file per paper
   environment). Each TeX anchor is a substring of the environment; each
   Lean anchor is a substring of a named declaration, located through the
   info-tree export `data/lean/*.json` (tools/ExportInfo.lean). Lean
   declarations must be definitions (incl. the frozen statement `Prop`s),
   never `theorem`/`lemma`s.
3. Positions: a copy of the paper with zero-width `\\pdfsavepos` markers
   around every TeX anchor is compiled in the same TeX version as the
   official PDF (Docker image `shiftsym-tex:jammy`, pdfTeX 1.40.22); the
   word boxes of that copy are compared with the official PDF and the build
   fails unless they are identical, so the recorded marker positions are
   positions in the official PDF. Rectangles are fitted to the glyph boxes
   of the official PDF (`data/pdf_chars.json`, tools/pdf_chars.py).
4. Paper line citations: Lean comments cite paper lines of the version their
   file was written against (frozen files are never renumbered). Each such
   version is mapped onto the current paper line by line, so the UI can show
   the current line next to every citation (`paper_cites`).
5. Output: `data/audit_data.json` (+ SHA-256 fingerprints of every input).

Usage (from anywhere):
  build.py --check [corr files...]   validate anchors only (fast, no TeX)
  build.py                           full build (needs docker)
  build.py --instance DIR ...        another paper (DIR/audit_config.json; see tools/instance.py)
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent
REPO = AUDIT.parents[2]
sys.path.insert(0, str(HERE))
from instance import from_argv  # noqa: E402

INST = from_argv()            # the main paper unless --instance DIR / CORR_AUDIT_INSTANCE
TEX = INST.tex
PDF = INST.pdf
LEAN_ROOT = INST.lean_root
DATA = INST.data
CORR = DATA / "corr"
LEAN_EXPORT = DATA / "lean"
CHARS = DATA / "pdf_chars.json"
OUT = DATA / "audit_data.json"
IMAGE = "shiftsym-tex:jammy"

THM_ENVS = INST.envs          # default: theorem, lemma, proposition, corollary
KINDS = {"same", "representation", "hypothesis", "generalization", "weaker", "paper-only",
         "lean-only", "citation", "definition"}
NOTES: list[str] = []

# geometry: a4paper, margin=1in  (PDF points, origin top-left)
PAGE_W, PAGE_H = 595.276, 841.89
TEXT_L, TEXT_R, TEXT_T, TEXT_B = 72.0, 523.276, 72.0, 769.89


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sha256s(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


# ---------------------------------------------------------------- TeX side

class Tex:
    def __init__(self, text: str):
        self.text = text
        self.line_start = [0]
        for i, ch in enumerate(text):
            if ch == "\n":
                self.line_start.append(i + 1)

    def offset(self, line: int) -> int:          # 1-based line -> offset
        return self.line_start[line - 1]

    def line_of(self, off: int) -> int:
        lo, hi = 0, len(self.line_start) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.line_start[mid] <= off:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def line_end(self, line: int) -> int:        # offset of the '\n' of line
        if line < len(self.line_start):
            return self.line_start[line] - 1
        return len(self.text)


def strip_comments_mask(text: str) -> list[bool]:
    """mask[i] is True when text[i] is inside a TeX comment."""
    mask = [False] * len(text)
    i = 0
    in_c = False
    while i < len(text):
        ch = text[i]
        if in_c:
            mask[i] = True
            if ch == "\n":
                in_c = False
        elif ch == "\\":
            i += 2
            continue
        elif ch == "%":
            in_c = True
            mask[i] = True
        i += 1
    return mask


def skip_balanced(text: str, i: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    while i < len(text):
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced")


def find_items(tex: Tex, aux: dict) -> list[dict]:
    text = tex.text
    cmask = strip_comments_mask(text)
    items = []
    pat = re.compile(r"\\begin\{(" + "|".join(THM_ENVS) + r")\}")
    for m in pat.finditer(text):
        if cmask[m.start()]:
            continue
        env = m.group(1)
        end_pat = re.compile(r"\\end\{" + env + r"\}")
        em = end_pat.search(text, m.end())
        i = m.end()
        title = None
        j = i
        while j < len(text) and text[j] in " \t\n":
            j += 1
        if j < len(text) and text[j] == "[":
            k = skip_balanced(text, j, "[", "]")
            title = text[j + 1:k - 1]
            i = k
        label = None
        lm = re.compile(r"\s*\\label\{([^}]*)\}").match(text, i)
        if lm:
            label = lm.group(1)
            i = lm.end()
        items.append({
            "env": env, "title": title, "label": label,
            "begin": m.start(), "body": i, "end_tag": em.start(), "end": em.end(),
            "line_begin": tex.line_of(m.start()), "line_end": tex.line_of(em.end() - 1),
        })
    for it in items:
        it["id"] = it["label"]
        num = aux.get(it["label"], {}).get("number", "?")
        it["number"] = num
        t = it["title"]
        if t:
            t = re.sub(r"\$([^$]*)\$", r"\1", t).replace("\\ge", "≥").replace("\\le", "≤").replace("\n", " ")
        it["display"] = f"{it['env'].capitalize()} {num}" + (f" ({t})" if t else "")
    return items


def load_aux(path: Path) -> dict:
    res = {}
    for line in path.read_text(errors="replace").splitlines():
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{([^}]*)\}", line)
        if m:
            res[m.group(1)] = {"number": m.group(2), "page": m.group(3)}
    return res


def ws_regex(s: str) -> re.Pattern:
    parts = re.split(r"\s+", s.strip())
    return re.compile(r"\s+".join(re.escape(p) for p in parts))


ARG_MACROS = {
    "frac", "tfrac", "dfrac", "binom", "tbinom", "dbinom", "gaussbinom", "genfrac", "sqrt",
    "mathrm", "mathbf", "mathcal", "mathbb", "mathfrak", "mathsf", "mathit", "boldsymbol",
    "operatorname", "text", "textrm", "textbf", "textit", "emph", "boxed", "substack",
    "left", "right", "bigl", "bigr", "Bigl", "Bigr", "biggl", "biggr", "Biggl", "Biggr",
    "big", "Big", "bigg", "Bigg", "bigm", "Bigm", "middle", "hat", "tilde", "bar", "overline",
    "underline", "widehat", "widetilde", "vec", "dot", "ddot", "pmod", "label", "ref", "eqref",
    "cite", "stackrel", "overset", "underset", "phantom", "smash", "mbox", "hbox", "not",
    "lvert", "rvert",
}
NO_LEFT = ("^", "_")
NO_RIGHT = ("^", "_", "'")


def insertion_problems(text: str, s: int, e: int, cmask) -> list[str]:
    probs = []
    frag = text[s:e]
    if cmask[s] or cmask[max(e - 1, s)]:
        probs.append("anchor lies in a TeX comment")
    if frag[:1] in NO_LEFT:
        probs.append("anchor starts with ^/_ (marker would become a script base)")
    nxt = text[e:e + 1]
    if nxt in NO_RIGHT:
        probs.append(f"anchor is followed by {nxt!r}: end marker would separate a base from its script; include the script")
    if text[s - 1:s] in NO_LEFT:
        probs.append("anchor is preceded by ^/_ : start marker would become the script; wrap the braces or start earlier")
    # preceding control word
    pm = re.search(r"\\([A-Za-z]+)\s*$", text[max(0, s - 40):s])
    if pm and pm.group(1) in ARG_MACROS:
        probs.append(f"anchor is preceded by \\{pm.group(1)} (would steal its argument)")
    em = re.search(r"\\([A-Za-z]+)\s*$", frag)
    if em and em.group(1) in ARG_MACROS:
        probs.append(f"anchor ends with \\{em.group(1)} (marker would become its argument)")
    if frag.endswith("\\"):
        probs.append("anchor ends with a backslash")
    # balance
    depth = 0
    i = 0
    dollars = 0
    while i < len(frag):
        ch = frag[i]
        if ch == "\\":
            if frag[i + 1:i + 2] in ("[", "]", "(", ")"):
                probs.append("anchor contains \\[ \\] \\( \\): keep anchors inside one math/text run")
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth < 0:
                break
        elif ch == "$":
            dollars += 1
        i += 1
    if depth != 0:
        probs.append("anchor has unbalanced braces")
    if dollars % 2:
        probs.append("anchor has an odd number of $ (would start in one mode and end in another)")
    # inside \label / \ref / \cite argument?
    back = text[max(0, s - 60):s]
    if re.search(r"\\(label|ref|eqref|cite)(\[[^\]]*\])?\{[^}]*$", back):
        probs.append("anchor is inside a \\label/\\ref/\\cite argument")
    return probs


def math_context(text: str, off: int, item_body: int) -> str:
    """'display', 'inline' or 'text' at offset off (heuristic scan from the env body)."""
    mode = "text"
    i = item_body
    stack = []
    while i < off:
        ch = text[i]
        if ch == "%":
            nl = text.find("\n", i)
            i = nl if nl >= 0 else off
            continue
        if ch == "\\":
            two = text[i:i + 2]
            if two == "\\[":
                mode = "display"
            elif two == "\\]":
                mode = "text"
            else:
                m = re.match(r"\\(begin|end)\{(equation\*?|align\*?|gather\*?|multline\*?)\}", text[i:i + 30])
                if m:
                    mode = "display" if m.group(1) == "begin" else "text"
            i += 2
            continue
        if ch == "$" and mode != "display":
            mode = "inline" if mode == "text" else "text"
        i += 1
    return mode


def env_end_insertion(text: str, it: dict) -> int:
    """Offset just after the last content of the environment, moved inside a
    trailing display / list so that the marker is in horizontal or math mode."""
    e = it["end_tag"]
    while True:
        j = e
        # skip whitespace and trailing comments
        while j > it["body"] and text[j - 1] in " \t\n":
            j -= 1
        seg = text[it["body"]:j]
        m = re.search(r"(\\\]|\\end\{(enumerate|itemize|equation\*?|align\*?|gather\*?)\})$", seg)
        if m:
            e = it["body"] + m.start()
            continue
        return j


# ---------------------------------------------------------------- Lean side

class LeanIndex:
    def __init__(self):
        self.decls: dict[str, dict] = {}
        self.files: dict[str, dict] = {}
        self.text: dict[str, str] = {}
        for p in sorted(LEAN_EXPORT.glob("*.json")):
            if p.name.startswith("_"):
                continue
            d = json.loads(p.read_text())
            f = d["file"]
            self.files[f] = {"export": p.name, "nodes": d["nodes"]}
            for dd in d["decls"]:
                self.decls.setdefault(dd["name"], {"file": f, **dd["range"]})

    DECL_KW = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                         r"(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\b", re.M)

    def is_theorem(self, name: str) -> bool:
        """True when the declaration is a `theorem`/`lemma` (i.e. it carries a proof)."""
        d = self.decls[name]
        seg = "\n".join(self.lines(d["file"])[d["sl"] - 1:d["el"]])
        m = self.DECL_KW.search(re.sub(r"/--.*?-/", "", seg, flags=re.S))
        return bool(m) and m.group(1) in ("theorem", "lemma")

    def src(self, f: str) -> str:
        if f not in self.text:
            self.text[f] = INST.lean_path(f).read_text()
        return self.text[f]

    def lines(self, f: str) -> list[str]:
        return self.src(f).split("\n")

    def resolve(self, a: dict) -> tuple[dict | None, list[str]]:
        errs = []
        if "decl" in a:
            d = self.decls.get(a["decl"])
            if d is None:
                cand = [k for k in self.decls if k.endswith("." + a["decl"].split(".")[-1])]
                return None, [f"unknown Lean declaration {a['decl']!r}" + (f" (did you mean {cand[:3]})" if cand else "")]
            f, sl, el = d["file"], d["sl"], d["el"]
        else:
            f = a.get("file")
            if not f or not INST.lean_path(f).exists():
                return None, [f"Lean anchor needs 'decl' or an existing 'file' (got {f!r})"]
            sl, el = a.get("lines", [1, len(self.lines(f))])
        lines = self.lines(f)
        seg = "\n".join(lines[sl - 1:el])
        seg_off = sum(len(x) + 1 for x in lines[:sl - 1])
        res = {"file": f, "decl": a.get("decl"), "decl_sl": sl, "decl_el": el}
        if not a.get("text"):
            res.update({"sl": sl, "sc": 0, "el": el, "ec": len(lines[el - 1])})
            return res, errs
        rx = ws_regex(a["text"])
        ms = list(rx.finditer(seg))
        occ = a.get("occ", 1)
        if len(ms) < occ:
            return None, [f"Lean text {a['text']!r} occurs {len(ms)}x in {a.get('decl') or f} (occ={occ})"]
        if len(ms) > 1 and "occ" not in a:
            errs.append(f"warning: Lean text {a['text']!r} occurs {len(ms)}x in {a.get('decl') or f}; using the first (set 'occ')")
        m = ms[occ - 1]
        s, e = seg_off + m.start(), seg_off + m.end()
        src = self.src(f)
        res["sl"] = src.count("\n", 0, s) + 1
        res["sc"] = s - (src.rfind("\n", 0, s) + 1)
        res["el"] = src.count("\n", 0, e) + 1
        res["ec"] = e - (src.rfind("\n", 0, e) + 1)
        nodes = self.files.get(f, {}).get("nodes", [])
        res["node_aligned"] = any(n["sl"] == res["sl"] and n["sc"] == res["sc"] and
                                  n["el"] == res["el"] and n["ec"] == res["ec"] for n in nodes)
        return res, errs


# ---------------------------------------------------------------- correspondences

def load_corr(files: list[Path]) -> dict[str, dict]:
    res = {}
    for p in files:
        d = json.loads(p.read_text())
        d["_file"] = p.name
        res[d["label"]] = d
    return res


def validate(corr: dict, items: list[dict], tex: Tex, lean: LeanIndex) -> tuple[list, list, list]:
    """Returns (resolved maps, errors, warnings)."""
    text = tex.text
    cmask = strip_comments_mask(text)
    by_id = {it["id"]: it for it in items}
    errors, warnings, resolved = [], [], []
    notes = NOTES
    for label, c in corr.items():
        src = c["_file"]
        if "proof" in c:
            errors.append(f"{src}: has a 'proof' block; proofs are not audited (the Lean kernel checks them)")
        for part in ("statement",):
            blk = c.get(part)
            iid = label
            if blk is None:
                errors.append(f"{src}: missing 'statement' block")
                continue
            if iid not in by_id:
                errors.append(f"{src}: no paper item {iid!r}")
                continue
            it = by_id[iid]
            for k in ("summary", "lean_decls", "maps"):
                if k not in blk:
                    errors.append(f"{src}:{part}: missing {k!r}")
            for ld in blk.get("lean_decls", []):
                if ld.get("decl") not in lean.decls:
                    errors.append(f"{src}:{part}: lean_decls: unknown declaration {ld.get('decl')!r}")
                elif lean.is_theorem(ld["decl"]):
                    errors.append(f"{src}:{part}: lean_decls: {ld['decl']} is a theorem/lemma; only definitions and statements are mapped")
            seen = set()
            for mp in blk.get("maps", []):
                mid = mp.get("id")
                where = f"{src}:{part}:{mid}"
                if not mid or mid in seen:
                    errors.append(f"{where}: missing or duplicate id")
                seen.add(mid)
                if mp.get("kind") not in KINDS:
                    errors.append(f"{where}: kind {mp.get('kind')!r} not in {sorted(KINDS)}")
                rm = {"item": iid, "id": mid, "kind": mp.get("kind"), "label": mp.get("label", ""),
                      "note": mp.get("note", ""), "tex": [], "lean": []}
                for ta in mp.get("tex") or []:
                    scope = ta.get("scope", "env")
                    if scope == "env":
                        lo, hi = it["body"], it["end_tag"]
                    elif isinstance(scope, dict) and "lines" in scope:
                        lo, hi = tex.offset(scope["lines"][0]), tex.line_end(scope["lines"][1])
                    else:
                        errors.append(f"{where}: bad tex scope {scope!r}")
                        continue
                    ms = [m for m in ws_regex(ta["text"]).finditer(text, lo, hi)]
                    occ = ta.get("occ", 1)
                    if len(ms) < occ:
                        errors.append(f"{where}: TeX text {ta['text']!r} occurs {len(ms)}x in scope (occ={occ})")
                        continue
                    if len(ms) > 1 and "occ" not in ta:
                        warnings.append(f"{where}: TeX text {ta['text']!r} occurs {len(ms)}x; using the first (set 'occ')")
                    m = ms[occ - 1]
                    for pr in insertion_problems(text, m.start(), m.end(), cmask):
                        errors.append(f"{where}: TeX anchor {ta['text']!r}: {pr}")
                    rm["tex"].append({"s": m.start(), "e": m.end(),
                                      "line": tex.line_of(m.start()), "line_end": tex.line_of(m.end()),
                                      "text": text[m.start():m.end()],
                                      "mode": math_context(text, m.start(), it["body"] if scope == "env" else lo)})
                for la in mp.get("lean") or []:
                    if la.get("decl") in lean.decls and lean.is_theorem(la["decl"]):
                        errors.append(f"{where}: Lean anchor in {la['decl']}, a theorem/lemma; only definitions and statements are mapped")
                        continue
                    r, errs = lean.resolve(la)
                    for e in errs:
                        (warnings if e.startswith("warning") else errors).append(f"{where}: {e}")
                    if r:
                        if not r.get("node_aligned", True) and la.get("text"):
                            notes.append(f"{where}: Lean text {la['text']!r} is not exactly one info-tree node (fine for binder groups, hypothesis lists, parenthesised terms)")
                        rm["lean"].append(r)
                if mp.get("kind") == "paper-only" and mp.get("lean"):
                    warnings.append(f"{where}: kind paper-only but has Lean anchors")
                if mp.get("kind") == "lean-only" and mp.get("tex"):
                    warnings.append(f"{where}: kind lean-only but has TeX anchors")
                if not mp.get("tex") and mp.get("kind") != "lean-only":
                    warnings.append(f"{where}: no TeX anchor (kind {mp.get('kind')})")
                resolved.append(rm)
    return resolved, errors, warnings


# ---------------------------------------------------------------- compile + positions

PREAMBLE_HOOK = r"""
\newwrite\AUout
\AtBeginDocument{\immediate\openout\AUout=\jobname.apos}
\makeatletter
\def\AUM#1{\pdfsavepos\write\AUout{#1 \the\pdflastxpos\space\the\pdflastypos\space\the\c@page}}
\makeatother
"""


def instrument(tex: Tex, items: list[dict], maps: list[dict]) -> str:
    text = tex.text
    ins: list[tuple[int, int, str]] = []          # (offset, order, string)
    for k, it in enumerate(items):
        b = it["body"]
        while text[b] in " \t\n":          # a newline after \label is ignored in vertical mode;
            b += 1                          # after \leavevmode it would become a space
        ins.append((b, 1, "\\leavevmode\\AUM{I%dB}" % k))
        ins.append((env_end_insertion(text, it), -1, "\\AUM{I%dE}" % k))
    for k, mp in enumerate(maps):
        for j, ta in enumerate(mp["tex"]):
            ins.append((ta["s"], 2, "\\AUM{M%d.%dS}" % (k, j)))
            ins.append((ta["e"], -2, "\\AUM{M%d.%dE}" % (k, j)))
    # at equal offsets: end markers (negative order) before start markers
    ins.sort(key=lambda x: (x[0], x[1]))
    out = []
    last = 0
    for off, _, s in ins:
        out.append(text[last:off])
        out.append(s)
        last = off
    out.append(text[last:])
    res = "".join(out)
    res = res.replace("\\begin{document}", PREAMBLE_HOOK + "\\begin{document}", 1)
    return res


def run_tex(workdir: Path, name: str, passes: int):
    for _ in range(passes):
        r = subprocess.run(["docker", "run", "--rm", "-u", f"{os.getuid()}:{os.getgid()}", "-e", "HOME=/work",
                            "-v", f"{workdir}:/work", IMAGE, "pdflatex", "-interaction=nonstopmode",
                            "-halt-on-error", name + ".tex"], capture_output=True, text=True)
        if r.returncode != 0:
            log = (workdir / (name + ".log")).read_text(errors="replace")
            err = "\n".join(l for l in log.splitlines() if l.startswith("!") or l.startswith("l."))[:3000]
            raise RuntimeError(f"pdflatex failed:\n{err}")


def words(pdf: Path) -> list[str]:
    r = subprocess.run(["pdftotext", "-bbox", str(pdf), "-"], capture_output=True, text=True, check=True)
    return [l.strip() for l in r.stdout.splitlines() if "<word" in l or "<page" in l]


def compile_positions(instrumented: str, keep: Path | None = None) -> tuple[dict, dict]:
    tmp = Path(tempfile.mkdtemp(prefix="corr_audit_", dir=os.environ.get("TMPDIR")))
    try:
        name = TEX.stem
        (tmp / (name + ".tex")).write_text(instrumented)
        for spec in INST.figures:                   # paper figures (main paper: charts/*.png, charts/*.pdf)
            dest = tmp / spec.get("dest", "")
            dest.mkdir(parents=True, exist_ok=True)
            for fig in sorted(REPO.glob(spec["glob"])):
                if fig.resolve() != PDF.resolve():
                    shutil.copy(fig, dest / fig.name)
        run_tex(tmp, name, 3)
        aux = load_aux(tmp / (name + ".aux"))
        pos = {}
        for line in (tmp / (name + ".apos")).read_text().splitlines():
            k, x, y, page = line.split()
            pos[k] = (int(page), int(x) / 65536 * 72 / 72.27, PAGE_H - int(y) / 65536 * 72 / 72.27)
        a = words(tmp / (name + ".pdf"))
        b = words(PDF)
        diff = [i for i, (u, v) in enumerate(zip(a, b)) if u != v]
        if len(a) != len(b) or diff:
            i = diff[0] if diff else min(len(a), len(b))
            page = sum(1 for w in a[:i] if "<page" in w)
            raise RuntimeError(f"LAYOUT CHANGED by the markers: {len(diff)} differing words "
                               f"(first on page {page}: {a[i] if i < len(a) else '-'} vs {b[i] if i < len(b) else '-'}); "
                               "an anchor perturbs the typesetting — move it")
        if keep:
            shutil.copy(tmp / (name + ".pdf"), keep)
        return pos, aux
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def load_chars() -> dict:
    if not CHARS.exists() or json.loads(CHARS.read_text()).get("pdf_sha256") != sha256(PDF):
        subprocess.run(["uv", "run", "--quiet", "--no-project", "--with", "pymupdf", "python", "-I",
                        str(HERE / "pdf_chars.py"), str(PDF), str(CHARS)], check=True)
    return json.loads(CHARS.read_text())


def fit_rects(p0, p1, mode: str, chars: dict) -> list[list[float]]:
    """Rectangles [page, x0, y0, x1, y1] (top-left origin, pt) between two markers."""
    (pg0, x0, b0), (pg1, x1, b1) = p0, p1
    H, D = (20.0, 15.0) if mode == "display" else (9.5, 3.8)
    if pg0 == pg1 and abs(b0 - b1) < 1.0 and x1 >= x0:
        cs = [c for c in chars["pages"][pg0 - 1]
              if x0 - 0.3 <= (c[0] + c[2]) / 2 <= x1 + 0.3 and c[1] < b0 + D and c[3] > b0 - H]
        if cs:
            top, bot = min(c[1] for c in cs), max(c[3] for c in cs)
        else:
            top, bot = b0 - 8.0, b0 + 2.5
        return [[pg0, round(x0 - 0.8, 2), round(top - 0.8, 2), round(max(x1, x0 + 2) + 0.8, 2), round(bot + 0.8, 2)]]
    if mode == "display" and pg0 == pg1 and abs(b0 - b1) < 22.0:
        # two rows of one displayed formula (e.g. a \substack): one box, grown
        # sideways along the glyphs of the rows the markers sit on
        lo, hi = min(b0, b1), max(b0, b1)
        band = [c for c in chars["pages"][pg0 - 1] if c[1] < hi + 4.0 and c[3] > lo - 4.0]
        L, R = min(x0, x1), max(x0, x1)
        grown = True
        while grown:
            grown = False
            for c in band:
                if R - 0.5 < c[0] < R + 3.0 and c[2] > R:
                    R, grown = c[2], True
                if L - 3.0 < c[2] < L + 0.5 and c[0] < L:
                    L, grown = c[0], True
        cs = [c for c in band if L - 0.3 <= (c[0] + c[2]) / 2 <= R + 0.3]
        top = min([c[1] for c in cs] + [lo - 8.0])
        bot = max([c[3] for c in cs] + [hi + 2.5])
        return [[pg0, round(L - 0.8, 2), round(top - 0.8, 2), round(R + 0.8, 2), round(bot + 0.8, 2)]]
    h, dd = (9.0, 3.0)
    rects = []
    if pg0 == pg1:
        rects.append([pg0, x0, b0 - h, TEXT_R, b0 + dd])
        if b1 - h > b0 + dd + 0.5:
            rects.append([pg0, TEXT_L, b0 + dd, TEXT_R, b1 - h])
        rects.append([pg1, TEXT_L, b1 - h, x1, b1 + dd])
    else:
        rects.append([pg0, x0, b0 - h, TEXT_R, b0 + dd])
        rects.append([pg0, TEXT_L, b0 + dd, TEXT_R, TEXT_B])
        for pg in range(pg0 + 1, pg1):
            rects.append([pg, TEXT_L, TEXT_T, TEXT_R, TEXT_B])
        rects.append([pg1, TEXT_L, TEXT_T, TEXT_R, b1 - h])
        rects.append([pg1, TEXT_L, b1 - h, x1, b1 + dd])
    return [[r[0]] + [round(v, 2) for v in r[1:]] for r in rects if r[3] > r[1] and r[4] > r[2]]


def env_rects(pb, pe, ends_display: bool) -> list[list[float]]:
    (pg0, _, b0), (pg1, _, b1) = pb, pe
    top = b0 - 11.5
    bot = b1 + (15.0 if ends_display else 4.5)
    L, R = TEXT_L - 4, TEXT_R + 4
    if pg0 == pg1:
        return [[pg0, L, round(top, 2), R, round(bot, 2)]]
    rects = [[pg0, L, round(top, 2), R, TEXT_B + 2]]
    for pg in range(pg0 + 1, pg1):
        rects.append([pg, L, TEXT_T - 2, R, TEXT_B + 2])
    rects.append([pg1, L, TEXT_T - 2, R, round(bot, 2)])
    return rects


# ---------------------------------------------------------------- paper line citations

# "paper line 262", "lines 980–1001", "lines 1213 and 1216", "lines 351–396, 502–517" (same
# pattern as CITE_RE in app/app.js, which finds the citations in the UI)
CITE_RE = re.compile(r"\b(?:[Pp]aper\s+)?(?:[Ll]ines?|ll?\.)\s+(\d{1,4}(?:\s*[–—-]\s*\d{1,4})?"
                     r"(?:\s*(?:,\s*and|,|and)\s*\d{1,4}(?:\s*[–—-]\s*\d{1,4})?)*)")
CITE_ITEM_RE = re.compile(r"(\d{1,4})(?:\s*[–—-]\s*(\d{1,4}))?")
CITE_QUOTE_RE = re.compile(r"[)\s,:;*]*\(?\s*[\"“]([^\"”]{8,120})")
CITE_SCOPE = INST.cite_scope   # files whose comments cite the paper (main: Shiftsym/Paper/; None: no citations)


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(REPO), *args], capture_output=True, text=True, check=True).stdout


def line_map(old: list[str], new: list[str]) -> tuple[list[int], str]:
    """For each line of `old` (1-based, index 0 unused): its line in `new`, and a status:
    '=' same text, '~' text changed, 'x' no counterpart (the number is then the nearest line)."""
    m, st = [0] * (len(old) + 1), ["?"] * (len(old) + 1)
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if op == "equal":
            for k in range(i2 - i1):
                m[i1 + k + 1], st[i1 + k + 1] = j1 + k + 1, "="
        elif op == "replace":
            for i in range(i1, i2):
                best, bj = max(((difflib.SequenceMatcher(None, old[i], new[j], autojunk=False).ratio(), j)
                                for j in range(j1, j2)), default=(0.0, j1))
                if best >= 0.5:
                    m[i + 1], st[i + 1] = bj + 1, "~"
                else:
                    m[i + 1], st[i + 1] = min(j1 + (i - i1), j2 - 1) + 1, "x"
        elif op == "delete":
            for i in range(i1, i2):
                m[i + 1], st[i + 1] = min(j1 + 1, len(new)), "x"
    return m, "".join(st)


def quote_hits(src: str, tex_lines: list[str]) -> int:
    """Citations directly followed by a quotation whose words are found at the cited lines."""
    words = lambda s: re.sub(r"[^a-z0-9]+", " ", s.lower()).split()
    hits = 0
    for c in CITE_RE.finditer(src):
        q = CITE_QUOTE_RE.match(src, c.end())
        ws = [w for w in words(q.group(1)) if len(w) > 2][:6] if q else []
        if len(ws) < 2:
            continue
        nums = [int(x) for x in re.findall(r"\d+", c.group(1))]
        lo, hi = max(1, min(nums) - 1), min(len(tex_lines), max(nums) + 1)
        near = set(words(" ".join(tex_lines[lo - 1:hi])))
        hits += sum(w in near for w in ws) >= 0.6 * len(ws)
    return hits


def version_label(text: str, fallback: str) -> str:
    m = re.search(r"\\date\{[^}]*\((v\d+(?:\.\d+)?)", text)
    return m.group(1) if m else fallback


def paper_citations(cur_text: str, lean_files) -> tuple[dict, list[str]]:
    """Map the paper versions cited in Lean comments onto the current paper.

    A file's citations refer to the paper just before the commit that added the file (Phase H
    statements: v3.1; group 12: v4; the window-20 supplement: v5). A file not yet committed
    cites the current paper. The version label is read from the paper's \\date line.
    """
    cur_lines = cur_text.split("\n")
    cur = version_label(cur_text, "current")
    if CITE_SCOPE is None:      # no Lean file of this instance cites lines of its paper
        return {"current": cur, "versions": {}, "bases": {}, "text": {}}, []
    added: dict[str, str] = {}   # file (relative to LEAN_ROOT) -> commit that added it (newest add)
    sha = None
    for ln in git("log", "--diff-filter=A", "--format=@%H", "--name-only", "--",
                  str((LEAN_ROOT / CITE_SCOPE).relative_to(REPO))).splitlines():
        if ln.startswith("@"):
            sha = ln[1:]
        elif ln.strip():
            added.setdefault(str((REPO / ln).relative_to(LEAN_ROOT)), sha)
    # pass 1: the cited version of every file, each version mapped once onto the current paper
    versions, lines, file_label, rev_label = {}, {cur: cur_lines}, {}, {}
    for f in sorted(lean_files):
        if not f.startswith(CITE_SCOPE) or f not in added:
            continue
        parents = git("rev-list", "--parents", "-n", "1", added[f]).split()
        # the commit that made that version of the paper
        rev = git("log", "-1", "--format=%H", parents[1] if len(parents) > 1 else parents[0], "--",
                  str(TEX.relative_to(REPO))).strip()
        if rev not in rev_label:
            text = git("show", f"{rev}:{TEX.relative_to(REPO)}")
            lab = version_label(text, rev[:7])
            if lab in versions or lab == cur:
                lab = f"{lab}@{rev[:7]}"
            rev_label[rev], lines[lab] = lab, text.split("\n")
            m, st = line_map(lines[lab], cur_lines)
            versions[lab] = {"rev": rev, "date": git("show", "-s", "--format=%cs", rev).strip(), "map": m, "st": st}
        file_label[f] = rev_label[rev]
    # pass 2: the cited lines (their text for the UI), and a check of each file's version
    bases, texts, warnings = {}, {}, []
    for f, lab in file_label.items():
        src = INST.lean_path(f).read_text()
        cites = [int(n) for c in CITE_RE.finditer(src) for n in re.findall(r"\d+", c.group(1))]
        if not cites:
            continue
        bases[f] = lab
        V = versions[lab]
        for n in cites:
            if not 1 <= n < len(V["map"]):
                warnings.append(f"{f}: paper line {n} does not exist in {lab}")
                continue
            texts.setdefault(lab, {})[str(n)] = lines[lab][n - 1].strip()[:240]
            texts.setdefault(cur, {})[str(V["map"][n])] = cur_lines[V["map"][n] - 1].strip()[:240]
        # the cited version must explain the file's quotations at least as well as any other
        own = quote_hits(src, lines[lab])
        for other, ls in lines.items():
            if other != lab and quote_hits(src, ls) > own:
                warnings.append(f"{f}: its quotations match paper {other} better than {lab}, the version "
                                f"before the commit that added the file")
    return {"current": cur, "versions": versions, "bases": bases, "text": texts}, warnings


# ---------------------------------------------------------------- main

def git_head() -> str:
    try:
        return subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
    except Exception:
        return "?"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="validate anchors only (no TeX run)")
    ap.add_argument("--layout", action="store_true", help="with --check: also compile and verify the layout for the given files")
    ap.add_argument("--verbose", action="store_true", help="also list anchors that are not single info-tree nodes")
    ap.add_argument("--keep-pdf", type=Path, help="copy the instrumented PDF here")
    ap.add_argument("files", nargs="*", type=Path)
    args = ap.parse_args()

    tex = Tex(TEX.read_text())
    aux_cache = DATA / "paper.aux.json"
    aux = json.loads(aux_cache.read_text()) if aux_cache.exists() else {}
    items = find_items(tex, aux)
    lean = LeanIndex()
    files = args.files or sorted(CORR.glob("*.json"))
    corr = load_corr(files)
    maps, errors, warnings = validate(corr, items, tex, lean)
    if args.verbose:
        for nt in NOTES:
            print("note ", nt)
    for w in warnings:
        print("WARN ", w)
    for e in errors:
        print("ERROR", e)
    nmaps = len(maps)
    print(f"{len(corr)} correspondence files, {nmaps} mappings, {len(errors)} errors, {len(warnings)} warnings"
          f" ({len(NOTES)} Lean anchors not exactly one info-tree node; --verbose lists them)")
    if errors:
        sys.exit(1)
    if args.check and not args.layout:
        return

    instr = instrument(tex, items, maps)
    print("compiling instrumented paper (3 pdflatex passes in docker) ...", flush=True)
    pos, aux_new = compile_positions(instr, args.keep_pdf)
    print("layout identical to the official PDF (all words at the same coordinates)")
    if args.check:
        missing = [mp["item"] + ":" + mp["id"] for k, mp in enumerate(maps)
                   for j in range(len(mp["tex"])) if f"M{k}.{j}S" not in pos or f"M{k}.{j}E" not in pos]
        if missing:
            print("ERROR markers not shipped (anchor inside a phantom/discarded box?):", missing)
            sys.exit(1)
        return
    aux_cache.write_text(json.dumps(aux_new, indent=1))
    if aux_new != aux:
        items = find_items(tex, aux_new)
    chars = load_chars()

    out_items = []
    by_item: dict[str, list] = {}
    for k, mp in enumerate(maps):
        for j, ta in enumerate(mp["tex"]):
            s, e = pos.get(f"M{k}.{j}S"), pos.get(f"M{k}.{j}E")
            if not s or not e:
                sys.exit(f"marker of {mp['item']}:{mp['id']} not shipped (anchor inside a phantom/discarded box?)")
            ta["rects"] = fit_rects(s, e, ta["mode"], chars)
        by_item.setdefault(mp["item"], []).append(mp)
    for k, it in enumerate(items):
        pb, pe = pos[f"I{k}B"], pos[f"I{k}E"]
        ends_display = env_end_insertion(tex.text, it) < it["end_tag"] - 1 and \
            bool(re.search(r"(\\\]|\\end\{(equation|align)\*?\})\s*$", tex.text[it["body"]:it["end_tag"]]))
        blk = corr.get(it["label"], {}).get("statement") or {}
        env_tex = tex.text[it["begin"]:it["end"]]
        mlist = by_item.get(it["id"], [])
        decls = []
        for ld in blk.get("lean_decls", []):
            d = lean.decls[ld["decl"]]
            decls.append({"decl": ld["decl"], "role": ld.get("role", ""), "file": d["file"],
                          "sl": d["sl"], "el": d["el"]})
        for mp in mlist:
            for la in mp["lean"]:
                if la.get("decl") and all(x["decl"] != la["decl"] for x in decls):
                    d = lean.decls[la["decl"]]
                    decls.append({"decl": la["decl"], "role": "referenced", "file": d["file"],
                                  "sl": d["sl"], "el": d["el"]})
        lean_src = "\n".join("\n".join(lean.lines(d["file"])[d["sl"] - 1:d["el"]]) for d in decls)
        h = sha256s(json.dumps({"tex": env_tex, "lean": lean_src, "corr": blk}, sort_keys=True))
        out_items.append({
            "id": it["id"], "env": it["env"], "label": it.get("label"),
            "number": it["number"], "title": it["title"], "display": it["display"],
            "tex_lines": [it["line_begin"], it["line_end"]], "tex": env_tex,
            "rects": env_rects(pb, pe, ends_display),
            "has_corr": bool(blk), "summary": blk.get("summary", ""), "deltas": blk.get("deltas", []),
            "lean_decls": decls, "maps": mlist, "hash": h,
        })
    lean_files = sorted({d["file"] for it in out_items for d in it["lean_decls"]} |
                        {la["file"] for it in out_items for mp in it["maps"] for la in mp["lean"]})
    fp = {
        "paper_pdf": {"path": str(PDF.relative_to(REPO)), "sha256": sha256(PDF)},
        "paper_tex": {"path": str(TEX.relative_to(REPO)), "sha256": sha256(TEX)},
        "lean": {f: sha256(INST.lean_path(f)) for f in sorted(lean.files)},
        "corr": {p.name: sha256(p) for p in sorted(CORR.glob("*.json"))},
        "exports": {p.name: sha256(p) for p in sorted(LEAN_EXPORT.glob("*.json")) if not p.name.startswith("_")},
    }
    cites, cite_warnings = paper_citations(
        tex.text, [str(p.relative_to(LEAN_ROOT)) for p in (LEAN_ROOT / CITE_SCOPE).rglob("*.lean")] if CITE_SCOPE else [])
    for w in cite_warnings:
        print("WARN ", w)
    print(f"paper line citations: {len(cites['bases'])} Lean files cite "
          + ", ".join(f"{lab} ({sum(b == lab for b in cites['bases'].values())} files)" for lab in cites["versions"])
          + f"; mapped onto the current paper ({cites['current']})")
    # per-page crop boxes for the "clip margins" view: the text block plus a small
    # pad, widened on any page whose glyphs (e.g. an overfull line) stick out
    content_boxes = []
    for pg in chars["pages"]:
        xs0 = min([c[0] for c in pg] + [TEXT_L]); ys0 = min([c[1] for c in pg] + [TEXT_T])
        xs1 = max([c[2] for c in pg] + [TEXT_R]); ys1 = max([c[3] for c in pg] + [TEXT_B])
        content_boxes.append([round(min(TEXT_L, xs0) - 8, 2), round(min(TEXT_T, ys0) - 8, 2),
                              round(max(TEXT_R, xs1) + 8, 2), round(max(TEXT_B, ys1) + 5, 2)])
    data = {
        "content_boxes": content_boxes,
        "built": subprocess.run(["date", "-Iseconds"], capture_output=True, text=True).stdout.strip(),
        "git_head": git_head(),
        "pdf_url": "/repo/" + str(PDF.relative_to(REPO)),
        "lean_root": str(LEAN_ROOT.relative_to(REPO)),
        "repo_abs": str(REPO),
        "page_size": [PAGE_W, PAGE_H],
        "items": out_items,
        "lean_files": lean_files,
        "lean_exports": {f: v["export"] for f, v in lean.files.items()},
        "paper_cites": cites,
        "fingerprints": fp,
    }
    if not INST.is_default():   # the main paper's bundle keeps its original keys
        data["name"] = INST.name
        data["lean_roots"] = {k: str(v.relative_to(REPO)) for k, v in INST.lean_roots.items()}
    OUT.write_text(json.dumps(data, ensure_ascii=False))
    n_cov = sum(1 for it in out_items if it["has_corr"])
    print(f"wrote {OUT.relative_to(REPO)}: {len(out_items)} items ({n_cov} with correspondences), "
          f"{sum(len(it['maps']) for it in out_items)} mappings")


if __name__ == "__main__":
    main()
