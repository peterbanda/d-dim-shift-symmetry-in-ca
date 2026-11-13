// Paper <-> Lean correspondence audit — UI.
// Data: /data/audit_data.json (tools/build.py) + /data/lean/*.json (tools/ExportInfo.lean).
// Every interaction is logged to the server (logs/events.jsonl).
import * as pdfjsLib from "https://cdnjs.cloudflare.com/ajax/libs/pdf.js/4.4.168/pdf.min.mjs";
pdfjsLib.GlobalWorkerOptions.workerSrc =
  "https://cdnjs.cloudflare.com/ajax/libs/pdf.js/4.4.168/pdf.worker.min.mjs";

const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const h = (tag, attrs = {}, ...kids) => {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") el.className = v;
    else if (k === "style") el.style.cssText = v;
    else if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else if (v !== undefined && v !== null && v !== false) el.setAttribute(k, v);
  }
  for (const c of kids.flat()) if (c !== null && c !== undefined && c !== false)
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  return el;
};
const KIND_LABEL = {
  same: "same", representation: "represent.", hypothesis: "hypothesis", generalization: "general.",
  "paper-only": "paper only", "lean-only": "Lean only", citation: "citation",
  definition: "definition", weaker: "weaker",
};
const kc = (kind) => `var(--k-${kind})`;
// the paper's preamble macros, so $...$ in notes renders like the PDF
const KATEX_MACROS = {
  "\\ZZ": "\\mathbb{Z}", "\\NN": "\\mathbb{N}", "\\FF": "\\mathbb{F}", "\\A": "\\mathcal{A}",
  "\\vv": "\\mathbf{v}", "\\uu": "\\mathbf{u}", "\\ww": "\\mathbf{w}", "\\ssb": "\\mathbf{s}",
  "\\gaussbinom": "\\genfrac{[}{]}{0pt}{}{#1}{#2}", "\\Fix": "\\operatorname{Fix}",
  "\\Stab": "\\operatorname{Stab}", "\\rk": "\\operatorname{rk}", "\\lcm": "\\operatorname{lcm}",
};
function texSpan(src, display) {
  const span = document.createElement("span");
  if (window.katex) {
    try {
      katex.render(src, span, { displayMode: display, throwOnError: false, strict: "ignore", macros: { ...KATEX_MACROS } });
      return span;
    } catch { /* fall through */ }
  }
  span.textContent = display ? `$$${src}$$` : `$${src}$`;
  return span;
}
// `code`, $$tex$$, $tex$, **bold** -> DOM (everything else stays plain text)
const RICH_RE = /(`+)([\s\S]*?)\1|\$\$([\s\S]+?)\$\$|\$(?![\s$])((?:\\.|[^$\\\n])+?)(?<!\s)\$|\*\*([^*\n]+)\*\*/g;
function rich(text) {
  const frag = document.createDocumentFragment();
  if (!text) return frag;
  let last = 0, m;
  RICH_RE.lastIndex = 0;
  while ((m = RICH_RE.exec(text))) {
    if (m.index > last) frag.append(text.slice(last, m.index));
    if (m[1]) frag.append(h("code", { class: "ic" }, m[2]));
    else if (m[3] !== undefined) frag.append(texSpan(m[3], true));
    else if (m[4] !== undefined) frag.append(texSpan(m[4], false));
    else frag.append(h("strong", {}, m[5]));
    last = RICH_RE.lastIndex;
  }
  frag.append(text.slice(last));
  return frag;
}
const lsGet = (k, d) => { try { const v = localStorage.getItem(k); return v === null ? d : JSON.parse(v); } catch { return d; } };
const lsSet = (k, v) => { try { localStorage.setItem(k, JSON.stringify(v)); } catch { /* ignore */ } };

// ------------------------------------------------------------------ state
const S = {
  data: null, items: [], idx: 0, item: null,
  pdf: null, scale: 1, pageEls: [], rendered: new Map(), crop: lsGet("audit.crop", true),
  files: new Map(),           // file -> {src, lines, lineOff, nodes, consts, decls}
  selMap: null, selNode: null, nodeStack: [],
  verdicts: {}, notes: {}, marks: {},
  viewedMaps: new Set(),
  activeMs: {}, wallMs: {}, lastInput: Date.now(), idle: false,
  extraCards: [],            // definitions opened by the auditor for this item
};
const SESSION = new Date().toISOString().replace(/[:.]/g, "-") + "-" + Math.random().toString(36).slice(2, 7);
const IDLE_MS = 120000;

// ------------------------------------------------------------------ logging
const LOGQ = [];
let flushT = null;
function log(type, extra = {}) {
  LOGQ.push({ type, t: new Date().toISOString(), ms: Date.now(), session: SESSION,
    item: S.item ? S.item.id : null, ...extra });
  clearTimeout(flushT);
  flushT = setTimeout(flush, 800);
}
async function flush() {
  if (!LOGQ.length) return;
  const batch = LOGQ.splice(0, LOGQ.length);
  try {
    const r = await fetch("/api/events", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(batch) });
    if (!r.ok) throw new Error(r.status);
  } catch (e) {
    LOGQ.unshift(...batch);
    toast("Could not reach the audit server — events are queued");
  }
}
function flushBeacon() {
  if (!LOGQ.length) return;
  navigator.sendBeacon("/api/events", new Blob([JSON.stringify(LOGQ.splice(0))], { type: "application/json" }));
}
function toast(msg) {
  const t = $("#toast"); t.textContent = msg; t.hidden = false;
  clearTimeout(t._t); t._t = setTimeout(() => (t.hidden = true), 2600);
}

// ------------------------------------------------------------------ time tracking
let lastTick = Date.now();
setInterval(() => {
  const now = Date.now(), dtm = now - lastTick; lastTick = now;
  if (!S.item) return;
  const id = S.item.id;
  const visible = document.visibilityState === "visible";
  const idleNow = now - S.lastInput > IDLE_MS;
  if (idleNow !== S.idle) { S.idle = idleNow; log(idleNow ? "idle_start" : "idle_end", { after_ms: now - S.lastInput }); }
  S.wallMs[id] = (S.wallMs[id] || 0) + dtm;
  if (visible && !idleNow) S.activeMs[id] = (S.activeMs[id] || 0) + dtm;
  renderProgress();
}, 1000);
for (const ev of ["mousemove", "mousedown", "keydown", "wheel", "touchstart"])
  window.addEventListener(ev, () => { S.lastInput = Date.now(); }, { passive: true });
document.addEventListener("visibilitychange", () => {
  log("visibility", { state: document.visibilityState });
  if (document.visibilityState === "hidden") { closeItemLog(); flushBeacon(); }
});
window.addEventListener("pagehide", () => { closeItemLog(); log("session_pause"); flushBeacon(); });
function closeItemLog() {
  if (S.item) log("item_close", { active_ms: S.activeMs[S.item.id] || 0, wall_ms: S.wallMs[S.item.id] || 0 });
}

// ------------------------------------------------------------------ Lean files
const decoder = (s) => Array.from(s);
async function loadLeanFile(file) {
  if (S.files.has(file)) return S.files.get(file);
  const p = (async () => {
    const src = await (await fetch(`/repo/${S.data.lean_root}/${file}`)).text();
    const lines = src.split("\n");
    const lineOff = [0, 0];
    let acc = 0;
    for (const l of lines) { acc += decoder(l).length + 1; lineOff.push(acc); }
    const exp = S.data.lean_exports[file];
    let nodes = [], consts = {};
    if (exp) {
      const j = await (await fetch(`/data/lean/${exp}`)).json();
      const seen = new Map();
      for (const n of j.nodes) {
        const a = lineOff[n.sl] + n.sc, b = lineOff[n.el] + n.ec;
        if (b <= a) continue;
        const key = `${a}:${b}:${n.k}`;
        const prev = seen.get(key);
        if (prev) { if (!prev.c && n.c) Object.assign(prev, n, { a, b }); continue; }
        const node = { ...n, a, b };
        seen.set(key, node); nodes.push(node);
      }
      for (const c of j.consts) consts[c.name] = c;
    }
    nodes.sort((x, y) => x.a - y.a || y.b - x.b);
    // paper line citations, by line: [{col (UTF-16 offset just after the citation), a, b}]
    const cites = new Map();
    if (S.data.paper_cites?.bases?.[file]) {
      let l = 1, start = 0;
      for (const c of findCites(src)) {
        while (l < lines.length && start + lines[l - 1].length < c.end - 1) { start += lines[l - 1].length + 1; l++; }
        if (!cites.has(l)) cites.set(l, []);
        cites.get(l).push({ col: c.end - start, a: c.a, b: c.b });
      }
    }
    return { file, src, lines, lineOff, nodes, consts, cites };
  })();
  S.files.set(file, p);
  return p;
}
const offOf = (F, l, c) => F.lineOff[l] + c;
function nodesAt(F, o) {
  return F.nodes.filter((n) => n.a <= o && o < n.b).sort((x, y) => (x.b - x.a) - (y.b - y.a) || (x.k === "t" ? -1 : 1));
}

// Lean tokenizer (per line, with block-comment state)
const KW = new Set("def theorem lemma private protected noncomputable instance structure class where by fun λ have show from exact intro intros rintro rw rwa erw simp simp_all simpa dsimp omega ring ring_nf linarith nlinarith positivity norm_num refine refine' obtain rcases cases induction calc at with match if then else let open namespace end section variable universe import abbrev example deriving do return suffices using unfold decide exact_mod_cast push_cast field_simp gcongr constructor use exists left right apply specialize congr ext funext subst trivial contradiction exfalso absurd by_contra by_cases push_neg push split_ifs interval_cases fin_cases nth_rewrite conv change set generalize clear revert all_goals any_goals first try repeat iterate case next on_goal focus aesop tauto infer_instance haveI letI".split(" "));
const DECLKW = new Set("def theorem lemma private protected noncomputable instance structure class where abbrev example namespace end section open import variable universe".split(" "));
const TY = new Set("ℕ ℤ ℚ ℝ ℂ Prop Type Sort Nat Int Rat Real Fin ZMod Set Finset".split(" "));
const SYM = new Set("∀ ∃ ∃! ↦ → ← ↔ ∧ ∨ ¬ ∑ ∏ ⋂ ⋃ ∈ ∉ ⊆ ⊂ ≤ ≥ < > ≠ = ∣ ⟨ ⟩ · ∘ ⁻¹ ⊤ ⊥ ⨆ ⨅ ⧸ ≃ ≅ ×".split(" "));
const TOKRE = /(--.*$)|(\/-)|("(?:[^"\\]|\\.)*")|(\d+(?:\.\d+)?)|([\p{L}_'!?\p{N}₀-ₜᵢ-ᵪₖ-ₜ][\p{L}_'!?.\p{N}₀-ₜᵢ-ᵪₖ-ₜ]*)|(\s+)|(.)/uy;
function tokenizeLine(line, state) {
  // returns [{text, cls}] ; state.depth = block comment nesting
  const out = [];
  let i = 0;
  while (i < line.length) {
    if (state.depth > 0) {
      const o = line.indexOf("/-", i), c = line.indexOf("-/", i);
      if (c >= 0 && (o < 0 || c < o)) { out.push({ text: line.slice(i, c + 2), cls: "c-com" }); i = c + 2; state.depth--; continue; }
      if (o >= 0) { out.push({ text: line.slice(i, o + 2), cls: "c-com" }); i = o + 2; state.depth++; continue; }
      out.push({ text: line.slice(i), cls: "c-com" }); break;
    }
    TOKRE.lastIndex = i;
    const m = TOKRE.exec(line);
    if (!m) { out.push({ text: line.slice(i), cls: "" }); break; }
    const t = m[0];
    if (m[1]) out.push({ text: t, cls: "c-com" });
    else if (m[2]) { out.push({ text: t, cls: "c-com" }); state.depth = 1; }
    else if (m[3]) out.push({ text: t, cls: "c-str" });
    else if (m[4]) out.push({ text: t, cls: "c-num" });
    else if (m[5]) out.push({ text: t, cls: DECLKW.has(t) ? "c-kw" : KW.has(t) ? "c-tac" : TY.has(t) ? "c-ty" : "" });
    else if (m[6]) out.push({ text: t, cls: "ws" });
    else out.push({ text: t, cls: SYM.has(t) ? "c-sym" : "" });
    i += t.length;
  }
  return out;
}

// ------------------------------------------------------------------ paper line citations
// Lean comments cite paper lines ("paper line 262", "lines 980–1001") of the paper version their
// file was written against; frozen files are never renumbered. tools/build.py maps each cited
// version onto the current paper (S.data.paper_cites, same CITE_RE), and a badge after the
// citation gives the line in the current paper wherever it differs.
const CITE_RE = /\b(?:[Pp]aper\s+)?(?:[Ll]ines?|ll?\.)\s+(\d{1,4}(?:\s*[–—-]\s*\d{1,4})?(?:\s*(?:,\s*and|,|and)\s*\d{1,4}(?:\s*[–—-]\s*\d{1,4})?)*)/g;
const CITE_ITEM_RE = /(\d{1,4})(?:\s*[–—-]\s*(\d{1,4}))?/g;
function findCites(text) {   // [{end, a, b}]: end = UTF-16 offset just after the cited line a or range a–b
  const out = [];
  for (const m of text.matchAll(CITE_RE)) {
    const at = m.index + m[0].length - m[1].length;
    for (const it of m[1].matchAll(CITE_ITEM_RE)) out.push({ end: at + it.index + it[0].length, a: +it[1], b: it[2] ? +it[2] : null });
  }
  return out;
}
function citeInfo(file, a, b) {   // null if the cited lines are still the same lines with the same text
  const pc = S.data.paper_cites, base = pc?.bases?.[file], V = base && pc.versions[base];
  if (!V) return null;
  const ends = (b ? [a, b] : [a]).map((n) => ({ n, now: V.map[n], st: n > 0 ? V.st[n] : undefined }));
  if (ends.some((e) => e.now === undefined || e.st === undefined)) return null;
  if (ends.every((e) => e.now === e.n && e.st === "=")) return null;
  const cls = ends.some((e) => e.st === "x") ? "gone" : ends.some((e) => e.st === "~") ? "chg" : "mov";
  const say = (e) => e.st === "x" ? `${base} line ${e.n} is no longer in the paper (nearest: line ${e.now})`
    : `${base} line ${e.n} is line ${e.now} of ${pc.current}${e.st === "~" ? ", with changed text" : ""}`;
  const tip = [`Cites paper ${base} (${V.date}), the version this file was written against.`, ...ends.map(say), "",
    ...ends.flatMap((e) => [`${base} ${e.n}: ${pc.text[base]?.[e.n] ?? ""}`, `${pc.current} ${e.now}: ${pc.text[pc.current]?.[e.now] ?? ""}`])];
  return { base, ends, cls, tip: tip.join("\n"), label: "→" + ends.map((e) => e.now).join("–") };
}
function citeBadge(file, a, b) {
  const ci = citeInfo(file, a, b);
  return ci && h("span", { class: `cite ${ci.cls}`, title: ci.tip,
    onclick: (e) => { e.stopPropagation(); inspectCite(file, ci); } }, ci.label);
}
// text with a badge after every citation whose line has moved or changed (cuts: [{at, a, b}], ascending)
function withCites(text, cuts, file, isRich) {
  const render = (s) => (isRich ? rich(s) : s);
  const badges = cuts.map((c) => ({ ...c, el: citeBadge(file, c.a, c.b) })).filter((c) => c.el);
  if (!badges.length) return render(text);
  // never cut inside a `code` or $tex$ span: such a badge goes to the end of the span
  const spans = isRich ? [...text.matchAll(new RegExp(RICH_RE.source, "g"))].map((m) => [m.index, m.index + m[0].length]) : [];
  const frag = document.createDocumentFragment();
  let last = 0;
  for (const c of badges) {
    let at = c.at;
    for (const [s, e] of spans) if (s < at && at < e) at = e;
    at = Math.max(at, last);
    frag.append(render(text.slice(last, at)), c.el);
    last = at;
  }
  frag.append(render(text.slice(last)));
  return frag;
}
// a constant's docstring (inspector), with the citation badges of its file (`here`: the file being
// inspected, which the export names "<this file>")
function docRich(ci, here) {
  const file = ci.module === "<this file>" ? here : ci.module?.startsWith("Shiftsym") ? ci.module.replace(/\./g, "/") + ".lean" : null;
  return file ? withCites(ci.doc, findCites(ci.doc).map((c) => ({ at: c.end, a: c.a, b: c.b })), file, true) : rich(ci.doc);
}
function inspectCite(file, ci) {
  const pc = S.data.paper_cites, V = pc.versions[ci.base];
  const parts = [h("h5", {}, "Paper line citation"),
    h("div", { style: "margin-bottom:8px" }, `${file} cites paper ${ci.base} (${V.date}, ${V.rev.slice(0, 7)}), the version it was written against.`)];
  for (const e of ci.ends) {
    parts.push(h("div", { class: "muted", style: "font-size:12px" }, `${ci.base}, line ${e.n}`),
      h("pre", { class: "texraw" }, pc.text[ci.base]?.[e.n] ?? ""),
      h("div", { class: "muted", style: "font-size:12px" }, `${pc.current} (current), line ${e.now}` +
        (e.st === "~" ? ": text changed" : e.st === "x" ? ": the cited line is gone; this is the nearest line" : "")),
      h("pre", {}, pc.text[pc.current]?.[e.now] ?? ""));
  }
  $("#insp-body").replaceChildren(...parts);
}

// ------------------------------------------------------------------ PDF
async function loadPdf() {
  S.pdf = await pdfjsLib.getDocument(S.data.pdf_url).promise;
  const box = $("#pdf");
  const saved = lsGet("audit.scale", null);
  S.scale = saved && saved >= 0.4 && saved <= 4 ? saved : fitScale();
  for (let p = 1; p <= S.pdf.numPages; p++) {
    const el = h("div", { class: "page", "data-page": p }, h("div", { class: "pin" }, h("canvas"), h("div", { class: "ov" })), h("div", { class: "pno" }, p));
    box.append(el);
    S.pageEls.push(el);
    el.querySelector(".ov").addEventListener("click", (e) => onPdfClick(e, p));
  }
  layoutPages();
  const io = new IntersectionObserver((ents) => {
    for (const e of ents) if (e.isIntersecting) renderPage(+e.target.dataset.page);
  }, { root: box, rootMargin: "600px 0px" });
  S.pageEls.forEach((el) => io.observe(el));
  box.addEventListener("scroll", scheduleArrows, { passive: true });
}
// visible part of page p (PDF points): the whole page, or its text block when cropping
function pageBox(p) {
  const [pw, ph] = S.data.page_size;
  return S.crop && S.data.content_boxes ? S.data.content_boxes[p - 1] : [0, 0, pw, ph];
}
function fitScale() {
  let w = 0;
  for (let p = 1; p <= S.pdf.numPages; p++) { const b = pageBox(p); w = Math.max(w, b[2] - b[0]); }
  return Math.max(0.6, ($("#pdf").clientWidth - 40) / w);
}
function layoutPages() {
  const [pw, ph] = S.data.page_size;
  S.pageEls.forEach((el, i) => {
    const [x0, y0, x1, y1] = pageBox(i + 1);
    el.style.width = `${(x1 - x0) * S.scale}px`; el.style.height = `${(y1 - y0) * S.scale}px`;
    el.querySelector(".pin").style.cssText = `left:${-x0 * S.scale}px;top:${-y0 * S.scale}px;width:${pw * S.scale}px;height:${ph * S.scale}px`;
  });
  $("#crop").classList.toggle("on", S.crop);
  $("#crop").textContent = S.crop ? "Margins: cropped" : "Margins: full";
  $("#zoomlvl").textContent = `${Math.round(S.scale * 100)}%`;
  S.rendered.clear();
  const box = $("#pdf");
  const top = box.scrollTop, bottom = top + box.clientHeight;
  S.pageEls.forEach((el, i) => { if (el.offsetTop < bottom + 600 && el.offsetTop + el.offsetHeight > top - 600) renderPage(i + 1); });
  drawHighlights();
}
async function renderPage(p) {
  const key = S.scale;
  if (S.rendered.get(p) === key) return;
  S.rendered.set(p, key);
  const page = await S.pdf.getPage(p);
  const dpr = window.devicePixelRatio || 1;
  const vp = page.getViewport({ scale: S.scale * dpr });
  const cv = S.pageEls[p - 1].querySelector("canvas");
  const tmp = document.createElement("canvas");
  tmp.width = vp.width; tmp.height = vp.height;
  await page.render({ canvasContext: tmp.getContext("2d"), viewport: vp }).promise;
  if (S.rendered.get(p) !== key) return;
  cv.width = tmp.width; cv.height = tmp.height;
  cv.getContext("2d").drawImage(tmp, 0, 0);
}
function setZoom(f) {
  const box = $("#pdf");
  const rel = box.scrollTop / Math.max(1, box.scrollHeight);
  S.scale = Math.min(4, Math.max(0.4, S.scale * f));
  lsSet("audit.scale", S.scale);
  layoutPages();
  box.scrollTop = rel * box.scrollHeight;
  log("pdf_zoom", { scale: S.scale });
  scheduleArrows();
}
function toggleCrop() {
  const box = $("#pdf");
  const rel = box.scrollTop / Math.max(1, box.scrollHeight);
  const fitted = Math.abs(S.scale - fitScale()) < 0.02;
  S.crop = !S.crop;
  lsSet("audit.crop", S.crop);
  if (fitted) { S.scale = fitScale(); lsSet("audit.scale", S.scale); }
  layoutPages();
  box.scrollTop = rel * box.scrollHeight;
  log("pdf_crop", { crop: S.crop, scale: S.scale });
  scheduleArrows();
}
function rectStyle(r) {
  const [, x0, y0, x1, y1] = r;
  return `left:${x0 * S.scale}px;top:${y0 * S.scale}px;width:${(x1 - x0) * S.scale}px;height:${(y1 - y0) * S.scale}px`;
}
function drawHighlights() {
  for (const el of S.pageEls) el.querySelector(".ov").replaceChildren();
  const it = S.item;
  if (!it) return;
  for (const r of it.rects) S.pageEls[r[0] - 1].querySelector(".ov").append(h("div", { class: "hl-env", style: rectStyle(r) }));
  // larger mapping rects first so smaller ones stay on top
  const all = [];
  for (const m of it.maps) for (const [ti, ta] of m.tex.entries()) for (const r of ta.rects || [])
    all.push({ m, ti, r, area: (r[3] - r[1]) * (r[4] - r[2]) });
  all.sort((a, b) => b.area - a.area);
  for (const { m, ti, r } of all) {
    const sel = S.selMap && S.selMap.id === m.id;
    const el = h("div", { class: "hl-map" + (sel ? " sel" : ""), style: rectStyle(r) + `;--kc:${kc(m.kind)}`,
      "data-map": m.id, "data-ti": ti, title: `${m.label}  [${KIND_LABEL[m.kind] || m.kind}]` });
    S.pageEls[r[0] - 1].querySelector(".ov").append(el);
  }
}
function onPdfClick(e, p) {
  if (!S.item) return;
  const ov = e.currentTarget.getBoundingClientRect();
  const x = (e.clientX - ov.left) / S.scale, y = (e.clientY - ov.top) / S.scale;
  let best = null;
  for (const m of S.item.maps) for (const ta of m.tex) for (const r of ta.rects || []) {
    if (r[0] !== p || x < r[1] || x > r[3] || y < r[2] || y > r[4]) continue;
    const area = (r[3] - r[1]) * (r[4] - r[2]);
    if (!best || area < best.area) best = { m, area };
  }
  if (best) selectMap(best.m, "pdf");
}
function scrollPdfTo(rect) {
  const box = $("#pdf");
  const el = S.pageEls[rect[0] - 1];
  const top0 = pageBox(rect[0])[1];
  const y = el.offsetTop + (rect[2] - top0) * S.scale;
  const yb = el.offsetTop + (rect[4] - top0) * S.scale;
  if (y < box.scrollTop + 20 || yb > box.scrollTop + box.clientHeight - 20)
    box.scrollTo({ top: y - box.clientHeight * 0.3, behavior: "smooth" });
}

// ------------------------------------------------------------------ item view
function itemStatus(id) { return S.verdicts[id]?.value || null; }
function renderSelect() {
  const sel = $("#itemsel");
  sel.replaceChildren(...S.items.map((it, i) => {
    const v = itemStatus(it.id);
    const mark = v === "up" ? "👍" : v === "down" ? "👎" : "·";
    return h("option", { value: i, selected: i === S.idx ? "" : null }, `${mark}  ${it.display}`);
  }));
  sel.value = String(S.idx);
}
function progressCounts() {
  const up = S.items.filter((it) => itemStatus(it.id) === "up").length;
  const down = S.items.filter((it) => itemStatus(it.id) === "down").length;
  return { judged: up + down, up, down };
}
function renderProgress() {
  if (S.progFreeze) return;           // a completion animation owns the counter
  const n = S.items.length;
  const { judged, up, down } = progressCounts();
  const tot = Object.values(S.activeMs).reduce((a, b) => a + b, 0);
  const cur = S.item ? S.activeMs[S.item.id] || 0 : 0;
  const fmt = (ms) => { const s = Math.floor(ms / 1000); return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, "0")}`; };
  $("#progress").innerHTML = `<b class="ctr" data-c="judged">${judged}</b>/${n} judged · 👍 <span class="ctr" data-c="up">${up}</span> · 👎 <span class="ctr" data-c="down">${down}</span> · this item ${fmt(cur)} · session ${fmt(tot)}${S.idle ? " · idle" : ""}`;
}

async function openItem(i, how = "nav") {
  if (S.item) closeItemLog();
  S.idx = (i + S.items.length) % S.items.length;
  S.item = S.items[S.idx];
  S.selMap = null; S.selNode = null; S.nodeStack = []; S.extraCards = [];
  lsSet("audit.idx", S.idx);
  log("item_open", { how, item_hash: S.item.hash });
  renderSelect();
  renderHead();
  drawHighlights();
  if (S.item.rects.length) scrollPdfTo(S.item.rects[0]);
  $("#rightscroll").scrollTop = 0;
  inspectorDefault();
  await renderCards();
  scheduleArrows();
}

function renderHead() {
  const it = S.item;
  const v = S.verdicts[it.id];
  const stale = v && v.value && v.hash && v.hash !== it.hash;
  const vb = (val, label) => h("button", {
    class: `${val}${v?.value === val ? " on" : ""}`, title: val === "up" ? "Correspondence holds (u)" : "Correspondence fails (d)",
    onclick: () => setVerdict(v?.value === val ? null : val),
  }, label);
  const note = h("textarea", { class: "note", placeholder: "Notes on this item (saved to the audit log)…" });
  note.value = S.notes[it.id]?.text || "";
  let nt = null;
  note.addEventListener("input", () => { clearTimeout(nt); nt = setTimeout(() => setNote(note.value), 900); });
  note.addEventListener("blur", () => { clearTimeout(nt); if ((S.notes[it.id]?.text || "") !== note.value) setNote(note.value); });

  const maps = h("div", { class: "maps" }, it.maps.map((m) => {
    const mk = S.marks[`${it.id}::${m.id}`]?.value;
    const mb = (val, label, title) => h("button", { class: `${val}${mk === val ? " on" : ""}`, title,
      onclick: (e) => { e.stopPropagation(); setMark(m, mk === val ? null : val); } }, label);
    return h("div", { class: `maprow${S.selMap?.id === m.id ? " sel" : ""}`, style: `--kc:${kc(m.kind)}`, "data-map": m.id,
      onclick: () => selectMap(m, "list") },
      h("span", { class: "k" }, KIND_LABEL[m.kind] || m.kind),
      h("span", { class: "lbl" + (S.viewedMaps.has(`${it.id}::${m.id}`) ? " viewed" : ""), title: m.note }, rich(m.label)),
      h("span", { class: "mk" }, mb("up", "✓", "This mapping is right"), mb("down", "✗", "This mapping is wrong")));
  }));

  $("#itemhead").replaceChildren(...[
    h("div", { class: "ih-top" },
      h("span", { class: "ih-title" }, it.display),
      h("span", { class: "ih-ref" }, `${S.data.fingerprints.paper_tex.path}:${it.tex_lines[0]}–${it.tex_lines[1]}`),
      h("span", { class: "ih-ref" }, `PDF p. ${it.rects[0]?.[0] ?? "?"}`)),
    h("div", { class: "verdict" },
      vb("up", "👍 holds"), vb("down", "👎 fails"),
      h("span", { class: "vtime" }, v?.value ? `set ${new Date(v.t).toLocaleString()}${v.auto ? (v.value === "up" ? " (all mappings ✓)" : " (all mappings judged, some ✗)") : ""}` : "not judged yet"),
      stale ? h("span", { class: "badge route-different", title: "The item's TeX, Lean or mapping changed since this verdict" }, "stale") : null),
    note,
    it.has_corr ? h("div", { class: "summary" }, rich(it.summary)) : h("div", { class: "summary muted" }, "No correspondence data for this item yet."),
    it.deltas.length ? h("div", {}, h("h4", {}, "Deltas (representation choices)"), h("ul", { class: "deltas" }, it.deltas.map((d) => h("li", {}, rich(d))))) : null,
    it.maps.length ? h("div", {}, h("h4", {}, `Mappings (${it.maps.length}) — click to link, ✓/✗ to mark`), maps) : null,
    h("div", { id: "uses" }),
    h("details", { class: "texsrc" }, h("summary", {}, "TeX source of this item"), h("pre", {}, it.tex)),
  ].filter(Boolean));
}

async function renderCards() {
  const it = S.item;
  const box = $("#cards");
  box.replaceChildren();
  const files = await Promise.all(it.lean_decls.map((d) => loadLeanFile(d.file)));
  if (S.item !== it) return;
  it.lean_decls.forEach((d, k) => box.append(cardFor(d, files[k])));
  for (const d of S.extraCards) box.append(cardFor(d, await loadLeanFile(d.file), true));
  markMapTokens();
  renderUses(files);
  applySelection();
}
function cardFor(d, F, removable = false) {
  const lines = [];
  const state = { depth: 0 };
  for (let l = 1; l < d.sl; l++) tokenizeLine(F.lines[l - 1], state);   // carry comment state
  for (let l = d.sl; l <= d.el; l++) {
    const toks = tokenizeLine(F.lines[l - 1] ?? "", state);
    const lc = F.cites?.get(l) || [];
    let o = F.lineOff[l], c16 = 0;
    const tx = h("span", { class: "tx" });
    for (const t of toks) {
      const n = decoder(t.text).length;
      const isRich = t.cls === "c-com" && /[`$]/.test(t.text);
      const cuts = t.cls === "c-com" ? lc.filter((c) => c.col > c16 && c.col <= c16 + t.text.length) : [];
      if (t.cls === "ws") tx.append(t.text);
      else if (cuts.length) tx.append(h("span", { class: `tk ${t.cls}`, "data-o": o, "data-n": n },
        withCites(t.text, cuts.map((c) => ({ at: c.col - c16, a: c.a, b: c.b })), d.file, isRich)));
      else if (isRich) tx.append(h("span", { class: `tk ${t.cls}`, "data-o": o, "data-n": n }, rich(t.text)));
      else tx.append(h("span", { class: `tk ${t.cls}`, "data-o": o, "data-n": n }, t.text));
      o += n; c16 += t.text.length;
    }
    lines.push(h("div", { class: "ln", "data-line": l }, h("span", { class: "no" }, l), tx));
  }
  const pre = h("pre", { class: "code" }, lines);
  pre.addEventListener("click", (e) => {
    const tk = e.target.closest(".tk");
    if (tk) onLeanClick(F, +tk.dataset.o, d);
  });
  const abs = S.data.repo_abs ? `${S.data.repo_abs}/${S.data.lean_root}/${d.file}` : null;
  return h("div", { class: "card", "data-file": d.file, "data-decl": d.decl },
    h("div", { class: "card-h" },
      h("span", { class: "role" }, d.role || ""),
      h("span", { class: "dname" }, d.decl),
      h("span", { class: "floc" }, abs ? h("a", { href: `vscode://file/${abs}:${d.sl}`, title: "Open in VS Code" }, `${d.file}:${d.sl}–${d.el}`) : `${d.file}:${d.sl}–${d.el}`),
      removable ? h("button", { class: "x", title: "Close", onclick: () => { S.extraCards = S.extraCards.filter((x) => x !== d); renderCards(); } }, "×") : null),
    pre);
}
function cardTokens(file) {
  return $$(`.card[data-file="${CSS.escape(file)}"] .tk`);
}
function markMapTokens() {
  S.item.maps.forEach((m, k) => { for (const la of m.lean) {
    const F = S.files.get(la.file);
    if (!F) continue;
    F.then((F) => {
      const a = offOf(F, la.sl, la.sc), b = offOf(F, la.el, la.ec);
      let last = null;
      for (const tk of cardTokens(la.file)) {
        const o = +tk.dataset.o;
        if (o >= a && o < b) { tk.classList.add("inmap"); last = tk; }
      }
      if (last) placeMapBadge(last.closest(".ln"), m, k);
    });
  } });
}
// in-situ ✓/✗ state of a mapping, at the end of the Lean line where its anchor ends
function mapBadgeState(m) {
  const v = S.marks[`${S.item.id}::${m.id}`]?.value;
  return v === "up" ? ["up", "✅", "approved"] : v === "down" ? ["down", "❌", "rejected"] : ["none", "○", "not marked yet"];
}
function placeMapBadge(ln, m, k) {
  let box = ln.querySelector(".mbs");
  if (!box) ln.append(box = h("span", { class: "mbs" }));
  if (box.querySelector(`.mb[data-map="${CSS.escape(m.id)}"]`)) return;
  const [cls, sym, what] = mapBadgeState(m);
  const b = h("span", { class: `mb ${cls}${S.selMap?.id === m.id ? " sel" : ""}`, "data-map": m.id, "data-k": k,
    title: `${m.label}: ${what}`, onclick: (e) => { e.stopPropagation(); selectMap(m, "badge"); } }, sym);
  const after = [...box.children].find((x) => +x.dataset.k > k);
  box.insertBefore(b, after || null);
}
function renderUses(files) {
  // Shiftsym constants referenced inside the statement declarations
  const it = S.item;
  const seen = new Map();
  it.lean_decls.forEach((d, k) => {
    const F = files[k];
    const a = F.lineOff[d.sl], b = F.lineOff[d.el + 1];
    for (const n of F.nodes) if (n.c && n.a >= a && n.b <= b && n.c !== d.decl) {
      const ci = F.consts[n.c];
      if (ci && ci.module && ci.module.startsWith("Shiftsym") && !seen.has(n.c)) seen.set(n.c, { ci, F });
    }
  });
  const box = $("#uses");
  if (!box || !seen.size) return;
  box.replaceChildren(h("h4", {}, "Project definitions used (click to open)"),
    h("div", { class: "uses" }, [...seen.values()].sort((x, y) => x.ci.name.localeCompare(y.ci.name)).map(({ ci }) =>
      h("span", { class: "chip", title: ci.type, onclick: () => openDefinition(ci) }, ci.name.replace(/^ShiftSym\./, "")))));
}

// ------------------------------------------------------------------ selection
async function selectMap(m, source) {
  S.selMap = m;
  S.viewedMaps.add(`${S.item.id}::${m.id}`);
  log("mapping_select", { mapping: m.id, source, kind: m.kind });
  $$(".maprow").forEach((r) => r.classList.toggle("sel", r.dataset.map === m.id));
  $$(".maprow .lbl").forEach((l) => { if (S.viewedMaps.has(`${S.item.id}::${l.parentElement.dataset.map}`)) l.classList.add("viewed"); });
  $$(".hl-map").forEach((el) => el.classList.toggle("sel", el.dataset.map === m.id));
  const r0 = m.tex[0]?.rects?.[0];
  if (r0 && source !== "pdf") scrollPdfTo(r0);
  inspectMap(m);
  await applySelection();
  if (m.lean[0] && source !== "lean") {
    const tk = $(".tk.msel");
    if (tk) tk.scrollIntoView({ block: "center", behavior: "smooth" });
  }
  scheduleArrows();
}
function clearSelection() {
  S.selMap = null; S.selNode = null; S.nodeStack = [];
  $$(".maprow.sel").forEach((r) => r.classList.remove("sel"));
  $$(".hl-map.sel").forEach((r) => r.classList.remove("sel"));
  applySelection();
  inspectorDefault();
  scheduleArrows();
}
async function applySelection() {
  $$(".mb").forEach((b) => b.classList.toggle("sel", b.dataset.map === S.selMap?.id));
  $$(".tk.msel").forEach((t) => t.classList.remove("msel"));
  $$(".tk.nsel").forEach((t) => t.classList.remove("nsel"));
  if (S.selMap) {
    for (const la of S.selMap.lean) {
      const F = await loadLeanFile(la.file);
      const a = offOf(F, la.sl, la.sc), b = offOf(F, la.el, la.ec);
      for (const tk of cardTokens(la.file)) {
        const o = +tk.dataset.o, e = o + +tk.dataset.n;
        if (o < b && e > a) { tk.classList.add("msel"); tk.style.setProperty("--kc", kc(S.selMap.kind)); }
      }
    }
  }
  if (S.selNode) {
    const { file, node } = S.selNode;
    for (const tk of cardTokens(file)) {
      const o = +tk.dataset.o, e = o + +tk.dataset.n;
      if (o < node.b && e > node.a) tk.classList.add("nsel");
    }
  }
  scheduleArrows();
}
function onLeanClick(F, o, d) {
  // 1. mapping: innermost mapping span containing the click
  let best = null;
  for (const m of S.item.maps) for (const la of m.lean) {
    if (la.file !== F.file) continue;
    const a = offOf(F, la.sl, la.sc), b = offOf(F, la.el, la.ec);
    if (a <= o && o < b && (!best || b - a < best.len)) best = { m, len: b - a };
  }
  // 2. info-tree node: innermost, or widen on repeated clicks
  const stack = nodesAt(F, o);
  let node = stack[0] || null;
  if (S.selNode && S.selNode.file === F.file && stack.length) {
    const cur = stack.findIndex((n) => n === S.selNode.node);
    if (cur >= 0) node = stack[Math.min(cur + 1, stack.length - 1)];
  }
  S.nodeStack = stack;
  S.selNode = node ? { file: F.file, node, decl: d.decl } : null;
  if (best && (!S.selMap || S.selMap.id !== best.m.id)) {
    S.selMap = best.m;
    S.viewedMaps.add(`${S.item.id}::${best.m.id}`);
    log("mapping_select", { mapping: best.m.id, source: "lean", kind: best.m.kind });
    $$(".maprow").forEach((r) => r.classList.toggle("sel", r.dataset.map === best.m.id));
    $$(".hl-map").forEach((el) => el.classList.toggle("sel", el.dataset.map === best.m.id));
    const r0 = best.m.tex[0]?.rects?.[0];
    if (r0) scrollPdfTo(r0);
  } else if (!best && S.selMap) {
    S.selMap = null;
    $$(".maprow.sel").forEach((r) => r.classList.remove("sel"));
    $$(".hl-map.sel").forEach((r) => r.classList.remove("sel"));
  }
  if (node) log("node_inspect", { file: F.file, decl: d.decl, kind: node.k, range: [node.sl, node.sc, node.el, node.ec], const: node.c || null, mapping: best?.m.id || null });
  applySelection();
  inspectNode(F, node, best?.m);
}

// ------------------------------------------------------------------ inspector
function inspectorDefault() {
  $("#insp-body").replaceChildren(h("div", { class: "muted" },
    "Click a highlighted region in the PDF, a mapping, or any Lean token to inspect it. Click the same token again to widen the selection to its enclosing expression. Constants can be opened as definition cards."));
}
// light clean-up of text-mode LaTeX so it reads like the PDF (math is left to KaTeX)
function cleanTex(t) {
  return t.replace(/\\label\{[^}]*\}/g, "")
    .replace(/\\(emph|textbf|textit|text)\{([^{}]*)\}/g, "$2")
    .replace(/\\(eq)?ref\{([^}]*)\}/g, "[$2]").replace(/\\cite(\[[^\]]*\])?\{([^}]*)\}/g, "[$2]")
    .replace(/``/g, "“").replace(/''/g, "”").replace(/~/g, " ").replace(/\\(i\.e|e\.g)\\ /g, "$1. ")
    .replace(/\s+/g, " ").trim();
}
function texRendered(ta) {
  const src = ta.text.replace(/\\label\{[^}]*\}/g, "");
  if (ta.mode === "display") return texSpan(src, true);
  if (ta.mode === "inline" && !src.includes("$")) return texSpan(src, false);
  return rich(cleanTex(src));
}
function texBlock(m) {
  if (!m.tex.length) return h("div", { class: "muted" }, "No TeX anchor: the paper has no counterpart (see note).");
  return m.tex.map((ta) => h("div", {},
    h("div", { class: "muted", style: "font-size:12px" }, `${S.data.fingerprints.paper_tex.path}:${ta.line}${ta.line_end !== ta.line ? "–" + ta.line_end : ""} (${ta.mode})`),
    h("div", { class: "texrender" }, texRendered(ta)),
    h("pre", { class: "texraw" }, ta.text)));
}
async function inspectMap(m) {
  const parts = [
    h("h5", {}, `Mapping · ${KIND_LABEL[m.kind] || m.kind}`),
    h("div", { style: "font-weight:600;margin-bottom:4px" }, rich(m.label)),
    m.note ? h("div", { style: "margin-bottom:8px" }, rich(m.note)) : null,
    h("h5", {}, "Paper (TeX source)"), ...[texBlock(m)].flat(),
    h("h5", {}, "Lean"),
  ];
  if (!m.lean.length) parts.push(h("div", { class: "muted" }, "No Lean anchor: nothing in the formalization corresponds (see note)."));
  for (const la of m.lean) {
    const F = await loadLeanFile(la.file);
    const a = offOf(F, la.sl, la.sc), b = offOf(F, la.el, la.ec);
    const exact = F.nodes.find((n) => n.a === a && n.b === b && n.k === "t");
    const txt = decoder(F.src).slice(a, b).join("");
    parts.push(h("div", { class: "muted", style: "font-size:12px" }, `${la.file}:${la.sl}:${la.sc}–${la.el}:${la.ec}${la.decl ? "  in " + la.decl : ""}`));
    parts.push(h("pre", {}, txt));
    if (exact) parts.push(h("div", { class: "kv" }, h("span", { class: "k" }, "elaborates to"), h("code", {}, exact.ex), h("span", { class: "k" }, "type"), h("code", {}, exact.ty)));
  }
  $("#insp-body").replaceChildren(...parts.filter(Boolean));
}
function inspectNode(F, node, m) {
  const parts = [];
  if (m) parts.push(h("div", { class: "muted", style: "font-size:12px;margin-bottom:6px" }, "In mapping “", rich(m.label), `” (${KIND_LABEL[m.kind] || m.kind}) — `, h("a", { href: "#", onclick: (e) => { e.preventDefault(); inspectMap(m); } }, "show mapping")));
  if (!node) { parts.push(h("div", { class: "muted" }, "No info-tree node here (keyword, binder punctuation, or comment).")); $("#insp-body").replaceChildren(...parts); return; }
  const crumbs = h("div", { class: "crumbs" }, S.nodeStack.slice(0, 12).map((n) =>
    h("span", { class: "chip" + (n === node ? " cur" : ""), title: n.ex, onclick: () => { S.selNode = { ...S.selNode, node: n }; applySelection(); inspectNode(F, n, m); } },
      n.k === "tac" ? `tactic ${n.sk.split(".").pop()}` : (n.c ? n.c.split(".").pop() : `${n.sk.split(".").pop()}`))));
  const src = decoder(F.src).slice(node.a, node.b).join("");
  parts.push(h("h5", {}, `${node.k === "tac" ? "Tactic" : "Term"} · ${F.file}:${node.sl}:${node.sc}–${node.el}:${node.ec}`));
  parts.push(h("div", { class: "muted", style: "font-size:12px" }, "Enclosing expressions (innermost first):"), crumbs);
  parts.push(h("pre", {}, src.length > 1200 ? src.slice(0, 1200) + " …" : src));
  if (node.k === "t") {
    parts.push(h("div", { class: "kv" }, h("span", { class: "k" }, "type"), h("code", {}, node.ty), h("span", { class: "k" }, "elaborated"), h("code", {}, node.ex)));
    if (node.c) {
      const ci = F.consts[node.c];
      if (ci) {
        parts.push(h("h5", { style: "margin-top:10px" }, `Constant ${ci.name}`));
        parts.push(h("pre", {}, ci.type));
        if (ci.doc) parts.push(h("div", { style: "white-space:pre-wrap;font-size:13px;margin-bottom:6px" }, docRich(ci, F.file)));
        const where = ci.range ? `${ci.module}:${ci.range.sl}` : ci.module;
        parts.push(h("div", { class: "muted", style: "font-size:12px" }, `defined in ${where}`, " ",
          ci.module && ci.module.startsWith("Shiftsym") && ci.range ? h("button", { onclick: () => openDefinition(ci) }, "Open definition") : null));
      }
    }
  } else {
    parts.push(h("h5", {}, "Goals before"), h("pre", {}, node.gb), h("h5", {}, "Goals after"), h("pre", {}, node.ga));
  }
  $("#insp-body").replaceChildren(...parts);
}
async function openDefinition(ci) {
  const file = ci.module.replace(/\./g, "/") + ".lean";
  if (ci.module === "<this file>") return;
  log("goto_def", { const: ci.name, file, line: ci.range?.sl });
  const d = { decl: ci.name, role: "opened definition", file, sl: ci.range.sl, el: ci.range.el };
  const exists = $$(".card").find((c) => c.dataset.decl === ci.name);
  if (exists) { exists.scrollIntoView({ block: "start", behavior: "smooth" }); return; }
  S.extraCards.push(d);
  await renderCards();
  const card = $$(".card").find((c) => c.dataset.decl === ci.name);
  if (card) card.scrollIntoView({ block: "start", behavior: "smooth" });
}

// ------------------------------------------------------------------ verdicts
function setVerdict(value, auto = false) {
  const it = S.item;
  const prev = S.verdicts[it.id]?.value || null;
  const t = new Date().toISOString();
  S.verdicts[it.id] = { value, t, hash: it.hash, auto };
  log("verdict", { value, previous: prev, auto, item_hash: it.hash, active_ms: S.activeMs[it.id] || 0,
    mappings_viewed: it.maps.filter((m) => S.viewedMaps.has(`${it.id}::${m.id}`)).length, mappings_total: it.maps.length });
  flush();
  renderHead(); renderSelect(); renderProgress();
  renderCards();
}
function setNote(text) {
  const it = S.item;
  S.notes[it.id] = { text, t: new Date().toISOString() };
  log("note", { text });
}
function setMark(m, value) {
  const it = S.item;
  S.marks[`${it.id}::${m.id}`] = { value, t: new Date().toISOString() };
  log("mapping_mark", { mapping: m.id, value });
  // every mapping judged => the item holds (all ✓) or fails (any ✗). The automatic
  // verdict is withdrawn once a mark is taken back; a manual verdict is never overridden.
  const ms = it.maps.map((x) => S.marks[`${it.id}::${x.id}`]?.value);
  const target = ms.length && ms.every(Boolean) ? (ms.includes("down") ? "down" : "up") : null;
  const v = S.verdicts[it.id];
  if (target && v?.value !== target) {
    if (v?.value && !v.auto) toast(`All mappings judged; your manual ${v.value === "up" ? "👍" : "👎"} is kept`);
    else return completeItem(target);
  }
  if (!target && v?.value && v.auto) return setVerdict(null, true);
  renderHead();
  renderCards();
}
function nextUnjudgedMap() {
  const ms = S.item.maps, cur = S.selMap ? ms.findIndex((m) => m.id === S.selMap.id) : -1;
  for (let k = 1; k <= ms.length; k++) {
    const m = ms[(cur + k) % ms.length];
    if (!S.marks[`${S.item.id}::${m.id}`]?.value) return selectMap(m, "key-unjudged");
  }
  toast("Every mapping of this item is judged");
}

// ------------------------------------------------------------------ completion animation
const REDUCED_MOTION = matchMedia("(prefers-reduced-motion: reduce)").matches;
async function completeItem(value) {
  const before = progressCounts();
  S.progFreeze = true;                // keep showing the old counts until the burst is over
  setVerdict(value, true);
  try {
    if (!REDUCED_MOTION) await (value === "up" ? celebrate() : commiserate());
    const after = progressCounts();
    await Promise.all(["judged", "up", "down"].filter((c) => after[c] !== before[c])
      .map((c) => rollCounter(c, after[c], getComputedStyle(document.documentElement).getPropertyValue(value === "up" ? "--up" : "--down").trim())));
  } finally {
    S.progFreeze = false;
    renderProgress();
  }
}
function fxLayer() {
  return $("#fx") || document.body.appendChild(h("div", { id: "fx" }));
}
function fxOrigin() {
  // the badge of the mapping just marked, if on screen; else the middle of the right panel
  const vis = (r) => r.width && r.top >= 0 && r.bottom <= innerHeight && r.left >= 0 && r.right <= innerWidth;
  const sel = $$(".mb.sel").map((e) => e.getBoundingClientRect()).find(vis);
  const r = sel || $("#right").getBoundingClientRect();
  return [r.left + r.width / 2, sel ? r.top + r.height / 2 : r.top + r.height * 0.45];
}
// a ballistic path in keyframes: launched at (vx, vy) px/s, gravity g px/s²
function flight(el, x0, y0, vx, vy, g, ms, spin) {
  const frames = [];
  for (let i = 0; i <= 8; i++) {
    const t = (i / 8) * ms / 1000;
    frames.push({ transform: `translate(${x0 + vx * t}px, ${y0 + vy * t + g * t * t / 2}px) rotate(${spin * t}deg)`,
      opacity: i < 6 ? 1 : 1 - (i - 5) / 3 });
  }
  return el.animate(frames, { duration: ms, easing: "linear", fill: "forwards" }).finished;
}
async function celebrate() {
  const fx = fxLayer(), [x, y] = fxOrigin();
  const colors = ["var(--up)", "var(--accent)", "#e6b800", "var(--k-hypothesis)", "var(--k-generalization)", "#ff7a59"];
  const runs = [];
  for (let i = 0; i < 90; i++) {
    const glyph = i % 9 === 0;
    const el = fx.appendChild(glyph ? h("span", { class: "fx-glyph" }, "✅")
      : h("span", { class: "fx-bit", style: `background:${colors[i % colors.length]}` }));
    const a = (-90 + (Math.random() - 0.5) * 140) * Math.PI / 180, v = 450 + Math.random() * 650;
    runs.push(flight(el, x, y, Math.cos(a) * v, Math.sin(a) * v, 1500, 1300 + Math.random() * 500, (Math.random() - 0.5) * 900));
  }
  const btn = $(".verdict button.on");
  if (btn) btn.animate([{ transform: "scale(1)" }, { transform: "scale(1.35)" }, { transform: "scale(1)" }], { duration: 500, easing: "ease-out" });
  await Promise.all(runs);
  fx.replaceChildren();
}
async function commiserate() {
  const fx = fxLayer(), [x, y] = fxOrigin();
  const runs = [$("#itemhead").animate(
    [0, -9, 8, -6, 5, -3, 0].map((dx) => ({ transform: `translateX(${dx}px)` })), { duration: 520, easing: "ease-in-out" }).finished];
  for (let i = 0; i < 16; i++) {
    const el = fx.appendChild(h("span", { class: "fx-glyph" }, "❌"));
    const a = (-90 + (Math.random() - 0.5) * 100) * Math.PI / 180, v = 160 + Math.random() * 220;
    runs.push(flight(el, x, y, Math.cos(a) * v, Math.sin(a) * v, 900, 1300 + Math.random() * 400, (Math.random() - 0.5) * 240));
  }
  await Promise.all(runs);
  fx.replaceChildren();
}
// odometer: the old number slides up and out, the new one slides in from below, then a pop
async function rollCounter(c, to, color) {
  const el = $(`#progress .ctr[data-c="${c}"]`);
  if (!el) return;
  if (!REDUCED_MOTION) await el.animate([{ transform: "translateY(0)", opacity: 1 }, { transform: "translateY(-0.9em)", opacity: 0 }],
    { duration: 220, easing: "ease-in" }).finished;
  el.textContent = to;
  if (REDUCED_MOTION) return;
  await el.animate([{ transform: "translateY(0.9em)", opacity: 0 }, { transform: "translateY(0)", opacity: 1 }],
    { duration: 260, easing: "ease-out" }).finished;
  const base = getComputedStyle(el).color;
  await el.animate([{ transform: "scale(1)", color: base }, { transform: "scale(1.6)", color }, { transform: "scale(1)", color: base }],
    { duration: 650, easing: "ease-out" }).finished;
}

// ------------------------------------------------------------------ arrows
let arrowRaf = 0;
function scheduleArrows() { cancelAnimationFrame(arrowRaf); arrowRaf = requestAnimationFrame(drawArrows); }
function visibleIn(r, box) { return r.bottom > box.top && r.top < box.bottom && r.right > box.left && r.left < box.right; }
function clampY(y, box) { return Math.min(box.bottom - 6, Math.max(box.top + 6, y)); }
function arrow(g, from, to, color, dashed) {
  const sx = from.x, sy = from.y, tx = to.x, ty = to.y;
  const dx = Math.max(40, (tx - sx) * 0.45);
  const p = document.createElementNS("http://www.w3.org/2000/svg", "path");
  p.setAttribute("d", `M${sx},${sy} C${sx + dx},${sy} ${tx - dx},${ty} ${tx},${ty}`);
  p.setAttribute("stroke", color);
  p.setAttribute("marker-end", "url(#ah)");
  if (dashed) p.classList.add("dash");
  const c = document.createElementNS("http://www.w3.org/2000/svg", "circle");
  c.setAttribute("cx", sx); c.setAttribute("cy", sy); c.setAttribute("r", 3.5); c.setAttribute("fill", color);
  g.append(p, c);
}
function drawArrows() {
  const g = $("#arrowg");
  g.replaceChildren();
  if (!S.item) return;
  const L = $("#pdf").getBoundingClientRect(), R = $("#rightscroll").getBoundingClientRect();
  const css = getComputedStyle(document.documentElement);
  if (S.selMap) {
    const color = css.getPropertyValue(`--k-${S.selMap.kind}`).trim() || "#c46a00";
    const src = $$(`.hl-map[data-map="${CSS.escape(S.selMap.id)}"]`).map((e) => e.getBoundingClientRect());
    const dst = $$(".tk.msel").map((e) => e.getBoundingClientRect());
    const sv = src.find((r) => visibleIn(r, L)) || src[0];
    const dv = dst.find((r) => visibleIn(r, R)) || dst[0];
    if (sv && dv) {
      const sOk = visibleIn(sv, L), dOk = visibleIn(dv, R);
      arrow(g, { x: Math.min(sv.right + 2, L.right - 2), y: clampY(sv.top + sv.height / 2, L) },
        { x: Math.max(dv.left - 4, R.left + 2), y: clampY(dv.top + dv.height / 2, R) }, color, !(sOk && dOk));
    } else if (sv) {
      const row = $(`.maprow[data-map="${CSS.escape(S.selMap.id)}"]`);
      if (row) {
        const rr = row.getBoundingClientRect();
        arrow(g, { x: Math.min(sv.right + 2, L.right - 2), y: clampY(sv.top + sv.height / 2, L) },
          { x: rr.left - 4, y: clampY(rr.top + rr.height / 2, R) }, color, true);
      }
    }
    return;
  }
  const envs = $$(".hl-env").map((e) => e.getBoundingClientRect());
  const ev = envs.find((r) => visibleIn(r, L)) || envs[0];
  const head = $("#itemhead").getBoundingClientRect();
  if (ev) {
    const col = css.getPropertyValue("--env-edge").trim();
    const vis = visibleIn(ev, L);
    const sy = vis ? clampY(Math.max(ev.top, L.top) + Math.min(28, ev.height / 2), L) : clampY(ev.top, L);
    arrow(g, { x: Math.min(ev.right + 2, L.right - 2), y: sy },
      { x: head.left - 4, y: clampY(head.top + 22, R) }, col, !vis || !visibleIn(head, R));
  }
}
window.addEventListener("resize", () => { scheduleArrows(); });

// ------------------------------------------------------------------ chrome
function initChrome() {
  $("#prev").onclick = () => openItem(S.idx - 1);
  $("#next").onclick = () => openItem(S.idx + 1);
  $("#itemsel").onchange = (e) => openItem(+e.target.value, "select");
  $("#zoomin").onclick = () => setZoom(1.15);
  $("#zoomout").onclick = () => setZoom(1 / 1.15);
  $("#zoomlvl").title = "Fit page width";
  $("#zoomlvl").onclick = () => setZoom(fitScale() / S.scale);
  $("#crop").onclick = toggleCrop;
  $("#rightscroll").addEventListener("scroll", scheduleArrows, { passive: true });
  $("#helpbtn").onclick = showHelp;
  $("#finish").onclick = finishAudit;
  $("#modal-close").onclick = () => ($("#modal").hidden = true);
  // pane divider
  const div = $("#divider");
  div.addEventListener("mousedown", (e) => {
    e.preventDefault();
    const move = (ev) => { const w = Math.min(window.innerWidth - 340, Math.max(260, ev.clientX)); $("#left").style.width = `${w}px`; scheduleArrows(); };
    const up = () => { window.removeEventListener("mousemove", move); window.removeEventListener("mouseup", up); lsSet("audit.leftw", $("#left").style.width); };
    window.addEventListener("mousemove", move); window.addEventListener("mouseup", up);
  });
  const lw = lsGet("audit.leftw", null); if (lw) $("#left").style.width = lw;
  const grip = $("#insp-grip");
  grip.addEventListener("mousedown", (e) => {
    e.preventDefault();
    const rr = $("#right").getBoundingClientRect();
    const move = (ev) => { const hgt = Math.min(rr.height - 120, Math.max(80, rr.bottom - ev.clientY)); $("#inspector").style.height = `${hgt}px`; scheduleArrows(); };
    const up = () => { window.removeEventListener("mousemove", move); window.removeEventListener("mouseup", up); };
    window.addEventListener("mousemove", move); window.addEventListener("mouseup", up);
  });
  document.addEventListener("keydown", (e) => {
    if (e.target.matches("textarea, input, select")) return;
    if (e.metaKey || e.ctrlKey || e.altKey) return;
    const k = e.key;
    if (k === "j" || k === "ArrowRight") openItem(S.idx + 1);
    else if (k === "k" || k === "ArrowLeft") openItem(S.idx - 1);
    else if ((k === "u" || k === "d") && S.selMap) {
      const val = k === "u" ? "up" : "down";
      setMark(S.selMap, S.marks[`${S.item.id}::${S.selMap.id}`]?.value === val ? null : val);
    }
    else if (k === "u") setVerdict(S.verdicts[S.item.id]?.value === "up" ? null : "up");
    else if (k === "d") setVerdict(S.verdicts[S.item.id]?.value === "down" ? null : "down");
    else if (k === "N") nextUnjudgedMap();
    else if (k === "n" || k === "p") {
      const ms = S.item.maps; if (!ms.length) return;
      const cur = S.selMap ? ms.findIndex((m) => m.id === S.selMap.id) : -1;
      selectMap(ms[(cur + (k === "n" ? 1 : -1) + ms.length) % ms.length], "key");
    } else if (k === "Escape") clearSelection();
    else if (k === "+" || k === "=") setZoom(1.15);
    else if (k === "-") setZoom(1 / 1.15);
    else if (k === "?") showHelp();
    else if (k === "m") toggleCrop();
    else return;
    e.preventDefault();
  });
}
function showHelp() {
  const rows = [["j / →", "next item"], ["k / ←", "previous item"], ["n / p", "next / previous mapping"], ["N", "next mapping not yet judged"],
    ["u", "mapping selected: mark it ✅ (toggle). Once every mapping is judged the item is marked 👍 (all ✅) or 👎 (any ❌). None selected: item verdict 👍 (toggle)"],
    ["d", "mapping selected: mark it ❌ (toggle). None selected: item verdict 👎 (toggle)"],
    ["Esc", "clear selection (u / d act on the item again)"], ["+ / −", "zoom PDF (click the % to fit width)"], ["m", "crop / show page margins"],
    ["click Lean token", "inspect innermost expression; click again to widen"], ["click PDF box", "select the mapping under the cursor"]];
  $("#modal-body").replaceChildren(h("h3", {}, "Keyboard and mouse"),
    h("table", { class: "keys" }, rows.map(([a, b]) => h("tr", {}, h("td", {}, h("kbd", {}, a)), h("td", {}, b)))),
    h("p", {}, "A badge such as ", h("span", { class: "cite mov" }, "→1366"), " after a paper line cited in a Lean comment gives that line in the current paper. ",
      "The Lean files cite the paper version they were written against, and the frozen files are never renumbered. ",
      h("span", { class: "cite chg" }, "amber"), ": the line's text has changed since; ", h("span", { class: "cite gone" }, "red"),
      ": the line is gone. Hover for both texts, click to show them in the inspector."),
    h("p", { class: "muted" }, `Session ${SESSION}. Every action is appended to logs/events.jsonl; “Finish audit” writes the report. Data built ${S.data.built} at git ${S.data.git_head.slice(0, 10)}.`));
  $("#modal").hidden = false;
}
async function finishAudit() {
  closeItemLog();
  await flush();
  const unjudged = S.items.filter((it) => !itemStatus(it.id)).length;
  const r = await fetch("/api/finish", { method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ session: SESSION, t: new Date().toISOString(), unjudged }) });
  const j = await r.json();
  if (S.item) log("item_open", { how: "resume", item_hash: S.item.hash });
  $("#modal-body").replaceChildren(h("h3", {}, "Audit report written"),
    h("p", {}, "Markdown: ", h("code", {}, j.md_path), h("br"), "JSON: ", h("code", {}, j.json_path), h("br"),
      "Raw events: ", h("code", {}, j.events_path)),
    unjudged ? h("p", { class: "muted" }, `${unjudged} item(s) are still unjudged — you can keep auditing and finish again later; each finish writes a new report.`) : null,
    h("pre", {}, j.markdown));
  $("#modal").hidden = false;
}

// ------------------------------------------------------------------ boot
async function boot() {
  initChrome();
  S.data = await (await fetch("/data/audit_data.json")).json();
  S.items = S.data.items;
  const st = await (await fetch("/api/state")).json();
  S.verdicts = st.verdicts; S.notes = st.notes; S.marks = st.marks;
  log("session_start", { ua: navigator.userAgent, viewport: [innerWidth, innerHeight], data_built: S.data.built,
    git_head: S.data.git_head, pdf_sha256: S.data.fingerprints.paper_pdf.sha256, tex_sha256: S.data.fingerprints.paper_tex.sha256,
    items: S.items.length });
  await loadPdf();
  const first = S.items.findIndex((it) => !itemStatus(it.id));
  await openItem(lsGet("audit.idx", first >= 0 ? first : 0), "start");
  renderProgress();
}
boot().catch((e) => { console.error(e); document.body.append(h("pre", { style: "position:fixed;bottom:0;left:0;background:#fee;color:#900;padding:8px;z-index:99" }, String(e.stack || e))); });
