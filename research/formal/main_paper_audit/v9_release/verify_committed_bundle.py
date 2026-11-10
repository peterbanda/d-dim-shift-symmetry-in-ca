"""Read-only verification of the committed v9 correspondence bundle.

Run from repository root. Uses local pdfTeX and PyMuPDF; writes compilation
files to a temporary directory and prints JSON. Does not rebuild production data.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import tempfile

import pymupdf

ROOT = Path('/tmp/shift-v9-release-gocm7h17/internal')
AUDIT = ROOT / 'research/formal/correspondence_audit'
sys.path.insert(0, str(AUDIT / 'tools'))
import build as b
import auditlog


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


data = json.loads((AUDIT / 'data/audit_data.json').read_text())
chars = json.loads((AUDIT / 'data/pdf_chars.json').read_text())
aux = json.loads((AUDIT / 'data/paper.aux.json').read_text())
checked = 0
for k in ['paper_pdf', 'paper_tex']:
    f = data['fingerprints'][k]
    assert digest(ROOT / f['path']) == f['sha256'], k
    checked += 1
for k, folder in [('lean', ROOT / data['lean_root']),
                  ('corr', AUDIT / 'data/corr'), ('exports', AUDIT / 'data/lean')]:
    for name, expected in data['fingerprints'][k].items():
        assert digest(folder / name) == expected, (k, name)
        checked += 1

# Re-extract every glyph, rather than trusting just the PDF hash in the cache.
pymupdf.TOOLS.set_small_glyph_heights(True)
pages = []
for page in pymupdf.open(b.PDF):
    boxes = []
    for block in page.get_text('rawdict')['blocks']:
        for line in block.get('lines', []):
            for span in line['spans']:
                for ch in span['chars']:
                    if ch['c'].strip():
                        boxes.append([round(v, 2) for v in ch['bbox']])
    pages.append(boxes)
assert chars == {'pdf_sha256': digest(b.PDF), 'pages': pages}

tex = b.Tex(b.TEX.read_text())
items = b.find_items(tex, aux)
lean = b.LeanIndex()
corr = b.load_corr(sorted(b.CORR.glob('*.json')))
maps, errors, warnings = b.validate(corr, items, tex, lean)
assert not errors, errors
assert len(items) == len(data['items']) == 25
assert len(maps) == 476

tmp = Path(tempfile.mkdtemp(prefix='v9-viewer-recheck-'))
(tmp / 'marked.tex').write_text(b.instrument(tex, items, maps))
for i in range(3):
    with (tmp / f'compile-{i}.log').open('w') as log:
        subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                        '-output-directory=' + str(tmp), str(tmp / 'marked.tex')],
                       cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
assert b.words(tmp / 'marked.pdf') == b.words(b.PDF), 'Word layout differs'
assert b.load_aux(tmp / 'marked.aux') == aux, 'Auxiliary labels differ'
pos = {}
for line in (tmp / 'marked.apos').read_text().splitlines():
    key, x, y, page = line.split()
    pos[key] = (int(page), int(x)/65536*72/72.27,
                b.PAGE_H-int(y)/65536*72/72.27)

by_item = {}
anchors = 0
for k, mp in enumerate(maps):
    for j, ta in enumerate(mp['tex']):
        ta['rects'] = b.fit_rects(pos[f'M{k}.{j}S'], pos[f'M{k}.{j}E'], ta['mode'], chars)
        anchors += 1
    by_item.setdefault(mp['item'], []).append(mp)
for k, (it, stored) in enumerate(zip(items, data['items'])):
    assert it['id'] == stored['id'] and it['number'] == stored['number']
    env_tex = tex.text[it['begin']:it['end']]
    assert env_tex == stored['tex']
    assert stored['tex_lines'] == [it['line_begin'], it['line_end']]
    assert by_item[it['id']] == stored['maps'], ('Mappings/coordinates differ', it['id'])
    ends_display = b.env_end_insertion(tex.text, it) < it['end_tag'] - 1 and bool(
        re.search(r'(\\\]|\\end\{(equation|align)\*?\})\s*$', tex.text[it['body']:it['end_tag']]))
    assert b.env_rects(pos[f'I{k}B'], pos[f'I{k}E'], ends_display) == stored['rects']
    for decl in stored['lean_decls']:
        fresh = lean.decls[decl['decl']]
        assert all(fresh[x] == decl[x] for x in ['file', 'sl', 'el'])
    src = '\n'.join('\n'.join(lean.lines(d['file'])[d['sl']-1:d['el']])
                    for d in stored['lean_decls'])
    block = corr[it['label']]['statement']
    assert b.sha256s(json.dumps({'tex': env_tex, 'lean': src, 'corr': block}, sort_keys=True)) == stored['hash']

state = auditlog.replay(auditlog.read_events())
stale, unjudged = [], []
for it in data['items']:
    v = state['verdicts'].get(it['id'], {})
    if not v.get('value'):
        unjudged.append(it['id'])
    else:
        assert v['value'] == 'up', (it['id'], v)
        if v['hash'] != it['hash']:
            stale.append(it['id'])
assert len(stale) == 24
assert not unjudged
assert any('S07_Dynamics_SymmetryBreaking' in f for f in data['lean_files'])
insolv = next(i for i in data['items'] if i['id'] == 'cor:insolv')
assert any(d['decl'] == 'ShiftSym.P07.insolvFullStatement' for d in insolv['lean_decls'])
print(json.dumps({'result': 'PASS', 'head': '444c7af',
    'fingerprints_checked': checked, 'items': len(items), 'mappings': len(maps),
    'tex_anchors_and_rectangles_reproduced': anchors, 'pages': len(pages),
    'glyph_boxes_reproduced': sum(map(len,pages)), 'word_layout_identical': True,
    'aux_labels_identical': True, 'all_item_hashes_reproduced': True,
    'stale_verdicts': stale, 'unjudged': unjudged, 'warnings': warnings,
    'temporary_build_directory': str(tmp)}, indent=2))
