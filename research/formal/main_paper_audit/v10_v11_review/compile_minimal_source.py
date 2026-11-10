"""Compile only the v11 TeX and its four figures; no ZIP or release mutation."""
from pathlib import Path
import subprocess,re,json,zipfile,tempfile,hashlib
import pymupdf
ROOT=Path(__file__).resolve().parents[4];OUT=Path(__file__).resolve().parent
WORK=Path(tempfile.mkdtemp(prefix='v11-minimal-source-'))
name='shift_symmetry_d_dimensions';src=(ROOT/(name+'.tex')).read_text()
figs=re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}',src)
files=[name+'.tex',*figs]
for rel in files:
 p=WORK/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((ROOT/rel).read_bytes())
for i in range(3):
 with (OUT/f'minimal_source_{i}.log').open('w') as f:
  subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',name+'.tex'],cwd=WORK,stdout=f,stderr=subprocess.STDOUT,check=True)
log=(WORK/(name+'.log')).read_text();assert not re.search(r'(undefined references|Citation .* undefined|Reference .* undefined|multiply defined)',log)
def words(p):
 s=subprocess.check_output(['pdftotext','-bbox',str(p),'-'],text=True)
 return [line.strip() for line in s.splitlines() if '<word' in line or '<page' in line]
assert words(WORK/(name+'.pdf'))==words(ROOT/(name+'.pdf'))
fonts=subprocess.check_output(['pdffonts',str(WORK/(name+'.pdf'))],text=True)
assert 'Type 3' not in fonts
(OUT/'minimal_source_fonts.txt').write_text(fonts)
pdf=pymupdf.open(WORK/(name+'.pdf'))
r={'files':files,'file_sha256':{rel:hashlib.sha256((WORK/rel).read_bytes()).hexdigest() for rel in files},'pages':len(pdf),'word_layout_identical_to_updated_paper':True,'undefined_references':False,'type3_fonts':False,'warnings':[x for x in log.splitlines() if any(k in x for k in ['Warning','Underfull','Overfull'])],'temporary_directory':str(WORK)}
(OUT/'minimal_source_build.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
for i,p in enumerate(pdf):
 if any(t in p.get_text() for t in ('Enumeration on a finite abelian', 'Read complexity', 'Dependence on the ranks', 'Verification and its audit')):p.get_pixmap(matrix=pymupdf.Matrix(1.3,1.3)).save(WORK/f'preview-{i+1}.png')
