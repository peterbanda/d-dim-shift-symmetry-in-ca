"""Make and compile the minimal arXiv source package for the citation update."""
from pathlib import Path
import subprocess,re,json,zipfile,tempfile,hashlib
import pymupdf
ROOT=Path(__file__).resolve().parents[4];OUT=Path(__file__).resolve().parent
WORK=Path(tempfile.mkdtemp(prefix='v9-arxiv-final-'))
name='shift_symmetry_d_dimensions';src=(ROOT/(name+'.tex')).read_text()
figs=re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}',src)
files=[name+'.tex',*figs]
for rel in files:
 p=WORK/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((ROOT/rel).read_bytes())
zip_path=OUT/'arxiv_source_v9_with_citations.zip'
with zipfile.ZipFile(zip_path,'w',zipfile.ZIP_DEFLATED) as z:
 for rel in files:z.write(WORK/rel,rel)
for i in range(3):
 with (OUT/f'arxiv_updated_{i}.log').open('w') as f:
  subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',name+'.tex'],cwd=WORK,stdout=f,stderr=subprocess.STDOUT,check=True)
log=(WORK/(name+'.log')).read_text();assert not re.search(r'(undefined references|Citation .* undefined|Reference .* undefined|multiply defined)',log)
def words(p):
 s=subprocess.check_output(['pdftotext','-bbox',str(p),'-'],text=True)
 return [line.strip() for line in s.splitlines() if '<word' in line or '<page' in line]
assert words(WORK/(name+'.pdf'))==words(ROOT/(name+'.pdf'))
fonts=subprocess.check_output(['pdffonts',str(WORK/(name+'.pdf'))],text=True)
assert 'Type 3' not in fonts
(OUT/'arxiv_updated_fonts.txt').write_text(fonts)
pdf=pymupdf.open(WORK/(name+'.pdf'))
r={'package':zip_path.name,'files':files,'file_sha256':{rel:hashlib.sha256((WORK/rel).read_bytes()).hexdigest() for rel in files},'zip_sha256':hashlib.sha256(zip_path.read_bytes()).hexdigest(),'pages':len(pdf),'word_layout_identical_to_updated_paper':True,'undefined_references':False,'type3_fonts':False,'warnings':[x for x in log.splitlines() if any(k in x for k in ['Warning','Underfull','Overfull'])],'temporary_directory':str(WORK)}
(OUT/'arxiv_updated_build.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
for i,p in enumerate(pdf):
 if 'Applications.' in p.get_text() or 'Earlier studies of CA' in p.get_text() or 'Anonymous Leader Election in One-' in p.get_text():p.get_pixmap(matrix=pymupdf.Matrix(1.3,1.3)).save(WORK/f'preview-{i+1}.png')
