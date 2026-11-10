"""Regenerate PDFs and viewer data after the requested citation-only edit.
Uses installed pdfTeX (same version as the submitted v9), not Docker.
No Lean source, verdict or frozen fingerprint is changed.
"""
from pathlib import Path
import os, sys, json, subprocess, shutil, tempfile, re, hashlib
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
TMP=Path(tempfile.mkdtemp(prefix='v9-citations-'))
AUDIT=ROOT/'research/formal/correspondence_audit'
before=subprocess.check_output(['git','show','HEAD:shift_symmetry_d_dimensions.tex'],cwd=ROOT)
if (OUT/'citations_build.json').exists():
    previous=Path(json.loads((OUT/'citations_build.json').read_text())['build_dir'])/'shift_symmetry_d_dimensions.tex'
    before=previous.read_bytes()
assert hashlib.sha256(before).hexdigest()==json.loads((AUDIT/'data/audit_data.json').read_text())['fingerprints']['paper_tex']['sha256']

def run(cmd,log,cwd=ROOT):
    with (OUT/log).open('w') as f:
        subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,check=True)

def compile_tex(work,name,log_prefix):
    for i in range(3):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(work),str(work/(name+'.tex'))],f'{log_prefix}_{i}.log')
    log=(work/(name+'.log')).read_text()
    assert not re.search(r'(undefined references|Citation .* undefined|Reference .* undefined|multiply defined)',log)
    return log

name='shift_symmetry_d_dimensions'
shutil.copy2(ROOT/(name+'.tex'),TMP/(name+'.tex'))
logs={name:compile_tex(TMP,name,'citations_paper')}
shutil.copy2(TMP/(name+'.pdf'),ROOT/(name+'.pdf'))
mobile=name+'_mobile'
shutil.copy2(ROOT/(mobile+'.tex'),TMP/(mobile+'.tex'))
logs[mobile]=compile_tex(TMP,mobile,'citations_mobile')
shutil.copy2(TMP/(mobile+'.pdf'),ROOT/(mobile+'.pdf'))
# Remap only line scopes, then use the production builder with a native
# pdfTeX runner. The builder's mandatory word-coordinate comparison stays on.
old=TMP/'before.tex'
old.write_bytes(before)
run(['python3',str(AUDIT/'tools/remap_anchors.py'),str(old),str(ROOT/(name+'.tex')),'--apply'],'citations_remap.log')
run([sys.executable,str(AUDIT/'tools/pdf_chars.py'),str(ROOT/(name+'.pdf')),str(AUDIT/'data/pdf_chars.json')],'citations_chars.log')
sys.path.insert(0,str(AUDIT/'tools'))
import build as b

def local_tex(work,name,passes):
    for i in range(passes):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error',name+'.tex'],f'citations_instrumented_{i}.log',work)
b.run_tex=local_tex
sys.argv=[str(AUDIT/'tools/build.py')]
with (OUT/'citations_bundle_build.log').open('w') as f:
    from contextlib import redirect_stdout
    with redirect_stdout(f):b.main()
summary={'build_dir':str(TMP),'texlive':subprocess.check_output(['pdflatex','--version'],text=True).splitlines()[0],
 'warnings':{n:[s for s in log.splitlines() if any(t in s for t in ['Warning','Overfull','Underfull','Output written'])] for n,log in logs.items()},
 'hashes':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in [name+'.tex',name+'.pdf',mobile+'.pdf','research/formal/correspondence_audit/data/audit_data.json']}}
(OUT/'citations_build.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
