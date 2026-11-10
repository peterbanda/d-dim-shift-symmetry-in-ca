"""Compile all exported project sources into an empty object directory (four workers).
Only pinned mathlib/dependency artifacts are reused. No internal project objects
are on LEAN_PATH. Replay the newly built public root and rerun its paper audit.
"""
from pathlib import Path
import concurrent.futures as cf
import subprocess, os, json, re, time
ROOT=Path(__file__).resolve().parents[4]; OUT=Path(__file__).resolve().parent
TMP=Path(json.loads((OUT/'workspace.json').read_text())['temporary_directory'])
SRC=TMP/'public/research/formal/shiftsym'; INTERNAL=ROOT/'research/formal/shiftsym'
LIB=SRC/'.lake/build-fresh/lib/lean'; LIB.mkdir(parents=True,exist_ok=False)
paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=INTERNAL,text=True).strip().split(':')
old=str(INTERNAL/'.lake/build/lib/lean'); assert old in paths
paths=[str(LIB) if p==old else p for p in paths]
env=dict(os.environ,LEAN_PATH=':'.join(paths)); lean=subprocess.check_output(['lake','env','which','lean'],cwd=INTERNAL,text=True).strip()
sources={'.'.join(p.relative_to(SRC).with_suffix('').parts):p for p in [SRC/'Shiftsym.lean',*(SRC/'Shiftsym').rglob('*.lean')]}
deps={m:{x for line in p.read_text().splitlines() if re.match(r'^\s*import ',line) for x in line.split()[1:] if x in sources} for m,p in sources.items()}
logs=OUT/'fresh_build_logs';logs.mkdir(exist_ok=True)
results=[];done=set();pending=set(sources);active={}
def compile(m):
    p=sources[m];dest=(LIB/p.relative_to(SRC)).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    with (logs/(m+'.log')).open('w') as f:r=subprocess.run([lean,'-o',str(dest),str(p.relative_to(SRC))],cwd=SRC,env=env,stdout=f,stderr=subprocess.STDOUT)
    return {'module':m,'exit':r.returncode,'seconds':round(time.monotonic()-start,2)}
with cf.ThreadPoolExecutor(max_workers=4) as pool:
 while pending or active:
    ready=sorted(m for m in pending if deps[m]<=done)
    for m in ready[:4-len(active)]:
        active[pool.submit(compile,m)]=m;pending.remove(m);print('START',m,flush=True)
    assert active,('Dependency cycle',pending)
    finished,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
    for f in finished:
        m=active.pop(f);r=f.result();results.append(r);print(r,flush=True)
        (OUT/'fresh_build_results.json').write_text(json.dumps(results,indent=2))
        if r['exit']:raise RuntimeError(r)
        done.add(m)
for label,path in [('paper_audit','Shiftsym/AuditPaper.lean'),('dependencies','../frozen_deps.lean'),('kernel_replay','../kernel_replay.lean')]:
 with (OUT/('fresh_'+label+'.log')).open('w') as f:r=subprocess.run([lean,path],cwd=SRC,env=env,stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode==0,label
 print('PASS',label,flush=True)
print('COMPLETE',len(done),'source modules',flush=True)
