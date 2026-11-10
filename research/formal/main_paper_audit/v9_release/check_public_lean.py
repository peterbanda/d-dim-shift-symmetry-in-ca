"""Check the public Lean closure with no internal-only project modules available.

Reuse cached artifacts ONLY for byte-identical sources, recompile the two
filtered modules, and replay every declaration in the public root closure.
This is a kernel/correspondence check, not a from-source rebuild of mathlib.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
TMP = Path(json.loads((OUT/'workspace.json').read_text())['temporary_directory'])
PUBLIC = TMP/'public'
INTERNAL_LEAN = ROOT/'research/formal/shiftsym'
PUBLIC_LEAN = PUBLIC/'research/formal/shiftsym'
LIB = PUBLIC_LEAN/'.lake/build/lib/lean'
LIB.mkdir(parents=True, exist_ok=True)
oldlib = INTERNAL_LEAN/'.lake/build/lib/lean'
reused = []
for src in PUBLIC_LEAN.rglob('*.lean'):
    rel = src.relative_to(PUBLIC_LEAN)
    if str(rel).startswith('.lake/') or rel.as_posix() in ['Shiftsym.lean','Shiftsym/Audit.lean']:
        continue
    assert src.read_bytes() == (INTERNAL_LEAN/rel).read_bytes(), rel
    old = (oldlib/rel).with_suffix('.olean')
    assert old.exists(), old
    dest = (LIB/rel).with_suffix('.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(old, dest)
    reused.append(rel.as_posix())
paths = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=INTERNAL_LEAN,text=True).strip().split(':')
assert str(oldlib) in paths
paths = [str(LIB) if p == str(oldlib) else p for p in paths]
env = dict(os.environ, LEAN_PATH=':'.join(paths))
lean = subprocess.check_output(['lake','env','which','lean'],cwd=INTERNAL_LEAN,text=True).strip()
jobs = [('audit_compile',[lean,'-o',str(LIB/'Shiftsym/Audit.olean'),'Shiftsym/Audit.lean']),
        ('root_compile',[lean,'-o',str(LIB/'Shiftsym.olean'),'Shiftsym.lean']),
        ('paper_audit',[lean,'Shiftsym/AuditPaper.lean']),
        ('frozen',['python3','../check_frozen.py']),
        ('placeholders',['python3','../check_placeholders.py']),
        ('dependencies',[lean,'../frozen_deps.lean']),
        ('kernel_replay',[lean,'../kernel_replay.lean'])]
results=[]
for name,cmd in jobs:
    print('START',name,flush=True)
    start=time.monotonic()
    with (OUT/(name+'.log')).open('w') as f:
        proc=subprocess.run(cmd,cwd=PUBLIC_LEAN,env=env,stdout=f,stderr=subprocess.STDOUT)
    result={'check':name,'exit':proc.returncode,'seconds':round(time.monotonic()-start,2)}
    results.append(result)
    (OUT/'public_lean_results.json').write_text(json.dumps({'reused_identical_sources':reused,'checks':results},indent=2)+'\n')
    print(result,flush=True)
    if proc.returncode:raise SystemExit(proc.returncode)
