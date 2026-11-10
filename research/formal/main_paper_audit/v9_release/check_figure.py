"""Definition-level Figure 1 check: enumerate all fixed binary masks for the
seven prime-order translations, then take a set union (no count formula or IE).
Also recompute the plotted configurations' stabilizers by numpy array rolls.
"""
from pathlib import Path
import json,itertools,hashlib,sys,os,importlib.util
import numpy as np
ROOT=Path(__file__).resolve().parents[4];OUT=Path(__file__).resolve().parent
TMP=Path(json.loads((OUT/'workspace.json').read_text())['temporary_directory'])
PUB=TMP/'public';os.chdir(PUB);sys.path.insert(0,str(PUB/'research/experiments'))
coords=list(itertools.product(range(6),repeat=2));idx={x:i for i,x in enumerate(coords)}
cyclic={}
for v in coords[1:]:
 group=frozenset(tuple(k*a%6 for a in v) for k in range(6))
 if len(group) in [2,3]:cyclic.setdefault(group,v)
all_fixed=set();counts=[]
for v in cyclic.values():
 unseen=set(coords);masks=[]
 while unseen:
  u=min(unseen);orb={tuple((a+k*b)%6 for a,b in zip(u,v)) for k in range(6)}
  unseen-=orb;masks.append(sum(1<<idx[x] for x in orb))
 configs=[0]
 for mask in masks:configs += [x|mask for x in configs]
 all_fixed.update(configs);counts.append({'generator':v,'fixed_configurations':len(configs)})
assert len(cyclic)==7 and len(all_fixed)==801064
spec=importlib.util.spec_from_file_location('fig',PUB/'compute_example_configs.py');fig=importlib.util.module_from_spec(spec);spec.loader.exec_module(fig)
captured=[]
def capture(ax,s,n,*args,**kwargs):captured.append((s,n))
fig.draw_2d=capture;fig.draw_3d=capture
import matplotlib.figure
matplotlib.figure.Figure.savefig=lambda *a,**kw:None
fig.main()
stabs=[]
for config,n in captured:
 d=len(next(iter(config)));a=np.empty((n,)*d,dtype=int)
 for u,x in config.items():a[u]=x
 stab=[v for v in itertools.product(range(n),repeat=d) if np.array_equal(a,np.roll(a,v,axis=tuple(range(d))))]
 stabs.append(stab)
assert stabs==[[(0,0),(3,0)],[(0,0),(2,2),(4,4)],[(0,0)],[(0,0,0),(0,2,2)]]
chart='charts/chart17_example_configs.pdf'
assert (PUB/chart).read_bytes()==(TMP/'internal'/chart).read_bytes()
r={'enumerated_union_cardinality':len(all_fixed),'minimal_fixed_sets':counts,'stabilizers_independent_roll_check':stabs,'regenerated_pdf_byte_identical':True}
(OUT/'figure_verification.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
