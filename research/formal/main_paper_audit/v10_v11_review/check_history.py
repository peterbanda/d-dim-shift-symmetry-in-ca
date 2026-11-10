"""Read-only independent reconstruction of positional verdict carry-forwards."""
from pathlib import Path
from functools import lru_cache
import subprocess,json,hashlib
ROOT=Path(__file__).resolve().parents[4]; OUT=Path(__file__).resolve().parent
BASE='research/formal/correspondence_audit'; LEAN='research/formal/shiftsym/'
@lru_cache(None)
def read(rev,path): return subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT,text=True)
def normalize(x):
    if isinstance(x,dict): return {k:normalize(v) for k,v in x.items() if k!='lines'}
    if isinstance(x,list): return [normalize(v) for v in x]
    return x
def corr(rev,iid):
    x=json.loads(read(rev,BASE+'/data/corr/'+iid.replace(':','_',1)+'.json'))
    return next(z for z in x['items'] if z['id']==iid) if 'items' in x else x
def declarations(rev,item):
    return [(d['decl'],d['file'],'\n'.join(read(rev,LEAN+d['file']).splitlines()[d['sl']-1:d['el']])) for d in item['lean_decls']]
def main():
    revs=subprocess.check_output(['git','log','--format=%H','--',BASE+'/data/audit_data.json'],cwd=ROOT,text=True).split()
    bundles={r:{i['id']:i for i in json.loads(read(r,BASE+'/data/audit_data.json'))['items']} for r in revs}
    events=[json.loads(l) for l in (ROOT/BASE/'logs/events.jsonl').read_text().splitlines()]
    checked=[];prior={};marks={}
    for e in events:
        if e['type']=='mapping_mark':marks[(e['item'],e['mapping'])]=e
        if e['type']!='verdict':continue
        iid=e['item']
        if e.get('carried_from_hash'):
            old=e['carried_from_bundle']; src=bundles[next(r for r in revs if r.startswith(old))][iid]
            dstrev=next(r for r in revs if bundles[r].get(iid,{}).get('hash')==e['item_hash']);dst=bundles[dstrev][iid]
            assert src['hash']==e['carried_from_hash']==prior[iid]['item_hash']
            assert e['value']==prior[iid]['value']
            assert src['tex']==dst['tex']
            assert declarations(old,src)==declarations(dstrev,dst)
            assert normalize(corr(old,iid))==normalize(corr(dstrev,iid))
            assert all(marks[(iid,m['id'])]['value']==e['value'] for m in dst['maps'])
            checked.append({'item':iid,'from':old,'to':dstrev[:7],'same_tex_declarations_links':True})
        prior[iid]=e
    frozen_changes={}
    for old,new in [('baea4fa','099e022'),('099e022','dde222d')]:
        oldrec={l.split()[1]:l.split()[0] for l in read(old,'research/formal/frozen_statements.sha256').splitlines() if l.strip() and not l.startswith('#')}
        # Check contents themselves, not merely that hash-file entries stayed equal.
        changed=[]
        for f in oldrec:
            if f.startswith('Shiftsym/Ext/'):continue
            if read(old,LEAN+f)!=read(new,LEAN+f):changed.append(f)
        frozen_changes[old+'..'+new]=changed
    result={'result':'PASS','carry_events_checked':len(checked),'edges':checked,'existing_nonextension_frozen_dependency_changes':frozen_changes}
    assert all(not v for v in frozen_changes.values())
    (OUT/'carry_history.json').write_text(json.dumps(result,indent=2));print('PASS',len(checked),'carry-forward events; existing frozen definitions unchanged')
if __name__=='__main__':main()
