from pathlib import Path
import os,subprocess,time,json,hashlib,re
root=Path(__file__).resolve().parent;workspace=root.parent.parent;pkg=root.parent/'early-certificate-205';bin=workspace/'toolchains/lean-4.35.0-rc2-linux/bin'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=bin.parent/'src/lean/lake/Lake/CLI/Check.lean';text=source.read_text();body=re.search(r'^def primitiveTargets[^\n]*\n(.*?)^def ',text,re.M|re.S).group(1);body='\n'.join(x.split('--',1)[0] for x in body.splitlines());prims=re.findall(r'``([A-Za-z_][A-Za-z0-9_\'.]*)',body)
cfg=json.loads((pkg/'comparator.json').read_text());targets=['Quot','Quot.mk','Quot.lift','Quot.ind']+cfg['theorem_names']+cfg['permitted_axioms']+prims
(root/'export-targets.json').write_text(json.dumps({'targets':targets,'primitive_source_sha256':sha(source)},indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=str(pkg)+os.pathsep+env.get('LEAN_PATH','');env['LEAN_NUM_THREADS']='8'
rows=[]
for module in ['Challenge','Solution']:
 src=pkg/(module+'.lean');obj=pkg/(module+'.olean');out=root/(module+'.ndjson');start=time.monotonic()
 cmd=[str(bin/'leanexport'),module,'--']+targets
 with out.open('wb') as f,(root/(module+'-export.log')).open('wb') as log:
  try:r=subprocess.run(cmd,env=env,stdout=f,stderr=log,timeout=300);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 row={'module':module,'command':cmd,'exit_code':code,'elapsed_seconds':round(time.monotonic()-start,2),'source_sha256':sha(src),'olean_sha256':sha(obj),'export_sha256':sha(out),'export_bytes':out.stat().st_size,'lean_path_prefix':str(pkg),'leanexport_sha256':sha(bin/'leanexport')};rows.append(row)
 (root/'export-receipts.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
 if code:raise SystemExit(code)
