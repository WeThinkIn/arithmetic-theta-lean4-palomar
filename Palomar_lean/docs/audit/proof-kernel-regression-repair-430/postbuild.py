from pathlib import Path
import subprocess,json,hashlib,os,time,concurrent.futures
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
b=json.loads((p/'build-result.json').read_text());assert b['exit_code']==0 and b['source_bindings_unchanged'];bindings=json.loads((p/'build-bindings.json').read_text());assert all(sha(project/f)==h for f,h in bindings.items())
assert not (p/'postbuild-result.json').exists()
affinity='/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py'
env=dict(os.environ,LEAN_NUM_THREADS='4',LEAN4_AGENT_LEAN_THREAD_BUDGET='4')
def run(name,args):
 log=p/(name+'.log');start=time.monotonic();cmd=['python3',str(w/'tools/run.py'),'python3',affinity]+args
 with log.open('w') as f:
  try:r=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=600);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 result={'name':name,'exit_code':code,'seconds':time.monotonic()-start,'command':cmd,'log_sha256':sha(log)};(p/(name+'-result.json')).write_text(json.dumps(result,indent=2)+'\n');return result
results=[run('exact-type-audit',['lake','env','lean','--root='+str(p),str(p/'ExactTypeAudit.lean')])]
assert results[-1]['exit_code']==0
roots=sorted({json.loads(f.read_text())['solution_module'] for f in project.glob('comparator*.json')})
for root in roots:
 s='''module
import all ROOT
import Lean
open Lean Elab Command
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `ROOT | throwError "Module not imported"
  let mut checked : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unexpected axioms for {name}: {axioms}"
    checked := checked + 1
  unless checked > 0 do throwError "No declarations checked"
  logInfo m!"ROOT_ALL_DECLARATIONS_STANDARD_AXIOMS {checked}"
'''.replace('ROOT',root)
 (p/(root+'Audit.lean')).write_text(s)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 results.extend(pool.map(lambda root:run(root+'-audit',['lake','env','lean','--root='+str(p),str(p/(root+'Audit.lean'))]),roots))
assert all(r['exit_code']==0 for r in results)
results.append(run('all103-endpoint-audit',['python3',str(w/'tools/audit_endpoint_batch.py'),'--number','431']))
results.append(run('original-baseline',['python3',str(w/'tools/check_baseline.py')]))
unchanged=all(sha(project/f)==h for f,h in bindings.items());passed=all(r['exit_code']==0 for r in results) and unchanged
out={'passed':passed,'source_bindings_unchanged':unchanged,'results':results,'official_comparator_pass':False,'all103_audit_receipt':'evidence/partial-endpoint-audit-431-result.json'};(p/'postbuild-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'passed':passed,'checks':len(results),'unchanged':unchanged}));raise SystemExit(not passed)
