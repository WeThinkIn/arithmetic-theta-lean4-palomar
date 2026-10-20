from pathlib import Path
import subprocess,json,hashlib,time,os,signal
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert (p/'applied.json').exists(),'Apply reviewed exact patches after workers freeze first'
assert not (p/'build-result.json').exists(),'Do not overwrite terminal evidence'
roots={'GoalRoot'}
for f in project.glob('comparator*.json'):
 d=json.loads(f.read_text());roots.add(d['solution_module'])
files=list((project/'Proof').rglob('*.lean'))+list(project.glob('*Solution.lean'))+list(project.glob('*Challenge.lean'))+list(project.glob('comparator*.json'))+[project/n for n in ['lakefile.toml','lean-toolchain','lake-manifest.json','docs/SourceObligations.json']]
bind={str(f.relative_to(project)):sha(f) for f in files};(p/'build-bindings.json').write_text(json.dumps(bind,indent=2)+'\n')
cmd=['python3',str(w/'tools/run.py'),'python3','/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py',str(w/'toolchains/lean-4.35.0-rc2-linux/bin/lake'),'build']+['+'+r for r in sorted(roots)]
checkpoint={'command':cmd,'roots':sorted(roots),'budget_seconds':10800,'lake_runtime_threads':32,'compiler_internal_threads':1,'source_bindings_sha256':sha(p/'build-bindings.json'),'sampling_seconds':15,'scope':'Actual full GoalRoot and all public Comparator Solution root dependency rebuilds, preserving standard kernels and source types; not independent Comparator acceptance'}
(p/'build-checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
def sample(pid):
 rows={}
 for f in Path('/proc').iterdir():
  if not f.name.isdigit():continue
  try:
   fields=(f/'stat').read_text().rsplit(')',1)[1].split();rows[int(f.name)]={'parent':int(fields[1]),'rss':int(fields[21])*os.sysconf('SC_PAGE_SIZE'),'comm':(f/'comm').read_text().strip()}
  except (FileNotFoundError,ProcessLookupError,PermissionError,ValueError,IndexError):continue
 descendants={pid};changed=True
 while changed:
  before=len(descendants);descendants|={i for i,r in rows.items() if r['parent'] in descendants};changed=len(descendants)>before
 live=[rows[i] for i in descendants if i in rows]
 mem={a.split(':')[0]:int(a.split()[1])*1024 for a in Path('/proc/meminfo').read_text().splitlines() if a.startswith(('MemAvailable:','MemTotal:'))}
 return {'seconds':round(time.monotonic()-start,2),'processes':len(live),'lean_processes':sum(r['comm']=='lean' for r in live),'rss_sum_bytes':sum(r['rss'] for r in live),'host':mem}
start=time.monotonic();peak=0;maxlean=0;timedout=False
with (p/'build.log').open('w') as log,(p/'resources.jsonl').open('w') as metrics:
 proc=subprocess.Popen(cmd,cwd=project,env=dict(os.environ,LEAN_NUM_THREADS='32',LEAN4_AGENT_LEAN_THREAD_BUDGET='32'),stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 (p/'process.json').write_text(json.dumps({'pid':proc.pid,'started_unix':time.time()})+'\n')
 while proc.poll() is None:
  row=sample(proc.pid);metrics.write(json.dumps(row)+'\n');metrics.flush();peak=max(peak,row['rss_sum_bytes']);maxlean=max(maxlean,row['lean_processes'])
  if time.monotonic()-start>10800:
   timedout=True;os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=15)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  try:proc.wait(timeout=15)
  except subprocess.TimeoutExpired:pass
 code=124 if timedout else proc.returncode
changed=[f for f,h in bind.items() if sha(project/f)!=h]
r={'exit_code':code,'seconds':time.monotonic()-start,'source_bindings_unchanged':not changed,'changed_inputs':changed,'roots':sorted(roots),'peak_sampled_process_tree_rss_sum_bytes':peak,'max_sampled_lean_processes':maxlean,'measurement_note':'RSS sum double-counts shared pages, sampling can miss peaks; not a cgroup limit or exact physical-memory peak','command':cmd,'log_sha256':sha(p/'build.log'),'bindings_sha256':sha(p/'build-bindings.json')}
(p/'build-result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True);raise SystemExit(code or bool(changed))
