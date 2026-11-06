from pathlib import Path
import subprocess,os,json,time,hashlib,sys
r=Path(__file__).resolve().parent;w=r.parent.parent;slug=sys.argv[1];d=r/slug;root={'split-square-degree':'SplitSquareDegree','split-discriminant':'SplitDiscriminant'}[slug]
c=w/'evidence/split-exact-integration-558'/(root+'Challenge-01.ndjson');s=w/'evidence/split-pruned-integration-561'/(root+'Solution-01.ndjson');cfg=d/'comparator.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();bindings={str(p):sha(p) for p in [c,s,cfg]};(d/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
cmd=['python3',str(w/'tools/run.py'),'python3','/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py','lake','comparator','--config',str(cfg),'--challenge-from-export',str(c),'--solution-from-export',str(s)]
start=time.monotonic()
with (d/'comparator.log').open('w') as f:
 try:code=subprocess.run(cmd,cwd=w/'project',env=dict(os.environ,LEAN_NUM_THREADS='8',COMPARATOR_BWRAP=str(w/'evidence/early-comparator-211/bubblewrap-0.12.0/build/bwrap')),stdout=f,stderr=subprocess.STDOUT,timeout=19800).returncode
 except subprocess.TimeoutExpired:code=124
row={'command':cmd,'exit_code':code,'elapsed_seconds':time.monotonic()-start,'bindings':bindings,'bindings_unchanged':all(sha(Path(p))==h for p,h in bindings.items()),'limitation':'Local stock comparator, con-ron/NanoDa/Lean default; official run and semantic registry review remain separate'};(d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:v for k,v in row.items() if k!='bindings'}),flush=True);raise SystemExit(code)
