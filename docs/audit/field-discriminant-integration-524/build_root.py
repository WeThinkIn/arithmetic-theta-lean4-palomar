from pathlib import Path
import subprocess,json,hashlib,time,os
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text());roots=[q['root']+kind for q in packages for kind in ['Challenge','Solution']]
files=[project/(n+'.lean') for n in roots]+[project/n for n in ['lakefile.toml','lean-toolchain','lake-manifest.json']]+[project/('comparator-'+q['slug']+'.json') for q in packages];bind={str(f):sha(f) for f in files};(p/'root-build-bindings.json').write_text(json.dumps(bind,indent=2)+'\n')
cmd=['python3',str(w/'tools/run.py'),'python3','/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py',str(w/'toolchains/lean-4.35.0-rc2-linux/bin/lake'),'build',*['+'+n for n in roots]];t=time.monotonic()
with (p/'root-build.log').open('w') as f:
 try:code=subprocess.run(cmd,cwd=project,env=dict(os.environ,LEAN_NUM_THREADS='32',LEAN4_AGENT_LEAN_THREAD_BUDGET='32'),stdout=f,stderr=subprocess.STDOUT,timeout=1800).returncode
 except subprocess.TimeoutExpired:code=124
out={'exit_code':code,'seconds':time.monotonic()-t,'command':cmd,'inputs_unchanged':all(sha(Path(x))==v for x,v in bind.items()),'bindings':bind,'log_sha256':sha(p/'root-build.log')};(p/'root-build-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='bindings'}));raise SystemExit(code)
