from pathlib import Path
import subprocess,json,hashlib,time,os
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
files=[project/'KeyTateNormalizationChallenge.lean',project/'KeyTateNormalizationSolution.lean',project/'lakefile.toml',project/'lean-toolchain',project/'lake-manifest.json',project/'comparator-key-tate.json']
bind={str(f):sha(f) for f in files};(p/'root-build-bindings.json').write_text(json.dumps(bind,indent=2)+'\n')
cmd=['python3',str(w/'tools/run.py'),'python3','/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py',str(w/'toolchains/lean-4.35.0-rc2-linux/bin/lake'),'build','+KeyTateNormalizationChallenge','+KeyTateNormalizationSolution'];t=time.monotonic()
with (p/'root-build.log').open('w') as f:
 try:r=subprocess.run(cmd,cwd=project,env=dict(os.environ,LEAN_NUM_THREADS='32',LEAN4_AGENT_LEAN_THREAD_BUDGET='32'),stdout=f,stderr=subprocess.STDOUT,timeout=1800);code=r.returncode
 except subprocess.TimeoutExpired:code=124
out={'exit_code':code,'seconds':time.monotonic()-t,'command':cmd,'inputs_unchanged':all(sha(Path(x))==v for x,v in bind.items()),'bindings':bind,'log_sha256':sha(p/'root-build.log')};(p/'root-build-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));raise SystemExit(code)
