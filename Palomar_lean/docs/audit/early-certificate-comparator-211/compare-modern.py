from pathlib import Path
import subprocess,os,time,json,hashlib
root=Path(__file__).resolve().parent;work=root/'project';bin=root.parent.parent/'toolchains/lean-4.35.0-rc2-linux/bin'
env=os.environ.copy();env['COMPARATOR_BWRAP']=str(root/'bubblewrap-0.12.0/build/bwrap');env['LEAN_NUM_THREADS']='8';env['TMPDIR']=str(root/'tmp');Path(env['TMPDIR']).mkdir(exist_ok=True)
config=root/'comparator-external.json';cmd=[str(bin/'lake'),'comparator','--config='+str(config),'--challenge-from-export='+str(root/'Challenge.ndjson'),'--solution-from-export='+str(root/'Solution.ndjson')];start=time.monotonic()
with (root/'comparator-modern.log').open('w') as log:
 try:r=subprocess.run(cmd,cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600);code=r.returncode
 except subprocess.TimeoutExpired:code=124
receipt={'command':cmd,'cwd':str(work),'exit_code':code,'elapsed_seconds':round(time.monotonic()-start,2),'normal_sandbox':True,'external_kernels':{'nanoda':'bundled','con-ron':'bundled --jobs=2'},'budget_seconds':600}
(root/'comparator-modern-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(code)
