from pathlib import Path
import os,subprocess,time,json,hashlib
root=Path(__file__).resolve().parent
env=os.environ.copy();env['LEAN_NUM_THREADS']='8';env['LEAN_PATH']=str(root)+os.pathsep+env.get('LEAN_PATH','')
for mod in ['MainIndependentDefinitions198','ReadyBridges198']:
 source=root/(mod+'.lean'); start=time.monotonic()
 with (root/(mod+'.log')).open('w') as log:
  try:r=subprocess.run(['lean','--root='+str(root),'-o',str(root/(mod+'.olean')),str(source)],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 receipt={'module':mod,'exit_code':code,'seconds':round(time.monotonic()-start,2),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
 with (root/'progress.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(json.dumps(receipt),flush=True)
 if code:raise SystemExit(code)
