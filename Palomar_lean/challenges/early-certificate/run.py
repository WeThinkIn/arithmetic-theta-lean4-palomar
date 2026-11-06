from pathlib import Path
import os,subprocess,time,json,hashlib,concurrent.futures
root=Path(__file__).resolve().parent
env=os.environ.copy();env['LEAN_NUM_THREADS']='8'
def check(mod):
 source=root/(mod+'.lean');start=time.monotonic()
 with (root/(mod+'.log')).open('w') as log:
  try:r=subprocess.run(['lean','--root='+str(root),'-o',str(root/(mod+'.olean')),str(source)],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=300);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 return {'module':mod,'exit_code':code,'seconds':round(time.monotonic()-start,2),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool: results=list(pool.map(check,['Challenge','Solution']))
(root/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
for result in results:print(json.dumps(result),flush=True)
raise SystemExit(any(x['exit_code'] for x in results))
