from pathlib import Path
import os,subprocess,time,json,hashlib,sys
r=Path(__file__).resolve().parent;binary=r.parent.parent/'toolchains/lean-4.35.0-rc2-linux/bin/lean'

name=sys.argv[1];attempt=sys.argv[2] if len(sys.argv)>2 else '01';env=os.environ.copy();env['LEAN_NUM_THREADS']='8';env['LEAN_PATH']=str(r)+os.pathsep+env.get('LEAN_PATH','')
cmd=[str(binary),'-R',str(r),'-o',str(r/(name+'.olean')),str(r/(name+'.lean'))]
start=time.monotonic()
with (r/(name+'-check-'+attempt+'.log')).open('w') as log:
 try:code=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600).returncode
 except subprocess.TimeoutExpired:code=124
row={'command':cmd,'exit_code':code,'elapsed_seconds':round(time.monotonic()-start,2),'lean_path':env.get('LEAN_PATH'),'source_sha256':hashlib.sha256((r/(name+'.lean')).read_bytes()).hexdigest(),'lean_sha256':hashlib.sha256(binary.read_bytes()).hexdigest()}
(r/(name+'-receipt-'+attempt+'.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True);sys.exit(code)
