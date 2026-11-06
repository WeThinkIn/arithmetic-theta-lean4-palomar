from pathlib import Path
import os, subprocess, time, signal, json, hashlib
p = Path(__file__).resolve().parent
w = p.parent.parent
b = w / 'toolchains/lean-4.35.0-rc2-linux/bin'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
assert not (p/'receipt.json').exists()
env = dict(os.environ, LEAN_NUM_THREADS='4', LEAN4_AGENT_LEAN_THREAD_BUDGET='4')
target = 'WeierstrassProjModel.kw_lrThird_minor_YZ'
mod = 'Definitions.Def_WeierstrassCurve_ProjModel_ThirdAddFormulas'
old = w/'evidence/proof-optimization-integration-407/baseline-objects'
new = w/'project/.lake/build/lib/lean'
paths = [base/(mod.replace('.', '/')+ext) for base in [old,new] for ext in ['.olean','.olean.private','.olean.server']]
bindings = {str(f):sha(f) for f in paths}
(p/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
targets = json.loads((w/'evidence/proof-optimized-export-416/export-targets.json').read_text())['targets']
targets = [target if x == 'ArithmeticThetaPalomarMain172.explicitFiniteDetermination' else x for x in targets]
rows=[]
def run(label,cmd,budget,env,stdout):
    start=time.monotonic();reason=None;peak=0
    with stdout.open('wb') as out, (p/(label+'.stderr.log')).open('wb') as err:
        proc=subprocess.Popen(cmd,env=env,stdout=out,stderr=err,start_new_session=True)
        (p/'active.json').write_text(json.dumps({'label':label,'pid':proc.pid,'command':cmd})+'\n')
        while proc.poll() is None:
            try:
                vals={s.split(':')[0]:int(s.split()[1])*1024 for s in Path(f'/proc/{proc.pid}/status').read_text().splitlines() if s.startswith(('VmRSS:','VmHWM:'))}
            except OSError: vals={}
            peak=max(peak,vals.get('VmHWM',0))
            available=next(int(s.split()[1])*1024 for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
            if time.monotonic()-start>budget:reason='target benchmark time budget'
            elif vals.get('VmRSS',0)>48*2**30 or available<36*2**30:reason='target benchmark memory guard'
            if reason:
                os.killpg(proc.pid,signal.SIGTERM)
                try:proc.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                break
            try:proc.wait(timeout=2)
            except subprocess.TimeoutExpired:pass
    row={'label':label,'command':cmd,'exit_code':proc.returncode,'seconds':time.monotonic()-start,'peak_hwm_bytes':peak,'stop_reason':reason,'output_bytes':stdout.stat().st_size,'output_sha256':sha(stdout)}
    rows.append(row);(p/(label+'-receipt.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
    return row
for label,base in [('old-ring',old),('new-grind',new)]:
    e=dict(env,LEAN_PATH=str(base)+os.pathsep+env['LEAN_PATH'])
    row=run(label+'-export',[str(b/'leanexport'),mod,'--']+targets,180,e,p/(label+'.ndjson'))
    assert row['exit_code']==0
for label in ['old-ring','new-grind']:
    run(label+'-check',[str(b/'leanchecker'),'--from-export',str(p/(label+'.ndjson'))],300,env,p/(label+'-check.log'))
r={'checks':rows,'input_bindings_unchanged':all(sha(Path(f))==h for f,h in bindings.items()),'official_acceptance':False,'scope':'Pinned stock Lean checker on each complete target-specific proof closure; exact original proposition, isolated original objects. No project artifact substitution; not full Palomar comparator.'}
(p/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
