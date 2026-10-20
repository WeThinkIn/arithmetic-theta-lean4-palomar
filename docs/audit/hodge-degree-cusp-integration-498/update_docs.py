from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/hodge-degree-cusp-scope-review-497';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/hodge-degree-cusp-integration-498';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-497';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/unary-geometric-integration-491/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==79
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=79,pending_count=24,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **77/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **79/103**, with 24 pending; these are local interface checks, not 79 official passes. [Component Hodge power degree](challenges/component-hodge-degree/README.md) adds full original031, retaining the actual canonical boundary Hodge extension and exact residue-weighted degree formula for every original nonzero section and tensor exponent, including zero. [Split-field component cusp bound](challenges/split-cusp/README.md) adds full original072 without an algebraic-closure hypothesis. Both exact original recoveries, target/semantic/standard-axiom audits and actual four-root build498 passed. [Latest coverage](docs/audit/hodge-degree-cusp-integration-498/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete component Hodge degree495 and split-field cusp496 add full original031/072. Original031 retains the full canonical boundary Hodge Extension: actual Tate curve/normalized differential, actual differential sheaf and pointed pullback comparison, every DiskTest and unique extending generator. It gives exact24*degree=n*2*L*#cusps and the bound byn*#SL2 for every original nonzero section of every tensor power n including zero, in every actual normal affine frame cover, with degree from actual residue fields. Original072 retains characteristic-zero fields with a specified primitive L-th root, full original level/quotient/compactification objects and actual cusps, with no algebraic closure premise. Challenge877lines/61559bytes and467lines/32449bytes;19/16explicit targets and467/280semantic declarations checked. Original theorem rfl recovery and all target/standard-axiom checks passed. Actual shared four-root build498 passed in {r['seconds']:.2f}s with valid dependency-cache reuse and unchanged inputs. Independent coverage79/103,24pending; official verification remains pending. These endpoints do not separately construct their supplied LevelData/Compactification/Hodge Extension. See docs/audit/hodge-degree-cusp-integration-498/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('031','component Hodge power degree495'),('072','split-field component cusp bound496')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual four-root build498 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('79/103 independent interfaces integrated,24pending; no new official pass.')
