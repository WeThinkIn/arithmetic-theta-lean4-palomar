from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/field-discriminant-scope-review-523';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/field-discriminant-integration-524';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-523';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/field-unary-integration-521/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==93
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=93,pending_count=10,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **92/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **93/103**, with 10 pending; these are local interface checks, not 93 official passes. [Arbitrary-field compact discriminant realization](challenges/field-discriminant/README.md) adds full original068: it constructs the unique genuine compact Hodge section with the COMPLETE normalized discriminant series over every characteristic-zero field under the original canonical geometry premises. Every disk and specified extending Hodge generator are retained, with all coefficients below2L zero and coefficient2L exactly one. Original statement recovery, semantic/target/standard-axiom audits and actual two-root build524 passed. [Latest coverage](docs/audit/field-discriminant-integration-524/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete interface522 adds full original068 over arbitrary characteristic-zero fields with every even L>=3 and the original canonical geometry premises. From the intrinsic open D2 it constructs the UNIQUE compact global section with correct restriction and COMPLETE normalized discriminant series at EVERY disk and specified Hodge generator; all coefficients below2L vanish and coefficient2L is exactly one. The literal full Euler product and actual all-scheme classifier/identity-ideal normalized Hodge comparisons are retained. Challenge982lines/95717bytes,18targets. All semantic/types/standard-axiom audits and full original theorem recovery pass. Actual shared two-root build524 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage93/103,10pending; not93officialpasses. Matrix-family assembly and full official verification/intake remain incomplete. See docs/audit/field-discriminant-integration-524/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('068', 'arbitrary-field compact discriminant realization522')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual two-root build524 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('93/103 independent interfaces integrated,10pending; no new official pass.')
