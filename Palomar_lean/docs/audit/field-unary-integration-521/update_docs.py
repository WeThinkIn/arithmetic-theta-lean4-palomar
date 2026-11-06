from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/field-unary-scope-review-520';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/field-unary-integration-521';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-520';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/compact-unary-split-integration-518/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==92
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=92,pending_count=11,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **91/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **92/103**, with 11 pending; these are local interface checks, not 92 official passes. [Arbitrary-field compact unary realization](challenges/field-unary/README.md) adds full original069: it constructs the unique genuine global Hodge section with the COMPLETE unary series equation over any characteristic-zero field under the original canonical geometry premises. Every coefficient extension and the normalized full-classifier/Hodge comparison are retained. Original statement recovery, semantic/target/standard-axiom audits and actual two-root build521 passed. [Latest coverage](docs/audit/field-unary-integration-521/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete interface519 adds full original069 over arbitrary characteristic-zero fields, with the original canonical geometry premises. The full all-scheme classifier and identity-ideal conormal derivative retain the original normalization; compiled equivalences recover every geometric-canonical comparison over EVERY algebraically closed coefficient extension. It constructs prescribed indices, actual open normalized power and the UNIQUE compact global section with the correct restriction, open frame, nonzero coefficient at every disk and COMPLETE unary power for every canonical marking and specified Hodge generator. Challenge984lines/96709bytes,18targets,638semanticdefinitions. All original recoveries and standard-axiom audits pass. Actual shared two-root build521 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage92/103,11pending; not92officialpasses. Matrix-family assembly and full official verification/intake remain incomplete. See docs/audit/field-unary-integration-521/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('069', 'arbitrary-field compact unary realization519')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual two-root build521 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('92/103 independent interfaces integrated,11pending; no new official pass.')
