from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/rigidification-cusp-scope-review-486';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/rigidification-cusp-integration-487';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-486';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/key-tate-integration-480/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==76
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=76,pending_count=27,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **74/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **76/103**, with27 pending; these are local interface checks, not76 official passes. [Arbitrary even-theta rigidification](challenges/arbitrary-rigidification/README.md) adds full original094 over every original rational algebra; [geometric component cusp bound](challenges/component-cusp/README.md) adds full original029 for the actual compactified level base and each irreducible component. Full key/naturality053054, key Tate055 and even-point evaluation099 remain covered. Exact original recovery, target/semantic/standard-axiom audits and actual four-root build487 passed. Both new Challenges meet official hard caps. [Latest coverage](docs/audit/rigidification-cusp-integration-487/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete arbitrary rigidification484 and component cusp485 add full original094/029. Original094 retains arbitrary universe u, all rational algebras, actual ideal/dual/curry/zeroScheme and unique rigidification, with no reducedness or Noetherianity hypothesis. Original029 retains its full actual Legendre atlas/sign quotient/compatibility/compactification constructors, irreducible component and actual boundary cusps, finite/nonempty/embedding and exact numerical bound. Challenges627lines/41768bytes and467lines/32559bytes,16 targets each;161/280 semantic definitions match. Exact original theorem recovery and all target/standard-axiom checks pass. Actual shared four-root build487 passed{r['seconds']:.2f}s using valid caches, unchanged inputs. Independent coverage76/103,27pending; official verification remains pending. See docs/audit/rigidification-cusp-integration-487/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('094','arbitrary even-theta rigidification484'),('029','geometric component cusp bound485')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual four-root build487 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('76/103 independent interfaces integrated,27pending; no new official pass.')
