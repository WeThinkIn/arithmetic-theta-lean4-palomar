from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/canonical-half-lines-scope-review-507';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/canonical-half-lines-integration-508';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-507';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/compact-isogeny-alpha-integration-504/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==84
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=84,pending_count=19,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **82/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **84/103**, with 19 pending; these are local interface checks, not 84 official passes. [Compact alpha canonical half-line](challenges/compact-alpha-half-line/README.md) and [isogeny canonical half-line](challenges/isogeny-half-line/README.md) add full original042/045. Both construct the effective half-divisor, actual bounded-pole sheaf O(E), canonical section and square isomorphism, with complete theta branches on the original disks. Canonical tensor comparisons are uniquely characterized on all local sections and proved equal to the original maps. Full original recoveries, semantic/target/axiom audits and actual four-root build508 passed. [Latest coverage](docs/audit/canonical-half-lines-integration-508/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete canonical half-lines505/506 add full original042/045. On every actual compact component both construct effective E, normality witness, actual bounded-pole sheaf O(E), canonical rational-one section, invertibility and beta:O(E)^2 isomorphic to the same Hodge line carrying1_E squared to the same alpha. All-frame Scheme.ord conditions and full original disk theta branches remain. Original045 retains the exact supplied cyclic isogeny,1/m normalization and CompactRealizes with varying cusp orders; it does not impose the fixed orders from042. Every-open local tensor uniqueness identifies the comparison with the exact original at all exponents. Challenges977/988lines,82742/86253bytes;22explicit targets each. Full original theorem recovery and semantic/target/standard-axiom audits passed. Actual four-root build508 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage84/103,19pending; not84officialpasses. Supplied geometry/compact realizations and common cover construction are not newly claimed. See docs/audit/canonical-half-lines-integration-508/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('042','compact alpha canonical half-line505'),('045','isogeny canonical half-line506')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual four-root build508 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('84/103 independent interfaces integrated,19pending; no new official pass.')
