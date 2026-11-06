from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/matrix-geometry-scope-review-531';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/matrix-geometry-integration-532';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-531';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/field-unary-naturality-integration-527/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==98
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=98,pending_count=5,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **94/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **98/103**, with 5 pending; these are local interface checks, not 98 official passes. [Sharp matrix geometry and cutoff](challenges/sharp-matrix-geometry/README.md) and [conservative matrix geometry and cutoff](challenges/conservative-matrix-geometry/README.md) add full original035/036/047/048. For EVERY arbitrary finite valid Gram family, the existence theorems construct ALL actual level/compactification/Hodge/disk/cover/frame/section data and complete theta expansions; both exact original cutoff consumers are retained. Original recoveries, semantic/target/standard-axiom audits and actual shared four-root build532 passed. [Latest coverage](docs/audit/matrix-geometry-integration-532/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete interfaces529530 add full original035036047048. Both existence theorems take ONLY positive rank/family size and EVERY arbitrary finite valid integral Gram family, and construct all arithmetic indexing/formal identities and actual level model, compactification, canonical Hodge extension, Tate disk, line, finite cover, frame, unary/matrix sections and COMPLETE theta expansions for every scalar combination. Sharp geometry retains the actual square line, etale cover of degree2^(distinctNormCount-1) and singleton-norm isomorphism; conservative geometry retains actual cusp half-divisor line and cover degree24*(exponent N)^indexCount. Both full all-frame Scheme.ord/residue-field degree predicates and EXACT original cutoff formulas remain intact. Original recoveries and all semantic/type/standard-axiom audits pass. Actual shared four-root build532 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage98/103,5pending; not98officialpasses. Remaining arithmetic common-cover, cyclotomic/extended modularity, global projective ratios and final image-consumer interfaces and full official verification/intake remain incomplete. See docs/audit/matrix-geometry-integration-532/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('035','conservative matrix geometry530'),('036','conservative geometric cutoff530'),('047','sharp matrix geometry529'),('048','sharp geometric cutoff529')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual four-root build532 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('98/103 independent interfaces integrated,5pending; no new official pass.')
