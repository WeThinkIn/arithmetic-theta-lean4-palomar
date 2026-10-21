from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/compact-unary-split-scope-review-517';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/compact-unary-split-integration-518';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-517';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/discriminant-common-cover-integration-513/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==91
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=91,pending_count=12,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **88/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **91/103**, with 12 pending; these are local interface checks, not 91 official passes. [Actual compact unary Hodge realization](challenges/compact-unary/README.md) adds full original028, constructing the unique genuine global section with the complete unary series equation. [Split-field discriminant divisor](challenges/split-discriminant/README.md) and [split-field square-cover degree](challenges/split-square-degree/README.md) add full original073/074 over arbitrary characteristic-zero fields with the specified primitive level root. All original statement recoveries, semantic/target/standard-axiom audits and actual six-root build518 passed. [Latest coverage](docs/audit/compact-unary-split-integration-518/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete interfaces514/515/516 add full original028/073/074.028 constructs actual open normalized unary data and the UNIQUE compact global section of the same Hodge line, with the actual restriction, open frame, nonzero coefficient at every disk and COMPLETE unary power at every canonical marking and specified generator. Its record transports preserve identical objects; all predicate/comparison bridges compile.073 proves the actual intrinsicD2 divisor2L at every cusp and0 off cusps in every normal frame over arbitrary split characteristic-zero fields.074 retains the actual square line and finite flat cover and proves the full all-frame residue-field-weighted degree equation and bound, including exponent0, with no algebraic-closure premise. Challenges905/874/925lines;17/20/19 explicit targets;553/531/498 semantic definitions. All original recoveries and axiom audits pass. Actual shared six-root build518 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage91/103,12pending; not91officialpasses. Arbitrary-field unary descent, matrix-family assembly and official acceptance remain incomplete. See docs/audit/compact-unary-split-integration-518/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('028', 'actual compact unary Hodge realization514'), ('073', 'split-field component discriminant divisor515'), ('074', 'split-field square-cover degree516')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual six-root build518 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('91/103 independent interfaces integrated,12pending; no new official pass.')
