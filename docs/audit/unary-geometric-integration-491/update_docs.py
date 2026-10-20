from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/unary-geometric-scope-review-490';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/unary-geometric-integration-491';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-490';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/rigidification-cusp-integration-487/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==77
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=77,pending_count=26,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **76/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **77/103**, with 26 pending; these are local interface checks, not 77 official passes. [Complete unary power geometric realization](challenges/unary-geometric/README.md) adds full original093: actual polygon tower, proper flat model, identity and group law, and a unique Kato function with the complete divisor, all original coprime norms and marked-point Laurent values. Original hypotheses and constructions are retained. Exact original recovery, target/semantic/standard-axiom audits and the actual two-root build491 passed. The Challenge meets official hard caps. [Latest coverage](docs/audit/unary-geometric-integration-491/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete unary power geometric realization489 adds full original093. The original characteristic-zero field and positive d,m,N, evenness and divisibility hypotheses are unchanged. The conclusion constructs the actual polygon tower, proper flat model, marked identity, original group law, integral locally Noetherian generic scheme and exact r=24*d*m^2, and one unique actual function-field element with full Kato divisor, every original positive coprime norm and every original normalized residue with actual marked lift, stalk regularity/value and complete Laurent quotient. Challenge461lines/30307bytes, Solution14lines/916bytes, one explicit main target;148 semantic declarations match. Exact original theorem recovery and all target/standard-axiom checks pass. Actual shared two-root build491 passed in {r['seconds']:.2f}s using valid dependency caches, with unchanged inputs. Independent coverage77/103,26pending; official verification remains pending. This endpoint does not separately establish a compact Hodge extension. See docs/audit/unary-geometric-integration-491/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('093','unary power geometric realization489')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual two-root build491 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('77/103 independent interfaces integrated,26pending; no new official pass.')
