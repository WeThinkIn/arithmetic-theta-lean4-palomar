from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/key-tate-package-478';review=w/'evidence/key-tate-scope-review-479';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'];assert all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/key-tate-integration-480';assert not out.exists();out.mkdir()
for n in ['acceptance.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-80:])+'\n')
for f in source.iterdir():
 if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,out/f.name)
dest=out/'scope-review-479';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/even-point-evaluation-integration-475/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
f=project/'challenges/key-tate/Scope.json';scopes['key-tate']=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==74
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=74,pending_count=29,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **73/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **74/103**, with29 pending; these are local interface checks, not74 official passes. [Complete key/naturality](challenges/phase-free-key/README.md) covers full original053/054; [actual even-point theta evaluation](challenges/even-point-evaluation/README.md) covers full099; [complete key Tate normalization](challenges/key-tate/README.md) adds full055, retaining the same key, actual tensor pullbacks and full Laurent normalization for every original Tate test. Exact original recovery, target/semantic/standard-axiom audits and actual root builds passed. All three Challenges meet official hard caps. [Latest coverage](docs/audit/key-tate-integration-480/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete key Tate normalization478/479/480 adds full original055 at its original universe zero, every positive N divisible by four, actual full Tate marking/reduction/test, canonical conormal-to-Hodge comparison, both actual tensor pullbacks, same key/evaluation square and full Laurent normalization including integral order zero-or-N/4 and exact canonical theta-square coefficient. Challenge982lines/86950bytes,34 selected support/main targets. All target universes/types, retained semantic bodies, standard-axiom closures and original055 rfl recovery pass. Actual named root build480 passed{r['seconds']:.2f}s using valid caches, unchanged inputs. Prepared independent coverage74/103,29pending; official verification remains pending. See docs/audit/key-tate-integration-480/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   if line.startswith('| accepted-055 |'):
    a=line.split('|');a[-2]=' complete independent key Tate normalization478; full original type recovered, target/semantic/axiom checks and actual root build480 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('Actual root integration complete:74/103 local independent interfaces,29pending; no new official pass.')
