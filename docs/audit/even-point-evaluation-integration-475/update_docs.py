from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/even-point-evaluation-package-473';review=w/'evidence/even-point-evaluation-scope-review-474';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'];assert all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/even-point-evaluation-integration-475';assert not out.exists();out.mkdir()
for n in ['acceptance.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-80:])+'\n')
for f in source.iterdir():
    if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,out/f.name)
dest=out/'scope-review-474';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/phase-free-key-integration-471/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
f=project/'challenges/even-point-evaluation/Scope.json';scopes['even-point-evaluation']=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==73
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=73,pending_count=30,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **72/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **73/103**, with30 pending; these are local interface checks, not73 official passes. [Complete key/naturality](challenges/phase-free-key/README.md) adds full original053/054; [actual even-point theta evaluation](challenges/even-point-evaluation/README.md) adds full099, including exact zero-scheme ideal, unique rigidification, generator/evaluation isomorphisms and frame generation on every subopen. All original types and semantic bridges recover exactly, standard-axiom audits pass, and actual root builds471/475 pass. Both Challenges meet official hard caps. [Latest coverage](docs/audit/even-point-evaluation-integration-475/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary='Complete actual even-point theta evaluation473/474/475 adds original099 at arbitrary universe u, without a full-marking or phase assumption. Actual kernel ideal/dual line/canonical section/pushforward/evaluation and all zero-scheme coefficients retained; invertibility, exact zero ideal, unique rigidification, generator/evaluation isomorphisms, composite identity and frame generation on every subopen are conclusions. All3 target types/universes,163 semantic definitions, standard axioms and original099 rfl recovery pass. Actual root build475 passed36.96s using valid caches with unchanged bindings. Prepared independent coverage is73/103,30pending; official verification remains pending. See docs/audit/even-point-evaluation-integration-475/coverage.json.'
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
    f=project/rel;s=f.read_text()
    if rel=='docs/Coverage.md':
        lines=s.splitlines()
        for i,line in enumerate(lines):
            if line.startswith('| accepted-099 |'):
                a=line.split('|');a[-2]=' complete independent actual even-point evaluation473; all original conclusions recovered, target/semantic/axiom checks and actual root build475 passed; official verification pending ';lines[i]='|'.join(a)
        s='\n'.join(lines)+'\n'
    f.write_text(s+'\n'+summary+'\n')
print('Actual root integration complete:73/103 local independent interfaces,30pending; no new official pass.')
