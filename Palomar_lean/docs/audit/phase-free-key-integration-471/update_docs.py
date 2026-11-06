from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/compact-key-surface-469';review=w/'evidence/phase-free-key-scope-review-470';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'];assert all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/phase-free-key-integration-471';assert not out.exists();out.mkdir()
for n in ['acceptance.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-80:])+'\n')
for f in source.iterdir():
    if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt','.template']:shutil.copyfile(f,out/f.name)
dest=out/'scope-review-470';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/phase-free-alpha-descent-integration-461/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
f=project/'challenges/phase-free-key/Scope.json';scopes['phase-free-key']=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==72
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=72,pending_count=31,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **70/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **72/103**, with31 pending; these are local interface checks, not72 official passes. The [complete phase-free key and naturality interface](challenges/phase-free-key/README.md) adds full original053/054, retaining actual theta ideal/dual/evaluation, every rigidification and arbitrary pointed Cartesian base change. All37 target types,380 semantic definitions, original theorem recovery and actual root build471 pass. Challenge1000lines/81891bytes meets the official hard caps. [Audit and source review](docs/audit/phase-free-key-integration-471/scope-review-470/Review.md). The earlier oversized466 candidate is preserved as historical evidence.'
f.write_text(s[:start]+text+s[end:])
summary='Complete phase-free key/naturality469/470/471 adds original053054 at arbitrary universe u, with actual theta ideal, internal-Hom dual, canonical section, pushforward evaluation and tensor square, all rigidifications, full alpha equality and key-morphism naturality.37 support/main targets are explicit; all target types/universes/axioms and380 semantic definitions match, and original053054 recover by rfl. Actual two-root build471 passed39.76s with unchanged bindings and valid dependency-cache reuse. Prepared independent coverage is72/103,31pending; inherited052095096097 are not recounted. Official verification remains pending. See docs/audit/phase-free-key-integration-471/coverage.json.'
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
    f=project/rel;s=f.read_text()
    if rel=='docs/Coverage.md':
        lines=s.splitlines()
        for i,line in enumerate(lines):
            if line.startswith(('| accepted-053 |','| accepted-054 |')):
                a=line.split('|');a[-2]=' complete independent key/naturality interface469; original full statements recovered, all37 target types and actual root build471 passed; official verification pending ';lines[i]='|'.join(a)
        s='\n'.join(lines)+'\n'
    f.write_text(s+'\n'+summary+'\n')
print('Actual root integration complete:72/103 local independent interfaces,31pending; no new official pass.')
