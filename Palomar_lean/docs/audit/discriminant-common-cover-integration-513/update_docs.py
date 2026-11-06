from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/discriminant-common-cover-scope-review-512';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/discriminant-common-cover-integration-513';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-512';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/canonical-half-lines-integration-508/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==88
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=88,pending_count=15,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **84/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **88/103**, with 15 pending; these are local interface checks, not 88 official passes. [Actual component discriminant divisor](challenges/component-discriminant/README.md) adds full original030. [Discriminant twist and unique Tate root](challenges/discriminant-twist-root/README.md) adds full original032/033. [Common half-Hodge cover](challenges/common-half-hodge/README.md) adds full original034, constructing the actual finite-etale cover of positive degree at most24 with its original complete disk branch. Full normalized Kato/initial-term conditions and canonical tensor comparisons are retained. All original recoveries, semantic/target/standard-axiom audits and actual six-root build513 passed. [Latest coverage](docs/audit/discriminant-common-cover-integration-513/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete discriminant-to-common-cover interfaces509/510/511 add full original030/032/033/034. Shared IsCompactD2 retains only its original open restriction to the full all-test intrinsic normalized5-Kato initial section; no divisor or expansion premise is added.030 constructs the actual all-frame divisor2L at cusps and0 off cusps.032 constructs the actual twist multiplication and generating24th-power section;033 constructs its unique full-disk frame with the COMPLETE Euler-product normalization.034 constructs the actual component disk factorization, cusp half-line, integral smooth proper finite-etale surjective cover of positive degree at most24, square isomorphism, sameD2equation, disk lift and COMPLETE prescribed branch for every extending Hodge generator. Exact original predicates/maps and both cover-record transports are compiled. Challenges873/963/927lines and76863/87398/82267bytes;20/22/20 explicit targets;531/583/572 semantic declarations. All original recoveries and target/standard-axiom audits passed. Actual shared six-root build513 passed in {r['seconds']:.2f}s with valid dependency caches and unchanged bindings. Coverage88/103,15pending; not88officialpasses. Matrix-family assembly and official acceptance remain incomplete. See docs/audit/discriminant-common-cover-integration-513/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('030','actual component discriminant divisor509'),('032','discriminant twist unit510'),('033','unique designated discriminant Tate root510'),('034','common half-Hodge cover511')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual six-root build513 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('88/103 independent interfaces integrated,15pending; no new official pass.')
