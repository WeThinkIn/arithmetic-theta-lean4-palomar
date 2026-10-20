from pathlib import Path
import datetime,hashlib,json,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/compact-isogeny-alpha-scope-review-503';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();packages=json.loads((p/'packages.json').read_text())
r=json.loads((p/'root-build-result.json').read_text());assert r['exit_code']==0 and r['inputs_unchanged'] and all(sha(Path(f))==v for f,v in r['bindings'].items())
out=project/'docs/audit/compact-isogeny-alpha-integration-504';assert not out.exists();out.mkdir()
for n in ['acceptance.json','packages.json','root-build-result.json','root-build-bindings.json','install.py','build_root.py','update_docs.py']:shutil.copyfile(p/n,out/n)
(out/'root-build-tail.log').write_text('\n'.join((p/'root-build.log').read_text().splitlines()[-100:])+'\n')
for q in packages:
 source=w/'evidence'/q['source'];dest=out/q['slug'];dest.mkdir()
 for f in source.iterdir():
  if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log','.txt']:shutil.copyfile(f,dest/f.name)
dest=out/'scope-review-503';dest.mkdir()
for n in ['Review.md','receipt.json','review.py']:shutil.copyfile(review/n,dest/n)
previous=json.loads((project/'docs/audit/hodge-degree-cusp-integration-498/coverage.json').read_text());scopes=previous['scopes'];bindings=previous['bindings'];assert all(sha(project/f)==h for f,h in bindings.items())
for q in packages:
 f=project/'challenges'/q['slug']/'Scope.json';scopes[q['slug']]=json.loads(f.read_text())['covered_original_endpoint_ids'];bindings[str(f.relative_to(project))]=sha(f)
allids={r['id'] for r in json.loads((project/'docs/SourceObligations.json').read_text())};covered=set().union(*map(set,scopes.values()));assert len(allids)==103 and covered<=allids and len(covered)==82
coverage=dict(previous,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prepared_interface_count=82,pending_count=21,scopes=scopes,covered_ids=sorted(covered),pending_ids=sorted(allids-covered),bindings=bindings)
for f in [out/'coverage.json',p/'coverage.json']:f.write_text(json.dumps(coverage,indent=2)+'\n')
f=project/'README.md';s=f.read_text();start=s.index('Current integrated independent interface coverage is **79/103**');end=s.index('\n',start)
text='Current integrated independent interface coverage is **82/103**, with 21 pending; these are local interface checks, not 82 official passes. [Compact full-level alpha](challenges/compact-alpha/README.md) adds full original041 with a unique actual global section, all-cusp orders and complete designated theta expansion. [Isogeny alpha expansion and cusp orders](challenges/isogeny-alpha-cusps/README.md) adds full original043/044 for the same actual cyclic quotient, original differential pullback and literal1/m normalization. All original recoveries, target/semantic/standard-axiom audits and actual four-root build504 passed. [Latest coverage](docs/audit/compact-isogeny-alpha-integration-504/coverage.json).'
f.write_text(s[:start]+text+s[end:])
summary=f"Complete compact alpha501 and isogeny alpha cusps502 add full original041/043/044. Original041 constructs the unique actual global alpha section on the supplied canonical compact Hodge extension, with intrinsic restriction on all original classifying tests, all-cusp exact even orders zero or L/4, and complete theta expansion in the same normalized generator. Original043/044 retain the actual cyclic quotient, its prescribed marking, intrinsic target alpha and literal1/m differential pullback: full signed designated expansion and every-cusp kernel coordinates, mixed component/toric degrees, exact order relation and unit coefficient are conclusions. Challenge935/999lines,64689/68126bytes;16/17 explicit targets and447/501 semantic declarations checked. Original theorem rfl recovery and target/standard-axiom checks passed. Actual shared four-root build504 passed in {r['seconds']:.2f}s with valid dependency-cache reuse and unchanged inputs. Independent coverage82/103,21pending; official verification remains pending. No construction credit for supplied geometric inputs or compact half-lines. See docs/audit/compact-isogeny-alpha-integration-504/coverage.json."
for rel in ['docs/MigrationStatus.md','docs/VerificationPlan.md','docs/Coverage.md']:
 f=project/rel;s=f.read_text()
 if rel=='docs/Coverage.md':
  lines=s.splitlines()
  for i,line in enumerate(lines):
   for id,label in [('041','compact full-level alpha501'),('043','isogeny alpha designated expansion502'),('044','isogeny alpha all-cusp orders502')]:
    if line.startswith('| accepted-'+id+' |'):
     a=line.split('|');a[-2]=f' complete independent {label}; full original type recovered, target/semantic/axiom checks and actual four-root build504 passed; official verification pending ';lines[i]='|'.join(a)
  s='\n'.join(lines)+'\n'
 f.write_text(s+'\n'+summary+'\n')
print('82/103 independent interfaces integrated,21pending; no new official pass.')
