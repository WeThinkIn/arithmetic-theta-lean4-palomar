from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();meta=json.loads((p/'package-description.json').read_text());attempts=meta['attempts'];checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());count=len(cfg['theorem_names']);assert len(set(cfg['theorem_names']))==count==meta['target_count']
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(c.encode())<=100*1024
rows=json.loads((p/('TargetHoleAudit-check-'+attempts['TargetHoleAudit']+'.log')).read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)};matched=set()
for r in rows:
 holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1 and not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==count
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED '+str(count) in (p/('TargetTypeAudit-check-'+attempts['TargetTypeAudit']+'.log')).read_text()
compat=int(re.search(r'BODIES_DEF_EQ (\d+)',(p/('DefinitionCompatibility-check-'+attempts['DefinitionCompatibility']+'.log')).read_text())[1]);counts={}
for n in ['Challenge','Solution']:
 m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-{attempts[n+"Audit"]}.log').read_text());assert m
 counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':meta['ids'],'new_original_endpoint_ids':meta['ids'],'universe':meta['universe'],'target_count':count,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':meta['retained'],'limitations':meta['limitations']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':meta['basis'],'source_bindings':inputs,'semantic_definitions':compat,'target_types':'All explicit target types/universes and standard axiom closures checked','namespace_map':meta['namespace_map'],'bridges':meta['bridges']},indent=2)+'\n')
(p/'README.md').write_text('# '+meta['title']+'\n\n'+meta['description']+'\n\n'+f'Challenge has {len(c.splitlines())} lines and {count} explicit support/main targets. All {compat} semantic types/available bodies match the Solution environment, and every literal proof hole is selected exactly once. The original theorem is recovered by compiled equality; target universes/types and all Solution declaration axiom closures pass. Actual root integration and official verification are separate steps. No whole-paper acceptance is claimed.\n\n'+meta['limitations']+'\n')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':meta['title']+' independent local interface checked','new_ids':meta['ids'],'checks':checks,'audit_counts':counts,'target_types_checked':count,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
