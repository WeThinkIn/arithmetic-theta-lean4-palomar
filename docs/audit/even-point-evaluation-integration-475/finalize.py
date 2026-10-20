from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;w=p.parent.parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
names=['Challenge','Solution','ChallengeAudit','SolutionAudit','DefinitionCompatibility','OriginalEndpointAudit','TargetTypeAudit','TargetHoleAudit'];checks={n:json.loads((p/f'{n}-receipt-01.json').read_text()) for n in names}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());assert len(set(cfg['theorem_names']))==len(cfg['theorem_names'])==3
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(c.encode())<=100*1024
rows=json.loads((p/'TargetHoleAudit-check-01.log').read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)};matched=set()
for r in rows:
    holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1 and not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==3
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED 3' in (p/'TargetTypeAudit-check-01.log').read_text()
compat=int(re.search(r'BODIES_DEF_EQ (\d+)',(p/'DefinitionCompatibility-check-01.log').read_text())[1]);counts={}
for n in ['Challenge','Solution']:
    m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
    counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':['accepted-099'],'new_original_endpoint_ids':['accepted-099'],'universe':'Original arbitrary universe u','target_count':3,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['Actual family, even point, order-two and avoidance conditions','Locally principal non-zero-divisor ideal invertibility and actual theta-line invertibility','Actual zeroSchemeIdeal built from all local coefficients and homomorphisms to the unit sheaf','Unique original rigidification at the identity','Actual pushforward generator is an isomorphism','Every normalized identity-evaluation map is an isomorphism','Actual generator/evaluation composite is the identity','Actual evaluation section generates the dual pushforward on every subopen']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Actual dual/evaluation support465 plus exact original Family/EvenPoint, Cartier ideal and zeroSchemeIdeal definitions','source_bindings':inputs,'semantic_definitions':f'{compat} retained non-Proposition types and available bodies match Solution','target_types':'All3 target types/universes and their standard axiom closures compared explicitly','namespace_map':{'ArithmeticThetaMultiplierKeyR0217':'ArithmeticThetaPalomarTheta473'},'evaluation_bridge':'evaluationSection_eq_original via canonical globalSectionsEquiv_eq_original','full_original_recovery':'Original099 theorem equality compiled by rfl','no_full_marking_assumption':True,'all_zero_scheme_coefficients_retained':True},indent=2)+'\n')
(p/'README.md').write_text('''# Complete actual even-point theta evaluation

Full original099 at arbitrary universe u, over every original characteristic-zero base scheme and actual even point, without assuming a chosen full marking or Miller phase. All conclusions are retained: invertibility of the actual point ideal and theta line, exact zeroSchemeIdeal equality, unique actual rigidification, isomorphism of the actual pushforward generator, and for every normalized rigidification, evaluation is an isomorphism, the generator/evaluation composite is the identity, and the actual evaluation section is a frame on every subopen.

The ideal is the kernel ideal of the actual point. Its line is the internal-Hom dual of its kernel module; the canonical section is curry of the ideal inclusion. zeroSchemeIdeal uses the actual local coefficient ideals from all local morphisms into the unit sheaf. Ideal invertibility retains non-zero-divisor generators on an affine basic-open cover. The canonical global-sections correspondence is uniquely fixed by actual categorical evaluation and proved equal to the original. No abstract line/scalar replacement is used.

Challenge imports Mathlib only and has517lines/31736bytes; Solution has91lines/8240bytes. Three targets comprise actual monoidal localization support, canonical global-sections equivalence and full099. All literal holes are selected once. The original theorem is recovered by compiled rfl equality, and the supplied audit programs check all target types/universes, semantic definition bodies and standard axiom closures. This local interface is not official acceptance; actual root build and official verification are tracked separately.
''')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original099 independent local interface checked','new_ids':['accepted-099'],'checks':checks,'audit_counts':counts,'target_types_checked':3,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
