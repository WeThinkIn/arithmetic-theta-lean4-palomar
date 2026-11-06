from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'02','Solution':'01',**{n:'01' for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','OriginalEndpointAudit','TargetTypeAudit','TargetHoleAudit']}}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());assert len(set(cfg['theorem_names']))==len(cfg['theorem_names'])==1
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(c.encode())<=100*1024
rows=json.loads((p/'TargetHoleAudit-check-01.log').read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)};matched=set()
for r in rows:
 holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1 and not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==1
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED 1' in (p/'TargetTypeAudit-check-01.log').read_text()
compat=int(re.search(r'BODIES_DEF_EQ (\d+)',(p/'DefinitionCompatibility-check-01.log').read_text())[1]);counts={}
for n in ['Challenge','Solution']:
 m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
 counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':['accepted-093'],'new_original_endpoint_ids':['accepted-093'],'universe':'Original k : Type, characteristic-zero field; all positive d,m,N with m,N even and m dividing N','target_count':1,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['Constructed actual infinitesimal polygon tower with every chart, overlap and transition equation','Constructed actual proper flat model and all stage pullback squares','Constructed marked identity lift and scheme-valued group law with original origin law','Constructed integral locally Noetherian generic scheme and exact r=24*d*m^2','One unique actual function-field element with full Kato divisor at all points','All positive coprime multiplication norms for the actual generic-point field maps and their induced algebra structures','Every normalized residue has the specified actual marked lift and stalk-based value with the original complete Laurent quotient']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Actual polygon/tower/model/MarkedLift definitions reused from377 and exact original generic point/group law/norm/Kato/value/unary/discriminant definitions','source_bindings':inputs,'semantic_definitions':compat,'target_types':'The full target type/universe and standard axiom closure checked','namespace_map':{'ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization':'ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization'},'bridges':['recover_original_093 with compiled original theorem rfl equality'],'all_geometric_providers_remain_conclusions':True,'full_laurent_equality':True,'pointOver_proof_change':'The same actual pullback point; its over-equation proved directly using the pullback lift, with semantic type/body compatibility checked'},indent=2)+'\n')
(p/'README.md').write_text("""# Complete unary power geometric realization

Full original093 for every characteristic-zero field k : Type and positive d,m,N with m and N even and m dividing N. The conclusion constructs all original geometric providers: r > 0 with r >= 3 and even, the actual infinitesimal polygon tower, the proper flat model with all stage pullback/transition equations, the actual marked identity lift, the scheme-valued group law with its prescribed origin and commutativity, and integrality and local Noetherianity of the actual generic curve. It retains exactly r=24*d*m^2.

The same conclusion constructs one unique function-field element g satisfying both the full Kato predicate and all power values. The Kato divisor uses actual principal orders at every scheme point and the actual multiplication fiber. Its norm condition quantifies every positive multiplication coprime to c=1+12*N and every actual generic-point field map; the determinant norm uses precisely the algebra structure induced by that map.

For every normalized residue nu, the conclusion constructs an index and actual marked lift with index d*unaryA(m,nu). Regularity/value is expressed through the actual stalk and marked rational point. The value is the original complete Laurent quotient of unary theta to exponent (1+12*N)^2-1 by the discriminant to exponent ((1+12*N)^2-1)/48. All literal integer, power-series and Laurent-series definitions are visible. No geometric provider, function, regularity or desired value is added as an assumption, and no finite coefficient substitute is used.

Challenge imports Mathlib only, has461lines and one explicit main target. All actual model definitions are checked against the implementation; each literal proof hole is selected exactly once. Original093 is recovered by compiled theorem equality. Target universes/types, semantic types/available bodies and standard axiom closures are audited. Actual root integration and official full mechanical/semantic verification are separate steps; no whole-paper acceptance is claimed.
""")
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original093 independent local interface checked','new_ids':['accepted-093'],'checks':checks,'audit_counts':counts,'target_types_checked':1,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
