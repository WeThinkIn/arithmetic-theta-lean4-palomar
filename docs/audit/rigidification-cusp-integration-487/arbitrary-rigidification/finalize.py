from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'01','Solution':'02',**{n:'01' for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','OriginalEndpointAudit','TargetTypeAudit','TargetHoleAudit']}}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());assert len(set(cfg['theorem_names']))==len(cfg['theorem_names'])==16
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(c.encode())<=100*1024
rows=json.loads((p/'TargetHoleAudit-check-01.log').read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)};matched=set()
for r in rows:
 holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1 and not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==16
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED 16' in (p/'TargetTypeAudit-check-01.log').read_text()
compat=int(re.search(r'BODIES_DEF_EQ (\d+)',(p/'DefinitionCompatibility-check-01.log').read_text())[1]);counts={}
for n in ['Challenge','Solution']:
 m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
 counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':['accepted-094'],'new_original_endpoint_ids':['accepted-094'],'universe':'Original arbitrary universe u; every commutative rational algebra, including nonreduced and empty affine bases','target_count':16,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['Actual projective Weierstrass curve and its scheme-valued group law','Full level-four marking with exact torsion and avoidance predicates','Actual marked even point and its kernel ideal','Ideal invertibility by affine non-zero-divisor generators','Actual internal-Hom dual line, canonical curry section and exact zeroSchemeIdeal','Unique normalized identity rigidification']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Actual internal-Hom/ideal/zeroScheme definitions from473 and exact projective model/full marking from469','source_bindings':inputs,'semantic_definitions':compat,'target_types':'All16 target types/universes and standard axiom closures checked','namespace_map':{'ArithmeticThetaThetaEvaluationR0212':'ArithmeticThetaPalomarRigidification484'},'bridges':['thetaMap_eq_original via original fromSection/ihom/curry identity','isRigidification_iff','recover_original_094 with compiled original theorem rfl equality'],'no_reduced_or_noetherian_assumption':True,'no_pointwise_zero_set_replacement':True},indent=2)+'\n')
(p/'README.md').write_text("""# Complete arbitrary even-theta rigidification

Full original094 at arbitrary universe u, for every commutative rational algebra and elliptic Weierstrass curve, the original scheme-valued group law with IsOriginLaw, and every full level-four marking. No reducedness, Noetherianity, normality or nonempty-base condition is added.

The even point is the sum of the two half-level labels. Its ideal is the actual kernel ideal; its line is the actual internal-Hom dual of the ideal module. The canonical curry section is proved equal to the original section-to-morphism construction. The conclusion retains invertibility of both ideal and line, equality of the full coefficient-based zeroSchemeIdeal with the point ideal, and existence and uniqueness of the identity rigidification with prescribed canonical value one.

Challenge imports Mathlib only, with627lines/41768bytes and16 explicit support/main proposition targets. Each hole is selected once. Original094 is recovered by compiled theorem equality; semantic definition types/available bodies and target universes/types/standard axioms are audited. These local checks are separate from actual root integration and official full mechanical/semantic acceptance. No whole-paper completion is claimed.
""")
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original094 independent local interface checked','new_ids':['accepted-094'],'checks':checks,'audit_counts':counts,'target_types_checked':16,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
