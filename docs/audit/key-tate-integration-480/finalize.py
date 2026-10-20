from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'04','Solution':'02',**{n:'01' for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','OriginalEndpointAudit','TargetTypeAudit','TargetHoleAudit']}}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());assert len(set(cfg['theorem_names']))==len(cfg['theorem_names'])==34
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(c.encode())<=100*1024
rows=json.loads((p/'TargetHoleAudit-check-01.log').read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)};matched=set()
for r in rows:
 holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1 and not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==34
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED 34' in (p/'TargetTypeAudit-check-01.log').read_text()
compat=int(re.search(r'BODIES_DEF_EQ (\d+)',(p/'DefinitionCompatibility-check-01.log').read_text())[1]);counts={}
for n in ['Challenge','Solution']:
 m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
 counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':['accepted-055'],'new_original_endpoint_ids':['accepted-055'],'universe':'Original k : Type, universe zero; every positive N divisible by four','target_count':34,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['Full original TateLevel and full N marking with explicit reduction fixing both quarter-level points','Every actual TateTest with Cartesian, zero, multiplication and marking equations','Actual conormal-to-Hodge derivative on the canonical inclusion-compatible identity ideal comparison','Both actual tensor pullbacks and the actual multiplier sheaf/frame','The same supplied key and identity evaluation square','Frame conclusion and full Laurent equality with integral order zero or N/4','Every canonical marking has precisely the specified theta(t^(N/2)) squared coefficient']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Full key469 semantic model, full Tate/boundary445 definitions, exact original KeyTateDefinitionsR0220; original TateTest structure retained','source_bindings':inputs,'semantic_definitions':f'{compat} retained non-Proposition types and available bodies match Solution','target_types':'All34 target types/universes and standard axiom closures checked','namespace_map':{'ArithmeticThetaKeyTateR0220':'ArithmeticThetaPalomarKeyTate478 (product/expansion only; original TateTest retained)','ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection':'ArithmeticThetaPalomarAffineHodge478','ArithmeticThetaBoundaryHodgeR0182':'ArithmeticThetaPalomarBoundary445'},'bridges':['idealIso_eq_original by unique inclusion-compatible comparison','hodgeIso_eq_original by canonical conormal map equality','productAt_eq_original by canonical tensor comparisons on all local pure tensors','evaluationSquare_eq_original from key466 support','recover_original_055 and compiled original theorem rfl equality'],'no_laurent_truncation':True,'no_compactification_extension_claim':True},indent=2)+'\n')
(p/'README.md').write_text('''# Complete phase-free key Tate normalization

This interface covers full original055, for the original characteristic-zero field k : Type and every positive N divisible by four. It retains the supplied full Tate N marking, its level-four reduction fixing both quarter-level points, all Cartesian/zero/multiplication/marking equations of each actual Tate test, the same supplied key and its actual identity evaluation square, both tensor pullbacks, and the actual pulled multiplier sheaf and frame.

The conormal-to-Hodge isomorphism is fixed by the unique inclusion-compatible identity-ideal comparison and the canonical conormal derivative. The tensor comparison is fixed on every local pure tensor. Both comparisons are proved equal to the original constructions; no arbitrary isomorphism or scalar substitute is introduced. The conclusion retains the frame assertion, full Laurent-series equality, integral order zero or N/4, and the exact canonical theta(t^(N/2)) squared coefficient for every canonical marking. This endpoint does not assert arbitrary compactification extension.

Challenge imports Mathlib only. It has982lines/86950bytes and34 explicit support/main proposition targets, each selected once. Solution has632lines/68368bytes. Actual structure definitions are retained; support proofs are proved in Solution. The initial1216line surface was reduced by constructor-aware removal of unrelated naturality data/conclusions and token-preserving line joining. No definition body, main hypothesis or original conclusion was weakened. Original055 is recovered by compiled theorem equality. The scripts audit target universes/types, retained semantic definition bodies and standard axiom closures.

These are local checks. Actual root integration and official full mechanical/semantic verification are separately tracked; no whole-paper acceptance is claimed.
''')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original055 independent local interface checked','new_ids':['accepted-055'],'checks':checks,'audit_counts':counts,'target_types_checked':34,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
