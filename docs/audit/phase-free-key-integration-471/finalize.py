from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;w=p.parent.parent;b=w/'evidence/phase-free-key-package-466'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'04','Solution':'01','ChallengeAudit':'01','SolutionAudit':'01','DefinitionCompatibility':'01','OriginalEndpointAudit':'01','TargetTypeAudit':'01','TargetHoleAudit':'01'}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
frozen=json.loads((b/'receipt.json').read_text());assert all(sha(b/f)==h for f,h in frozen['bindings'].items())
assert (p/'Solution.lean').read_bytes()==(b/'Solution.lean').read_bytes()
cfg=json.loads((p/'comparator.json').read_text());assert len(set(cfg['theorem_names']))==len(cfg['theorem_names'])==37
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())==1000 and len(c.encode())<=100*1024
rows=json.loads((p/'TargetHoleAudit-check-01.log').read_text());assert {r['name'] for r in rows}==set(cfg['theorem_names'])
actual={i for i,l in enumerate(c.splitlines(),1) if re.search(r'\bsorry\b',l)}
matched=set()
for r in rows:
    holes=actual.intersection(range(r['start'],r['end']+1));assert len(holes)==1
    assert not matched.intersection(holes);matched.update(holes);r['hole_line']=next(iter(holes))
assert actual==matched and len(actual)==37
(p/'Targets.json').write_text(json.dumps({'targets':rows,'every_literal_hole_selected_exactly_once':True},indent=2)+'\n')
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
assert 'ALL_EXPLICIT_TARGETS_CHECKED 37' in (p/'TargetTypeAudit-check-01.log').read_text()
assert 'BODIES_DEF_EQ 380' in (p/'DefinitionCompatibility-check-01.log').read_text()
counts={}
for n in ['Challenge','Solution']:
    m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
    counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Challenge']['project_imports']==0 and counts['Solution']['propagated_holes']==0
scope={'covered_original_endpoint_ids':['accepted-052','accepted-053','accepted-054','accepted-095','accepted-096','accepted-097'],'new_original_endpoint_ids':['accepted-053','accepted-054'],'universe':'Original arbitrary universe u','target_count':37,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['All original marked tests, multiplier laws, and cotangent/alpha nonvacuity witnesses','Actual even-point kernel ideal, ideal module, internal-Hom dual and curried canonical section','Actual theta pushforward, adjunction evaluation, evaluation section and tensor square','Every original rigidification and uniquely normalized key isomorphism','Arbitrary pointed Cartesian base change, even-point compatibility, actual cotangent and multiplier maps','Full alpha-section equality and complete key-morphism equality','Unique actual evaluation-compatible inverse-square comparison']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
inputs={str(b/f):sha(b/f) for f in ['Challenge.lean','Solution.lean','receipt.json','comparator.json','DependencyProbe-check-01.log']}
inputs[str(w/'project/docs/SourceObligations.json')]=sha(w/'project/docs/SourceObligations.json')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Frozen complete original053054 candidate466, actual dual support465 and complete alpha descent459','source_bindings':inputs,'transformation':'Remove declarations outside the needed key closure while retaining original nonvacuity/existence supports; replace22 Proposition proof bodies with37 total explicitly compared targets; whitespace-only joining elsewhere','transformation_details':'transformation.json','semantic_definitions':'380 non-Proposition types and available bodies definitionally equal to Solution; no unspecified semantic definition_names','target_types':'All37 types/universes compared explicitly to original/Solution declarations with standard axiom closure','full_original_recovery':'Original053054 theorem equality proved by rfl; inherited052095096097 also recovered','bridges':['globalSectionsEquiv_eq_original','evaluationSection_eq_original','evaluationSquare_eq_original','isKey_iff','productComparison_eq_original','alphaNatural_iff','evaluationSquareCompatible_iff','recover_original_053','recover_original_054'],'prototype_source':'docs/audit/phase-free-key-candidate-466/Challenge.uncompressed.lean.txt'},indent=2)+'\n')
(p/'README.md').write_text('''# Complete phase-free key and naturality

Full original053/054 at arbitrary universe u, with actual theta ideal, internal-Hom dual, canonical section, pushforward evaluation and its tensor square. Every original rigidification, marked test and Cartesian comparison remains. The key is uniquely specified on the actual evaluation square; naturality retains both complete section equality and key-morphism equality, with unique evaluation-compatible comparison.

The Mathlib-only Challenge is1000lines/81891bytes. It preserves the actual semantic constructions, including the canonical global-sections equivalence fixed on every open/local vector and proved equal to the original.37 support/main propositions are explicitly selected;22 long auxiliary proofs from the oversized466 prototype are now compared as support targets. These are Solution proof obligations, not new assumptions of the main theorems. Every literal Challenge hole is selected exactly once. Solution is byte-identical to checked466 and has no sorry or nonstandard axioms.

All37 target types/universes match their Solution declarations.380 non-Proposition types and available bodies match; all678 Challenge and171 new Solution declarations pass the stated axiom audit. Full original053/054 are recovered by compiled rfl equality; inherited052095096097 are not new endpoint credit. Scope.json and SourceMap.json describe fidelity. This is local evidence; official mechanical/semantic acceptance remains pending. The preferred300line/32KiB review surface is exceeded even though the hard caps are met. The expanded source and original proof bodies remain published with466.

Attempt01 exposed an assembly delimiter bug (named arguments containing := and a where block); it failed compilation and was never integrated. A top-level delimiter parser corrected it. Attempts02/03 compiled but were over the line cap; final04 compiles at1000lines. Final source types and bodies, including every new support target, were independently checked by the supplied Lean audit programs.
''')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original053054 local interface checked within hard source caps','new_ids':['accepted-053','accepted-054'],'checks':checks,'audit_counts':counts,'target_types_checked':37,'semantic_declarations_compatible':380,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log','.template'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','stats']}))
