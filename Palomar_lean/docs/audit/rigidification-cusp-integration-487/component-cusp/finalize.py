from pathlib import Path
import datetime,hashlib,json,re
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'02','Solution':'01',**{n:'01' for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','OriginalEndpointAudit','TargetTypeAudit','TargetHoleAudit']}}
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
scope={'covered_original_endpoint_ids':['accepted-029'],'new_original_endpoint_ids':['accepted-029'],'universe':'Original k : Type, algebraically closed characteristic-zero field; every even L >= 3','target_count':16,'no_added_main_assumptions':True,'official_verified':False,'full_paper_claimed':False,'retained':['Actual projective Weierstrass model, full marking and represented level scheme','Actual Legendre atlas, free simultaneous-sign action, quotient with full orbit relation and universal property','Exact compatible two-marking locus and quotient','Actual dense open inclusion into smooth proper projective compactification with closed embedding','Actual irreducible component containing every supplied x','Actual boundary complement and cusp subtype','Finite and nonempty cusps, injection into signed primitive pairs, exact 2*L*card inequality against SL2(ZMod L)']}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'basis':'Constructor-aware original029 closure483; exact model/atlas/compatibility/compactification definitions copied from originals','source_bindings':inputs,'semantic_definitions':compat,'target_types':'All16 target types/universes and standard axiom closures checked','namespace_map':{'ArithmeticThetaComponentDegreeR0184':'ArithmeticThetaPalomarComponent485'},'bridges':['componentOpen_eq_original by equality of the actual irreducible-component carrier','recover_original_029 with compiled original theorem rfl equality'],'projectivity_fields_retained':True,'sign_quotient_universal_property_retained':True,'no_extra_proper_components_due_to_dense_open':True},indent=2)+'\n')
(p/'README.md').write_text("""# Complete geometric component cusp bound

Full original029 for every algebraically closed characteristic-zero field k : Type, every even L >= 3, every original compatible LevelData and its original compactification, and every point x on that compactification. The conclusion retains all four clauses: actual cusps are finite and nonempty, embed into signed primitive pairs, and satisfy the exact inequality 2*L*card(cusps) <= card(SL2(ZMod L)).

The Challenge spells out the actual projective Weierstrass model, scheme-valued group laws, full marking and represented level scheme, Legendre atlas and its simultaneous-sign descent. The sign quotient retains finiteness, etaleness, degree two, actual orbit relation and categorical universal property. The compatible locus fixes both ordered two-marking sections and retains its represented equalizer and degree. Compactification retains the actual base map, dense open inclusion, properness, relative smooth dimension one, and a closed embedding over the base into projective space.

The component is literally irreducibleComponent x, with its openness proved as a support target, and is proved equal to the original open component. Cusps are the actual points of that component lying outside the given open base. No abstract finite-set replacement or change of numerical constants is used. The theorem has the same original given LevelData/Compactification premises; it does not itself claim their existence or a compact Hodge extension.

Challenge imports Mathlib only and has467lines, below hard limits;16 support/main proposition targets cover every literal hole once. Original029 is recovered by compiled theorem equality. Target universes/types/standard axioms and retained semantic definition bodies are audited. Local compilation and root integration are distinct from official full mechanical/semantic acceptance; no whole-paper completion is claimed.
""")
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original029 independent local interface checked','new_ids':['accepted-029'],'checks':checks,'audit_counts':counts,'target_types_checked':16,'semantic_declarations_compatible':compat,'all_holes_selected_exactly_once':True,'full_original_theorem_equality_audit_passed':True,'no_new_main_assumptions':True,'stats':{n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']},'official_pass':False,'actual_root_build_pending':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','semantic_declarations_compatible','stats']}))
