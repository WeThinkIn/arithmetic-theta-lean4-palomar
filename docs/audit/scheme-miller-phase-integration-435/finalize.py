from pathlib import Path
import json,hashlib,re,ast,datetime
p=Path(__file__).resolve().parent;w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'02','Solution':'01','ChallengeAudit':'01','SolutionAudit':'01','OriginalEndpointAudit':'01','DefinitionCompatibility':'02'}
checks={n:json.loads((p/(n+'-receipt-'+a+'.json')).read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/(n+'.lean')) for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
tree=ast.parse((w/'evidence/period-one-scope-review-409/review_static.py').read_text());ns={};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tokens'],type_ignores=[]),'tokens','exec'),ns)
for n in ['Challenge','Solution']:assert ns['tokens']((p/(n+'.lean')).read_text())==ns['tokens']((p/(n+'.uncompressed.lean.txt')).read_text())
assert not any(t in ['sorry','admit','axiom'] for t in ns['tokens']((p/'Solution.lean').read_text()))
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(re.findall(r'\bsorry\b',c))==3
cfg=json.loads((p/'comparator.json').read_text());assert len(cfg['theorem_names'])==3
for n in cfg['theorem_names']:assert 'theorem '+n.split('.')[-1] in c
counts={}
for n in ['Challenge','Solution']:
 s=(p/(n+'Audit-check-01.log')).read_text();m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',s);assert m;counts[n]={'declarations':int(m[1]),'propagated_holes':int(m[2]),'project_imports':int(m[3])}
assert counts['Challenge']['project_imports']==0 and counts['Challenge']['propagated_holes']==3 and counts['Solution']['propagated_holes']==0
assert 'SEMANTIC_TYPES_AND_AVAILABLE_BODIES_DEF_EQ 208' in (p/'DefinitionCompatibility-check-02.log').read_text()
scope={'covered_original_endpoint_ids':['accepted-051'],'universe':'Original arbitrary universe u retained','target_count':3,'retained':['arbitrary actual smooth proper geometrically connected elliptic scheme family','actual full level4 group sections and torsion disjointness','unique global regular Miller phase','unit and square-minus-one conclusions','primitive order4 conditional only on nontrivial global sections','every actual affine Weierstrass test, including nonreduced, disconnected and empty bases','existence of affine coordinates and unit-denominator normalized polynomial ratio','actual generic tangent functions and chord-formula translations','actual moved-divisor evaluation with full Laurent infinity expansion','every characteristic-zero field fiber and all local pairing data'],'nonvacuity_support':['actual local pairing data for every split cubic with distinct roots','original arbitrary-ring fiber-basis theorem with unique fiber coordinates, genuine four-torsion basis and original labels'],'new_endpoint_count':1,'official_verified':False,'full_paper_claimed':False}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'base':'Exact lower scheme/projective/law definitions from394, same public original names; no imported project module in Challenge','new_definitions':'Exact source slices in assemble.py, comment/signature formatting only','semantic_compatibility':'208 non-proof declarations: original types and available definition bodies checked definitionally equal in an environment importing only original sources and Solution; constructors included','original_type_recovery':'recover_original_051 and compiled original theorem equality by rfl; generic universe u retained','source_bindings':inputs},indent=2)+'\n')
(p/'Targets.json').write_text(json.dumps({'targets':cfg['theorem_names'],'all_three_holes_selected':True},indent=2)+'\n')
(p/'README.md').write_text('''# Complete scheme Miller phase

Independent Mathlib-only Challenge for complete original accepted-051, with the exact generic-universe statement. Retains the actual global phase and every affine test, including nilpotents and empty bases, normalized unit-denominator equations, and actual moved-divisor pairing on every field fiber. Primitive order4 remains conditional on nontrivial global sections. Two explicit support targets construct local pairing data and the original arbitrary-ring split fiber basis; no geometric-point-only replacement is made.

Challenge660lines, Solution23lines; all341 Challenge declarations and4 Solution declarations audited. The208 non-proof declarations have original definitionally equal types and available bodies. All three holes are selected once. Full original051 is recovered by a compiled rfl audit. This is a locally checked independent interface, not official Palomar acceptance or completion of052 or the paper.
''')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original051 independent local candidate checked','new_ids':['accepted-051'],'checks':checks,'audit_counts':counts,'semantic_declarations_compatible':208,'original_full_type_recovered':True,'lexical_formatting_equivalence':True,'input_bindings_unchanged':True,'stats':{n:{'lines':len((p/(n+'.lean')).read_text().splitlines()),'bytes':(p/(n+'.lean')).stat().st_size,'sha256':sha(p/(n+'.lean'))} for n in ['Challenge','Solution']},'official_pass':False}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','stats']}))
