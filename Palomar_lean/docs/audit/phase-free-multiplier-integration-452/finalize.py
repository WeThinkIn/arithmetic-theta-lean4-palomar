from pathlib import Path
import json,hashlib,re,ast,datetime
p=Path(__file__).resolve().parent;w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'01','Solution':'01','ChallengeAudit':'01','SolutionAudit':'01','OriginalEndpointAudit':'01','DefinitionCompatibility':'01'}
checks={n:json.loads((p/(n+'-receipt-'+a+'.json')).read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/(n+'.lean')) for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
tree=ast.parse((w/'evidence/period-one-scope-review-409/review_static.py').read_text());ns={};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tokens'],type_ignores=[]),'tokens','exec'),ns)
for n in ['Challenge','Solution']:assert ns['tokens']((p/(n+'.lean')).read_text())==ns['tokens']((p/(n+'.uncompressed.lean.txt')).read_text())
assert not any(t in ['sorry','admit','axiom'] for t in ns['tokens']((p/'Solution.lean').read_text()))
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(re.findall(r'\bsorry\b',c))==9
cfg=json.loads((p/'comparator.json').read_text());assert len(cfg['theorem_names'])==9
for n in cfg['theorem_names']:assert 'theorem '+n.split('.')[-1] in c
counts={}
for n in ['Challenge','Solution']:
 s=(p/(n+'Audit-check-'+attempts[n+'Audit']+'.log')).read_text();m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',s);assert m;counts[n]={'declarations':int(m[1]),'propagated_holes':int(m[2]),'project_imports':int(m[3])}
assert counts['Challenge']['project_imports']==0 and counts['Challenge']['propagated_holes']>=9 and counts['Solution']['propagated_holes']==0
compat_log=(p/'DefinitionCompatibility-check-01.log').read_text()
compat_count=int(re.search(r'BODIES_DEF_EQ (\d+)',compat_log)[1])
assert compat_count>=199
scope={'covered_original_endpoint_ids':['accepted-095','accepted-097','accepted-052'],'new_original_endpoint_ids':['accepted-095','accepted-097'],'universe':'Original arbitrary universe u', 'target_count':9, 'retained':['Actual even two-torsion point on the actual scheme family','All scheme-valued MarkedTest objects with full level4 marking and pointed Cartesian multiplicative comparison','IsInvertible by actual local unit-sheaf trivializations','Frames generate on every subopen and are natural for every actual TestMap','Inverse character for every actual Miller phase and even-stabilizer marking change','Exact reversal law with original reversal matrix','Unique multiplier up to the unique frame-preserving actual sheaf isomorphism','Unique actual base-change isomorphism compatible on every relative marked test using canonical pullback composition','Inherited complete052 unchanged'], 'no_new_main_assumptions':True,'new_endpoint_count':2,'official_verified':False,'full_paper_claimed':False}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'base':'Frozen437 interface plus exact source definitions for even point, all scheme marked tests, frames and relative test comparisons','semantic_compatibility':str(compat_count)+' non-proof Challenge/Solution declarations have matching types and available bodies','namespace_maps':{},'compiled_bridges':['recover_original_095','recover_original_097','recover_original_052'],'source_bindings':inputs,'original_type_recovery':'Whole original095/097 recovered at arbitrary universe u; equality of theorems compiled by rfl'},indent=2)+'\n')
stack=[];last=None;holes=[]
for i,line in enumerate(c.splitlines(),1):
 text=line.strip();m=re.match(r'(namespace|section)\b\s*(.*)',text)
 if m:stack.append((m[1],m[2]));continue
 if text=='end' or text.startswith('end '):
  if stack:stack.pop()
  continue
 m=re.match(r'(theorem|lemma|def)\s+(\S+)',text)
 if m:last=('.'.join([v for k,v in stack if k=='namespace']+[m[2]]),i)
 if re.search(r'\bsorry\b',text):holes.append({'name':last[0],'declaration_line':last[1],'hole_line':i})
assert [h['name'] for h in holes]==cfg['theorem_names']
(p/'Targets.json').write_text(json.dumps({'targets':holes,'all_nine_holes_selected_once':True},indent=2)+'\n')
(p/'README.md').write_text("""# Complete phase-free multiplier and base change

Independent Mathlib-only Challenge retains full original095 and097 at arbitrary universe u. IsMultiplier requires an actual locally invertible sheaf, a frame on every full-marking test, naturality over every actual marked Cartesian map, inverse character for every actual Miller phase/even-stabilizer change and the exact reversal law. Multiplier existence and uniqueness up to the unique frame-preserving isomorphism are outputs. Base change has its full original universal compatibility on relative marked tests, using literal canonical pullback compositions.

Nine support/main holes are selected exactly once. Solution declarations have only standard axioms. Full original095/097 statements are recovered with compiled rfl checks. All non-proof Challenge declarations have their types and available bodies compared in the Solution environment. Inherited052 is not counted twice. This does not claim the later key, alpha descent or fourth tensor trivialization endpoints. See receipt.json for measured checks. Local evidence is not official acceptance or whole-paper completion.
""")
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original095/097 independent local candidate checked','new_ids':['accepted-095','accepted-097'],'checks':checks,'audit_counts':counts,'challenge_solution_semantic_declarations_compatible':compat_count,'original_full_type_recovered':True,'original_maps_and_predicates_recovered':True,'lexical_formatting_equivalence':True,'input_bindings_unchanged':True,'stats':{n:{'lines':len((p/(n+'.lean')).read_text().splitlines()),'bytes':(p/(n+'.lean')).stat().st_size,'sha256':sha(p/(n+'.lean'))} for n in ['Challenge','Solution']},'official_pass':False}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','stats']}))
