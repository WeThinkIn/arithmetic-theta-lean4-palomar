from pathlib import Path
import json,hashlib,re,ast,datetime
p=Path(__file__).resolve().parent;w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'01','Solution':'03','ChallengeAudit':'01','SolutionAudit':'02','OriginalEndpointAudit':'02','DefinitionCompatibility':'02'}
checks={n:json.loads((p/(n+'-receipt-'+a+'.json')).read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/(n+'.lean')) for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
tree=ast.parse((w/'evidence/period-one-scope-review-409/review_static.py').read_text());ns={};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tokens'],type_ignores=[]),'tokens','exec'),ns)
for n in ['Challenge','Solution']:assert ns['tokens']((p/(n+'.lean')).read_text())==ns['tokens']((p/(n+'.uncompressed.lean.txt')).read_text())
assert not any(t in ['sorry','admit','axiom'] for t in ns['tokens']((p/'Solution.lean').read_text()))
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(re.findall(r'\bsorry\b',c))==11
cfg=json.loads((p/'comparator.json').read_text());assert len(cfg['theorem_names'])==11
for n in cfg['theorem_names']:assert 'theorem '+n.split('.')[-1] in c
counts={}
for n in ['Challenge','Solution']:
 s=(p/(n+'Audit-check-'+attempts[n+'Audit']+'.log')).read_text();m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',s);assert m;counts[n]={'declarations':int(m[1]),'propagated_holes':int(m[2]),'project_imports':int(m[3])}
assert counts['Challenge']['project_imports']==0 and counts['Challenge']['propagated_holes']>=11 and counts['Solution']['propagated_holes']==0
compat_log=(p/'DefinitionCompatibility-check-02.log').read_text()
compat_count=int(re.search(r'BODIES_DEF_EQ (\d+)',compat_log)[1])
assert compat_count>=199
scope={'covered_original_endpoint_ids':['accepted-096','accepted-095','accepted-097','accepted-052'],'new_original_endpoint_ids':['accepted-096'],'universe':'Original arbitrary universe u', 'target_count':11, 'retained':['Actual sheafified binary tensor of the cotangent ideal pullback with the multiplier','Every original MarkedTest','Existence of the inclusion-compatible actual cotangent comparison on each test','Existence of the original realizing alpha on each test','Complete tensor equality for every compatible cotangent map and every realizing alpha','Canonical binary tensor comparison uniquely fixed on every local pure tensor for arbitrary modules','Unique descended global section, which is a frame on every subopen','Original IsMultiplier assumptions retained','Inherited complete052095097 unchanged'], 'no_new_main_assumptions':True,'new_endpoint_count':1,'official_verified':False,'full_paper_claimed':False}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'base':'Frozen450 full multiplier interface plus458 canonical binary tensor and concrete357 identity-ideal comparisons','semantic_compatibility':str(compat_count)+' non-proof Challenge/Solution declarations have matching types and available bodies; original predicates and tensor map separately recovered','namespace_maps':{'ArithmeticThetaPhaseFreeKeyR0219.Descends':'ArithmeticThetaPalomarAlphaDescent459.Descends','ArithmeticThetaMultiplierKeyR0217.productLine':'ArithmeticThetaPalomarAlphaDescent459.productLine','ArithmeticThetaSchemeHodgeR0205.CotangentCompatible':'ArithmeticThetaPalomarIdentity357.CotangentCompatible'},'compiled_bridges':['cotangentCompatible_iff','tensorComparison_eq_original','descends_iff','recover_original_096'],'source_bindings':inputs,'original_type_recovery':'Whole original096 recovered at arbitrary universe u; theorem equality compiled by rfl; both nonvacuity existentials and all universal test clauses retained'},indent=2)+'\n')
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
(p/'Targets.json').write_text(json.dumps({'targets':holes,'all_eleven_holes_selected_once':True},indent=2)+'\n')
(p/'README.md').write_text("""# Complete phase-free alpha descent

Independent Mathlib-only Challenge retains full original096 at arbitrary universe u: unique descended global section in the actual cotangent tensor multiplier line, and frame generation on every subopen. Descends retains every original MarkedTest, both nonvacuity existentials for the actual cotangent comparison and realizing alpha, and complete tensor equality for every such comparison and section.

The canonical binary tensor map is uniquely fixed on every local pure tensor for arbitrary modules and proved equal to the original. The cotangent comparison and full Descends predicate are recovered by compiled equivalences; full original096 has a compiled rfl theorem audit. Eleven support/main targets are explicit. Inherited052095097 are not counted twice. See receipt.json for all-declaration and definition-body checks. Local evidence is not official acceptance or whole-paper completion.
""")
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original096 independent local candidate checked','new_ids':['accepted-096'],'checks':checks,'audit_counts':counts,'challenge_solution_semantic_declarations_compatible':compat_count,'original_full_type_recovered':True,'original_maps_and_predicates_recovered':True,'lexical_formatting_equivalence':True,'input_bindings_unchanged':True,'stats':{n:{'lines':len((p/(n+'.lean')).read_text().splitlines()),'bytes':(p/(n+'.lean')).stat().st_size,'sha256':sha(p/(n+'.lean'))} for n in ['Challenge','Solution']},'official_pass':False}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','stats']}))
