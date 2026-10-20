from pathlib import Path
import json,hashlib,re,ast,datetime
p=Path(__file__).resolve().parent;w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'01','Solution':'02','ChallengeAudit':'01','SolutionAudit':'01','OriginalEndpointAudit':'01','DefinitionCompatibility':'01'}
checks={n:json.loads((p/(n+'-receipt-'+a+'.json')).read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/(n+'.lean')) for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==h for f,h in inputs.items())
tree=ast.parse((w/'evidence/period-one-scope-review-409/review_static.py').read_text());ns={};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tokens'],type_ignores=[]),'tokens','exec'),ns)
for n in ['Challenge','Solution']:assert ns['tokens']((p/(n+'.lean')).read_text())==ns['tokens']((p/(n+'.uncompressed.lean.txt')).read_text())
assert not any(t in ['sorry','admit','axiom'] for t in ns['tokens']((p/'Solution.lean').read_text()))
c=(p/'Challenge.lean').read_text();assert len(c.splitlines())<=1000 and len(re.findall(r'\bsorry\b',c))==7
cfg=json.loads((p/'comparator.json').read_text());assert len(cfg['theorem_names'])==7
for n in cfg['theorem_names']:assert 'theorem '+n.split('.')[-1] in c
counts={}
for n in ['Challenge','Solution']:
 s=(p/(n+'Audit-check-01.log')).read_text();m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',s);assert m;counts[n]={'declarations':int(m[1]),'propagated_holes':int(m[2]),'project_imports':int(m[3])}
assert counts['Challenge']['project_imports']==0 and counts['Challenge']['propagated_holes']>=7 and counts['Solution']['propagated_holes']==0
assert 'CHALLENGE_SOLUTION_SEMANTIC_TYPES_AND_AVAILABLE_BODIES_DEF_EQ 199' in (p/'DefinitionCompatibility-check-01.log').read_text()
scope={'covered_original_endpoint_ids':['accepted-052'],'universe':'Original arbitrary universe u retained','target_count':7,'retained':['actual arbitrary elliptic scheme family and full level4 marking','same actual global Miller phase','actual cotangent sheaf as pullback of the kernel ideal','same inclusion-normalized ideal comparison and actual pointed-square pullback','canonical conormal map uniquely fixed on all ideal sections on all opens','canonical differential map uniquely fixed on every local universal derivative','actual Z-chart equation dx=(2y+a1*x+a3)delta','full affine root data with coordinate existence and unit coefficient','every matrix preserving the original even quadratic form','constructed changed actual full marking, unchanged phase, exact original characterExponent equality for every realizing section'],'support_nonvacuity':['normalized differential frames exist','canonical conormal map exists uniquely','actual global realizing alpha exists uniquely'],'no_new_main_assumptions':True,'new_endpoint_count':1,'official_verified':False,'full_paper_claimed':False}
(p/'Scope.json').write_text(json.dumps(scope,indent=2)+'\n')
(p/'SourceMap.json').write_text(json.dumps({'base':'Exact geometry/marking/Miller normalization definitions from433, excluding field-pairing-only definitions unused by052','canonical_maps':'401 canonical differential map and436 canonical conormal map uniquely characterized on actual local derivatives; all their proof obligations selected','semantic_compatibility':'199 non-proof declarations have definitionally equal Challenge/Solution types and available bodies; original-map identities and original RealizesAlpha iff are separately proved','namespace_maps':{'ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha':'ArithmeticThetaPalomarSchemeAlpha437.RealizesAlpha','ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha':'ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha','ArithmeticThetaSchemeHodgeR0205.Cotangent':'ArithmeticThetaPalomarSchemeAlpha437.Cotangent'},'compiled_bridges':['affineAlpha_iff','idealCompatible_iff','affineHodgeMap_eq','affineAlpha_eq','realizesAlpha_iff','recover_original_052'],'source_bindings':inputs,'original_type_recovery':'Whole original052 recovered by realizesAlpha_iff in both directions; original theorem equality compiled by rfl; original universe u retained'},indent=2)+'\n')
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
(p/'Targets.json').write_text(json.dumps({'targets':holes,'all_seven_holes_selected_once':True},indent=2)+'\n')
(p/'README.md').write_text('''# Complete scheme alpha character

Independent Mathlib-only Challenge for complete original accepted-052 at arbitrary universe u. Retains the same global Miller phase, actual cotangent and ideal inclusion, canonical pointed pullback and conormal derivative, whole Z-chart differential normalization, and actual full-marking character for every even-stabilizer matrix. Independent uniqueness specifications determine both canonical maps; compiled identities recover the original maps. The global alphaExists support target prevents a vacuous premise. No reducedness, nonemptiness or normality is added to the main scheme statement.

Challenge732lines, Solution257lines. All349 Challenge and85 Solution declarations were audited;16 propagated sorry closures originate from seven selected support/main targets. Solution has only standard axioms.199 non-proof declarations agree between Challenge and Solution; full original052 is recovered through separately proved affine/global predicate equivalences, with a compiled rfl original-theorem audit. This is local evidence, not official Palomar acceptance or full-paper completion.
''')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'complete original052 independent local candidate checked','new_ids':['accepted-052'],'checks':checks,'audit_counts':counts,'challenge_solution_semantic_declarations_compatible':199,'original_full_type_recovered':True,'original_maps_and_predicates_recovered':True,'lexical_formatting_equivalence':True,'input_bindings_unchanged':True,'stats':{n:{'lines':len((p/(n+'.lean')).read_text().splitlines()),'bytes':(p/(n+'.lean')).stat().st_size,'sha256':sha(p/(n+'.lean'))} for n in ['Challenge','Solution']},'official_pass':False}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','audit_counts','stats']}))
