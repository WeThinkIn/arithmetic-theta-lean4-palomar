from pathlib import Path
import datetime, hashlib, json, re, shutil
p=Path(__file__).resolve().parent; w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'01','Solution':'02','ChallengeAudit':'01','SolutionAudit':'01','DefinitionCompatibility':'01','OriginalBridgeAudit':'03'}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==v for f,v in inputs.items())
assert len(re.findall(r'\bsorry\b',(p/'Challenge.lean').read_text()))==2
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
cfg=json.loads((p/'comparator.json').read_text());cfg.update(challenge_module='Challenge',solution_module='Solution',permitted_axioms=['propext','Classical.choice','Quot.sound'])
(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
counts={}
for n in ['Challenge','Solution']:
    m=re.search(r'AUDIT checked=(\d+) propagated_holes=(\d+) project_imports=(\d+)',(p/f'{n}Audit-check-01.log').read_text());assert m
    counts[n]=dict(zip(['declarations','propagated_holes','project_imports'],map(int,m.groups())))
assert counts['Solution']['propagated_holes']==0 and counts['Challenge']['project_imports']==0
review='''# Actual dual and evaluation correspondence

This support package retains the actual natural-family presheaf internal Hom, its tensor adjunction, and the sheafification/localization monoidal closed structure. Scheme.Modules.dual is literally internal Hom into the structure sheaf. The ideal module is the kernel of the actual ideal subscheme map; its dual section is the curry of the actual ideal inclusion. No arbitrary dual object, scalar surrogate or invertibility hypothesis is substituted.

The global-section-to-morphism additive equivalence is characterized uniquely by evaluation on every local section over every open. The evaluation on the right uses the actual categorical counit applied to the actual tensor of sections. The Solution proves existence and uniqueness, equality to the original ihomGlobalSectionsEquiv, and equality of its inverse on every morphism. This gives the required bridge for the actual theta evaluation section without copying unrelated restriction proofs from the 1110-line source module.

Two support targets are explicitly selected: SheafOfModules.presheafW_isMonoidal and canonicalGlobalSectionsEquiv. Their proof holes propagate into monoidal/dual definitions in the Challenge, which is expected and audited. The Solution imports the original first theorem and proves the second. ChallengeAudit checks all266 declarations and finds111 propagated sorry closures; SolutionAudit checks8 new declarations with no sorry. DefinitionCompatibility compares88 non-Proposition declarations, including available bodies. OriginalBridgeAudit compares121 named declaration types/universes and their original/Solution axiom closures, excluding compiler-generated ._proof_ names because those depend on compilation context; all generated Challenge declarations are still covered by ChallengeAudit. Only propext, Classical.choice and Quot.sound occur on the Solution/original side.

Challenge525lines, Solution57lines. Both compile with Lean4.35.0-rc2. Initial Solution failure was only an incorrect U.unop projection, corrected to U. Bridge-audit attempts01/02 record a counter type annotation issue and a generated-private-proof-name mismatch; final03 checks the stated121 named declarations and succeeds. These failed attempts are preserved.

This is reusable support, not a completed original endpoint, official comparator acceptance, independent external scope review or whole-paper verification. Original053/054 still require full combined key and naturality interfaces within the official source budget. Local independent endpoint coverage remains70/103.
'''
(p/'Review.md').write_text(review)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'actual dual and canonical evaluation support locally checked','new_endpoint_credit':0,'official_pass':False,'checks':checks,'audit_counts':counts,'semantic_declarations_compatible':88,'named_declaration_types_and_closures_checked':121,'support_targets':cfg['theorem_names'],'input_bindings_unchanged':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n')
dest=w/'project/docs/audit/actual-dual-evaluation-465';assert not dest.exists();dest.mkdir()
for f in p.iterdir():
    if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.log']:shutil.copyfile(f,dest/f.name)
print(json.dumps({'frozen':str(p),'published_source_directory':str(dest),'audit_counts':counts,'new_endpoint_credit':0}))
