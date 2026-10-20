from pathlib import Path
import datetime, hashlib, json, re, shutil
p=Path(__file__).resolve().parent; w=p.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
attempts={'Challenge':'02','Solution':'02','ChallengeAudit':'01','SolutionAudit':'01','DefinitionCompatibility':'01','OriginalEndpointAudit':'01','DependencyProbe':'01'}
checks={n:json.loads((p/f'{n}-receipt-{a}.json').read_text()) for n,a in attempts.items()}
assert all(r['exit_code']==0 and r['source_sha256']==sha(p/f'{n}.lean') for n,r in checks.items())
inputs=json.loads((p/'input-bindings.json').read_text());assert all(sha(Path(f))==v for f,v in inputs.items())
cfg=json.loads((p/'comparator.json').read_text());assert len(cfg['theorem_names'])==15
assert len(re.findall(r'\bsorry\b',(p/'Challenge.lean').read_text()))==15
assert not re.search(r'\b(sorry|admit|axiom)\b',(p/'Solution.lean').read_text())
rows=json.loads((p/'DependencyProbe-check-01.log').read_text())
needed=set();unused=set()
for r in rows:
    if r['start'] is None:continue
    target=needed if r['needed'] else unused
    target.update(range(r['start'],r['end']+1))
analysis={'module_declarations':len(rows),'type_and_body_closure_declarations':sum(r['needed'] for r in rows),'unused_range_lines_outside_needed_ranges':len(unused-needed),'caveat':'This is an observed source-range upper bound on direct removal, not a proved minimum. Elaborator instances/simp attributes and surrounding syntax can require additional retention; no pruning applied.'}
(p/'dependency-analysis.json').write_text(json.dumps(analysis,indent=2)+'\n')
stats={n:{'lines':len((p/f'{n}.lean').read_text().splitlines()),'bytes':(p/f'{n}.lean').stat().st_size,'sha256':sha(p/f'{n}.lean')} for n in ['Challenge','Solution']}
assert stats['Challenge']['lines']==1375 and stats['Challenge']['bytes']<100*1024
review='''# Complete key and naturality: checked oversized candidate

This local candidate recovers the full original accepted053 and accepted054, with original universes and quantifiers, through compiled predicate/map bridges and rfl equality of recovered original theorems. It retains every actual marked test and multiplier law, both cotangent/alpha witnesses in Descends, the actual ideal of the even point, the internal-Hom dual ideal module, its curried canonical section, actual pushforward/evaluation, every rigidification, and the full evaluation-square-normalized unique key isomorphism. Naturality retains the pointed Cartesian map, the even-point compatibility, the actual cotangent and multiplier comparisons, the full alpha equality, the unique evaluation-compatible inverse-square comparison, and equality of the complete key morphisms. No main assumption is added.

The actual dual/evaluation support465 is included. The global-section equivalence is uniquely characterized on every local vector by the actual categorical evaluation and proved equal to the original. evaluationSection, evaluationSquare, IsKey and EvaluationSquareCompatible have compiled exact bridges. The binary tensor comparison458 gives the original productComparison; no arbitrary comparison map is substituted. Full original053/054 recovery passes OriginalEndpointAudit by rfl.

Challenge and Solution compile (33.66s and25.40s). All776 Challenge declarations and171 new Solution declarations pass axiom audit. Challenge has15 explicitly selected support/main holes and151 propagated sorry closures, no project imports. Solution has zero sorry closures. All411 non-Proposition Challenge/Solution declarations have matching types and available bodies. The original theorem recovery and the stated evaluation/naturality bridges use only propext, Classical.choice and Quot.sound.

This is NOT submission-ready: Challenge is1375 physical lines and94505bytes, exceeding the1000-line limit, although under100KiB. It is archived as an oversized prototype, without a Lake root/workflow installation, official dispatch, or endpoint coverage increment. Current integrated independent coverage remains70/103,33pending. The Solution is518lines/54914bytes.

Constructor-aware type-and-body traversal from the two key targets finds478 of776 module declarations in the closure. Declaration-range comparison identifies145 unused range lines outside needed ranges. This does not justify deleting all those lines: some instances and simp attributes can be required during elaboration, and a range need not include its surrounding syntax. Even the optimistic direct removal leaves1230lines, so it would not meet the cap. No dependency pruning was applied. A next candidate needs a more compact, fully specified internal-Hom/adjunction presentation, additional legitimate source organization, or an officially accepted larger-source route; deleting original key clauses is not a valid solution.

The source-exact internal-Hom support contains complete construction proofs. A useful compact alternative would keep the same presheaf of natural families, canonical tensor/evaluation/curry operations and characterize the adjunction by its full local formula, selecting its support theorem explicitly and proving equality to the original. Any alternative must still recover actual dual objects and evaluation sections, not just an unspecified abstract dual. This is a proposed next step, not an implemented or accepted replacement.

Failed attempt01 is preserved: an unclosed copied section/missing pullbackUnitIso definition in Challenge and definitionally equal goals needing rfl in Solution. Attempt02 succeeds after restoring the actual pullback unit construction and closing those goals; no source proposition was weakened. This root-authored review is not an independent external scope verdict. No official kernel acceptance is claimed.
'''
(p/'Review.md').write_text(review)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'full original053054 locally recovered, oversized candidate not integrated','candidate_original_ids':['accepted-053','accepted-054'],'new_endpoint_credit':0,'official_pass':False,'submission_ready':False,'reason':'Challenge1375lines exceeds1000-line official cap','checks':checks,'stats':stats,'dependency_analysis':analysis,'semantic_declarations_compatible':411,'full_original_theorem_equality_audit_passed':True,'input_bindings_unchanged':True}
out['bindings']={f.name:sha(f) for f in p.iterdir() if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log'] and f.name!='receipt.json'}
(p/'receipt.json').write_text(json.dumps(out,indent=2)+'\n')
dest=w/'project/docs/audit/phase-free-key-candidate-466';assert not dest.exists();dest.mkdir()
for f in p.iterdir():
    if f.is_file() and f.suffix in ['.lean','.json','.py','.md','.txt','.log']:shutil.copyfile(f,dest/f.name)
print(json.dumps({'status':out['status'],'stats':stats,'dependency_analysis':analysis,'new_endpoint_credit':0}))
