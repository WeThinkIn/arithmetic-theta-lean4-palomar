from pathlib import Path
import ast,hashlib,json,shutil,textwrap,yaml
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/even-point-evaluation-package-473';review=w/'evidence/even-point-evaluation-scope-review-474';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((review/'receipt.json').read_text());assert r['local_scope_review_passed'];assert all(sha(Path(f))==h for f,h in r['bindings'].items());assert sha(review/'Review.md')==r['review_sha256']
r=json.loads((source/'receipt.json').read_text());assert all(sha(source/f)==h for f,h in r['bindings'].items())
files=[source/n for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','comparator.json','Targets.json']]+[review/'Review.md',review/'receipt.json']
(p/'acceptance.json').write_text(json.dumps({'accepted_for_local_integration':True,'new_ids':['accepted-099'],'basis':'Complete frozen473 source/type/axiom checks and474 root scope review; no official acceptance','bindings':{str(f):sha(f) for f in files}},indent=2)+'\n')
slug='even-point-evaluation';root='EvenPointEvaluation';config='comparator-'+slug+'.json';dest=project/'challenges'/slug;assert not dest.exists();dest.mkdir()
for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','Targets.json']:shutil.copyfile(source/n,dest/n)
lake=(project/'lakefile.toml').read_text()
for kind in ['Challenge','Solution']:
    name=root+kind;assert f'name = "{name}"' not in lake;shutil.copyfile(source/f'{kind}.lean',project/f'{name}.lean');lake+=f'\n[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n'
cfg=json.loads((source/'comparator.json').read_text());cfg.update(challenge_module=root+'Challenge',solution_module=root+'Solution');(project/config).write_text(json.dumps(cfg,indent=2)+'\n')
meta=yaml.safe_load((project/'submissions/main-complete/formalization.yaml').read_text())
desc='Full original099 at arbitrary universe u: actual even-point ideal and dual line, exact zeroSchemeIdeal, unique identity rigidification, isomorphism of the actual pushforward generator, and every normalized evaluation isomorphism with generator/evaluation identity and frame generation on every subopen. No full marking or phase assumption. Three support/main targets selected; no whole-paper completion claimed.'
meta['project']['name']='Complete actual even-point theta evaluation';meta['project']['description']=desc;meta['status']['scope']=desc
meta['fidelity']['divergences']='Full original099 statement and universe recovered by compiled rfl equality; actual ideal/kernel/dual/canonical section/pushforward/evaluation and all local zero-scheme coefficients retained. Canonical global-sections equivalence proved equal to original. No new main assumption. Three targets and163 semantic definitions checked; Challenge517lines/31736bytes.'
assert meta['project']['authors']==meta['project']['responsible_maintainers']==['Jue Ding'];assert meta['project']['license']=='Apache-2.0'
d=project/'submissions'/slug;assert not d.exists();d.mkdir();(d/'formalization.yaml').write_text(yaml.safe_dump(meta,sort_keys=False,allow_unicode=True))
f=project/'.github/workflows/palomar-preflight.yml';workflow=f.read_text().replace('          - comparator-scheme-tate-unit.json','          - comparator-scheme-tate-unit.json\n          - '+config).replace("'comparator.json', 'comparator-early.json'",repr(config)+", 'comparator.json', 'comparator-early.json'",1).replace('metadata_paths = {','metadata_paths = {'+repr(config)+': '+repr('submissions/'+slug+'/formalization.yaml')+', ',1)
script=yaml.safe_load(workflow)['jobs']['request']['steps'][0]['run'];ast.parse(textwrap.dedent(script.split("<<'PY'\n",1)[1].rsplit('\nPY',1)[0]));assert config in workflow
f.write_text(workflow);(project/'lakefile.toml').write_text(lake)
template=(w/'evidence/phase-free-alpha-descent-integration-461/build_root.py').read_text().replace('PhaseFreeAlphaDescent','EvenPointEvaluation').replace('comparator-phase-free-alpha-descent','comparator-even-point-evaluation')
(p/'build_root.py').write_text(template)
print('Installed complete099 roots/config/metadata; no official dispatch.')
