from pathlib import Path
import ast,hashlib,json,shutil,textwrap,yaml
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/key-tate-package-478';review=w/'evidence/key-tate-scope-review-479';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((review/'receipt.json').read_text());assert r['local_scope_review_passed'];assert all(sha(Path(f))==h for f,h in r['bindings'].items());assert sha(review/'Review.md')==r['review_sha256']
r=json.loads((source/'receipt.json').read_text());assert all(sha(source/f)==h for f,h in r['bindings'].items())
files=[source/n for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','comparator.json','Targets.json']]+[review/'Review.md',review/'receipt.json']
(p/'acceptance.json').write_text(json.dumps({'accepted_for_local_integration':True,'new_ids':['accepted-055'],'basis':'Complete frozen478 source/type/axiom checks and479 root scope review; no official acceptance','bindings':{str(f):sha(f) for f in files}},indent=2)+'\n')
slug='key-tate';root='KeyTateNormalization';config='comparator-'+slug+'.json';dest=project/'challenges'/slug;assert not dest.exists();dest.mkdir()
for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','Targets.json']:shutil.copyfile(source/n,dest/n)
lake=(project/'lakefile.toml').read_text()
for kind in ['Challenge','Solution']:
    name=root+kind;assert f'name = "{name}"' not in lake;shutil.copyfile(source/f'{kind}.lean',project/f'{name}.lean');lake+=f'\n[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n'
cfg=json.loads((source/'comparator.json').read_text());cfg.update(challenge_module=root+'Challenge',solution_module=root+'Solution');(project/config).write_text(json.dumps(cfg,indent=2)+'\n')
meta=yaml.safe_load((project/'submissions/main-complete/formalization.yaml').read_text())
desc='Full original055 for every characteristic-zero field k : Type and positive N divisible by four: actual full Tate marking and level-four reduction, every actual Tate test, same supplied key/evaluation square, both tensor pullbacks, canonical conormal-to-Hodge comparison, actual multiplier sheaf/frame and full Laurent normalization. Retains order zero-or-N/4 and exact canonical theta-square coefficient.34 support/main targets; no whole-paper completion claimed.'
meta['project']['name']='Complete phase-free key Tate normalization';meta['project']['description']=desc;meta['status']['scope']=desc
meta['fidelity']['divergences']='Full original055 type recovered by compiled rfl theorem equality. Original TateTest retained; canonical inclusion-compatible ideal, conormal-to-Hodge and both tensor comparisons proved equal to original constructions. No new main assumption or Laurent truncation.34 target types/universes and all retained semantic definitions checked. Challenge982lines/86950bytes.'
assert meta['project']['authors']==meta['project']['responsible_maintainers']==['Jue Ding'];assert meta['project']['license']=='Apache-2.0'
d=project/'submissions'/slug;assert not d.exists();d.mkdir();(d/'formalization.yaml').write_text(yaml.safe_dump(meta,sort_keys=False,allow_unicode=True))
f=project/'.github/workflows/palomar-preflight.yml';workflow=f.read_text().replace('          - comparator-scheme-tate-unit.json','          - comparator-scheme-tate-unit.json\n          - '+config).replace("'comparator.json', 'comparator-early.json'",repr(config)+", 'comparator.json', 'comparator-early.json'",1).replace('metadata_paths = {','metadata_paths = {'+repr(config)+': '+repr('submissions/'+slug+'/formalization.yaml')+', ',1)
script=yaml.safe_load(workflow)['jobs']['request']['steps'][0]['run'];ast.parse(textwrap.dedent(script.split("<<'PY'\n",1)[1].rsplit('\nPY',1)[0]));assert config in workflow
f.write_text(workflow);(project/'lakefile.toml').write_text(lake)
template=(w/'evidence/phase-free-alpha-descent-integration-461/build_root.py').read_text().replace('PhaseFreeAlphaDescent','KeyTateNormalization').replace('comparator-phase-free-alpha-descent','comparator-key-tate')
(p/'build_root.py').write_text(template)
print('Installed complete055 roots/config/metadata; no official dispatch.')
