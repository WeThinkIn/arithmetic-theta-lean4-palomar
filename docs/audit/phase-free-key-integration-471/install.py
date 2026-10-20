from pathlib import Path
import ast,hashlib,json,shutil,textwrap,yaml
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';source=w/'evidence/compact-key-surface-469';review=w/'evidence/phase-free-key-scope-review-470';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((review/'receipt.json').read_text());assert r['local_scope_review_passed'];assert all(sha(Path(f))==h for f,h in r['bindings'].items());assert sha(review/'Review.md')==r['review_sha256']
r=json.loads((source/'receipt.json').read_text());assert all(sha(source/f)==h for f,h in r['bindings'].items())
files=[source/n for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','comparator.json','Targets.json']]+[review/'Review.md',review/'receipt.json']
(p/'acceptance.json').write_text(json.dumps({'accepted_for_local_integration':True,'new_ids':['accepted-053','accepted-054'],'basis':'Complete frozen469 source/type/axiom checks and470 root scope review; no official acceptance','bindings':{str(f):sha(f) for f in files}},indent=2)+'\n')
slug='phase-free-key';root='PhaseFreeKey';config='comparator-'+slug+'.json';dest=project/'challenges'/slug;assert not dest.exists();dest.mkdir()
for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','Targets.json']:shutil.copyfile(source/n,dest/n)
lake=(project/'lakefile.toml').read_text()
for kind in ['Challenge','Solution']:
    name=root+kind;assert f'name = "{name}"' not in lake;shutil.copyfile(source/f'{kind}.lean',project/f'{name}.lean');lake+=f'\n[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n'
cfg=json.loads((source/'comparator.json').read_text());cfg.update(challenge_module=root+'Challenge',solution_module=root+'Solution');(project/config).write_text(json.dumps(cfg,indent=2)+'\n')
meta=yaml.safe_load((project/'submissions/main-complete/formalization.yaml').read_text())
desc='Full original053054 at arbitrary universe u: actual even-point theta ideal and dual line, canonical section, pushforward evaluation and tensor square; unique normalized key isomorphism and its full naturality under arbitrary pointed Cartesian base change. Every original rigidification, multiplier law, cotangent/alpha witness and full morphism equality retained.37 support/main targets selected. Inherited052095096097 not recounted. No whole-paper completion claimed.'
meta['project']['name']='Complete phase-free key and naturality';meta['project']['description']=desc;meta['status']['scope']=desc
meta['fidelity']['divergences']='Original053054 full statements/universes recovered through actual dual/evaluation and canonical tensor comparison bridges, with compiled rfl original-theorem equality.22 auxiliary Proposition proofs become explicit support comparison targets; no semantic definition hole or new main assumption. All37 target types/universes and380 semantic definitions checked. Challenge1000lines/81891bytes meets hard caps but exceeds preferred review surface.'
assert meta['project']['authors']==meta['project']['responsible_maintainers']==['Jue Ding'];assert meta['project']['license']=='Apache-2.0'
d=project/'submissions'/slug;assert not d.exists();d.mkdir();(d/'formalization.yaml').write_text(yaml.safe_dump(meta,sort_keys=False,allow_unicode=True))
f=project/'.github/workflows/palomar-preflight.yml';workflow=f.read_text().replace('          - comparator-scheme-tate-unit.json','          - comparator-scheme-tate-unit.json\n          - '+config).replace("'comparator.json', 'comparator-early.json'",repr(config)+", 'comparator.json', 'comparator-early.json'",1).replace('metadata_paths = {','metadata_paths = {'+repr(config)+': '+repr('submissions/'+slug+'/formalization.yaml')+', ',1)
script=yaml.safe_load(workflow)['jobs']['request']['steps'][0]['run'];ast.parse(textwrap.dedent(script.split("<<'PY'\n",1)[1].rsplit('\nPY',1)[0]));assert config in workflow
f.write_text(workflow);(project/'lakefile.toml').write_text(lake)
template=(w/'evidence/phase-free-alpha-descent-integration-461/build_root.py').read_text().replace('PhaseFreeAlphaDescent','PhaseFreeKey').replace('comparator-phase-free-alpha-descent','comparator-phase-free-key')
(p/'build_root.py').write_text(template)
print('Installed complete053054 roots/config/metadata; no official dispatch.')
