from pathlib import Path
import ast,hashlib,json,shutil,textwrap,yaml
p=Path(__file__).resolve().parent;w=p.parent.parent;project=w/'project';review=w/'evidence/field-discriminant-scope-review-523';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((review/'receipt.json').read_text());assert r['local_scope_review_passed'] and all(sha(Path(f))==h for f,h in r['bindings'].items());assert sha(review/'Review.md')==r['review_sha256']
meta_description=json.loads((w/'evidence/field-discriminant-package-522/package-description.json').read_text())
packages=[dict(slug='field-discriminant',root='FieldDiscriminant',source='field-discriminant-package-522',ids=['accepted-068'],title=meta_description['title'],description=meta_description['description'])]
lake=(project/'lakefile.toml').read_text();f=project/'.github/workflows/palomar-preflight.yml';workflow=f.read_text();accepted={}
for q in packages:
 source=w/'evidence'/q['source'];r=json.loads((source/'receipt.json').read_text());assert all(sha(source/n)==h for n,h in r['bindings'].items());accepted[q['slug']]={'bindings':{str(source/n):sha(source/n) for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','comparator.json','Targets.json']},'new_ids':q['ids']}
 dest=project/'challenges'/q['slug'];assert not dest.exists();dest.mkdir()
 for n in ['Challenge.lean','Solution.lean','Scope.json','SourceMap.json','receipt.json','README.md','Targets.json']:shutil.copyfile(source/n,dest/n)
 for kind in ['Challenge','Solution']:
  name=q['root']+kind;assert f'name = "{name}"' not in lake;shutil.copyfile(source/f'{kind}.lean',project/f'{name}.lean');lake+=f'\n[[lean_lib]]\nname = "{name}"\nroots = ["{name}"]\n'
 config='comparator-'+q['slug']+'.json';cfg=json.loads((source/'comparator.json').read_text());cfg.update(challenge_module=q['root']+'Challenge',solution_module=q['root']+'Solution');(project/config).write_text(json.dumps(cfg,indent=2)+'\n')
 meta=yaml.safe_load((project/'submissions/main-complete/formalization.yaml').read_text());meta['project']['name']=q['title'];meta['project']['description']=q['description'];meta['status']['scope']=q['description'];meta['fidelity']['divergences']='Full original endpoint type and universe recovered by compiled theorem equality. Actual mathematical definitions retained with explicit original-construction equality bridges.All explicit support/main targets, all semantic types/available bodies and standard axioms checked. No new main assumption. Official verification pending.'
 assert meta['project']['authors']==meta['project']['responsible_maintainers']==['Jue Ding'];assert meta['project']['license']=='Apache-2.0'
 dest=project/'submissions'/q['slug'];assert not dest.exists();dest.mkdir();(dest/'formalization.yaml').write_text(yaml.safe_dump(meta,sort_keys=False,allow_unicode=True))
 workflow=workflow.replace('          - comparator-scheme-tate-unit.json','          - comparator-scheme-tate-unit.json\n          - '+config).replace("'comparator.json', 'comparator-early.json'",repr(config)+", 'comparator.json', 'comparator-early.json'",1).replace('metadata_paths = {','metadata_paths = {'+repr(config)+': '+repr('submissions/'+q['slug']+'/formalization.yaml')+', ',1)
script=yaml.safe_load(workflow)['jobs']['request']['steps'][0]['run'];ast.parse(textwrap.dedent(script.split("<<'PY'\n",1)[1].rsplit('\nPY',1)[0]));f.write_text(workflow);(project/'lakefile.toml').write_text(lake)
(p/'packages.json').write_text(json.dumps(packages,indent=2)+'\n');(p/'acceptance.json').write_text(json.dumps({'accepted_for_local_integration':True,'basis':'Frozen complete522 source/type/axiom audits and523 root scope review; no official acceptance','packages':accepted,'review_sha256':sha(review/'receipt.json')},indent=2)+'\n');print('Installed two roots and full original068 configuration; no official dispatch.')
