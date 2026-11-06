from pathlib import Path
import re,json,hashlib,shutil,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'field-unary-package-519';src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
marker='namespace ArithmeticThetaPalomarField519\ntheorem fieldCompactUnary'
c=read(b/'Challenge.lean');c=c[:c.rindex(marker)]
s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import FieldCompactUnaryR0236','public import FieldCompactDiscriminantR0236')
for kind,t in [('Challenge',c),('Solution',s)]:
 t=re.sub(r'namespace ArithmeticThetaPalomarUnary514\n.*?end ArithmeticThetaPalomarUnary514\n','',t,flags=re.S)
 if kind=='Challenge':c=t
 else:s=t
c+=ns('ArithmeticThetaDiscriminant',cut('DiscriminantDefinitions','noncomputable def partialEuler','noncomputable def swap')+cut('DiscriminantDefinitions','noncomputable def P','abbrev K'))
c+=ns('ArithmeticThetaHodgeInitialR0163','variable (k : Type) [Field k] [CharZero k]\n'+cut('HodgeInitialDefinitionsR0163','def discriminantSeries','end ArithmeticThetaHodgeInitialR0163'))
t=cut('ArithmeticSectionsDefinitionsR0236','def RealizesDiscriminant','end ArithmeticThetaArithmeticSectionsR0236');t=t.replace('restrictPower k','ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k').replace('pullToOpen k','ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k').replace('diskPower k','ArithmeticThetaPalomarUnary514.BoundaryHodge.diskPower k')
opens='ArithmeticThetaTensorPower ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelCompactificationR0179'
common=ns('ArithmeticThetaPalomarFieldD2_522',t,opens);c+=common;s+=common
s+=ns('ArithmeticThetaPalomarFieldD2_522','''theorem realizes_iff_original (k : Type) [Field k] [CharZero k] (L : ℕ) {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤)) (s : Γ(tensorPower X.space H.line 24, ⊤)) : RealizesDiscriminant k L H d s ↔ ArithmeticThetaArithmeticSectionsR0236.RealizesDiscriminant k L H d s := by
  simp only [RealizesDiscriminant, ArithmeticThetaArithmeticSectionsR0236.RealizesDiscriminant, ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarUnary514.BoundaryHodge.diskPower, ArithmeticThetaBoundaryHodgeR0182.diskPower, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
''',opens)
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-068');typ=o['type'].replace('ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical','ArithmeticThetaPalomarField519.Boundary.GeometricallyCanonical').replace('ArithmeticThetaOpenHodgeR0180.IsD2','ArithmeticThetaPalomarD2_509.OpenHodge.IsD2').replace('ArithmeticThetaArithmeticSectionsR0236.RealizesDiscriminant','ArithmeticThetaPalomarFieldD2_522.RealizesDiscriminant');claim='theorem fieldCompactDiscriminant : '+typ+' := by\n'
c+=ns('ArithmeticThetaPalomarFieldD2_522',claim+'  sorry\n')
bridges='[ArithmeticThetaPalomarField519.geometric_iff_original, ArithmeticThetaPalomarD2_509.isD2_iff_original, realizes_iff_original]'
s+=ns('ArithmeticThetaPalomarFieldD2_522',claim+'  simpa only '+bridges+' using '+o['declaration']+'\n'+'theorem recover_original_068 : '+o['type']+' := by\n  simpa only '+bridges+' using fieldCompactDiscriminant\n')
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 (p/(n+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(n+'.lean')).write_text(v);print(n,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1]='ArithmeticThetaPalomarFieldD2_522.fieldCompactDiscriminant';(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit']:
 t=read(b/(n+'.lean')).replace(str(b),str(p));t=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,t);(p/(n+'.lean')).write_text(t)
(p/'OriginalEndpointAudit.lean').write_text('module\nimport all Solution\nset_option maxRecDepth 8192\nset_option backward.isDefEq.respectTransparency false\nexample : ArithmeticThetaPalomarFieldD2_522.recover_original_068 = '+o['declaration']+' := by rfl\n#print axioms ArithmeticThetaPalomarFieldD2_522.fieldCompactDiscriminant\n#print axioms ArithmeticThetaPalomarFieldD2_522.realizes_iff_original\n#print axioms ArithmeticThetaPalomarField519.geometric_iff_original\n')
for n in ['compile.py','finalize.py','compact.py']:shutil.copyfile(b/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
