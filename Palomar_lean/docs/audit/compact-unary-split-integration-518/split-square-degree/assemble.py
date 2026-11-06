from pathlib import Path
import re,json,hashlib,shutil,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'component-hodge-degree-package-495';src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
ob=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-074');typ=ob['type'];marker='namespace ArithmeticThetaPalomarHodge495\ntheorem componentHodgePowerDegree'
c=read(b/'Challenge.lean');c=c[:c.rindex(marker)]
c+=ns('ArithmeticThetaNormalizedSections',cut('NormalizedSectionDefinitions','def NormalAffine','/-- The literal coefficient'))
c+=ns('ArithmeticThetaCurveDegree',cut('CurveDegreeDefinitions','def OneDimensionalCharts','def principalOrder'))
c+=ns('ArithmeticThetaSquareLinesR0192',cut('SquareLineComparisonDefinitionsR0192','structure SquareLine','/-- Pullback retains'),'ArithmeticThetaTensorPower')
c+=ns('ArithmeticThetaSimultaneousUnaryR0187',cut('SimultaneousUnaryRootsDefinitionsR0187','structure RootCover','/-- The root sections'))
c+=ns('ArithmeticThetaSharpCoverR0194',cut('SharpCoverRatiosDefinitionsR0194','def SquareCoverDegree','/-- Full q='),'ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaSquareLinesR0192 ArithmeticThetaTensorPower ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder')
s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import ComponentHodgePowerDegreeR0184','public import SplitSquareCoverDegreeR0239')
claim='theorem splitSquareCoverDegree : '+typ+' := by\n'
c+=ns('ArithmeticThetaPalomarSplit516',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarSplit516',claim+'  exact '+ob['declaration']+'\ntheorem recover_original_074 : '+typ+' := splitSquareCoverDegree\n')
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 (p/(n+'.uncompressed.lean.txt')).write_text(t);(p/(n+'.lean')).write_text(fmt['compact'](t))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1]='ArithmeticThetaPalomarSplit516.splitSquareCoverDegree';(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
for n in ['ChallengeAudit','SolutionAudit','TargetHoleAudit','TargetTypeAudit','DefinitionCompatibility']:
 s=read(b/(n+'.lean')).replace(str(b),str(p));s=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,s);(p/(n+'.lean')).write_text(s)
(p/'OriginalEndpointAudit.lean').write_text('module\nimport all Solution\nset_option backward.isDefEq.respectTransparency false\nexample : ArithmeticThetaPalomarSplit516.recover_original_074 = '+ob['declaration']+' := by rfl\n#print axioms ArithmeticThetaPalomarSplit516.recover_original_074\n')
for n in ['compile.py','finalize.py']:shutil.copyfile(p.parent/'component-discriminant-package-509'/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');print({n:len((p/(n+'.lean')).read_text().splitlines()) for n in ['Challenge','Solution']})
