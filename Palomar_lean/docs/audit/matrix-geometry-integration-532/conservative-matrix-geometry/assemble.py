from pathlib import Path
import re,json,hashlib,shutil,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'sharp-matrix-geometry-package-529';src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):t=read(src/(f+'.lean'));return t[t.index(a):t.index(z,t.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
c=read(b/'Challenge.lean');c=c[:c.index('namespace ArithmeticThetaPalomarSharp529')]
s=read(b/'Solution.lean');s=s[:s.index('namespace ArithmeticThetaPalomarSharp529')];s=s.replace('public import SharpMatrixGeometricFamilyR0195','public import ArithmeticGeometricFamilyExistenceR0189').replace('public import SharpGeometricCutoffR0195','public import GeometricFamilyConservativeCutoffR0189')
for namespace in ['ArithmeticThetaSquareLinesR0192','ArithmeticThetaSharpCoverR0194','ArithmeticThetaSharpKernelR0195']:
 c=re.sub(r'namespace '+namespace+r'\n.*?end '+namespace+r'\n','',c,flags=re.S)
opens='ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185'
c+=ns('ArithmeticThetaCommonHalfHodgeR0185',cut('CommonHalfHodgeDefinitionsR0185','structure DivisorLine','/-- Literal Euler product'),'ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184')
c+=ns('ArithmeticThetaLatticeSectionsR0188',cut('LatticeGlobalSectionsDefinitionsR0188','abbrev coverLine','/-- Scalars on the actual curve'),opens)
c+=ns('ArithmeticThetaConservativeKernelR0189',cut('ConservativeKernelDefinitionsR0189','def cutoff','end ArithmeticThetaConservativeKernelR0189'),opens)
t=read(b/'Challenge.lean');a=t.index('def squareOnDisk');z=t.index('end ArithmeticThetaPalomarSharp529',a);t=t[a:z]
common=ns('ArithmeticThetaPalomarConservative530',t+cut('LatticeGlobalSectionsDefinitionsR0188','def GeometricFamily','end ArithmeticThetaLatticeSectionsR0188'),opens);c+=common;s+=common
bridges='''theorem squareOnDisk_eq_original (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : squareOnDisk k p J H β f d hf = ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H β f d hf := by
  simp only [squareOnDisk, ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem pullbackPowerSection_eq_original {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : pullbackPowerSection p H n F = ArithmeticThetaNormalizedSections.pullbackPowerSection p H n F := by
  simp only [pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem geometric_iff_original {n h : ℕ} (A : Matrices n h) (U : Indexing A) {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D} (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : GeometricFamily A U H V ↔ ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by
  simp only [GeometricFamily, ArithmeticThetaLatticeSectionsR0188.GeometricFamily, squareOnDisk_eq_original, pullbackPowerSection_eq_original]
''';s+=ns('ArithmeticThetaPalomarConservative530',bridges,opens)
obs=json.loads(read(w/'project/docs/SourceObligations.json'));names=[]
for i,n in [('035','arithmeticGeometricFamilyExistence'),('036','geometricFamilyConservativeCutoff')]:
 o=next(x for x in obs if x['id']=='accepted-'+i);typ=o['type'].replace('ArithmeticThetaLatticeSectionsR0188.GeometricFamily','ArithmeticThetaPalomarConservative530.GeometricFamily');claim='theorem '+n+' : '+typ+' := by\n';c+=ns('ArithmeticThetaPalomarConservative530',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarConservative530',claim+'  simpa only [geometric_iff_original] using '+o['declaration']+'\n'+'theorem recover_original_'+i+' : '+o['type']+' := by\n  simpa only [geometric_iff_original] using '+n+'\n');names.append('ArithmeticThetaPalomarConservative530.'+n)
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 (p/(n+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(n+'.lean')).write_text(v);print(n,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-2:]=names;(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit']:
 t=read(b/(n+'.lean')).replace(str(b),str(p));t=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,t);(p/(n+'.lean')).write_text(t)
t='module\nimport all Solution\nset_option maxRecDepth 8192\nset_option backward.isDefEq.respectTransparency false\n'
for i in ['035','036']:
 o=next(x for x in obs if x['id']=='accepted-'+i);t+='example : ArithmeticThetaPalomarConservative530.recover_original_'+i+' = '+o['declaration']+' := by rfl\n'
t+='\n'.join('#print axioms '+n for n in names)+'\n#print axioms ArithmeticThetaPalomarConservative530.geometric_iff_original\n';(p/'OriginalEndpointAudit.lean').write_text(t)
for n in ['compile.py','finalize.py','compact.py','pack_fields.py']:shutil.copyfile(b/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
