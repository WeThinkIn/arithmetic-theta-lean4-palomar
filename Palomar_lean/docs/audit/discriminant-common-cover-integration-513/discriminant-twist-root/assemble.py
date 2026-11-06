from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=w/'evidence/component-discriminant-package-509';c=read(b/'Challenge.lean');c=c[:c.rindex('namespace ArithmeticThetaPalomarD2_509\ntheorem componentDiscriminantDivisor')]
s=read(b/'Solution.lean');s=s[:s.rindex('namespace ArithmeticThetaPalomarD2_509\ntheorem componentDiscriminantDivisor')];s=s.replace('public import ComponentDiscriminantDivisorR0184','public import DiscriminantTwistUnitR0185\npublic import DiscriminantTateRootR0185')
c+=ns('ArithmeticThetaLineRoot','variable (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)\n'+cut('LocalFrameBridge','def localFrameOfIso','theorem localFrameOfIso_apply'))
t=cut('LocalTensorFrame','variable (X :','  let J := Opens.grothendieckTopology X')+'  sorry\n'+cut('LocalTensorFrame','def localTensorTrivialization (','theorem tensorFrame_apply');c+=ns('ArithmeticThetaSheafTensor',t,'ArithmeticThetaLineRoot')
c+=ns('ArithmeticThetaTensorPower',cut('TensorPowerDefinitions','def unitFrame','/-- Actual tensor power'),'ArithmeticThetaLineRoot ArithmeticThetaSheafTensor')
c+=ns('ArithmeticThetaRootTorsor',cut('GlobalizationDefinitions','def IsGeneratingSection','/-- The actual canonical iterated pullback'))
c+=ns('ArithmeticThetaDiscriminant',cut('DiscriminantDefinitions','noncomputable def partialEuler','noncomputable def swap')+cut('DiscriminantDefinitions','noncomputable def P','abbrev K'))
opens='ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184'
c+=ns('ArithmeticThetaCommonHalfHodgeR0185',cut('CommonHalfHodgeDefinitionsR0185','structure DivisorLine','/-- The normalized D2'),opens)
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','def scalar','/-- Local-frame formula'),'ArithmeticThetaRelativeDiscriminantR0171')
var='variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)\n'
t=var+cut('CommonHalfHodgeDefinitionsR0185','def IsTwist','/-- Canonical comparison over a specified commuting triangle')
t=t.replace('restrict k L D X x','ArithmeticThetaPalomarD2_509.ComponentDegree.restrict k L D X x').replace('pullback_sheafTensor_iso Z _ f','ArithmeticThetaPalomarHalf505.binary f').replace('pullback_tensorPower_iso Z _ f','ArithmeticThetaPalomarHalf505.powerComparison Z _ f').replace('pullbackPowerSection f','ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection f')
common=ns('ArithmeticThetaPalomarTwist510',t,opens+' ArithmeticThetaCommonHalfHodgeR0185');c+=common;s+=common
bridges=ns('ArithmeticThetaPalomarTwist510',var+'''theorem isTwist_iff_original {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (s : Γ(tensorPower X.space H.line 24, ⊤)) (W : Twist k L D X x A H) : IsTwist k L D X x s W ↔ ArithmeticThetaCommonHalfHodgeR0185.IsTwist k L D X x s W := by
  simp only [IsTwist, ArithmeticThetaCommonHalfHodgeR0185.IsTwist, ArithmeticThetaPalomarD2_509.restrict_eq_original]
theorem pullMultiply_eq_original {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (W : Twist k L D X x A H) {Z : Scheme} (f : Z ⟶ Component k L D X x) : pullMultiply k L D X x W f = ArithmeticThetaCommonHalfHodgeR0185.pullMultiply k L D X x W f := by
  simp only [pullMultiply, ArithmeticThetaCommonHalfHodgeR0185.pullMultiply, ArithmeticThetaPalomarHalf505.binary_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem isTateRoot_iff_original {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} (W : Twist k L D X x A H) (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) (v : Γ((Scheme.Modules.pullback f).obj W.line, ⊤)) : IsTateRoot k L D X x W V f hf v ↔ ArithmeticThetaCommonHalfHodgeR0185.IsTateRoot k L D X x W V f hf v := by
  simp only [IsTateRoot, ArithmeticThetaCommonHalfHodgeR0185.IsTateRoot, pullMultiply_eq_original, ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
''',opens+' ArithmeticThetaCommonHalfHodgeR0185');s+=bridges
obs=json.loads(read(w/'project/docs/SourceObligations.json'));names=[]
for i,n in [('032','discriminantTwistUnit'),('033','discriminantTateRoot')]:
 o=next(x for x in obs if x['id']=='accepted-'+i);typ=o['type'].replace('ArithmeticThetaComponentDegreeR0184.IsCompactD2','ArithmeticThetaPalomarD2_509.ComponentDegree.IsCompactD2').replace('ArithmeticThetaCommonHalfHodgeR0185.IsTwist','ArithmeticThetaPalomarTwist510.IsTwist').replace('ArithmeticThetaCommonHalfHodgeR0185.IsTateRoot','ArithmeticThetaPalomarTwist510.IsTateRoot');claim='theorem '+n+' :\n'+typ+' := by\n';c+=ns('ArithmeticThetaPalomarTwist510',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarTwist510',claim+'  simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, isTwist_iff_original, isTateRoot_iff_original] using '+o['declaration']+'\n'+'theorem recover_original_'+i+' :\n'+o['type']+' := by\n  simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, isTwist_iff_original, isTateRoot_iff_original] using '+n+'\n');names.append('ArithmeticThetaPalomarTwist510.'+n)
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if n!='ArithmeticThetaPalomarD2_509.componentDiscriminantDivisor']+['ArithmeticThetaSheafTensor.localTensorTrivializationHom_isIso']+names;(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
