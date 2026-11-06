from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=w/'evidence/component-discriminant-package-509';marker='namespace ArithmeticThetaPalomarD2_509\ntheorem componentDiscriminantDivisor';c=read(b/'Challenge.lean');c=c[:c.rindex(marker)];s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import ComponentDiscriminantDivisorR0184','public import CommonHalfHodgeCoverR0185')
c+=ns('ArithmeticThetaDiscriminant',cut('DiscriminantDefinitions','noncomputable def partialEuler','noncomputable def swap')+cut('DiscriminantDefinitions','noncomputable def P','abbrev K'))
opens='ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184'
c+=ns('ArithmeticThetaCommonHalfHodgeR0185',cut('CommonHalfHodgeDefinitionsR0185','structure DivisorLine','structure Twist'),opens)
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','def scalar','/-- Local-frame formula'),'ArithmeticThetaRelativeDiscriminantR0171')
var='variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)\n'
t=cut('CommonHalfHodgeDefinitionsR0185','def along','end ArithmeticThetaCommonHalfHodgeR0185');t=t.replace('ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.tensorComparison','ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison').replace('pullbackPowerSection map','ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection map').replace('restrict k L D X x','ArithmeticThetaPalomarD2_509.ComponentDegree.restrict k L D X x')
common=ns('ArithmeticThetaPalomarCommon511',var+t,opens+' ArithmeticThetaCommonHalfHodgeR0185');c+=common;s+=common
bridges='''theorem pullSquare_eq_original {Z Y B : Scheme} (g : Z ⟶ Y) (p : Y ⟶ B) (f : Z ⟶ B) (h : g ≫ p = f) (A J : B.Modules) (β : tensorPower Y ((Scheme.Modules.pullback p).obj A) 2 ≅ (Scheme.Modules.pullback p).obj J) : pullSquare g p f h A J β = ArithmeticThetaCommonHalfHodgeR0185.pullSquare g p f h A J β := by
  simp only [pullSquare, ArithmeticThetaCommonHalfHodgeR0185.pullSquare, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, along, ArithmeticThetaCommonHalfHodgeR0185.along]
'''
for name,source,target in [('toOriginal','HalfCover','ArithmeticThetaCommonHalfHodgeR0185.HalfCover'),('ofOriginal','ArithmeticThetaCommonHalfHodgeR0185.HalfCover','HalfCover')]:
 bridges+='def '+name+' {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} {s : Γ(tensorPower X.space H.line 24, ⊤)} (C : '+source+' k L D X x A H s) : '+target+' k L D X x A H s where\n'
 for field in ['space','map','integral','finite','etale','surjective','proper','smooth','rank','square']:bridges+='  '+field+' := C.'+field+'\n'
 bridges+='''  discriminant := by
    simpa only [ArithmeticThetaPalomarD2_509.NormalizedSections.pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, ArithmeticThetaPalomarHalf505.powerComparison_eq_original, ArithmeticThetaPalomarD2_509.restrict_eq_original] using C.discriminant
'''
bridges+='''theorem hasBranch_toOriginal {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} {s : Γ(tensorPower X.space H.line 24, ⊤)} (C : HalfCover k L D X x A H s) (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) : HasBranch k L D X x C V f hf ↔ ArithmeticThetaCommonHalfHodgeR0185.HasBranch k L D X x (toOriginal k L D X x C) V f hf := by
  simp only [HasBranch, ArithmeticThetaCommonHalfHodgeR0185.HasBranch, toOriginal, pullSquare_eq_original]
theorem hasBranch_ofOriginal {A : DivisorLine (Component k L D X x)} {H : Extension k L D X} {s : Γ(tensorPower X.space H.line 24, ⊤)} (C : ArithmeticThetaCommonHalfHodgeR0185.HalfCover k L D X x A H s) (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk) : HasBranch k L D X x (ofOriginal k L D X x C) V f hf ↔ ArithmeticThetaCommonHalfHodgeR0185.HasBranch k L D X x C V f hf := by
  simp only [HasBranch, ArithmeticThetaCommonHalfHodgeR0185.HasBranch, ofOriginal, pullSquare_eq_original]
theorem common_iff_original (H : Extension k L D X) (s : Γ(tensorPower X.space H.line 24, ⊤)) (V : DiskTest k L D X) : CommonHalfHodge k L D X H s V ↔ ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodge k L D X H s V := by
  constructor
  · rintro ⟨f, hf, A, hA, C, hC⟩
    exact ⟨f, hf, A, hA, toOriginal k L D X _ C, (hasBranch_toOriginal k L D X _ C V f hf).mp hC⟩
  · rintro ⟨f, hf, A, hA, C, hC⟩
    exact ⟨f, hf, A, hA, ofOriginal k L D X _ C, (hasBranch_ofOriginal k L D X _ C V f hf).mpr hC⟩
''';s+=ns('ArithmeticThetaPalomarCommon511',var+bridges,opens+' ArithmeticThetaCommonHalfHodgeR0185')
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-034');typ=o['type'].replace('ArithmeticThetaComponentDegreeR0184.IsCompactD2','ArithmeticThetaPalomarD2_509.ComponentDegree.IsCompactD2').replace('ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodge','ArithmeticThetaPalomarCommon511.CommonHalfHodge');claim='theorem commonHalfHodgeCover :\n'+typ+' := by\n';c+=ns('ArithmeticThetaPalomarCommon511',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarCommon511',claim+'  simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, common_iff_original] using ArithmeticThetaCommonHalfHodgeR0185.common_half_hodge_cover\n'+'theorem recover_original_034 :\n'+o['type']+' := by\n  simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, common_iff_original] using commonHalfHodgeCover\n')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if n!='ArithmeticThetaPalomarD2_509.componentDiscriminantDivisor']+['ArithmeticThetaPalomarCommon511.commonHalfHodgeCover'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
