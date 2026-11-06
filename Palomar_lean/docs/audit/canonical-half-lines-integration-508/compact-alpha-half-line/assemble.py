from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
c=read(w/'evidence/compact-alpha-package-501/Challenge.lean');c=c[:c.index('namespace ArithmeticThetaPalomarCompactAlpha501')]
b=read(w/'evidence/component-hodge-degree-package-495/Challenge.lean');c+=b[b.index('namespace ArithmeticThetaPalomarComponent485'):b.index('namespace ArithmeticThetaCurveDegree')]
c+=ns('ArithmeticThetaNormalizedSections',cut('NormalizedSectionDefinitions','def NormalAffine','/-- The literal coefficient'))
c+=ns('ArithmeticThetaSheafTensor','variable (X : Scheme.{u})\n'+cut('ActualSheafTensor','def tensorUnitMap','/-- Universal property')+cut('ActualSheafTensor','def tensorSection','theorem tensorSection_restrict'),'')
c+=ns('ArithmeticThetaTensorPower',cut('TensorPowerDefinitions','def tensorPowerSection','/-- Ordered product'),'ArithmeticThetaSheafTensor')
b=read(w/'evidence/canonical-binary-tensor-458/Challenge.lean');c+=b[b.index('namespace ArithmeticThetaPalomarBinaryTensor458'):]
common=ns('ArithmeticThetaPullback',cut('PullbackUnit','def pullback_unit_iso','end ArithmeticThetaPullback'))
common+=ns('ArithmeticThetaPalomarHalf505','''open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) :=
  Classical.choose (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
''')
# Binary congruence is the literal original body.
common+=ns('ArithmeticThetaPullback','''local instance : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
'''.replace('local instance :','local instance instMonoidalCategoryPresheafOfModules_pullbackTensor (X : Scheme.{u}) :')+cut('PullbackTensor','def sheafTensorCongr','/-- The sectionwise tensor pairing'),'ArithmeticThetaSheafTensor')
common+=ns('ArithmeticThetaPalomarHalf505','''open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n
  | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f
  | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
''')
c+=common
c+=ns('ArithmeticThetaLineRoot','variable (X : Scheme.{u}) [IsIntegral X]\n'+cut('LineRootGluing','theorem germ_restrict','theorem overlap_nonempty'))
c+=ns('ArithmeticThetaSectionCompletion',cut('NormalOrderCriterion','theorem normal_stalk_dvr','  obtain ⟨U,')+'  sorry\n','ArithmeticThetaNormalizedSections')
t=cut('EffectiveDivisorLine','abbrev RationalSections','/-- Bounded-pole rational sections satisfy')
t+=cut('EffectiveDivisorLine','theorem divisorPresheaf_isSheaf','  classical')+'  sorry\n'
t+=cut('EffectiveDivisorLine','def divisorSheaf','theorem divisorCanonicalSection_ne_zero')
c+=ns('ArithmeticThetaGeometricPrerequisites',t,'ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections')
c+=ns('ArithmeticThetaCommonHalfHodgeR0185',cut('CommonHalfHodgeDefinitionsR0185','structure DivisorLine','def Represents')+'variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space)\n'+cut('CommonHalfHodgeDefinitionsR0185','def diskHodgeIso','structure Twist'),'ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184')
# Keep all original compact-alpha/half-divisor/sheaf data definitions; replace only the branch's canonical comparison by a uniquely characterized, proved-equal construction.
t=cut('SquareLineComparisonDefinitionsR0192','variable (k :','/-- The prescribed theta frame')
c+=ns('ArithmeticThetaSquareLinesR0192',t,'ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaGlobalFourTorsionR0190')
branch='variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)\n'+cut('SquareLineComparisonDefinitionsR0192','def AlphaHalfBranch','end ArithmeticThetaSquareLinesR0192').replace('pullback_tensorPower_iso','powerComparison')
branch=ns('ArithmeticThetaPalomarHalf505',branch,'ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaGlobalFourTorsionR0190')
c+=branch
s='''module
public import CompactAlphaCanonicalHalfLineR0192
public import SchemeDiscriminantExistenceR0244
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
'''
b=read(w/'evidence/canonical-binary-tensor-458/Solution.lean');s+=b[b.index('namespace ArithmeticThetaPalomarBinaryTensor458'):]
# Imported original unit/congruence already exist.
a=common.index('namespace ArithmeticThetaPalomarHalf505');z=common.index('namespace ArithmeticThetaPullback',a);s+=common[a:z];a=common.index('namespace ArithmeticThetaPalomarHalf505',z);s+=common[a:]
s+=ns('ArithmeticThetaPalomarComponent485','''theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
''','ArithmeticThetaLevelCompactificationR0179')
s+=ns('ArithmeticThetaPalomarHalf505','''theorem binary_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : binary f H K = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K := by
  have h := Classical.choose_spec (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
  have hq : ArithmeticThetaPalomarBinaryTensor458.Compatible f H K _ _ (Iso.refl _) (Iso.refl _) (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K) := by
    intro U s t
    change (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _ (Scheme.Modules.pullbackLocalSection f (ArithmeticThetaSheafTensor.tensorSection Y H K U s t)) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section]
    rfl
  exact (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).unique h hq
theorem powerComparison_eq_original (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) (n : ℕ) : powerComparison X Y f H n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerComparison, ArithmeticThetaPullback.pullback_tensorPower_iso, binary_eq_original, ih]
''')
s+=branch
s+=ns('ArithmeticThetaPalomarHalf505','''theorem branch_iff_original (k : Type) [Field k] [CharZero k] (L : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (β : ArithmeticThetaTensorPower.tensorPower _ A.line 2 ≅ ArithmeticThetaComponentDegreeR0184.hodge k L D X x H) : AlphaHalfBranch k L D X H x A β ↔ ArithmeticThetaSquareLinesR0192.AlphaHalfBranch k L D X H x A β := by
  simp only [AlphaHalfBranch, ArithmeticThetaSquareLinesR0192.AlphaHalfBranch, powerComparison_eq_original]
''')
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-042');typ=o['type'].replace('ArithmeticThetaSquareLinesR0192.AlphaHalfBranch','ArithmeticThetaPalomarHalf505.AlphaHalfBranch');claim='theorem compactAlphaCanonicalHalfLine :\n'+typ+' := by\n';c+=ns('ArithmeticThetaPalomarHalf505',claim+'  sorry\n')
s+=ns('ArithmeticThetaPalomarHalf505',claim+'''  simpa only [branch_iff_original] using ArithmeticThetaSquareLinesR0192.compact_alpha_canonical_half_line
'''+ 'theorem recover_original_042 :\n'+o['type']+''' := by
  simpa only [branch_iff_original] using compactAlphaCanonicalHalfLine
''')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/component-hodge-degree-package-495/comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if not n.startswith('ArithmeticThetaPalomarHodge495.')]+['ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor','ArithmeticThetaSectionCompletion.normal_stalk_dvr','ArithmeticThetaGeometricPrerequisites.divisorPresheaf_isSheaf','ArithmeticThetaPalomarHalf505.compactAlphaCanonicalHalfLine'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/compact-alpha-package-501/compile.py').read_bytes())
