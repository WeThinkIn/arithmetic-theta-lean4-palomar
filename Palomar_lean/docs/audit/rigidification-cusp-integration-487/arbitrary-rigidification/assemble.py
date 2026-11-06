from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
t=read(w/'evidence/even-point-evaluation-package-473/Challenge.lean');c=t[:t.index('namespace ArithmeticThetaPalomarDual465')]
s=read(w/'evidence/actual-dual-evaluation-465/Solution.lean').replace('public import Mathlib','public import Mathlib\npublic import ArbitraryEvenThetaRigidificationR0213',1)
m=read(w/'evidence/compact-key-surface-469/Challenge.lean');c+='open AlgebraicGeometry\nset_option maxHeartbeats 1600000\nset_option maxRecDepth 4096\n'+m[m.index('namespace NeronModelInfra'):m.index('namespace GoodReductionJacobian')]
def block(src,a,z):i=src.index(a);return src[i:src.index(z,i)+len(z)]+'\n'
c+=block(m,'namespace ArithmeticThetaRelativeDiscriminantR0171\nabbrev Base','end ArithmeticThetaRelativeDiscriminantR0171')
c+=block(m,'namespace ArithmeticThetaFullLevelCoverR0175','end ArithmeticThetaFullLevelCoverR0175')
src=read(w/'project/Proof/GlobalFourTorsionDefinitionsR0190.lean');two=src[src.index('def twoLabel'):src.index('def quarterPoint')]
c+='namespace ArithmeticThetaGlobalFourTorsionR0190\nopen ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175\nvariable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))\n'+two+'end ArithmeticThetaGlobalFourTorsionR0190\n'
c+=t[t.index('namespace AlgebraicGeometry\nstructure Scheme.Modules.IsInvertible'):t.index('namespace ArithmeticThetaPalomarTheta473')]
head='''namespace ArithmeticThetaPalomarRigidification484
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (M : FullLevel R W G 4 (𝟙 (Base R)))
'''
defs='''def evenPoint : Base R ⟶ Curve R W := twoLabel R W G 4 M 2
def thetaIdeal : (Curve R W).IdealSheafData := (evenPoint R W G M).ker
def thetaLine : (Curve R W).Modules := (thetaIdeal R W G M).invModule
def thetaMap : (𝟙_ (Curve R W).Modules) ⟶ thetaLine R W G M := (thetaIdeal R W G M).invModuleSection
def originGenerator : (𝟙_ (Base R).Modules) ⟶ (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) :=
  (Scheme.Modules.pullbackUnitIso (origin R W)).inv ≫ (Scheme.Modules.pullback (origin R W)).map (thetaMap R W G M)
def IsRigidification (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅ (𝟙_ (Base R).Modules)) : Prop := originGenerator R W G M ≫ e.hom = 𝟙 _
'''
c+=head+defs;s+=head+defs
s+='''theorem thetaMap_eq_original : thetaMap R W G M = ArithmeticThetaThetaEvaluationR0212.thetaMap R W G M :=
  (ArithmeticThetaThetaEvaluationR0212.EvenThetaRigidification.thetaMap_eq R W G M).symm
theorem isRigidification_iff (e : (Scheme.Modules.pullback (origin R W)).obj (thetaLine R W G M) ≅ (𝟙_ (Base R).Modules)) :
    IsRigidification R W G M e ↔ ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e := by
  unfold IsRigidification originGenerator
  rw [thetaMap_eq_original]
  rfl
'''
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-094');typ=o['type'].replace('ArithmeticThetaThetaEvaluationR0212.','ArithmeticThetaPalomarRigidification484.')
c+='theorem arbitraryEvenThetaRigidification :\n'+typ+' := by sorry\n'
s+='theorem arbitraryEvenThetaRigidification :\n'+typ+''' := by
  intro R _ _ W _ G hG M
  have h := ArithmeticThetaUniversalEvaluationR0213.arbitrary_even_theta_rigidification R W G hG M
  convert h using 1 <;> (try simp only [thetaMap_eq_original, isRigidification_iff]) <;> rfl
'''
s+='theorem recover_original_094 :\n'+o['type']+''' := by
  intro R _ _ W _ G hG M
  have h := arbitraryEvenThetaRigidification R W G hG M
  convert h using 1 <;> (try simp only [thetaMap_eq_original, isRigidification_iff]) <;> rfl
'''
c+='end ArithmeticThetaPalomarRigidification484\n';s+='end ArithmeticThetaPalomarRigidification484\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/compact-key-surface-469/comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if n.startswith(('HomogeneousIdealQuotientGrading.','WeierstrassProjModel.','ProjWeierstrassCubicPrime.'))]+['SheafOfModules.presheafW_isMonoidal','ArithmeticThetaPalomarRigidification484.arbitraryEvenThetaRigidification'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/compact-key-surface-469/compile.py').read_bytes())
