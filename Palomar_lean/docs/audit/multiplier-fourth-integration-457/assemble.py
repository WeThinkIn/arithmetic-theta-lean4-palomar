from pathlib import Path
import re,json,hashlib,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
base=w/'evidence/phase-free-multiplier-package-450';c=read(base/'Challenge.uncompressed.lean.txt');s=read(base/'Solution.uncompressed.lean.txt').replace('public import','public import MultiplierFourthTrivializationR0219\npublic import SchemeDiscriminantExistenceR0244\npublic import',1)
tc=read(w/'evidence/canonical-tensor-comparison-382/Challenge.lean').replace('local instance : MonoidalCategory X.PresheafOfModules :=','local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor : MonoidalCategory X.PresheafOfModules :=');ts=read(w/'evidence/canonical-tensor-comparison-382/Solution.lean')
c+='open MonoidalCategory\n'
c+=tc[tc.index('namespace ArithmeticThetaSheafTensor'):tc.index('namespace AlgebraicGeometry')]
c+=tc[tc.index('namespace ArithmeticThetaPalomarCanonicalTensor382'):];s+=ts[ts.index('namespace ArithmeticThetaPalomarCanonicalTensor382'):]
unit='''namespace ArithmeticThetaPalomarFourth454
open ArithmeticThetaTensorPower ArithmeticThetaPalomarCanonicalTensor382
instance opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := CategoryTheory.final_of_representablyFlat _
def unitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ h
def powerPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Y.Modules)
    (hH : Scheme.Modules.IsInvertible H) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n :=
  (canonicalTensorComparison f H ((Scheme.Modules.pullback f).obj H) hH (Iso.refl _) n).exists.choose
'''
c+=unit;s+=unit
s+='''theorem powerPullback_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Y.Modules)
    (hH : Scheme.Modules.IsInvertible H) (n : ℕ) :
    powerPullback f H hH n = ArithmeticThetaPullback.pullback_tensorPower_iso X Y f H n := by
  apply (canonicalTensorComparison f H ((Scheme.Modules.pullback f).obj H) hH (Iso.refl _) n).unique
  · exact (canonicalTensorComparison f H ((Scheme.Modules.pullback f).obj H) hH (Iso.refl _) n).exists.choose_spec
  · intro U t
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_tensorPower_local_section X Y f H n U t
theorem unitPullback_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) : unitPullback f = Scheme.Modules.pullbackUnitIso f := rfl
'''
pred='''open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def FourthNormalized (L : S.Modules) (m : Frames E P L) (hL : Scheme.Modules.IsInvertible L)
    (t : tensorPower S L 4 ≅ SheafOfModules.unit S.ringCatSheaf) : Prop :=
  ∀ A : MarkedTest E P,
    (unitPullback A.map).hom.app ⊤
      (((Scheme.Modules.pullback A.map).map t.hom).app ⊤
        ((powerPullback A.map L hL 4).inv.app ⊤
          (tensorPowerSection A.base ((Scheme.Modules.pullback A.map).obj L) 4 ⊤ (m A)))) = (1 : Γ(A.base, ⊤))
'''
c+=pred;s+=pred
s+='''theorem fourthNormalized_iff (L : S.Modules) (m : Frames E P L) (hL : Scheme.Modules.IsInvertible L)
    (t : tensorPower S L 4 ≅ SheafOfModules.unit S.ringCatSheaf) :
    FourthNormalized E P L m hL t ↔ ArithmeticThetaPhaseFreeKeyR0219.FourthNormalized E P L m t := by
  simp only [FourthNormalized, ArithmeticThetaPhaseFreeKeyR0219.FourthNormalized,
    powerPullback_eq_original, unitPullback_eq_original]
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'));o=next(x for x in obs if x['id']=='accepted-100')
typ=o['type'].replace('ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m →','(hm : ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m) →').replace('ArithmeticThetaPhaseFreeKeyR0219.FourthNormalized E P L m t','FourthNormalized E P L m hm.1 t')
d='theorem multiplierFourthTrivialization :\n'+typ+' := by\n';c+=d+'  sorry\n';s+=d+'''  intro k _ _ S σ E P L m hm
  simpa only [fourthNormalized_iff] using (ArithmeticThetaPhaseFreeKeyR0219.multiplier_fourth_trivialization k S σ E P L m hm)
'''
s+='theorem recover_original_100 :\n'+o['type']+' := by\n'+'''  intro k _ _ S σ E P L m hm
  simpa only [fourthNormalized_iff] using (multiplierFourthTrivialization k S σ E P L m hm)
'''
c+='end ArithmeticThetaPalomarFourth454\n';s+='end ArithmeticThetaPalomarFourth454\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(base/'comparator.json'));cfg['theorem_names']+=['ArithmeticThetaPalomarCanonicalTensor382.canonicalTensorComparison','ArithmeticThetaPalomarFourth454.multiplierFourthTrivialization'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((base/'compile.py').read_bytes())
