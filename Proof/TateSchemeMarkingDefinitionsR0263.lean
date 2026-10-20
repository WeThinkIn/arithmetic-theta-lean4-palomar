module

public import SchemeGeometricThetaNaturalityR0262

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaTateSchemeMarkingR0263
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (V : TateLevel k (2*m))

abbrev family : ArithmeticThetaLocalWeierstrassR0203.Family (Puncture k) :=
  @ArithmeticThetaSchemeDiscriminantR0244.weierstrassFamily (LaurentSeries k) _
    (TateCurve k (2*m)) V.elliptic V.law V.originLaw

abbrev pointX : point (family k V) := V.marking.x
abbrev pointY : point (family k V) := V.marking.y

/-- The same comparison is formed over an arbitrary ring before specialization,
so no conversion between concrete Laurent-ring instance presentations is hidden. -/
def weierstrassLineComparison (R : Type) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (d : ℕ) :
    thetaLine (ArithmeticThetaSchemeDiscriminantR0244.weierstrassFamily R W G hG) d ≅
      tensorObj (Scheme.Modules.dual (((ArithmeticThetaRelativeKatoR0169.origin R W).ker ^ d).module))
        ((Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.structureMap R W)).obj
          ((ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).tensorPow d)) := by
  have hz := ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero R W G hG
  exact (eqToIso (congrArg (fun (o : ArithmeticThetaLocalWeierstrassR0203.Base R ⟶
      ArithmeticThetaRelativeKatoR0169.Curve R W) => Scheme.Modules.dual ((o.ker ^ d).module)) hz)) ⊗ᵢ
    ((Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.structureMap R W)).mapIso
      (Scheme.Modules.tensorPowMapIso
        (ArithmeticThetaSchemeDiscriminantR0244.weierstrassHodgeIso R W G hG) d))

/-- The comparison uses the actual origin equality and conormal derivative. -/
def cubicLineComparison (d : ℕ) : thetaLine (family k V) d ≅ tateThetaLine k (2*m) d := by
  letI := V.elliptic
  dsimp only [family, tateThetaLine, tateHodgeLine]
  convert weierstrassLineComparison (LaurentSeries k) (TateCurve k (2*m)) V.law V.originLaw d using 1
  rfl

variable {ζ : kˣ} (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

def modelComparison : (Scheme.Modules.pullback Q.cubic.hom).obj (thetaLine (family k V) m) ≅
    Scheme.Modules.dual (ArithmeticThetaGenericEvaluationR0140.genericPower k Q.model Q.origin m) :=
  (Scheme.Modules.pullback Q.cubic.hom).mapIso (cubicLineComparison k V m) ≪≫ Q.thetaComparison he

/-- Literal comparison of sheaf lifts, hence an equality on every open. -/
def Matches (g : (family k V).curve ⟶ (family k V).curve)
    (f : ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model)
    (a : Lift (family k V) m g)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f) : Prop :=
  ∃ h : Q.cubic.hom ≫ g = f ≫ Q.cubic.hom,
    SectionAction.changeLine f (modelComparison k V Q he)
      (SectionAction.baseChangedLift Q.cubic.hom g f h a) =
    LocalTheta.dualLift f _ (Q.ideal_invertible he) e.symm

abbrev sectionEquiv := LocalTheta.modelFunctionalEquiv k Q.model Q.origin m Q.cubic
  (thetaLine (family k V) m) (modelComparison k V Q he)

def basisSection (ν : Fin m) : Γ(thetaLine (family k V) m, ⊤) :=
  (sectionEquiv k V Q he).symm
    (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he Q.model Q.isModel Q.origin Q.markedOrigin ν)

abbrev FiberFrame := (Scheme.Modules.pullback (family k V).zero).obj (thetaLine (family k V) m) ≅
  (SheafOfModules.unit (Puncture k).ringCatSheaf : (Puncture k).Modules)

def value (e : FiberFrame k V) (v : Γ(thetaLine (family k V) m, ⊤)) : LaurentSeries k :=
  SectionAction.pointValue (family k V).zero (thetaLine (family k V) m) e v

def ExactValues : Prop :=
  Nonempty (FiberFrame k V) ∧ ∀ e : FiberFrame k V,
    value k V e (basisSection k V Q he ⟨0,hm⟩) ≠ 0 ∧
    ∀ ν : Fin m,
      value k V e (basisSection k V Q he ν) / value k V e (basisSection k V Q he ⟨0,hm⟩) =
        algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ν) /
        algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ⟨0,hm⟩)

def scalarLiftFacts (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointX k V))) : Prop :=
  Matches k V Q he _ Q.mapA a (Q.canonicalA he hζ) ∧
  ∀ ι : Lift (family k V) m (inverse (family k V)),
    NormalizedInversion (family k V) m ι → Symmetric (family k V) m (pointX k V) ι a

def shiftLiftFacts
    (a : Lift (family k V) m (translation (family k V) (pointY k V))) : Prop :=
  Matches k V Q he _ Q.mapB a (Q.canonicalB he) ∧
  ∀ ι : Lift (family k V) m (inverse (family k V)),
    NormalizedInversion (family k V) m ι → Symmetric (family k V) m (pointY k V) ι a

def inversionLiftFacts (a : Lift (family k V) m (inverse (family k V))) : Prop :=
  Matches k V Q he _ Q.mapS a (Q.canonicalS he) ∧ NormalizedInversion (family k V) m a

/-- Actual all-open pushforward action compared with the old geometric action. -/
def OperatorComparison : Prop :=
  ∀ (g : (family k V).curve ⟶ (family k V).curve)
    (f : ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model ⟶
      ArithmeticThetaGenericEvaluationR0140.genericScheme k Q.model)
    (a : Lift (family k V) m g)
    (e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m f),
    Matches k V Q he g f a e →
      ∀ v : Γ(thetaLine (family k V) m, ⊤),
        sectionEquiv k V Q he (SectionAction.globalAct g a v) =
          ArithmeticThetaGeometricLiftsR0141.act k Q.model Q.origin m f e
            (sectionEquiv k V Q he v)

/-- The precise phase in the actual Laurent-base global unit ring. -/
def phase : ((Puncture k).presheaf.obj (Opposite.op ⊤))ˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom.comp
    (algebraMap k (LaurentSeries k))).toMonoidHom (ζ^2)

end ArithmeticThetaTateSchemeMarkingR0263
