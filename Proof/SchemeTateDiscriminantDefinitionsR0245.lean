module

public import SchemeDiscriminantNaturalityR0244
public import OpenDiscriminantFullTateExpansionR0182
public import SchemeDiscriminantDefinitionsR0244
public import BoundaryHodgeDefinitionsR0182

@[expose] public section

/-! The same intrinsic scheme section evaluated through actual unmarked Tate
comparisons. These definitions assume no discriminant expansion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaSchemeTateDiscriminantR0245
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182

variable (k : Type) [Field k] [CharZero k] (L : ℕ)

abbrev TateSections :=
  (HodgePower (LaurentSeries k) (TateCurve k L) 24).presheaf.obj (Opposite.op ⊤)

def NormalizedDiscriminant (d : TateSections k L) : Prop :=
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  ArithmeticThetaArbitraryDiscriminantR0243.IsD2 (TateCurve k L) d

def FullExpansion (δ : CurveFrame k L) (d : TateSections k L) : Prop :=
  d = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k)
      (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L) •
    ArithmeticThetaTensorPower.tensorPowerSection (Puncture k)
      (Hodge (LaurentSeries k) (TateCurve k L)) 24 ⊤ (hodgeGenerator k L δ)

/-- No level structure, modular classifying map, or section is part of a test.
The base, pointed Cartesian curve map and normalized differential are specified. -/
structure TateTest (l : Type) [Field l] [CharZero l] (ι : k →+* l)
    {S : Scheme} (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : Family S) where
  elliptic : (TateCurve l L).IsElliptic
  law : Law (LaurentSeries l) (TateCurve l L)
  originLaw : IsOriginLaw (LaurentSeries l) (TateCurve l L) law
  base : Puncture l ⟶ S
  base_eq : base ≫ σ = Spec.map
    (CommRingCat.ofHom ((algebraMap l (LaurentSeries l)).comp ι))
  comparison : @Comparison S (Puncture l) E
    (@weierstrassFamily (LaurentSeries l) inferInstance (TateCurve l L) elliptic law originLaw) base
  differential : CurveFrame l L
  normalized : ArithmeticThetaBoundaryHodgeR0182.Normalized l L differential

def value {l : Type} [Field l] [CharZero l] {ι : k →+* l}
    {S : Scheme} {σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k}
    {E : Family S} (V : TateTest k L l ι σ E) (d : Sections E) : TateSections l L :=
  letI := V.elliptic
  weierstrassValue (LaurentSeries l) (TateCurve l L) V.law V.originLaw
    (ArithmeticThetaSchemeDiscriminantR0244.pull V.comparison d)

def HasTateExpansions {S : Scheme}
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : Family S) (d : Sections E) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] (ι : k →+* l) (L : ℕ),
    3 ≤ L → Even L → ∀ V : TateTest k L l ι σ E,
    FullExpansion l L V.differential (value k L V d)

end ArithmeticThetaSchemeTateDiscriminantR0245
