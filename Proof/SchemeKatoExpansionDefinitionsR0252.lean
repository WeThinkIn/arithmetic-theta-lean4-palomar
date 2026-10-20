module

public import SchemeKatoNormR0251
public import PeriodOneFullKatoNormR0248

@[expose] public section

/-! Comparisons of the canonical section with the actual period-one full
Tate expansion. Only predicates and aliases are introduced in this file. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoExpansionR0252
open CategoryTheory AlgebraicGeometry

/-- The germ of the same canonical unit is the normalized field function. -/
def FieldAgreement (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve F W)]
    [IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve F W)]
    (G : ArithmeticThetaRelativeKatoR0169.Law F W) (c : ℕ)
    (v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection F W G c) : Prop :=
  ∃ hU : Nonempty (ArithmeticThetaArbitraryKatoUnitR0249.complement F W G c),
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F W G c
      (@Scheme.germToFunctionField (ArithmeticThetaRelativeKatoR0169.Curve F W) _
        (ArithmeticThetaArbitraryKatoUnitR0249.complement F W G c) hU (v : _))

/-- Every faithful coordinate evaluation reads the same full section; existence
of the evaluation is supplied by the accepted period-one theorem. -/
def PeriodUnitExpansion (k : Type) [Field k] [CharZero k]
    [(ArithmeticThetaPeriodOneNormR0248.periodCurve k).IsElliptic]
    [IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve k
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k))]
    [IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve k
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k))]
    (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k)
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k)) (c : ℕ)
    (v : ArithmeticThetaArbitraryKatoUnitR0249.UnitSection (LaurentSeries k)
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G c) : Prop :=
  ∃ hU : Nonempty (ArithmeticThetaArbitraryKatoUnitR0249.complement (LaurentSeries k)
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G c),
  ∀ ev : (ArithmeticThetaPeriodOneNormR0248.Curve k
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k)).functionField →+*
      ArithmeticThetaPeriodOneNormR0248.Series k,
    ArithmeticThetaPeriodOneNormR0248.IsEvaluation k
      (ArithmeticThetaPeriodOneNormR0248.periodCurve k) 1 ev →
    ArithmeticThetaUnsplitExpansionR0158.HasExpansion k 1 c 0
      (ev (@Scheme.germToFunctionField (ArithmeticThetaPeriodOneNormR0248.Curve k
        (ArithmeticThetaPeriodOneNormR0248.periodCurve k)) _
        (ArithmeticThetaArbitraryKatoUnitR0249.complement (LaurentSeries k)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve k) G c) hU (v : _)))

/-- All period-one tests, over every coefficient-field extension. The actual
unit is pulled by C.map.appLE, then restricted to the generic point and read by
one constructed faithful full-coordinate evaluation. No product equation or
choice of a new unit is included in the test data. -/
def TateExpansion (k : Type) [Field k] [CharZero k]
    {B : Scheme.{0}} (σ : B ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family B) (c : ℕ)
    (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] [Algebra k l],
  ∃ hE : (ArithmeticThetaPeriodOneNormR0248.periodCurve l).IsElliptic,
  ∃ hI : IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  ∃ hN : IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  letI := hE
  letI := hI
  letI := hN
  ∃ ev : (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)).functionField →+*
      ArithmeticThetaPeriodOneNormR0248.Series l,
    ArithmeticThetaPeriodOneNormR0248.IsEvaluation l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l) 1 ev ∧
    Function.Injective ev ∧
    ∀ (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l))
      (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G)
      (b : ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries l) ⟶ B),
      b ≫ σ = Spec.map (CommRingCat.ofHom
        ((algebraMap l (LaurentSeries l)).comp (algebraMap k l))) →
      ∀ C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E
        (ArithmeticThetaSchemeDiscriminantR0244.weierstrassFamily (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G hG) b,
      ∃ e : ArithmeticThetaArbitraryKatoUnitR0249.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c ≤
          C.map ⁻¹ᵁ ArithmeticThetaSchemeKatoUnitR0250.complement E c,
      ∃ hU : Nonempty (ArithmeticThetaArbitraryKatoUnitR0249.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c),
        ArithmeticThetaUnsplitExpansionR0158.HasExpansion l 1 c 0
          (ev (@Scheme.germToFunctionField (ArithmeticThetaPeriodOneNormR0248.Curve l
            (ArithmeticThetaPeriodOneNormR0248.periodCurve l)) _
            (ArithmeticThetaArbitraryKatoUnitR0249.complement (LaurentSeries l)
              (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c) hU
            (C.map.appLE _ _ e (v : _))))

end ArithmeticThetaSchemeKatoExpansionR0252
