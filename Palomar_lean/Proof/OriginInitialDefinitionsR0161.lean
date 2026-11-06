module

public import UnaryKatoPowerDefinitionsR0160
public import CompletedModelChartMapsR0152
public import UnsplitKatoFullExpansionR0158
public import KatoAnnularDefinitionsR0152

@[expose] public section

/-! The actual identity-chart Taylor map and its stalk filtration comparison.
The inner variable is the base parameter t; the outer variable is u=z-1.
These definitions specify maps and equalities, without asserting their existence. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaOriginInitialR0161
open CategoryTheory AlgebraicGeometry

variable (k : Type) [Field k] [CharZero k]
abbrev Chart := ArithmeticThetaKatoAnnularR0152.Chart k
abbrev ChartField := ArithmeticThetaKatoAnnularR0152.ChartField k
abbrev Bivariate := PowerSeries (PowerSeries k)
abbrev Iterated := LaurentSeries (LaurentSeries k)

def zInverse : Bivariate k := PowerSeries.invOfUnit (1 + PowerSeries.X) 1

/-- Continuity is coefficientwise for the BASE t-adic filtration, not the
u-adic topology. All coefficients, including the constant coefficient, occur. -/
def IsChartTaylor (σ : Chart k →+* Bivariate k) : Prop :=
  (∀ b : PowerSeries k, σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
    PowerSeries.C b) ∧
  σ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = 1 + PowerSeries.X ∧
  σ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
    PowerSeries.C PowerSeries.X * zInverse k ∧
  ∀ (n : ℕ) (b : Chart k),
    b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n →
    ∀ i : ℕ, PowerSeries.coeff i (σ b) ∈
      (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) ^ n

def toIterated : Bivariate k →+* Iterated k :=
  (HahnSeries.ofPowerSeries ℤ (LaurentSeries k)).comp
    (PowerSeries.map (HahnSeries.ofPowerSeries ℤ k))

def ExtendsTaylor (σ : Chart k →+* Bivariate k)
    (Ψ : ChartField k →+* Iterated k) : Prop :=
  Ψ.comp (ArithmeticThetaKatoAnnularR0152.chartToField k) =
    (toIterated k).comp σ

/-- Transport the already defined complete rational gamma series coefficient
by coefficient along Q=t^r and Q-coefficients into k. -/
def gammaTaylor (r c : ℕ) : Iterated k :=
  (HahnSeries.ofPowerSeries ℤ (LaurentSeries k))
    (PowerSeries.mk (fun n => (HahnSeries.ofPowerSeries ℤ k)
      (PowerSeries.subst (PowerSeries.X ^ r)
        (PowerSeries.map (algebraMap ℚ k)
          (PowerSeries.coeff n (ArithmeticThetaDiscriminant.gamma c))))))

def f5Taylor (r : ℕ) : Iterated k :=
  HahnSeries.C ((ArithmeticThetaLaurentNormR0064.t k ^ r)^2) *
    ((-((HahnSeries.ofPowerSeries ℤ (LaurentSeries k))
      (1 + PowerSeries.X))) ^ 10)⁻¹ * (gammaTaylor k r 1)^25 /
    gammaTaylor k r 5

variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}

abbrev Origin (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) :=
  ArithmeticThetaGenericEvaluationR0140.genericPoint k M s hs

abbrev OriginStalk (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) :=
  (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).presheaf.stalk
    (Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)))

/-- The same actual field expansion extends the actual local ring, evaluates
at the actual identity, and reflects every power of its maximal ideal. -/
def IsOriginTaylor (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (E : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField →+*
      Iterated k)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k)) : Prop :=
  (∀ b : OriginStalk k M s hs,
    (HahnSeries.ofPowerSeries ℤ (LaurentSeries k)) (κ b) =
      E (algebraMap (OriginStalk k M s hs)
        (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField b)) ∧
  (∀ b : OriginStalk k M s hs,
    PowerSeries.constantCoeff (κ b) = Scheme.stalkClosedPointTo (Origin k M s hs) b) ∧
  ∀ (b : OriginStalk k M s hs) (n : ℕ),
    b ∈ (IsLocalRing.maximalIdeal (OriginStalk k M s hs)) ^ n ↔
      ∀ i : ℕ, i < n → PowerSeries.coeff i (κ b) = 0

/-- A genuine nonzero class in m^24/m^25 of the ACTUAL identity stalk,
represented by 5g, with its coefficient in the specified Taylor parameter.
This is not yet the conormal-to-Hodge tensor identification or global descent. -/
def HasDiscriminantInitial
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (g : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k)) : Prop :=
  ∃ b : OriginStalk k M s hs,
    algebraMap (OriginStalk k M s hs)
      (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField b = 5*g ∧
    b ∈ (IsLocalRing.maximalIdeal (OriginStalk k M s hs)) ^ 24 ∧
    b ∉ (IsLocalRing.maximalIdeal (OriginStalk k M s hs)) ^ 25 ∧
    PowerSeries.coeff 24 (κ b) = ArithmeticThetaUnaryKatoPowerR0160.discriminant k r

end ArithmeticThetaOriginInitialR0161
