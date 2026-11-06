module

public import RamifiedFunctionFieldExpansionR0155
public import RamifiedKatoBaseChangeR0155
public import LaurentFormalFNormR0064
public import LaurentFormalFPeriodicityR0064
public import KatoAnnularDefinitionsR0152
public import LaurentNormDefinitionsR0064

@[expose] public section

/-! Concrete annular evaluation and the literal quotient at arbitrary integral
period. The geometric and product identities are separate proof obligations. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAnnularNormBridgeR0156

variable (k : Type) [Field k] [CharZero k]
abbrev Coeff := ArithmeticThetaLaurentNormR0064.Coeff k
abbrev Series := ArithmeticThetaLaurentNormR0064.Series k
abbrev Chart := ArithmeticThetaKatoAnnularR0152.Chart k
abbrev ChartField := ArithmeticThetaKatoAnnularR0152.ChartField k

def coefficientMap : k →+* Coeff k :=
  (algebraMap (LaurentPolynomial k) (Coeff k)).comp LaurentPolynomial.C

def baseSeries (b : PowerSeries k) : Series k :=
  algebraMap (PowerSeries (Coeff k)) (Series k) (PowerSeries.map (coefficientMap k) b)

def coordinate (a : kˣ) (n : ℕ) : Coeff k :=
  coefficientMap k (a : k) * ArithmeticThetaLaurentNormR0064.w k ^ n

/-- The specified full coefficient map, coordinates and t-adic continuity.
The target has a transcendental coordinate, not a selected rational point. -/
def IsEvaluation (a : kˣ) (n : ℕ) (ev : ChartField k →+* Series k) : Prop :=
  (∀ b : PowerSeries k,
    ev (ArithmeticThetaKatoAnnularR0152.chartToField k
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) = baseSeries k b) ∧
  ev (ArithmeticThetaKatoAnnularR0152.chartToField k
    (ArithmeticThetaAnnularTorsionPrereqR0053.cx k)) = HahnSeries.C (coordinate k a n) ∧
  ev (ArithmeticThetaKatoAnnularR0152.chartToField k
    (ArithmeticThetaAnnularTorsionPrereqR0053.cy k)) =
      HahnSeries.C (coordinate k a n)⁻¹ * ArithmeticThetaLaurentNormR0064.t (Coeff k) ∧
  (∀ (N : ℕ) (b : Chart k), b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k N →
    ∀ e : ℤ, e < (N : ℤ) →
      (ev (ArithmeticThetaKatoAnnularR0152.chartToField k b)).coeff e = 0)

/-- The literal f_c for Q=t^r and z=t^j*x. Its gamma factors retain all
horizontal zeros; division occurs only in the actual chart fraction field. -/
def literalTheta (r c : ℕ) (hr : 0 < r) (hc : 1 < c) (hdiv : c ∣ r)
    (hcop : Nat.Coprime c 6) (ζ : k) (hζ : IsPrimitiveRoot ζ c) (j : Fin r) : ChartField k :=
  ArithmeticThetaLocalOrdersR0066.toFunctionField k
    (ArithmeticThetaAnnularTorsionPrereqR0053.tpower k ((r * (c^2-1) / 12 : ℕ) : ℤ)) *
    (ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.gammaLocal k r j.val hr j.isLt)) ^ (c^2) /
    ((-ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.localZ k j.val)) ^ (c*(c-1)/2) *
    ArithmeticThetaLocalOrdersR0066.toFunctionField k
      (ArithmeticThetaLocalNormR0054.poweredLocal k r c j.val ζ hr hc hdiv hcop hζ j.isLt))

end ArithmeticThetaAnnularNormBridgeR0156
