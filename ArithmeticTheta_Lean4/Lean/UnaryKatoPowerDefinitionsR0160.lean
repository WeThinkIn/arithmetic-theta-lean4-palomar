import ActualTorsionPowerValueR0159
import UnaryThetaProduct
import DiscriminantInitial
import ProperFlatPolygonTowerR0130
import ProjectiveTowerEffectivityR0135
import CompatibleProjectiveEmbeddingsR0135
import CompatibleFormalSectionBasisR0134
import MarkedSectionAlgebraizationR0136
import ActualGenericGroupLawR0146

/-! Literal series and actual marked-point value predicates for equation (power).
No construction or equality is asserted by these ordinary definitions. -/
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaUnaryKatoPowerR0160
open CategoryTheory AlgebraicGeometry

def integerSeries (k : Type) [Field k] : PowerSeries ℤ →+* LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k).comp (PowerSeries.map (Int.castRingHom k))

/-- q=t^(24*d*m), so Q=q^m=t^(24*d*m^2). -/
def unary (k : Type) [Field k] (d m : ℕ) (ν : ℤ) : LaurentSeries k :=
  integerSeries k (PowerSeries.subst (PowerSeries.X^d)
    (ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν))

/-- The displayed D₂(Q)=Q² product_(n≥1)(1-Q^n)^48, at Q=t^r. -/
def discriminant (k : Type) [Field k] [CharZero k] (r : ℕ) : LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k) (PowerSeries.subst (PowerSeries.X^r)
    (PowerSeries.map (algebraMap ℚ k)
      (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48)))

/-- Exact values at the actual marked sections z=-t^(d*unaryA), for every
normalized residue. Existence of the index and section belongs to the conclusion. -/
def PowerValues (k : Type) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r}
    {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
    (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    [IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)]
    (d m N : ℕ)
    (g : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField) : Prop :=
  ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) →
    ∃ (j : Fin r) (p : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
      (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j (-1) p),
      j.val = d * ArithmeticThetaUnaryProduct.unaryA m ν ∧
      ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k)
        (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)
        (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g
        (unary k d m ν ^ ((1+12*N)^2-1) /
          discriminant k r ^ (((1+12*N)^2-1)/48))

section
open ArithmeticThetaInfinitesimalPolygonR0129 (Tower)
open ArithmeticThetaProjectiveEffectivityR0135 (Model IsModel)
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138 (zeroIndex)
open ArithmeticThetaMarkedGroupLawR0146 (Law IsOriginLaw)
open ArithmeticThetaGenericEvaluationR0140 (genericScheme)
open ArithmeticThetaKatoExistenceR0151 (IsKatoFunction)

/-- Geometric realization of the unary power-value identity.

The witnesses first give a positive even period, its tower and algebraized model,
then a marked origin and group law. Integrality and local Noetherianity of the
generic scheme are witnessed as well and installed for the final assertion.
That assertion fixes `r = 24 * d * m^2` and gives a unique Kato function with
the exact marked-point values specified by `PowerValues`. -/
def GeometricRealization (k : Type) [Field k] [CharZero k] (d m N : ℕ) : Prop :=
  ∃ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r)
    (T : Tower k r hr) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
    (hI : IsIntegral (genericScheme k M))
    (hNoeth : IsLocallyNoetherian (genericScheme k M)),
    letI : IsIntegral (genericScheme k M) := hI
    letI : IsLocallyNoetherian (genericScheme k M) := hNoeth
    r = 24 * d * m^2 ∧
      ∃! g : (genericScheme k M).functionField,
        IsKatoFunction k M s hs.1 G (1 + 12 * N) g ∧ PowerValues k M d m N g

end

end ArithmeticThetaUnaryKatoPowerR0160
