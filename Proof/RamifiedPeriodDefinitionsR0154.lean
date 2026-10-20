module

public import CompletedNormProductR0153
public import LiteralQuotientAlgebraizationR0153
public import RamifiedMonomialBasisR0096
public import Mathlib.RingTheory.PowerSeries.Expand

@[expose] public section

/-! Ramification t ↦ s^d of the actual polygon charts and models.
The predicates below specify maps by equations. Existence, injectivity,
cartesian geometry and Kato compatibility are separate obligations. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRamifiedPeriodR0154
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152

variable (k : Type u) [Field k] [CharZero k]

def baseMap (d : ℕ) (hd : 0 < d) : PowerSeries k →+* PowerSeries k :=
  (PowerSeries.expand d (Nat.ne_of_gt hd)).toRingHom

def baseMorphism (d : ℕ) (hd : 0 < d) : baseScheme k ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (baseMap k d hd))

def IsLaurentExtension (d : ℕ) (hd : 0 < d)
    (ell : LaurentSeries k →+* LaurentSeries k) : Prop :=
  ∀ b : PowerSeries k, ell (algebraMap (PowerSeries k) (LaurentSeries k) b) =
    algebraMap (PowerSeries k) (LaurentSeries k) (baseMap k d hd b)

def LaurentDegree (d : ℕ) (ell : LaurentSeries k →+* LaurentSeries k) : Prop :=
  letI := ell.toAlgebra
  FiniteDimensional (LaurentSeries k) (LaurentSeries k) ∧
    Module.finrank (LaurentSeries k) (LaurentSeries k) = d

/-- On refined chart dj+q, x_old=s^q x_new and y_old=s^(d-q-1)y_new.
The product is s^d; all exponents are nonnegative, including both endpoints. -/
def IsChartRamification (d : ℕ) (hd : 0 < d) (q : Fin d)
    (ρ : Chart k →+* Chart k) : Prop :=
  (∀ b : PowerSeries k, ρ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
    ArithmeticThetaAnnularTorsionPrereqR0053.base k (baseMap k d hd b)) ∧
  ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ q.val *
      ArithmeticThetaAnnularTorsionPrereqR0053.cx k ∧
  ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
    ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ (d-q.val-1) *
      ArithmeticThetaAnnularTorsionPrereqR0053.cy k

def ExtendsChart (ρ : Chart k →+* Chart k)
    (E : ChartField k →+* ChartField k) : Prop :=
  ∀ b : Chart k, E (chartToField k b) = chartToField k (ρ b)

def coarseIndex (r d : ℕ) (hd : 0 < d) (i : Fin (r*d)) : Fin r :=
  ⟨i.val / d, (Nat.div_lt_iff_lt_mul hd).2 i.isLt⟩

def residueIndex (r d : ℕ) (hd : 0 < d) (i : Fin (r*d)) : Fin d :=
  ⟨i.val % d, Nat.mod_lt _ hd⟩

def markedIndex (r d : ℕ) (hd : 0 < d) (i : Fin r) : Fin (r*d) :=
  ⟨i.val*d, Nat.mul_lt_mul_of_pos_right i.isLt hd⟩

variable {r d : ℕ} {hr : 0 < r} {hd : 0 < d} {hrd : 0 < r*d}
variable (T : Tower k r hr) (Tb : Tower k (r*d) hrd)

/-- Actual stage morphisms, with specified coefficient and chart reductions,
including every cyclic boundary and every transition. -/
def IsTowerRamification (ρ : Fin d → (Chart k →+* Chart k))
    (f : ∀ n, (Tb.atlas n).X ⟶ (T.atlas n).X) : Prop :=
  (∀ n, ∃ β : R k n →+* R k n,
    β.comp (trunc (PowerSeries k) PowerSeries.X n) =
      (trunc (PowerSeries k) PowerSeries.X n).comp (baseMap k d hd) ∧
    f n ≫ (T.atlas n).p = (Tb.atlas n).p ≫ Spec.map (CommRingCat.ofHom β) ∧
    ∀ i : Fin (r*d), ∃ η : A k n →+* A k n,
      η.comp (ArithmeticThetaKatoAnnularR0152.reduction k n) = (ArithmeticThetaKatoAnnularR0152.reduction k n).comp (ρ (residueIndex r d hd i)) ∧
      (Tb.atlas n).chart i ≫ f n = Spec.map (CommRingCat.ofHom η) ≫
        (T.atlas n).chart (coarseIndex r d hd i)) ∧
  (∀ n N (h : n ≤ N), Tb.transition n N h ≫ f N = f n ≫ T.transition n N h)

variable (M : Model k T) (Mb : Model k Tb)

/-- Actual model morphism over t=s^d, specified on all completed charts. -/
def IsModelRamification (ρ : Fin d → (Chart k →+* Chart k))
    (χ : Fin r → (chartScheme k ⟶ M.X))
    (χb : Fin (r*d) → (chartScheme k ⟶ Mb.X)) (F : Mb.X ⟶ M.X) : Prop :=
  F ≫ M.p = Mb.p ≫ baseMorphism k d hd ∧
  ∀ i : Fin (r*d), χb i ≫ F =
    Spec.map (CommRingCat.ofHom (ρ (residueIndex r d hd i))) ≫ χ (coarseIndex r d hd i)

def IsGenericLift (F : Mb.X ⟶ M.X)
    (f : genericScheme k Mb ⟶ genericScheme k M) : Prop :=
  f ≫ genericInclusion k M = genericInclusion k Mb ≫ F

end ArithmeticThetaRamifiedPeriodR0154
