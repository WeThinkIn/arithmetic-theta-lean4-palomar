import RamifiedLiteralNormRealizationR0156
import ActualKatoAnnularComparisonR0152
import ActualKatoFieldBaseChangeR0151

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaCoefficientNormDescentR0157
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoAnnularR0152

variable (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
variable (ι : k →+* l)

def baseMap : PowerSeries k →+* PowerSeries l := PowerSeries.map ι

def baseMorphism : baseScheme l ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (baseMap k l ι))

def IsLaurentMap (ell : LaurentSeries k →+* LaurentSeries l) : Prop :=
  ∀ b : PowerSeries k, ell (algebraMap (PowerSeries k) (LaurentSeries k) b) =
    algebraMap (PowerSeries l) (LaurentSeries l) (baseMap k l ι b)

/-- Coefficient change on the actual completed node, including its filtration. -/
def IsChartMap (ρ : Chart k →+* Chart l) : Prop :=
  (∀ b : PowerSeries k, ρ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
    ArithmeticThetaAnnularTorsionPrereqR0053.base l (baseMap k l ι b)) ∧
  ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) = ArithmeticThetaAnnularTorsionPrereqR0053.cx l ∧
  ρ (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) = ArithmeticThetaAnnularTorsionPrereqR0053.cy l ∧
  (∀ (n : ℕ) (b : Chart k), b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration k n →
    ρ b ∈ ArithmeticThetaAnnularTorsionPrereqR0053.filtration l n)

def ExtendsChart (ρ : Chart k →+* Chart l) (E : ChartField k →+* ChartField l) : Prop :=
  ∀ b : Chart k, E (chartToField k b) = chartToField l (ρ b)

variable {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (Tl : Tower l r hr)

/-- Actual finite-stage coefficient maps, all chart equations and transitions. -/
def IsTowerMap (ρ : Chart k →+* Chart l)
    (f : ∀ n, (Tl.atlas n).X ⟶ (T.atlas n).X) : Prop :=
  (∀ n, ∃ β : R k n →+* R l n,
    β.comp (trunc (PowerSeries k) PowerSeries.X n) =
      (trunc (PowerSeries l) PowerSeries.X n).comp (baseMap k l ι) ∧
    IsPullback (f n) (Tl.atlas n).p (T.atlas n).p (Spec.map (CommRingCat.ofHom β)) ∧
    ∀ j : Fin r, ∃ η : A k n →+* A l n,
      η.comp (ArithmeticThetaKatoAnnularR0152.reduction k n) =
        (ArithmeticThetaKatoAnnularR0152.reduction l n).comp ρ ∧
      (Tl.atlas n).chart j ≫ f n = Spec.map (CommRingCat.ofHom η) ≫ (T.atlas n).chart j) ∧
  (∀ n N (h : n ≤ N), Tl.transition n N h ≫ f N = f n ≫ T.transition n N h)

variable (M : Model k T) (Ml : Model l Tl)

def IsModelMap (ρ : Chart k →+* Chart l)
    (χ : Fin r → (chartScheme k ⟶ M.X)) (χl : Fin r → (chartScheme l ⟶ Ml.X))
    (F : Ml.X ⟶ M.X) : Prop :=
  IsPullback F Ml.p M.p (baseMorphism k l ι) ∧
  ∀ j : Fin r, χl j ≫ F = Spec.map (CommRingCat.ofHom ρ) ≫ χ j

def IsGenericLift (F : Ml.X ⟶ M.X)
    (b : genericScheme l Ml ⟶ genericScheme k M) : Prop :=
  b ≫ genericInclusion k M = genericInclusion l Ml ≫ F

end ArithmeticThetaCoefficientNormDescentR0157
