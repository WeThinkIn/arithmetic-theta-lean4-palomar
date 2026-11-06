import ActualKatoAnnularComparisonR0152
import AlgebraizedActionLawsR0137
import MarkedPointAdditionR0146
import ActualSplitTorsionKernelR0152

/-! Specified translations and completed scaling maps for the norm comparison.
No norm, field-action, or expansion assertion is built into these data. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaKatoAnnularR0152

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Pullback will be taken along the accepted actual rotation and scaling. -/
def translation (M : Model k T) (rot : M.X ≅ M.X)
    (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv) (i : Fin r) (a : kˣ) :
    genericScheme k M ⟶ genericScheme k M :=
  iterateHom (rotationMap k M rot scal inv ha) i.val ≫ scalarMap k M rot scal inv ha a

def shift (j i : Fin r) : Fin r := ⟨(j.val + i.val) % r, Nat.mod_lt _ hr⟩

/-- Defined by modular reduction, with d-divisibility proved in consumers. -/
def kernelIndex (d : ℕ) (a : Fin d) : Fin r :=
  ⟨((r / d) * a.val) % r, Nat.mod_lt _ hr⟩

/-- These are equations in the genuine completed node, fixing its entire base. -/
def IsScaling (a : kˣ) (e : Chart k ≃+* Chart k) : Prop :=
  (∀ b : PowerSeries k, e (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
    ArithmeticThetaAnnularTorsionPrereqR0053.base k b) ∧
  e (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
    ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C (a : k)) *
      ArithmeticThetaAnnularTorsionPrereqR0053.cx k ∧
  e (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
    ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C ((a⁻¹ : kˣ) : k)) *
      ArithmeticThetaAnnularTorsionPrereqR0053.cy k

def ExtendsScaling (e : Chart k ≃+* Chart k)
    (E : ChartField k ≃+* ChartField k) : Prop :=
  ∀ b : Chart k, E (chartToField k b) = chartToField k (e b)

/-- Every field automorphism must be induced by the specified geometric map. -/
def IsFieldAction (M : Model k T) [IsIntegral (genericScheme k M)]
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (ha : Actions k M rot scal inv)
    (σ : Fin r → kˣ → ((genericScheme k M).functionField ≃+*
      (genericScheme k M).functionField)) : Prop :=
  ∀ i a, ArithmeticThetaGeometricNormR0150.IsFieldMap
    (translation k M rot scal inv ha i a) (σ i a).toRingHom

end ArithmeticThetaSplitNormR0153
