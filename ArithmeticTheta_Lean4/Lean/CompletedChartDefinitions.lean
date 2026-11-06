import ProperFormalFunctions
import ProperCoherentFormalSections
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.LaurentSeries

/-! Actual structural section modules and their parameter completions.
No existence, regularity, normality, flatness or algebraization is stored as data. -/
open AlgebraicGeometry CategoryTheory Opposite
universe u
noncomputable section
namespace ArithmeticThetaCompletedCharts

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R)

/-- Sections of O with the R-action induced by f. -/
abbrev Sections (U : X.Opens) := (OModulePresheaf.unit f).obj U

/-- Parameter-adic completion of the actual section module. Its underlying
filtration is t^n Γ(U,O), not an arbitrary finite R-module. -/
abbrev Completed (U : X.Opens) := AdicCompletion (Ideal.span {t}) (Sections R X f U)

/-- The actual restriction, completed and then restricted to R-scalars. -/
def completedRestriction {U V : X.Opens} (h : V ≤ U) :
    Completed R X f t U →ₗ[R] Completed R X f t V :=
  (AdicCompletion.map (Ideal.span {t}) ((OModulePresheaf.unit f).res h)).restrictScalars R

/-- Completion of the actual restriction of a global regular function. -/
def globalToCompleted (U : X.Opens) : Sections R X f ⊤ →ₗ[R] Completed R X f t U :=
  (AdicCompletion.of (Ideal.span {t}) (Sections R X f U)).comp
    ((OModulePresheaf.unit f).res (show U ≤ ⊤ from le_top))

abbrev CompletedFamily (C : X.OrderedAffineCover) := ∀ i : C.ι, Completed R X f t (C.U i)

/-- Equality in the completion of the actual overlap section ring. -/
def Compatible (C : X.OrderedAffineCover) (z : CompletedFamily R X f t C) : Prop :=
  ∀ i j, completedRestriction R X f t (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) (z i) =
    completedRestriction R X f t (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) (z j)

/-- Inversion of powers of the same base parameter on the completed module. -/
abbrev LocalizedCompleted (U : X.Opens) :=
  LocalizedModule (Submonoid.powers t) (Completed R X f t U)

abbrev toLocalized (U : X.Opens) : Completed R X f t U →ₗ[R] LocalizedCompleted R X f t U :=
  LocalizedModule.mkLinearMap (Submonoid.powers t) (Completed R X f t U)

def localizedRestriction {U V : X.Opens} (h : V ≤ U) :
    LocalizedCompleted R X f t U →ₗ[R] LocalizedCompleted R X f t V :=
  IsLocalizedModule.map (Submonoid.powers t) (toLocalized R X f t U)
    (toLocalized R X f t V) (completedRestriction R X f t h)

abbrev LocalizedFamily (C : X.OrderedAffineCover) :=
  ∀ i : C.ι, LocalizedCompleted R X f t (C.U i)

def LocalizedCompatible (C : X.OrderedAffineCover) (z : LocalizedFamily R X f t C) : Prop :=
  ∀ i j, localizedRestriction R X f t (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) (z i) =
    localizedRestriction R X f t (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) (z j)

end ArithmeticThetaCompletedCharts
