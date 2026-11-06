import Mathlib
import FunctionOrders
import SmoothPrerequisites

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

def baseToResidue (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : k →+* X.residueField x :=
  (Scheme.Γevaluation X x).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

def placeDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) := (baseToResidue k f x).toAlgebra
  Module.finrank k (X.residueField x)

def OneDimensionalCharts (X : Scheme.{u}) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U],
    Ring.DimensionLEOne Γ(X, U)

def principalOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) : X → ℤ :=
  fun x => Scheme.ord g x

def weightedDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (D : X →₀ ℤ) : ℤ :=
  D.sum (fun x n => (placeDegree k f x : ℤ) * n)

def MatchesPrincipalOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (D : X →₀ ℤ) : Prop :=
  ∀ x, D x = principalOrder X g x

end ArithmeticThetaCurveDegree
