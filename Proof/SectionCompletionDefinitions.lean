module

public import SectionDegreeBound
public import DivisorDegreeLaws
public import GenericLineCoefficients
public import SchemeExpansionOrder
public import CuspOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

universe u v w
noncomputable section
namespace ArithmeticThetaSectionCompletion

/-- The specific action of global regular functions induced by their generic
point germs. This only supplies the nonempty-top instance explicitly. -/
instance globalFunctionFieldAlgebra (X : Scheme.{u}) [IsIntegral X] :
    Algebra Γ(X, ⊤) X.functionField :=
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, Set.mem_univ _⟩⟩
  (X.germToFunctionField ⊤).hom.toAlgebra

/-- The classical rational-function model L(D), with zero handled separately
because Scheme.ord uses a totalized zero value. -/
def divisorFunctionSet (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (D : X →₀ ℤ) : Set X.functionField :=
  {g | g = 0 ∨ ∀ x : X, 0 ≤ Scheme.ord g x + D x}

/-- Ratio of two actual global sections, in the given actual frame. -/
def sectionRatio (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    {ι : Type v} (C : NormalFrameCover X H ι) (i : ι)
    (s s₀ : Γ(H, ⊤)) : X.functionField :=
  sectionCoefficient X H (C.opens i) (C.frame i) s /
    sectionCoefficient X H (C.opens i) (C.frame i) s₀

/-- The maximal-ideal adic completion of an actual local ring. -/
abbrev completedLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- The canonical completion map followed by a chosen completed coordinate.
No arbitrary expansion homomorphism or uniformizer-order premise occurs. -/
def completionExpansion (R : Type u) [CommRing R] [IsLocalRing R]
    (k : Type w) [Field k]
    (e : completedLocalRing R ≃+* PowerSeries k) : R →+* PowerSeries k :=
  e.toRingHom.comp (algebraMap R (completedLocalRing R))

/-- The actual germ of a global section's coordinate in its local frame. -/
def sectionGerm (X : Scheme.{u}) (H : X.Modules) {ι : Type v}
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤))
    (i : ι) (x : X) (hx : x ∈ C.opens i) : X.presheaf.stalk x :=
  X.presheaf.germ (C.opens i) x hx
    (sectionCoordinate X H (C.opens i) (C.frame i) s)

/-- Completed expansion of a section in an actual local frame. -/
def completedSection (X : Scheme.{u}) (H : X.Modules) {ι : Type v}
    (C : NormalFrameCover X H ι) (s : Γ(H, ⊤))
    (i : ι) (x : X) (hx : x ∈ C.opens i) (k : Type w) [Field k]
    (e : completedLocalRing (X.presheaf.stalk x) ≃+* PowerSeries k) : PowerSeries k :=
  completionExpansion (X.presheaf.stalk x) k e (sectionGerm X H C s i x hx)

end ArithmeticThetaSectionCompletion
