module
public import RelativeWeierstrassPresentationR0174
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal
namespace PalomarConormal673
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (e : S ⟶ X)
/-- The conormal map sends every pulled-back ideal section to the pulled-back relative differential.
This condition uniquely specifies the map on all open sets and all ideal sections. -/
theorem normalized_iff_original
    (m : (Scheme.Modules.pullback e).obj e.ker.module ⟶
      (Scheme.Modules.pullback e).obj c.kaehler) :
    (∀ (U : X.Opens) (x : Γ(e.ker.module, U)),
      m.app (e ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection e x) =
        Scheme.Modules.pullbackLocalSection e (relativeD c U (e.ker.moduleι.app U x))) ↔
      m = conormalMap c e := by
  constructor
  · intro h
    apply Scheme.Modules.pullback_hom_ext e
    intro U x
    exact (h U x).trans (conormalMap_pullback c e U x).symm
  · rintro rfl
    exact conormalMap_pullback c e
end PalomarConormal673
