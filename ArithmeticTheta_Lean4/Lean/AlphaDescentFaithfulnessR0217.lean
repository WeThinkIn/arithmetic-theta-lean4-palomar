import InverseCharacterMultiplierR0217

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open ArithmeticThetaPullback
universe u
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ArithmeticThetaMultiplierKeyR0217.AlphaDescentFaithfulness

theorem pullback_hom_injective {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsAffineHom p] [Flat p] [Surjective p]
    {M N : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) (f g : M ⟶ N)
    (h : (Scheme.Modules.pullback p).map f = (Scheme.Modules.pullback p).map g) : f = g := by
  apply (Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    p M N hM hN).1
  ext i
  exact h

theorem pullback_section_injective {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsAffineHom p] [Flat p] [Surjective p]
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M) :
    Function.Injective (pullbackGlobalSection p M) := by
  intro s t h
  let f := ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection M s
  let g := ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection M t
  have hfg : f = g := by
    apply pullback_hom_injective p (Scheme.Modules.isInvertible_unit Y) hM
    apply InverseCharacterMultiplier.hom_ext_of_frame
      (pullbackGlobalSection p (𝟙_ Y.Modules) (1 : Γ(Y, ⊤)))
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame
        p _ _ (InverseCharacterMultiplier.unit_frame Y))
    erw [← Scheme.Modules.pullbackLocalSection_app p f (1 : Γ(Y, ⊤)),
      ← Scheme.Modules.pullbackLocalSection_app p g (1 : Γ(Y, ⊤))]
    simpa [f, g, ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection_apply,
      pullbackGlobalSection, Scheme.Modules.pullbackLocalSection] using h
  have hst := congrArg (fun j => j.app ⊤ (1 : Γ(Y, ⊤))) hfg
  simpa [f, g, ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection_apply] using hst

#print axioms pullback_section_injective
end ArithmeticThetaMultiplierKeyR0217.AlphaDescentFaithfulness
