module
public import RelativeHodgePowerBaseChangeR0171
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSheafTensor ArithmeticThetaPullback
namespace PalomarTensor688
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules)
/-- The tensor comparison is uniquely determined on pulled-back pure local tensors,
for every open set and every pair of module sections. -/
theorem normalized_iff_original
    (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅
      sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K)) :
    (∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)),
      q.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t)) =
        tensorSection X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K)
          (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) (Scheme.Modules.pullbackLocalSection f t)) ↔
    q = pullback_sheafTensor_iso X Y f H K := by
  constructor
  · intro h
    apply Iso.ext
    apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
    apply ArithmeticThetaSheafTensor.tensor_hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    change q.hom.app (f ⁻¹ᵁ U.unop)
      (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U.unop s t)) =
      (pullback_sheafTensor_iso X Y f H K).hom.app (f ⁻¹ᵁ U.unop)
        (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U.unop s t))
    exact (h U.unop s t).trans
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section X Y f H K U.unop s t).symm
  · rintro rfl
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section X Y f H K
end PalomarTensor688
