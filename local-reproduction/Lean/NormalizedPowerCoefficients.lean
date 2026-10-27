import LocalPowerPullback

open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower ArithmeticThetaPullback
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField

universe u
noncomputable section

namespace ArithmeticThetaNormalizedSections

/-- Restricting the canonical global pullback agrees with the local adjunction unit. -/
theorem pullbackPowerSection_restrict (Y X : Scheme.{u}) (p : Y ⟶ X)
    (H : X.Modules) (n : ℕ) (U : X.Opens) (F : Γ(tensorPower X H n, ⊤)) :
    (tensorPower Y ((Scheme.Modules.pullback p).obj H) n).presheaf.map
      (homOfLE le_top).op (pullbackPowerSection p H n F) =
    (pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower X H n) U
        ((tensorPower X H n).presheaf.map (homOfLE le_top).op F)) := by
  have hcomp := PresheafOfModules.naturality_apply
    (pullback_tensorPower_iso Y X p H n).hom.val
    (homOfLE (show p ⁻¹ᵁ U ≤ p ⁻¹ᵁ (⊤ : X.Opens) from p.preimage_mono le_top)).op
    (pullbackGlobalSection p (tensorPower X H n) F)
  have hunit := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tensorPower X H n)).val
    (homOfLE (show U ≤ ⊤ from le_top)).op F
  exact hcomp.symm.trans (congrArg
    ((pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ U)) hunit.symm)

/-- The local coordinate of the actual global tensor pullback is the pulled scalar. -/
theorem pullbackPowerSection_coordinate (Y X : Scheme.{u}) (p : Y ⟶ X)
    (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U))
    (he : FramePullbackCompatible p H U e eY) (n : ℕ)
    (F : Γ(tensorPower X H n, ⊤)) :
    sectionCoordinate Y (tensorPower Y ((Scheme.Modules.pullback p).obj H) n)
      (p ⁻¹ᵁ U) (tensorPowerFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U) eY n)
      (pullbackPowerSection p H n F) =
    p.app U (sectionCoordinate X (tensorPower X H n) U (tensorPowerFrame X H U e n) F) := by
  unfold sectionCoordinate
  rw [pullbackPowerSection_restrict, local_power_pullback_coordinate Y X p H U e eY he]
  exact LinearEquiv.symm_apply_apply _ _

/-- Actual tensor-power coefficients commute with the normalization's function-field map. -/
theorem normalization_powerCoefficient
    (X : Scheme.{u}) [IsIntegral X] (E : Type u) [Field E] [Algebra X.functionField E]
    (H : X.Modules) (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (eY : LocalFrame (extensionNormalization X E)
      ((Scheme.Modules.pullback (extensionFromNormalization X E)).obj H)
      (extensionFromNormalization X E ⁻¹ᵁ U))
    (he : FramePullbackCompatible (extensionFromNormalization X E) H U e eY)
    (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) :
    powerCoefficient (extensionNormalization X E)
      ((Scheme.Modules.pullback (extensionFromNormalization X E)).obj H)
      (extensionFromNormalization X E ⁻¹ᵁ U) eY n
      (pullbackPowerSection (extensionFromNormalization X E) H n F) =
    normalizationBaseFieldMap X E (powerCoefficient X H U e n F) := by
  unfold powerCoefficient sectionCoefficient
  rw [pullbackPowerSection_coordinate _ _ _ _ _ _ _ he]
  exact (ConcreteCategory.congr_hom (normalizationBaseFieldMap_germ X E U)
    (sectionCoordinate X (tensorPower X H n) U (tensorPowerFrame X H U e n) F)).symm

end ArithmeticThetaNormalizedSections
