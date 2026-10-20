module

public import NormalizedSectionDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
open ArithmeticThetaPullback

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace ArithmeticThetaNormalizedSections

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- The canonical pullback comparison preserves every pure tensor on an arbitrary open. -/
theorem pullback_sheafTensor_local_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H K : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (pullback_sheafTensor_iso X Y p H K).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (sheafTensor Y H K) U (tensorSection Y H K U s t)) =
    tensorSection X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K)
      (p ⁻¹ᵁ U) (pullbackLocalSection p H U s) (pullbackLocalSection p K U t) := by
  change (sheafTensorCongr X
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm).hom.app (p ⁻¹ᵁ U)
    ((sheafificationTensorIso X ((presheafPullback X Y p).obj H.val)
      ((presheafPullback X Y p).obj K.val)).hom.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (presheafPullbackTensorMap X Y p H.val K.val)).val.app (op (p ⁻¹ᵁ U))
        (((SheafOfModules.sheafificationCompPullback p.toRingCatSheafHom).app
          (tensorPresheaf Y H K)).hom.val.app (op (p ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
            (sheafTensor Y H K)).app U
            (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              (tensorPresheaf Y H K)).app (op U) (s ⊗ₜ[Γ(Y, U)] t)))))) = _
  erw [sheafificationCompPullback_unit_apply X Y p (tensorPresheaf Y H K) U
    (s ⊗ₜ[Γ(Y, U)] t)]
  erw [sheafifyMap_unit_apply X (presheafPullbackTensorMap X Y p H.val K.val)
    (p ⁻¹ᵁ U)]
  erw [presheafPullbackTensorMap_unit_apply X Y p H.val K.val U s t]
  erw [sheafificationTensorIso_unit_apply X ((presheafPullback X Y p).obj H.val)
    ((presheafPullback X Y p).obj K.val) (p ⁻¹ᵁ U)]
  erw [sheafTensorCongr_section X
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).symm
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).symm (p ⁻¹ᵁ U)]
  change tensorSection X _ _ (p ⁻¹ᵁ U)
    (((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).inv.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((presheafPullback X Y p).obj H.val)).app (op (p ⁻¹ᵁ U))
        (((presheafAdjunction X Y p).unit.app H.val).app (op U) s)))
    (((SheafOfModules.pullbackIso p.toRingCatSheafHom).app K).inv.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((presheafPullback X Y p).obj K.val)).app (op (p ⁻¹ᵁ U))
        (((presheafAdjunction X Y p).unit.app K.val).app (op U) t))) = _
  erw [pullbackIso_inv_unit_apply X Y p H U s, pullbackIso_inv_unit_apply X Y p K U t]
  rfl

/-- The structure-sheaf comparison acts by the actual ring map on every local section. -/
theorem pullback_unit_local_section (Y X : Scheme.{u}) (p : Y ⟶ X)
    (U : X.Opens) (a : Γ(X, U)) :
    (pullback_unit_iso Y X p).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (SheafOfModules.unit X.ringCatSheaf) U a) = p.app U a := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app (op U)) h)
    (show (SheafOfModules.unit X.ringCatSheaf).val.obj (op U) from a)

/-- The tensor comparison takes each frame-coordinate section to its pulled coefficient. -/
theorem local_power_pullback_frame (Y X : Scheme.{u}) (p : Y ⟶ X)
    (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U))
    (he : FramePullbackCompatible p H U e eY) (n : ℕ) (a : Γ(X, U)) :
    (pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower X H n) U
        ((tensorPowerFrame X H U e n).equiv U le_rfl a)) =
    (tensorPowerFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U) eY n).equiv
      (p ⁻¹ᵁ U) le_rfl (p.app U a) := by
  induction n generalizing a with
  | zero => exact pullback_unit_local_section Y X p U a
  | succ n ih =>
    change (sheafTensorCongr Y (pullback_tensorPower_iso Y X p H n) (Iso.refl _)).hom.app
      (p ⁻¹ᵁ U)
      ((pullback_sheafTensor_iso Y X p (tensorPower X H n) H).hom.app (p ⁻¹ᵁ U)
        (pullbackLocalSection p (sheafTensor X (tensorPower X H n) H) U
          ((tensorFrame X (tensorPower X H n) H U (tensorPowerFrame X H U e n) e).equiv
            U le_rfl a))) = _
    rw [tensorFrame_apply, pullback_sheafTensor_local_section, sheafTensorCongr_section]
    rw [ih 1, he U le_rfl a]
    simp only [map_one]
    rfl

/-- Local coordinate formula for every section of the actual tensor power, including zero. -/
theorem local_power_pullback_coordinate (Y X : Scheme.{u}) (p : Y ⟶ X)
    (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U)
    (eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U))
    (he : FramePullbackCompatible p H U e eY) (n : ℕ) (F : Γ(tensorPower X H n, U)) :
    (pullback_tensorPower_iso Y X p H n).hom.app (p ⁻¹ᵁ U)
      (pullbackLocalSection p (tensorPower X H n) U F) =
    (tensorPowerFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U) eY n).equiv
      (p ⁻¹ᵁ U) le_rfl (p.app U (((tensorPowerFrame X H U e n).equiv U le_rfl).symm F)) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    local_power_pullback_frame Y X p H U e eY he n
      (((tensorPowerFrame X H U e n).equiv U le_rfl).symm F)

end ArithmeticThetaNormalizedSections
