module

public import PullbackTensor
public import PullbackTensorDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace ArithmeticThetaPullback

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

/-- Naturality of the sheafification unit, evaluated on a local section. -/
theorem sheafifyMap_unit_apply (X : Scheme.{u}) {M N : X.PresheafOfModules}
    (f : M ⟶ N) (U : X.Opens) (m : M.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M).app
        (op U) m) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app N).app
      (op U) (f.app (op U) m) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op U))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.naturality f).symm) m

/-- The comparison of the two composite left adjoints preserves their unit sections. -/
theorem sheafificationCompPullback_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (M : Y.PresheafOfModules) (U : Y.Opens) (m : M.obj (op U)) :
    ((SheafOfModules.sheafificationCompPullback p.toRingCatSheafHom).app M).hom.val.app
      (op (p ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj M)).app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M).app
          (op U) m)) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((presheafPullback X Y p).obj M)).app (op (p ⁻¹ᵁ U))
      (((presheafAdjunction X Y p).unit.app M).app (op U) m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom))
    ((presheafAdjunction X Y p).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj))) M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app (op U)) h) m

/-- The explicit construction of pullback carries the actual unit to its presheaf form. -/
theorem pullbackIso_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) :
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).hom.val.app (op (p ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H).app U s) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((presheafPullback X Y p).obj H.val)).app (op (p ⁻¹ᵁ U))
      (((presheafAdjunction X Y p).unit.app H.val).app (op U) s) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction p.toRingCatSheafHom)
    (SheafOfModules.PullbackConstruction.adjunction p.toRingCatSheafHom) H
  have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app (op U)) h)
    (show H.val.obj (op U) from s)
  exact h'

/-- The inverse construction comparison returns the actual adjunction-unit section. -/
theorem pullbackIso_inv_unit_apply (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) :
    ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).inv.val.app (op (p ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((presheafPullback X Y p).obj H.val)).app (op (p ⁻¹ᵁ U))
        (((presheafAdjunction X Y p).unit.app H.val).app (op U) s)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app H).app U s := by
  rw [← pullbackIso_unit_apply X Y p H U s]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app (op (p ⁻¹ᵁ U)))
      ((SheafOfModules.pullbackIso p.toRingCatSheafHom).app H).hom_inv_id) _

/-- The sheafified tensor comparison sends pure presheaf tensors to pure sheaf tensors. -/
theorem sheafificationTensorIso_unit_apply (X : Scheme.{u})
    (M N : X.PresheafOfModules) (U : X.Opens) (m : M.obj (op U)) (n : N.obj (op U)) :
    (sheafificationTensorIso X M N).hom.val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (M ⊗ N)).app (op U) (m ⊗ₜ[Γ(X, U)] n)) =
    tensorSection X _ _ U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M).app
        (op U) m)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app N).app
        (op U) n) := by
  exact sheafifyMap_unit_apply X _ U _

/-- Isomorphism functoriality acts on the two factors of a pure tensor. -/
theorem sheafTensorCongr_section (X : Scheme.{u}) {H H' K K' : X.Modules}
    (e : H ≅ H') (d : K ≅ K') (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (sheafTensorCongr X e d).hom.app U (tensorSection X H K U s t) =
      tensorSection X H' K' U (e.hom.app U s) (d.hom.app U t) := by
  exact sheafTensorMap_section X e.hom d.hom U s t

/-- The canonical pullback comparison preserves every pure global tensor. -/
theorem pullback_sheafTensor_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H K : Y.Modules) (s : Γ(H, ⊤)) (t : Γ(K, ⊤)) :
    (pullback_sheafTensor_iso X Y p H K).hom.app (p ⁻¹ᵁ (⊤ : Y.Opens))
      (pullbackGlobalSection p (sheafTensor Y H K) (tensorSection Y H K ⊤ s t)) =
    tensorSection X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K)
      (p ⁻¹ᵁ (⊤ : Y.Opens)) (pullbackGlobalSection p H s) (pullbackGlobalSection p K t) := by
  let U : Y.Opens := ⊤
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

/-- At exponent zero the canonical structure-sheaf comparison preserves one. -/
theorem pullback_unit_section (X Y : Scheme.{u}) (p : X ⟶ Y) :
    (pullback_unit_iso X Y p).hom.app (p ⁻¹ᵁ (⊤ : Y.Opens))
      (pullbackGlobalSection p (SheafOfModules.unit Y.ringCatSheaf) (1 : Γ(Y, ⊤))) =
    (1 : Γ(X, p ⁻¹ᵁ (⊤ : Y.Opens))) := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom
  have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app (op ⊤)) h)
    (show (SheafOfModules.unit Y.ringCatSheaf).val.obj (op ⊤) from (1 : Γ(Y, ⊤)))
  change _ = p.app ⊤ 1 at h'
  exact h'.trans (map_one (p.app ⊤).hom)

/-- Every recursively defined tensor power of a global section commutes with pullback. -/
theorem pullback_tensorPower_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H : Y.Modules) (n : ℕ) (s : Γ(H, ⊤)) :
    (pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ (⊤ : Y.Opens))
      (pullbackGlobalSection p (tensorPower Y H n) (tensorPowerSection Y H n ⊤ s)) =
    tensorPowerSection X ((Scheme.Modules.pullback p).obj H) n (p ⁻¹ᵁ (⊤ : Y.Opens))
      (pullbackGlobalSection p H s) := by
  induction n with
  | zero => exact pullback_unit_section X Y p
  | succ n ih =>
    change (sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)).hom.app
      (p ⁻¹ᵁ (⊤ : Y.Opens))
      ((pullback_sheafTensor_iso X Y p (tensorPower Y H n) H).hom.app
        (p ⁻¹ᵁ (⊤ : Y.Opens))
        (pullbackGlobalSection p (sheafTensor Y (tensorPower Y H n) H)
          (tensorSection Y (tensorPower Y H n) H ⊤ (tensorPowerSection Y H n ⊤ s) s))) = _
    rw [pullback_sheafTensor_section, sheafTensorCongr_section, ih]
    rfl

/-- Every ordered finite product commutes with pullback, including the empty product. -/
theorem pullback_tensorProduct_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H : Y.Modules) (n : ℕ) (s : Fin n → Γ(H, ⊤)) :
    (pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ (⊤ : Y.Opens))
      (pullbackGlobalSection p (tensorPower Y H n) (tensorProductSection Y H n ⊤ s)) =
    tensorProductSection X ((Scheme.Modules.pullback p).obj H) n (p ⁻¹ᵁ (⊤ : Y.Opens))
      (fun i => pullbackGlobalSection p H (s i)) := by
  induction n with
  | zero => exact pullback_unit_section X Y p
  | succ n ih =>
    change (sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)).hom.app
      (p ⁻¹ᵁ (⊤ : Y.Opens))
      ((pullback_sheafTensor_iso X Y p (tensorPower Y H n) H).hom.app
        (p ⁻¹ᵁ (⊤ : Y.Opens))
        (pullbackGlobalSection p (sheafTensor Y (tensorPower Y H n) H)
          (tensorSection Y (tensorPower Y H n) H ⊤
            (tensorProductSection Y H n ⊤ (fun i => s i.castSucc)) (s (Fin.last n))))) = _
    rw [pullback_sheafTensor_section, sheafTensorCongr_section, ih]
    rfl

end ArithmeticThetaPullback
