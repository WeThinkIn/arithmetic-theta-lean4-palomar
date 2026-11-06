module

public import PullbackTensorSections
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open ArithmeticThetaSheafTensor ArithmeticThetaPullback
universe u
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ArithmeticThetaMultiplierKeyR0217.AlphaTensorCoherence
theorem pullback_tensor_local (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H K : Y.Modules) (U : Y.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
    (pullback_sheafTensor_iso X Y p H K).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (tensorSection Y H K U s t)) =
    tensorSection X ((Scheme.Modules.pullback p).obj H) ((Scheme.Modules.pullback p).obj K)
      (p ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection p s) (Scheme.Modules.pullbackLocalSection p t) := by
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


theorem tensor_comp (X Y Z : Scheme.{u}) (p : X ⟶ Y) (q : Y ⟶ Z)
    (H K : Z.Modules) :
    ((Scheme.Modules.pullbackComp p q).app (sheafTensor Z H K)).hom ≫
      (pullback_sheafTensor_iso X Z (p ≫ q) H K).hom =
    (Scheme.Modules.pullback p).map (pullback_sheafTensor_iso Y Z q H K).hom ≫
      (pullback_sheafTensor_iso X Y p ((Scheme.Modules.pullback q).obj H)
        ((Scheme.Modules.pullback q).obj K)).hom ≫
      (sheafTensorCongr X ((Scheme.Modules.pullbackComp p q).app H)
        ((Scheme.Modules.pullbackComp p q).app K)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).injective
  apply tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change Γ(H, U.unop) at s
  change Γ(K, U.unop) at t
  change (pullback_sheafTensor_iso X Z (p ≫ q) H K).hom.app _
      (((Scheme.Modules.pullbackComp p q).app (sheafTensor Z H K)).hom.app _
        (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q
          (tensorSection Z H K U.unop s t)))) =
    (sheafTensorCongr X ((Scheme.Modules.pullbackComp p q).app H)
        ((Scheme.Modules.pullbackComp p q).app K)).hom.app _
      ((pullback_sheafTensor_iso X Y p ((Scheme.Modules.pullback q).obj H)
        ((Scheme.Modules.pullback q).obj K)).hom.app _
        (((Scheme.Modules.pullback p).map (pullback_sheafTensor_iso Y Z q H K).hom).app _
          (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q
            (tensorSection Z H K U.unop s t)))))
  simp only [Iso.app_hom]
  rw [Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection,
    ← Scheme.Modules.pullbackLocalSection_app, pullback_tensor_local,
    pullback_tensor_local]
  erw [pullback_tensor_local X Z (p ≫ q) H K U.unop s t]
  erw [sheafTensorCongr_section X ((Scheme.Modules.pullbackComp p q).app H)
    ((Scheme.Modules.pullbackComp p q).app K) (p ⁻¹ᵁ (q ⁻¹ᵁ U.unop))
    (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q s))
    (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q t))]
  simp only [Iso.app_hom]
  erw [Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection p q H U.unop s,
    Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection p q K U.unop t]
  rfl

theorem tensor_naturality (X Y : Scheme.{u}) (p : X ⟶ Y)
    {H H' K K' : Y.Modules} (e : H ≅ H') (d : K ≅ K') :
    (Scheme.Modules.pullback p).map (sheafTensorCongr Y e d).hom ≫
      (pullback_sheafTensor_iso X Y p H' K').hom =
    (pullback_sheafTensor_iso X Y p H K).hom ≫
      (sheafTensorCongr X ((Scheme.Modules.pullback p).mapIso e)
        ((Scheme.Modules.pullback p).mapIso d)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  apply tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change Γ(H, U.unop) at s
  change Γ(K, U.unop) at t
  change (pullback_sheafTensor_iso X Y p H' K').hom.app _
      (((Scheme.Modules.pullback p).map (sheafTensorCongr Y e d).hom).app _
        (Scheme.Modules.pullbackLocalSection p (tensorSection Y H K U.unop s t))) =
    (sheafTensorCongr X ((Scheme.Modules.pullback p).mapIso e)
      ((Scheme.Modules.pullback p).mapIso d)).hom.app _
      ((pullback_sheafTensor_iso X Y p H K).hom.app _
        (Scheme.Modules.pullbackLocalSection p (tensorSection Y H K U.unop s t)))
  rw [← Scheme.Modules.pullbackLocalSection_app, sheafTensorCongr_section,
    pullback_tensor_local, pullback_tensor_local, sheafTensorCongr_section,
    Scheme.Modules.pullbackLocalSection_app, Scheme.Modules.pullbackLocalSection_app]
  rfl

theorem congr_comp {X : Scheme.{u}} {H H' H'' K K' K'' : X.Modules}
    (e : H ≅ H') (e' : H' ≅ H'') (d : K ≅ K') (d' : K' ≅ K'') :
    (sheafTensorCongr X e d).hom ≫ (sheafTensorCongr X e' d').hom =
      (sheafTensorCongr X (e ≪≫ e') (d ≪≫ d')).hom := by
  simp only [sheafTensorCongr, Functor.mapIso_hom, tensorIso_hom, Iso.trans_hom,
    ← Functor.map_comp, tensorHom_comp_tensorHom]

theorem tensor_congr (X Y : Scheme.{u}) (p q : X ⟶ Y) (h : p = q) (H K : Y.Modules) :
    ((Scheme.Modules.pullbackCongr h).app (sheafTensor Y H K)).hom ≫
      (pullback_sheafTensor_iso X Y q H K).hom =
    (pullback_sheafTensor_iso X Y p H K).hom ≫
      (sheafTensorCongr X ((Scheme.Modules.pullbackCongr h).app H)
        ((Scheme.Modules.pullbackCongr h).app K)).hom := by
  subst q
  simp [Scheme.Modules.pullbackCongr, sheafTensorCongr]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem tensor_over (X Y : Scheme.{u}) (p : X ⟶ Y) (q : X ⟶ X)
    (h : q ≫ p = p) (H K : Y.Modules) (J : X.Modules)
    (c : (Scheme.Modules.pullback p).obj H ≅ J)
    (d : (Scheme.Modules.pullback q).obj J ≅ J)
    (hc : (Scheme.Modules.pullback q).map c.hom ≫ d.hom =
      ((Scheme.Modules.pullbackComp q p).app H).hom ≫
        ((Scheme.Modules.pullbackCongr h).app H).hom ≫ c.hom) :
    (((Scheme.Modules.pullbackComp q p).app (sheafTensor Y H K)) ≪≫
      (Scheme.Modules.pullbackCongr h).app (sheafTensor Y H K)).hom ≫
      (pullback_sheafTensor_iso X Y p H K ≪≫ sheafTensorCongr X c (Iso.refl _)).hom =
    (Scheme.Modules.pullback q).map
      (pullback_sheafTensor_iso X Y p H K ≪≫ sheafTensorCongr X c (Iso.refl _)).hom ≫
      (pullback_sheafTensor_iso X X q J ((Scheme.Modules.pullback p).obj K) ≪≫
        sheafTensorCongr X d ((Scheme.Modules.pullbackComp q p).app K ≪≫
          (Scheme.Modules.pullbackCongr h).app K)).hom := by
  have he : (Scheme.Modules.pullback q).mapIso c ≪≫ d =
      (Scheme.Modules.pullbackComp q p).app H ≪≫ (Scheme.Modules.pullbackCongr h).app H ≪≫ c := by
    apply Iso.ext
    exact hc
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullbackCongr h).app (sheafTensor Y H K)).hom,
    tensor_congr X Y (q ≫ p) p h H K]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullbackComp q p).app (sheafTensor Y H K)).hom,
    tensor_comp X X Y q p H K]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback q).map (sheafTensorCongr X c (Iso.refl _)).hom),
    tensor_naturality X X q c (Iso.refl _)]
  simp only [Category.assoc]
  rw [← Category.assoc (sheafTensorCongr X ((Scheme.Modules.pullbackComp q p).app H)
      ((Scheme.Modules.pullbackComp q p).app K)).hom,
    congr_comp, congr_comp, congr_comp, he]
  simp only [Iso.trans_assoc, Iso.trans_refl, Functor.mapIso_refl, Iso.refl_trans]

#print axioms tensor_over

#print axioms tensor_comp
#print axioms tensor_naturality
#print axioms tensor_congr

end ArithmeticThetaMultiplierKeyR0217.AlphaTensorCoherence
