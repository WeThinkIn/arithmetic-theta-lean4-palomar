module

public import NormalizedSectionDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace ArithmeticThetaNormalizedSections

/-- A frame gives a trivialization on the corresponding open subscheme. -/
def frameRestrictIso (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ≅ H.restrict U.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ ModuleCat.isoMk
        (show AddCommGrpCat.of Γ(X, U.ι ''ᵁ V.unop) ≅ AddCommGrpCat.of Γ(H, U.ι ''ᵁ V.unop) from
        (forget₂ (ModuleCat Γ(X, U.ι ''ᵁ V.unop)) Ab).mapIso
          (e.equiv (U.ι ''ᵁ V.unop) (U.ι_image_le V.unop)).toModuleIso)
        (by
          intro (r : Γ(X, U.ι ''ᵁ V.unop))
          ext (a : Γ(X, U.ι ''ᵁ V.unop))
          symm
          change e.equiv _ _ (r * a) = (U.ι.appIso V.unop).inv r • e.equiv _ _ a
          rw [Scheme.Opens.ι_appIso]
          exact (e.equiv _ _).map_smul r a))
      (fun {V W} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (e.naturality _ _ (U.ι.image_mono f.unop.le) _ a).symm))

/-- The restriction unit is invertible on every subopen of the restricting open. -/
theorem overRestrictUnit_isIso (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) :
    IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app H).over U) := by
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (H.presheaf.map
    (homOfLE (U.ι.image_preimage_le V.unop.left)).op)
  have h : U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop.left) = V.unop.left := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr V.unop.hom.le]
  have he : homOfLE (U.ι.image_preimage_le V.unop.left) = eqToHom h := Subsingleton.elim _ _
  rw [he]
  infer_instance

/-- Restriction-unit comparison on the original open site. -/
def overRestrictUnitIso (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) :
    SheafOfModules.over H U ≅
      SheafOfModules.over ((Scheme.Modules.pushforward U.ι).obj (H.restrict U.ι)) U := by
  haveI := overRestrictUnit_isIso X H U
  exact asIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app H).over U)

/-- Convert a trivialization on an open subscheme into the original-site frame. -/
def frameOfRestrictIso (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (E : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ H.restrict U.ι) :
    LocalFrame X H U :=
  localFrameOfIso X H U (
    overRestrictUnitIso X (SheafOfModules.unit X.ringCatSheaf) U ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
        ((Scheme.Modules.pushforward U.ι).mapIso (Scheme.Modules.restrictUnitIso U.ι)) ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
        ((Scheme.Modules.pushforward U.ι).mapIso E) ≪≫
      (overRestrictUnitIso X H U).symm)

/-- The converted frame agrees with its given open-subscheme trivialization. -/
theorem frameOfRestrictIso_apply (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (E : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ H.restrict U.ι)
    (V : X.Opens) (hVU : V ≤ U) (a : Γ(X,V)) :
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app H).app V
      ((frameOfRestrictIso X H U E).equiv V hVU a) =
    (Scheme.Modules.Hom.app E.hom) (U.ι ⁻¹ᵁ V) (U.ι.app V a) := by
  let T := op (Over.mk (homOfLE hVU))
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app T) (overRestrictUnitIso X H U).inv_hom_id)
  change (overRestrictUnitIso X H U).hom.val.app T
    ((overRestrictUnitIso X H U).inv.val.app T
      ((Scheme.Modules.Hom.app E.hom) (U.ι ⁻¹ᵁ V)
        ((Scheme.Modules.restrictUnitIso U.ι).hom.app (U.ι ⁻¹ᵁ V)
          (((Scheme.Modules.restrictAdjunction U.ι).unit.app
            (SheafOfModules.unit X.ringCatSheaf)).app V a)))) = _
  change ∀ x, (overRestrictUnitIso X H U).hom.val.app T
    ((overRestrictUnitIso X H U).inv.val.app T x) = x at h
  rw [h]
  change (Scheme.Modules.Hom.app E.hom) (U.ι ⁻¹ᵁ V) ((U.ι.appIso (U.ι ⁻¹ᵁ V)).hom (U.ι.app V a)) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- The two pushforwards around the open restriction square agree. -/
def restrictPushforwardIso {Y X : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pushforward (p ∣_ U) ⋙ Scheme.Modules.pushforward U.ι ≅
      Scheme.Modules.pushforward (p ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward p :=
  Scheme.Modules.pushforwardComp (p ∣_ U) U.ι ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι p U) ≪≫
    (Scheme.Modules.pushforwardComp (p ⁻¹ᵁ U).ι p).symm

/-- Restriction and pullback commute by the uniqueness of left adjoints. -/
def restrictPullbackIso {Y X : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (p ∣_ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
    (Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ U).ι)).leftAdjointUniq
    (((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (p ∣_ U))).ofNatIsoRight
        (restrictPushforwardIso p U))

/-- The pulled-back trivialization on the inverse-image open subscheme. -/
def pulledRestrictIso {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (e : LocalFrame X H U) :
    SheafOfModules.unit (p ⁻¹ᵁ U).toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback p).obj H).restrict (p ⁻¹ᵁ U).ι :=
  (ArithmeticThetaPullback.pullback_unit_iso _ _ (p ∣_ U)).symm ≪≫
    (Scheme.Modules.pullback (p ∣_ U)).mapIso (frameRestrictIso X H U e) ≪≫
    ((restrictPullbackIso p U).app H).symm

/-- The square comparison carries the composite adjunction units to each other. -/
theorem restrictPullbackIso_unit {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (U V : X.Opens) (s : Γ(H,V)) :
    ((restrictPullbackIso p U).hom.app H).app ((p ⁻¹ᵁ U).ι ⁻¹ᵁ (p ⁻¹ᵁ V))
      (((Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback p).obj H)).app (p ⁻¹ᵁ V)
        (pullbackLocalSection p H V s)) =
    ((restrictPushforwardIso p U).hom.app
        ((Scheme.Modules.pullback (p ∣_ U)).obj (H.restrict U.ι))).app V
      (pullbackLocalSection (p ∣_ U) (H.restrict U.ι) (U.ι ⁻¹ᵁ V)
        (((Scheme.Modules.restrictAdjunction U.ι).unit.app H).app V s)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ U).ι))
    (((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (p ∣_ U))).ofNatIsoRight
        (restrictPushforwardIso p U)) H
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ Scheme.Modules.Hom.app f V) h) s

/-- Change-of-morphism pushforward comparison preserves structure coefficients. -/
theorem pushforwardCongr_coefficient {Y X : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (V : X.Opens) (a : Γ(X,V)) :
    ((Scheme.Modules.pushforwardCongr h).hom.app
      (SheafOfModules.unit Y.ringCatSheaf)).app V (f.app V a) = g.app V a := by
  subst g
  change Y.presheaf.map (eqToHom rfl).op (f.app V a) = f.app V a
  simp

/-- The open-square comparison preserves the composed structure-sheaf maps. -/
theorem restrictPushforwardIso_coefficient {Y X : Scheme.{u}} (p : Y ⟶ X)
    (U V : X.Opens) (a : Γ(X,V)) :
    ((restrictPushforwardIso p U).hom.app
      (SheafOfModules.unit (p ⁻¹ᵁ U).toScheme.ringCatSheaf)).app V
      ((p ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V a)) =
    (p ⁻¹ᵁ U).ι.app (p ⁻¹ᵁ V) (p.app V a) := by
  exact pushforwardCongr_coefficient (morphismRestrict_ι p U) V a

/-- The original frame commutes with restriction to its open subscheme. -/
theorem frameRestrictIso_unit (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) (V : X.Opens) (hVU : V ≤ U) (a : Γ(X,V)) :
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app H).app V (e.equiv V hVU a) =
    (Scheme.Modules.Hom.app (frameRestrictIso X H U e).hom) (U.ι ⁻¹ᵁ V)
      (U.ι.app V a) := by
  exact e.naturality V (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) (U.ι.image_preimage_le V) hVU a

/-- Pulling back a global trivialization preserves every coefficient via the unit. -/
theorem pullback_global_iso_unit {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (E : SheafOfModules.unit X.ringCatSheaf ≅ H) (V : X.Opens) (a : Γ(X,V)) :
    pullbackLocalSection p H V ((Scheme.Modules.Hom.app E.hom) V a) =
    (((ArithmeticThetaPullback.pullback_unit_iso Y X p).symm ≪≫
      (Scheme.Modules.pullback p).mapIso E).hom).app (p ⁻¹ᵁ V) (p.app V a) := by
  have hn := ConcreteCategory.congr_hom (congrArg (fun f ↦ Scheme.Modules.Hom.app f V)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality E.hom)) a
  have hu := ConcreteCategory.congr_hom (congrArg (fun f ↦ Scheme.Modules.Hom.app f V)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom)) a
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ Scheme.Modules.Hom.app f (p ⁻¹ᵁ V))
      (ArithmeticThetaPullback.pullback_unit_iso Y X p).hom_inv_id)
      (pullbackLocalSection p (SheafOfModules.unit X.ringCatSheaf) V a)
  change (ArithmeticThetaPullback.pullback_unit_iso Y X p).hom.app (p ⁻¹ᵁ V)
    (pullbackLocalSection p (SheafOfModules.unit X.ringCatSheaf) V a) = p.app V a at hu
  change pullbackLocalSection p H V ((Scheme.Modules.Hom.app E.hom) V a) =
    ((Scheme.Modules.pullback p).map E.hom).app (p ⁻¹ᵁ V)
      (pullbackLocalSection p (SheafOfModules.unit X.ringCatSheaf) V a) at hn
  rw [← hu]
  exact hn.trans (congrArg
    (((Scheme.Modules.pullback p).map E.hom).app (p ⁻¹ᵁ V)) hi.symm)

/-- The constructed trivialization satisfies the adjunction-unit coefficient law. -/
theorem pulledRestrictIso_unit {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (e : LocalFrame X H U) (V : X.Opens) (hVU : V ≤ U)
    (a : Γ(X,V)) :
    ((Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app
      ((Scheme.Modules.pullback p).obj H)).app (p ⁻¹ᵁ V)
      (pullbackLocalSection p H V (e.equiv V hVU a)) =
    (Scheme.Modules.Hom.app (pulledRestrictIso p H U e).hom)
      ((p ⁻¹ᵁ U).ι ⁻¹ᵁ (p ⁻¹ᵁ V))
      ((p ⁻¹ᵁ U).ι.app (p ⁻¹ᵁ V) (p.app V a)) := by
  let C := (restrictPullbackIso p U).app H
  let J := (ArithmeticThetaPullback.pullback_unit_iso _ _ (p ∣_ U)).symm ≪≫
    (Scheme.Modules.pullback (p ∣_ U)).mapIso (frameRestrictIso X H U e)
  let W := (p ⁻¹ᵁ U).ι ⁻¹ᵁ (p ⁻¹ᵁ V)
  have hinj := (CategoryTheory.Iso.toLinearEquiv
    ((SheafOfModules.evaluation (p ⁻¹ᵁ U).toScheme.ringCatSheaf (op W)).mapIso C)).injective
  apply hinj
  change C.hom.app W
    (((Scheme.Modules.restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app
      ((Scheme.Modules.pullback p).obj H)).app (p ⁻¹ᵁ V)
      (pullbackLocalSection p H V (e.equiv V hVU a))) =
    C.hom.app W (C.inv.app W (J.hom.app W
      ((p ⁻¹ᵁ U).ι.app (p ⁻¹ᵁ V) (p.app V a))))
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ Scheme.Modules.Hom.app f W) C.inv_hom_id)
  change ∀ x, C.hom.app W (C.inv.app W x) = x at hc
  rw [hc]
  change ((restrictPullbackIso p U).hom.app H).app W _ = _
  rw [restrictPullbackIso_unit, frameRestrictIso_unit,
    pullback_global_iso_unit]
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ Scheme.Modules.Hom.app f V)
      ((restrictPushforwardIso p U).hom.naturality J.hom))
    ((p ∣_ U).app (U.ι ⁻¹ᵁ V) (U.ι.app V a))
  exact hn.trans (congrArg (J.hom.app W)
    (restrictPushforwardIso_coefficient p U V a))

/-- Every actual local frame pulls back, compatibly with the actual adjunction unit. -/
theorem exists_pullbackFrame (Y X : Scheme.{u}) (p : Y ⟶ X) (H : X.Modules)
    (U : X.Opens) (e : LocalFrame X H U) :
    ∃ eY : LocalFrame Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U),
      FramePullbackCompatible p H U e eY := by
  let eY := frameOfRestrictIso Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
    (pulledRestrictIso p H U e)
  refine ⟨eY, ?_⟩
  intro V hVU a
  let T := op (Over.mk (homOfLE (p.preimage_mono hVU)))
  have hinj := (CategoryTheory.Iso.toLinearEquiv
    ((SheafOfModules.evaluation (Y.ringCatSheaf.over (p ⁻¹ᵁ U)) T).mapIso
      (overRestrictUnitIso Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)))).injective
  apply hinj
  exact (pulledRestrictIso_unit p H U e V hVU a).trans
    (frameOfRestrictIso_apply Y ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
      (pulledRestrictIso p H U e) (p ⁻¹ᵁ V) (p.preimage_mono hVU) (p.app V a)).symm

/-- Pullback along an arbitrary scheme morphism preserves local rank-one triviality. -/
theorem pullback_isLineBundle (Y X : Scheme.{u}) (p : Y ⟶ X) (H : X.Modules) :
    IsLineBundle X H → IsLineBundle Y ((Scheme.Modules.pullback p).obj H) := by
  intro hH y
  obtain ⟨U, hy, ⟨E⟩⟩ := hH (p.base y)
  obtain ⟨eY, _⟩ := exists_pullbackFrame Y X p H U (localFrameOfIso X H U E)
  exact ⟨p ⁻¹ᵁ U, hy, ⟨localFrameIso Y ((Scheme.Modules.pullback p).obj H) _ eY⟩⟩

end ArithmeticThetaNormalizedSections
