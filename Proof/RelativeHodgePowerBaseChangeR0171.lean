module

public import RelativeDiscriminantDefinitionsR0171
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
public import TensorPowerLaws
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Opposite
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower ArithmeticThetaPullback
namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The canonical pullback comparison preserves every pure local tensor. -/
theorem pullback_sheafTensor_local_section (X Y : Scheme.{u}) (p : X ⟶ Y)
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

/-- At exponent zero the canonical structure-sheaf comparison preserves one. -/
theorem pullback_unit_local_section (X Y : Scheme.{u}) (p : X ⟶ Y) (U : Y.Opens) :
    (pullback_unit_iso X Y p).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (1 : Γ(Y, U))) =
    (1 : Γ(X, p ⁻¹ᵁ U)) := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom
  have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.val.app (op U)) h)
    (show (SheafOfModules.unit Y.ringCatSheaf).val.obj (op U) from (1 : Γ(Y, U)))
  change _ = p.app U 1 at h'
  exact h'.trans (map_one (p.app U).hom)

/-- Every recursively defined tensor power of a local section commutes with pullback. -/
theorem pullback_tensorPower_local_section (X Y : Scheme.{u}) (p : X ⟶ Y)
    (H : Y.Modules) (n : ℕ) (U : Y.Opens) (s : Γ(H, U)) :
    (pullback_tensorPower_iso X Y p H n).hom.app (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p (tensorPowerSection Y H n U s)) =
    tensorPowerSection X ((Scheme.Modules.pullback p).obj H) n (p ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection p s) := by
  induction n with
  | zero => exact pullback_unit_local_section X Y p U
  | succ n ih =>
    change (sheafTensorCongr X (pullback_tensorPower_iso X Y p H n) (Iso.refl _)).hom.app
      (p ⁻¹ᵁ U)
      ((pullback_sheafTensor_iso X Y p (tensorPower Y H n) H).hom.app
        (p ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection p
          (tensorSection Y (tensorPower Y H n) H U (tensorPowerSection Y H n U s) s))) = _
    rw [pullback_sheafTensor_local_section, sheafTensorCongr_section, ih]
    rfl


/-- Functoriality of the actual recursively sheafified tensor power. -/
def powerCongr (X : Scheme.{u}) {H K : X.Modules} (e : H ≅ K) :
    (n : ℕ) → tensorPower X H n ≅ tensorPower X K n
  | 0 => Iso.refl _
  | n + 1 => sheafTensorCongr X (powerCongr X e n) e

theorem powerCongr_section (X : Scheme.{u}) {H K : X.Modules} (e : H ≅ K)
    (n : ℕ) (U : X.Opens) (s : Γ(H, U)) :
    (powerCongr X e n).hom.app U (tensorPowerSection X H n U s) =
      tensorPowerSection X K n U (e.hom.app U s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sheafTensorCongr X (powerCongr X e n) e).hom.app U
      (tensorSection X _ _ U (tensorPowerSection X H n U s) s) = _
    rw [sheafTensorCongr_section, ih]
    rfl

open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull

/-- The degree-one exterior presheaf is the original module presheaf. -/
def exteriorOnePresheafIso {C : Type u} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.exteriorPower 1 M ≅ M :=
  PresheafOfModules.isoMk
    (fun U => (exteriorPower.oneEquiv (R.obj U) (M.obj U)).toModuleIso)
    (by
      intro U V i
      ext x
      obtain ⟨m, rfl⟩ := (exteriorPower.oneEquiv (R.obj U) (M.obj U)).symm.surjective x
      change exteriorPower.oneEquiv (R.obj V) (M.obj V)
          ((PresheafOfModules.exteriorPower 1 M).map i
            (exteriorPower.ιMulti (R.obj U) 1 (fun _ => m))) =
        M.map i ((exteriorPower.oneEquiv (R.obj U) (M.obj U))
          (exteriorPower.ιMulti (R.obj U) 1 (fun _ => m)))
      rw [PresheafOfModules.exteriorPower_map_ιMulti, exteriorPower.oneEquiv_ιMulti,
        exteriorPower.oneEquiv_ιMulti])

def exteriorOneIso (X : Scheme.{u}) (M : X.PresheafOfModules) :
    (Scheme.Modules.presheafExteriorPower X 1).obj M ≅ M :=
  exteriorOnePresheafIso X.sheaf.obj M

/-- The canonical degree-one determinant identification. -/
def detOneIso (X : Scheme.{u}) (M : X.Modules) : Scheme.Modules.det 1 M ≅ M := by
  let M' : SheafOfModules.{u} X.ringCatSheaf := M
  let e := asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.app M')
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorOneIso X M.val) ≪≫ e

theorem detOneIso_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    (detOneIso X M).hom.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X 1).obj M.val)).app (op U)
          (exteriorPower.ιMulti _ 1 (fun _ => m))) = m := by
  unfold detOneIso
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M).val.app (op U))
    ((((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (exteriorOneIso X M.val).hom).val.app (op U)) _) = m
  rw [sheafifyMap_unit_apply]
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M).val.app (op U))
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M.val).app (op U)
      ((exteriorPower.oneEquiv Γ(X, U) Γ(M, U)) (exteriorPower.ιMulti Γ(X, U) 1 (fun _ => m)))) = m
  rw [exteriorPower.oneEquiv_ιMulti]
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).right_triangle_components M
  have hh := ConcreteCategory.congr_hom (congrArg (fun k => k.app (op U)) h)
    (show ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj M).obj (op U) from m)
  exact hh

theorem detOneIso_inv_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    (detOneIso X M).inv.app U m =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X 1).obj M.val)).app (op U)
          (exteriorPower.ιMulti Γ(X, U) 1 (fun _ => m))) := by
  nth_rw 1 [← detOneIso_section X M U m]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op U))
    (detOneIso X M).hom_inv_id) _

section DifferentialMap
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The morphism induced by the actual square on relative differential sheaves. -/
def differentialMap : (Scheme.Modules.pullback φ).obj gY.kaehler ⟶ gX.kaehler :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm
    (k1 gY gX φ hφ)

/-- Its value on the universal derivation is the derivation of the actual
scheme pullback of the function. This holds on every open. -/
theorem differentialMap_D (U : Y.Opens) (a : Γ(Y, U)) :
    (differentialMap gY gX φ hφ).app (φ ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection φ
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a)) =
      ArithmeticThetaCompactifiedDifferentialR0145.relativeD gX (φ ⁻¹ᵁ U) (φ.app U a) := by
  rw [differentialMap, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  change (k1 gY gX φ hφ).app U (gY.kaehlerToSections U (dK gY U a)) = _
  rw [k1_kaehlerToSections, k1app_dK]
  rfl

/-- The actual differential map is the degree-one form comparison transported
through the canonical exterior-power identification. -/
theorem differentialMap_eq_topMap :
    differentialMap gY gX φ hφ =
      (Scheme.Modules.pullback φ).map (detOneIso Y gY.kaehler).inv ≫
        θ gY gX φ hφ 1 ≫ (detOneIso X gX.kaehler).hom := by
  apply Scheme.Modules.pullback_hom_ext φ
  intro U s
  change (differentialMap gY gX φ hφ).app _ (Scheme.Modules.pullbackLocalSection φ s) =
    (detOneIso X gX.kaehler).hom.app _
      ((θ gY gX φ hφ 1).app _
        (((Scheme.Modules.pullback φ).map (detOneIso Y gY.kaehler).inv).app _
          (Scheme.Modules.pullbackLocalSection φ s)))
  rw [← Scheme.Modules.pullbackLocalSection_app, detOneIso_inv_section,
    θ_pullbackLocalSection]
  change (differentialMap gY gX φ hφ).app _ (Scheme.Modules.pullbackLocalSection φ s) =
    (detOneIso X gX.kaehler).hom.app _
      ((kd gY gX φ hφ 1).app U (T0.unitD gY 1 U
        (exteriorPower.ιMulti Γ(Y, U) 1 (fun _ => s))))
  rw [kd_unitD, kdfun_ιMulti]
  exact (Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ (k1 gY gX φ hφ) s).trans
    (detOneIso_section X gX.kaehler (φ ⁻¹ᵁ U) (k1h gY gX φ hφ U s)).symm


theorem topMap_local_formula (d : ℕ) :
      ∀ (U : Y.Opens) (_hU : IsAffineOpen U) (W : X.Opens) (_hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              ((θ gY gX φ hφ d).app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η) := by
  intro U _ W _ hWU instAW instABW instAYW η

  letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
  letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
  letI : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
    (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
  haveI : IsScalarTower A B Γ(X, φ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (fac gY gX φ hφ U))
  letI : Algebra Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := tower_sections gX hWU

  rw [θ_pullbackLocalSection, T0.topToSections_eq, kd_unitD, kdfun_apply, key gY gX φ hφ d U η,
    ← T0.topToSections_eq]
  change T0.resD gX d hWU (gX.topToSections d (φ ⁻¹ᵁ U)
    (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η)) = _
  rw [T0.resD_top, emap_eq_topFormMap gX d hWU]
  have hA : NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) d
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η) =
      NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η :=
    NeronModelInfra.TopFormOrder.topFormMap_topFormMap ..
  exact congrArg (gX.topToSections d W) hA

theorem differentialMap_isIso
    (hc : CategoryTheory.IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 gY] : IsIso (differentialMap gY gX φ hφ) := by
  letI : IsIso (θ gY gX φ hφ 1) :=
    Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
      gY gX φ hc 1 (θ gY gX φ hφ 1) (topMap_local_formula gY gX φ hφ 1)
  rw [differentialMap_eq_topMap]
  infer_instance

end DifferentialMap

section PullbackComposition
variable {X Y Z : Scheme.{u}}

theorem pullbackComp_inv_section (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).app M).inv.app ((f ≫ g) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection (f ≫ g) s) =
    Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s) :=
  ConcreteCategory.congr_hom (Scheme.Modules.unit_app_comp_pullbackComp_inv f g M U) s

theorem pullbackComp_hom_section (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).app M).hom.app ((f ≫ g) ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s)) =
    Scheme.Modules.pullbackLocalSection (f ≫ g) s := by
  rw [← pullbackComp_inv_section]
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.val.app (op ((f ≫ g) ⁻¹ᵁ U)))
    ((Scheme.Modules.pullbackComp f g).app M).inv_hom_id) _

def pullbackEqIso {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)

theorem pullbackEqIso_section {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M, U)) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    res ((Scheme.Modules.pullback g).obj M) hf
      ((pullbackEqIso h M).hom.app _ (Scheme.Modules.pullbackLocalSection f s)) =
    res ((Scheme.Modules.pullback g).obj M) hg (Scheme.Modules.pullbackLocalSection g s) := by
  subst g
  rfl

theorem hom_res {M N : X.Modules} (k : M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(M, U)) : res N h (k.app U s) = k.app V (res M h s) :=
  (PresheafOfModules.naturality_apply k.val (homOfLE h).op s).symm

end PullbackComposition

/-- The comparison for pullbacks along the two sides of a commutative square. -/
def squarePullbackIso {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y)
    (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback s).obj M) ≅
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M) :=
  (Scheme.Modules.pullbackComp a s).app M ≪≫ pullbackEqIso h M ≪≫
    ((Scheme.Modules.pullbackComp t b).app M).symm

theorem squarePullbackIso_section {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y)
    (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) (V : A.Opens)
    (h₁ : V ≤ a ⁻¹ᵁ (s ⁻¹ᵁ U)) (h₂ : V ≤ t ⁻¹ᵁ (b ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M)) h₁
      ((squarePullbackIso a s t b h M).hom.app _
        (Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection s m))) =
    res ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M)) h₂
      (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.pullbackLocalSection b m)) := by
  change res _ h₁ (((Scheme.Modules.pullbackComp t b).app M).inv.app _
    ((pullbackEqIso h M).hom.app _
      (((Scheme.Modules.pullbackComp a s).app M).hom.app _
        (Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection s m))))) = _
  erw [pullbackComp_hom_section a s M U m]
  rw [hom_res]
  erw [pullbackEqIso_section h M U m V h₁ h₂]
  rw [← hom_res]
  erw [pullbackComp_inv_section t b M U m]
  rfl

section PointedComparison
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hc : CategoryTheory.IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 gY]
    (s : Spec (CommRingCat.of A) ⟶ Y) (t : Spec (CommRingCat.of B) ⟶ X)
    (hpt : t ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s)

/-- Pullback of the actual Cartesian differential comparison to the pointed sections. -/
def pointedDifferentialIso :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((Scheme.Modules.pullback s).obj gY.kaehler) ≅
        (Scheme.Modules.pullback t).obj gX.kaehler := by
  letI := differentialMap_isIso gY gX φ hc.w hc
  exact squarePullbackIso _ s t φ hpt.symm gY.kaehler ≪≫
    (Scheme.Modules.pullback t).mapIso (asIso (differentialMap gY gX φ hc.w))

theorem pointedDifferentialIso_D (U : Y.Opens) (a : Γ(Y, U))
    (V : (Spec (CommRingCat.of B)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ (s ⁻¹ᵁ U))
    (h₂ : V ≤ t ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₁
      ((pointedDifferentialIso gY gX φ hc s t hpt).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (Scheme.Modules.pullbackLocalSection s
            (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a)))) =
    res ((Scheme.Modules.pullback t).obj gX.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection t
        (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gX (φ ⁻¹ᵁ U) (φ.app U a))) := by
  change res _ h₁ (((Scheme.Modules.pullback t).map
    (differentialMap gY gX φ hc.w)).app _
      ((squarePullbackIso _ s t φ hpt.symm gY.kaehler).hom.app _
        (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection s
          (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a))))) = _
  rw [hom_res, squarePullbackIso_section _ s t φ hpt.symm gY.kaehler U
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD gY U a) V h₁ h₂, ← hom_res]
  rw [← Scheme.Modules.pullbackLocalSection_app, differentialMap_D]

end PointedComparison

/-- Tensor powers of a specified line comparison, with the zero power included. -/
def tensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules)
    (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) :
    (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X K n :=
  pullback_tensorPower_iso X Y p H n ≪≫ powerCongr X e n

theorem tensorComparison_section {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules)
    (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ)
    (U : Y.Opens) (s : Γ(H, U)) :
    (tensorComparison p H K e n).hom.app _
      (Scheme.Modules.pullbackLocalSection p (tensorPowerSection Y H n U s)) =
    tensorPowerSection X K n (p ⁻¹ᵁ U)
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s)) := by
  change (powerCongr X e n).hom.app _
    ((pullback_tensorPower_iso X Y p H n).hom.app _
      (Scheme.Modules.pullbackLocalSection p (tensorPowerSection Y H n U s))) = _
  rw [pullback_tensorPower_local_section, powerCongr_section]

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170

section RelativeComparison
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)
    (Gs : Law S Ws) (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsBaseChange R W G S Ws Gs ι b)

/-- The comparison is built from the exact base and pointed curve maps. -/
def hodgeIso : (Scheme.Modules.pullback (baseMap R S ι)).obj (Hodge R W) ≅ Hodge S Ws := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact pointedDifferentialIso (structureMap R W) (structureMap S Ws) b hb.1
    (origin R W) (origin S Ws) hb.2.1

omit [IsDomain R] [IsDomain S] in
theorem hodgeIso_D (U : (Curve R W).Opens) (a : Γ(Curve R W, U))
    (V : (Base S).Opens)
    (h₁ : V ≤ (baseMap R S ι) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U))
    (h₂ : V ≤ (origin S Ws) ⁻¹ᵁ (b ⁻¹ᵁ U)) :
    res (Hodge S Ws) h₁
      ((hodgeIso R W G S Ws Gs ι b hb).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap R S ι) (localDifferential R W U a))) =
    res (Hodge S Ws) h₂ (localDifferential S Ws (b ⁻¹ᵁ U) (b.app U a)) := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  exact pointedDifferentialIso_D (structureMap R W) (structureMap S Ws) b hb.1
    (origin R W) (origin S Ws) hb.2.1 U a V h₁ h₂

def hodgePowerIso (n : ℕ) :
    (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅ HodgePower S Ws n :=
  tensorComparison (baseMap R S ι) (Hodge R W) (Hodge S Ws) (hodgeIso R W G S Ws Gs ι b hb) n

theorem hodgePowerIso_spec (n : ℕ) :
    IsPowerBaseChange R W S Ws ι b n (hodgePowerIso R W G S Ws Gs ι b hb n) := by
  intro U a V h₁ h₂
  change res _ h₁ ((tensorComparison _ _ _ _ n).hom.app _
    (Scheme.Modules.pullbackLocalSection _
      (tensorPowerSection _ _ n _ (localDifferential R W U a)))) = _
  rw [tensorComparison_section]
  change (tensorPower (Base S) (Hodge S Ws) n).presheaf.map (homOfLE h₁).op
    (tensorPowerSection _ _ n _ _) =
      (tensorPower (Base S) (Hodge S Ws) n).presheaf.map (homOfLE h₂).op
        (tensorPowerSection _ _ n _ _)
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection (Base S) (Hodge S Ws) n V)
    (hodgeIso_D R W G S Ws Gs ι b hb U a V h₁ h₂)

end RelativeComparison

section LocalFrames
variable {X : Scheme.{u}}

theorem res_res (M : X.Modules) {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (m : Γ(M, U)) : res M hWV (res M hVU m) = res M (hWV.trans hVU) m := by
  unfold res
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_refl (M : X.Modules) {U : X.Opens} (m : Γ(M, U)) : res M le_rfl m = m := by
  change M.presheaf.map (𝟙 (op U)) m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem res_smul (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(X, U)) (m : Γ(M, U)) :
    res M h (a • m) = X.presheaf.map (homOfLE h).op a • res M h m :=
  Scheme.Modules.map_smul M (homOfLE h) a m

theorem frame_restrict (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (m : Γ(M, U)) (hm : IsFrame M U m) : IsFrame M V (res M hVU m) := by
  intro W hWV
  simpa only [res_res] using hm W (hWV.trans hVU)

/-- A finite generating sum of sections of a line has a summand which is a
frame near each point. The proof uses the actual local ring at that point. -/
theorem local_frame_from_sum (M : X.Modules) {U : X.Opens} {ι : Type u} [Fintype ι]
    (a : ι → Γ(X, U)) (t : ι → Γ(M, U)) (x : X) (hx : x ∈ U)
    (hs : IsFrame M U (∑ j, a j • t j)) :
    ∃ (j : ι) (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ IsFrame M V (res M hVU (t j)) := by
  classical
  let s : Γ(M, U) := ∑ j, a j • t j
  have hb : Function.Bijective (fun c : Γ(X, U) => c • s) := by
    simpa only [res_refl] using hs U le_rfl
  choose c hc using fun j => hb.2 (t j)
  change ∀ j, c j • s = t j at hc
  have hsum : ∑ j, a j * c j = 1 := by
    apply hb.1
    change (∑ j, a j * c j) • s = (1 : Γ(X, U)) • s
    rw [one_smul, Finset.sum_smul]
    simp_rw [mul_smul, hc]
    rfl
  obtain ⟨j, hju⟩ : ∃ j, IsUnit (X.presheaf.germ U x hx (c j)) := by
    by_contra hcon
    push Not at hcon
    have h1 : X.presheaf.germ U x hx (∑ j, a j * c j) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [map_sum]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon j))
    rw [hsum, map_one] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨j, X.basicOpen (c j), X.basicOpen_le _, (X.mem_basicOpen (c j) x hx).2 hju, ?_⟩
  intro V hV
  have hVU : V ≤ U := hV.trans (X.basicOpen_le _)
  have hu : IsUnit (X.presheaf.map (homOfLE hVU).op (c j)) := by
    have h0 := RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toSheafedSpace) (c j)
    have hcomp : X.presheaf.map (homOfLE hVU).op (c j) =
        X.presheaf.map (homOfLE hV).op
          (X.presheaf.map (homOfLE (X.basicOpen_le (c j))).op (c j)) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hcomp]
    exact h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hV).op))
  have htV : res M hVU (t j) = X.presheaf.map (homOfLE hVU).op (c j) • res M hVU s := by
    rw [← res_smul, hc]
  have hm : Function.Bijective (fun g : Γ(X, V) => g * X.presheaf.map (homOfLE hVU).op (c j)) := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact (Units.mulRight u).bijective
  simp only [res_res]
  have heq : (fun g : Γ(X, V) => g • res M hVU (t j)) =
      (fun g : Γ(X, V) => g • res M hVU s) ∘
        (fun g => g * X.presheaf.map (homOfLE hVU).op (c j)) := by
    funext g
    simp only [Function.comp_apply, htV, mul_smul]
  rw [heq]
  exact (hs V hVU).comp hm

end LocalFrames

section ExactFrames
variable {A : Type u} [CommRing A] {X : Scheme.{u}}

theorem relativeD_res (g : X ⟶ Spec (CommRingCat.of A)) {U V : X.Opens}
    (h : V ≤ U) (a : Γ(X, U)) :
    res g.kaehler h (ArithmeticThetaCompactifiedDifferentialR0145.relativeD g U a) =
      ArithmeticThetaCompactifiedDifferentialR0145.relativeD g V
        (X.presheaf.map (homOfLE h).op a) := by
  change g.kaehler.val.map (homOfLE h).op (unit1 g U (dK g U a)) = _
  rw [map_unit1, kp_map_dK]
  rfl

theorem basis_one_frame (M : X.Modules) {U : X.Opens} (s : Γ(M, U))
    (h : ∀ (V : X.Opens) (hVU : V ≤ U),
      ∃ b : Module.Basis (Fin 1) Γ(X, V) Γ(M, V), b 0 = res M hVU s) : IsFrame M U s := by
  intro V hVU
  obtain ⟨b, hb⟩ := h V hVU
  rw [← hb]
  constructor
  · intro a c hac
    have hh := congrArg (fun m => b.repr m 0) hac
    simpa using hh
  · intro m
    refine ⟨b.repr m 0, ?_⟩
    simpa using b.sum_repr m

/-- Smooth relative curves have exact differential frames locally at every point. -/
theorem exists_exact_differential_frame (g : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 g] (x : X) :
    ∃ (U : X.Opens) (a : Γ(X, U)), x ∈ U ∧
      IsFrame g.kaehler U (ArithmeticThetaCompactifiedDifferentialR0145.relativeD g U a) := by
  classical
  obtain ⟨U₀, hx₀, e, he⟩ :=
    Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension g 1 x
  have he' := Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen g.kaehler e he
  obtain ⟨U, hU, hxU, hUU₀⟩ := exists_isAffineOpen_mem_and_subset hx₀
  let s : Γ(g.kaehler, U) := res g.kaehler hUU₀ (e 0)
  have hs : IsFrame g.kaehler U s := by
    apply basis_one_frame
    intro V hVU
    obtain ⟨b, hb⟩ := he' V (hVU.trans hUU₀)
    exact ⟨b, (hb 0).trans (res_res g.kaehler hUU₀ hVU (e 0)).symm⟩
  letI : Algebra A Γ(X, U) := g.sectionsAlgebra U
  obtain ⟨ω, hω⟩ := (Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen g hU).2 s
  obtain ⟨l, hl⟩ := KaehlerDifferential.linearCombination_surjective A Γ(X, U) ω
  let t : l.support → Γ(g.kaehler, U) := fun j =>
    ArithmeticThetaCompactifiedDifferentialR0145.relativeD g U j.1
  let a : l.support → Γ(X, U) := fun j => l j.1
  have hsum : (∑ j, a j • t j) = s := by
    rw [← hω, ← hl]
    change _ = g.kaehlerToSectionsₗ U (Finsupp.linearCombination Γ(X, U) (KaehlerDifferential.D A Γ(X, U)) l)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    simp only [map_smul]
    calc
      _ = ∑ j : l.support, l j.1 • g.kaehlerToSectionsₗ U
          (KaehlerDifferential.D A Γ(X, U) j.1) := by
        apply Finset.sum_congr rfl
        intro j _
        rfl
      _ = _ := by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach l.support (fun z => l z • g.kaehlerToSectionsₗ U
            (KaehlerDifferential.D A Γ(X, U) z)))
  have hs' : IsFrame g.kaehler U (∑ j, a j • t j) := hsum.symm ▸ hs
  obtain ⟨j, V, hVU, hxV, hV⟩ := local_frame_from_sum g.kaehler a t x hxU hs'
  refine ⟨V, X.presheaf.map (homOfLE hVU).op j.1, hxV, ?_⟩
  simpa only [t, relativeD_res] using hV

end ExactFrames

section FrameTransport
variable {X Y : Scheme.{u}}

theorem pullback_frame (p : X ⟶ Y) (M : Y.Modules) {U : Y.Opens} (s : Γ(M, U))
    (hs : IsFrame M U s) :
    IsFrame ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection p s) := by
  have h : Scheme.Modules.IsFrameOn s U := fun {_} h₁ _ => hs _ h₁
  have hp := Scheme.Modules.IsFrameOn.pullbackLocalSection p h
  exact fun V hV => hp hV hV

def frameTrivialization (M : X.Modules) {U : X.Opens} (s : Γ(M, U)) (hs : IsFrame M U s) :
    ArithmeticThetaLineRoot.LocalFrame X M U where
  equiv V hVU := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Γ(X, V) Γ(M, V) (res M hVU s)) (hs V hVU)
  naturality V W hWV hVU a := by
    change res M hWV (a • res M hVU s) = X.presheaf.map (homOfLE hWV).op a • _
    rw [res_smul, res_res]

theorem tensorPower_frame (M : X.Modules) {U : X.Opens} (s : Γ(M, U))
    (hs : IsFrame M U s) (n : ℕ) :
    IsFrame (tensorPower X M n) U (tensorPowerSection X M n U s) := by
  intro V hVU
  let e := frameTrivialization M s hs
  let en := (tensorPowerFrame X M U e n).equiv V hVU
  have he : res (tensorPower X M n) hVU (tensorPowerSection X M n U s) = en 1 := by
    change (tensorPower X M n).presheaf.map (homOfLE hVU).op _ = _
    rw [tensorPowerSection_restrict]
    have h := tensorPowerSection_frame X M U e n V hVU (1 : Γ(X, V))
    have he1 : e.equiv V hVU 1 = res M hVU s := one_smul Γ(X, V) _
    rw [he1, one_pow] at h
    exact h
  have hfun : (fun a : Γ(X, V) => a • res (tensorPower X M n) hVU
      (tensorPowerSection X M n U s)) = en := by
    funext a
    rw [he, ← en.map_smul]
    simp only [smul_eq_mul, mul_one]
  rw [hfun]
  exact en.bijective

end FrameTransport

/-- A sheaf morphism is determined on any covering family of genuine frames. -/
theorem hom_ext_frames {X : Scheme.{u}} {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ x : X, ∃ (U : X.Opens) (s : Γ(M, U)),
      x ∈ U ∧ IsFrame M U s ∧ f.app U s = g.app U s) : f = g := by
  classical
  choose U s hx hs heq using h
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, Scheme.Modules.isSheaf N⟩
    (fun x => V ⊓ U x) V (fun _ => homOfLE inf_le_left)
    (fun x hxV => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV, hx x⟩)
  intro x
  change res N inf_le_left (f.app V m) = res N inf_le_left (g.app V m)
  rw [hom_res, hom_res]
  obtain ⟨a, ha⟩ := (hs x (V ⊓ U x) inf_le_right).2 (res M inf_le_left m)
  change a • res M inf_le_right (s x) = res M inf_le_left m at ha
  rw [← ha, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  rw [← hom_res, ← hom_res, heq]

section RelativeUniqueness
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)
    (Gs : Law S Ws) (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsBaseChange R W G S Ws Gs ι b)

include hb in
omit [IsDomain R] [IsDomain S] in
theorem powerBaseChange_unique (n : ℕ)
    (e f : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅ HodgePower S Ws n)
    (he : IsPowerBaseChange R W S Ws ι b n e) (hf : IsPowerBaseChange R W S Ws ι b n f) : e = f := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  obtain ⟨U, a, hxU, hU⟩ := exists_exact_differential_frame (structureMap R W)
    ((origin R W) ((baseMap R S ι) x))
  let V := (baseMap R S ι) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U)
  have h₂ : V ≤ (origin S Ws) ⁻¹ᵁ (b ⁻¹ᵁ U) := by
    intro y hy
    change (origin S Ws ≫ b) y ∈ U
    rw [hb.2.1]
    exact hy
  refine ⟨V, Scheme.Modules.pullbackLocalSection (baseMap R S ι) (localPower R W n U a), hxU, ?_, ?_⟩
  · apply pullback_frame
    apply tensorPower_frame
    exact pullback_frame (origin R W) (structureMap R W).kaehler _ hU
  · have he' := he U a V le_rfl h₂
    have hf' := hf U a V le_rfl h₂
    simpa only [res_refl] using he'.trans hf'.symm

end RelativeUniqueness

end ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

namespace ArithmeticThetaRelativeDiscriminantR0171
open HodgeBaseChange

/-- The uniquely characterized comparison on actual Hodge tensor powers for
an arbitrary pointed Cartesian base change of the relative Weierstrass family. -/
theorem relative_hodge_power_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b) (n : ℕ), ∃! e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).obj (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n)) (ArithmeticThetaRelativeDiscriminantR0171.HodgePower S Ws n), ArithmeticThetaRelativeDiscriminantR0171.IsPowerBaseChange R W S Ws ι b n e := by
  intro R _ _ _ _ _ W _ _ _ _ _ G _hG S _ _ _ _ _ Ws _ _ _ _ _ Gs _hGs ι b hb n
  refine ⟨hodgePowerIso R W G S Ws Gs ι b hb n,
    hodgePowerIso_spec R W G S Ws Gs ι b hb n, ?_⟩
  intro e he
  exact powerBaseChange_unique R W G S Ws Gs ι b hb n e
    (hodgePowerIso R W G S Ws Gs ι b hb n) he
    (hodgePowerIso_spec R W G S Ws Gs ι b hb n)

#print axioms relative_hodge_power_base_change

end ArithmeticThetaRelativeDiscriminantR0171
