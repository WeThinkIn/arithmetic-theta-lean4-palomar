module

public import GlobalizationDefinitions
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
public import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
public import Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
public import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
public import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

@[expose] public section

/-! Coherent sheaves and actual formal sections.
Canonical library imports own the identical section-module, restriction, Čech
gluing, and affine pullback declarations formerly duplicated here. The accepted
coherent-sheaf bridge and final algebraization argument retain their actual
structural maps, scalar actions, and public interfaces. See RecoveryComparison.json.
-/

/- Checked affine and sheaf comparison support: AffineBridgeProbe. -/
section
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

namespace AffineBC

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

noncomputable abbrev ΓR : (Spec R).Modules ⥤ ModuleCat R := moduleSpecΓFunctor (R := R)

noncomputable abbrev pb : (Spec R).Modules ⥤ (Spec S).Modules := Scheme.Modules.pullback (Spec.map φ)

noncomputable abbrev pf : (Spec S).Modules ⥤ (Spec R).Modules := Scheme.Modules.pushforward (Spec.map φ)

noncomputable abbrev adj : pb φ ⊣ pf φ := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)

noncomputable abbrev ext : ModuleCat R ⥤ ModuleCat S := ModuleCat.extendScalars φ.hom
noncomputable abbrev res : ModuleCat S ⥤ ModuleCat R := ModuleCat.restrictScalars φ.hom
noncomputable abbrev adjER : ext φ ⊣ res φ := ModuleCat.extendRestrictScalarsAdj φ.hom

theorem isIso_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (F.map f) :=
  ⟨⟨F.map (inv f), by rw [← F.map_comp, IsIso.hom_inv_id, F.map_id], by rw [← F.map_comp, IsIso.inv_hom_id, F.map_id]⟩⟩

theorem isIso_tilde_unit (N : ModuleCat.{u} R) : IsIso ((tilde.adjunction (R := R)).unit.app N) := by
  infer_instance

noncomputable def unitΓ (M : (Spec R).Modules) : (ΓR).obj M ⟶ (res φ).obj ((ΓR).obj ((pb φ).obj M)) :=
  (ΓR).map ((adj φ).unit.app M) ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M)

noncomputable def baseChangeΓ (M : (Spec R).Modules) : (ext φ).obj ((ΓR).obj M) ⟶ (ΓR).obj ((pb φ).obj M) :=
  ((adjER φ).homEquiv _ _).symm (unitΓ φ M)

theorem baseChangeΓ_eq (M : (Spec R).Modules) :
    baseChangeΓ φ M = (ext φ).map (unitΓ φ M) ≫ (adjER φ).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

theorem unitΓ_naturality {M M' : (Spec R).Modules} (g : M ⟶ M') :
    (ΓR).map g ≫ unitΓ φ M' = unitΓ φ M ≫ (res φ).map ((ΓR).map ((pb φ).map g)) := by
  have h1 : g ≫ (adj φ).unit.app M' = (adj φ).unit.app M ≫ (pf φ).map ((pb φ).map g) := by
    have := (adj φ).unit.naturality g
    simpa only [Functor.comp_map, Functor.id_map] using this
  have h1' : (ΓR).map g ≫ (ΓR).map ((adj φ).unit.app M')
      = (ΓR).map ((adj φ).unit.app M) ≫ (ΓR).map ((pf φ).map ((pb φ).map g)) :=
    ((ΓR).map_comp _ _).symm.trans ((congrArg (ΓR).map h1).trans ((ΓR).map_comp _ _))
  have h2 : (ΓR).map ((pf φ).map ((pb φ).map g)) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M')
      = (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj M) ≫ (res φ).map ((ΓR).map ((pb φ).map g)) :=
    (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.naturality ((pb φ).map g)
  unfold unitΓ
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker h1' _)).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ h2).trans (Category.assoc _ _ _).symm))

theorem baseChangeΓ_naturality {M M' : (Spec R).Modules} (g : M ⟶ M') :
    (ext φ).map ((ΓR).map g) ≫ baseChangeΓ φ M' = baseChangeΓ φ M ≫ (ΓR).map ((pb φ).map g) := by
  rw [baseChangeΓ_eq, baseChangeΓ_eq]
  have un := unitΓ_naturality φ g
  have hF : (ext φ).map ((ΓR).map g) ≫ (ext φ).map (unitΓ φ M')
      = (ext φ).map (unitΓ φ M) ≫ (ext φ).map ((res φ).map ((ΓR).map ((pb φ).map g))) :=
    ((ext φ).map_comp _ _).symm.trans ((congrArg (ext φ).map un).trans ((ext φ).map_comp _ _))
  have hc : (ext φ).map ((res φ).map ((ΓR).map ((pb φ).map g))) ≫ (adjER φ).counit.app ((ΓR).obj ((pb φ).obj M'))
      = (adjER φ).counit.app ((ΓR).obj ((pb φ).obj M)) ≫ (ΓR).map ((pb φ).map g) :=
    (adjER φ).counit_naturality _
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker hF _)).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ hc).trans (Category.assoc _ _ _).symm))

def UnitCompat (N : ModuleCat.{u} R) : Prop :=
  ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N ≫
      (pf φ ⋙ moduleSpecΓFunctor (R := R)).map (tilde.pullbackSpecIso φ N).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj N)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N))

theorem unitΓ_tilde (N : ModuleCat.{u} R) (hunit : UnitCompat φ N) :
    (tilde.adjunction (R := R)).unit.app N ≫ unitΓ φ (tilde N) ≫ (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom) =
      (adjER φ).unit.app N ≫ (res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N)) := by
  have hcu : ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N
      = (tilde.adjunction (R := R)).unit.app N ≫ (ΓR).map ((adj φ).unit.app (tilde N)) :=
    Adjunction.comp_unit_app _ _ N
  have h2 : (ΓR).map ((pf φ).map (tilde.pullbackSpecIso φ N).hom) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ext φ).obj N))
      = (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((pb φ).obj (tilde N)) ≫
        (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom) :=
    (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.naturality (tilde.pullbackSpecIso φ N).hom

  have lhs : ((tilde.adjunction (R := R)).comp (adj φ)).unit.app N ≫
      (pf φ ⋙ moduleSpecΓFunctor (R := R)).map (tilde.pullbackSpecIso φ N).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ext φ).obj N))
      = (tilde.adjunction (R := R)).unit.app N ≫ unitΓ φ (tilde N) ≫
        (res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom) := by
    unfold unitΓ
    exact (eq_whisker hcu _).trans ((Category.assoc _ _ _).trans
      (whisker_eq _ ((whisker_eq _ h2).trans (Category.assoc _ _ _).symm)))
  exact lhs.symm.trans hunit

theorem baseChangeΓ_tilde (N : ModuleCat.{u} R) (hunit : UnitCompat φ N) :
    (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
        baseChangeΓ φ (tilde N) ≫ (ΓR).map (tilde.pullbackSpecIso φ N).hom =
      (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) := by
  have key := unitΓ_tilde φ N hunit
  have key' := congrArg (fun t => (ext φ).map t ≫ (adjER φ).counit.app _) key
  simp only [Functor.map_comp, Category.assoc] at key'

  have hc1 : (ext φ).map ((res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (adjER φ).counit.app ((ΓR).obj ((pb φ).obj (tilde N))) ≫ (ΓR).map (tilde.pullbackSpecIso φ N).hom :=
    (adjER φ).counit_naturality _
  have hc2 : (ext φ).map ((res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (adjER φ).counit.app ((ext φ).obj N) ≫ (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) :=
    (adjER φ).counit_naturality _
  have htri : (ext φ).map ((adjER φ).unit.app N) ≫ (adjER φ).counit.app ((ext φ).obj N) = 𝟙 _ :=
    (adjER φ).left_triangle_components N
  have rhs : (ext φ).map ((adjER φ).unit.app N) ≫
      (ext φ).map ((res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) :=
    (whisker_eq _ hc2).trans ((Category.assoc _ _ _).symm.trans ((eq_whisker htri _).trans (Category.id_comp _)))
  have lhs : (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫ (ext φ).map (unitΓ φ (tilde N)) ≫
      (ext φ).map ((res φ).map ((ΓR).map (tilde.pullbackSpecIso φ N).hom)) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (ext φ).map ((tilde.adjunction (R := R)).unit.app N) ≫
        baseChangeΓ φ (tilde N) ≫ (ΓR).map (tilde.pullbackSpecIso φ N).hom := by
    rw [baseChangeΓ_eq]
    exact whisker_eq _ ((whisker_eq _ hc1).trans (Category.assoc _ _ _).symm)
  have rhs2 : (ext φ).map ((adjER φ).unit.app N ≫ (res φ).map ((tilde.adjunction (R := S)).unit.app ((ext φ).obj N))) ≫
      (adjER φ).counit.app ((ΓR).obj (tilde ((ext φ).obj N)))
      = (tilde.adjunction (R := S)).unit.app ((ext φ).obj N) :=
    (eq_whisker ((ext φ).map_comp _ _) _).trans ((Category.assoc _ _ _).trans rhs)
  first
    | exact lhs.symm.trans (key'.trans rhs)
    | exact lhs.symm.trans (key'.trans rhs2)

theorem isIso_baseChangeΓ (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (hunit : ∀ N, UnitCompat φ N) :
    IsIso (baseChangeΓ φ M) := by

  have hiso1 : IsIso (baseChangeΓ φ (tilde ((ΓR).obj M))) := by
    have htilde := baseChangeΓ_tilde φ ((ΓR).obj M) (hunit _)
    have i1 : IsIso ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M))) :=
      @isIso_map _ _ _ _ _ _ _ _ (isIso_tilde_unit _)
    have i2 : IsIso ((ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) := isIso_map _ _
    have i5 : IsIso ((tilde.adjunction (R := S)).unit.app ((ext φ).obj ((ΓR).obj M))) := isIso_tilde_unit _
    have i3 : IsIso ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M)) ≫
        baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) :=
      htilde ▸ i5
    have i4 := @IsIso.of_isIso_comp_left _ _ _ _ _
      ((ext φ).map ((tilde.adjunction (R := R)).unit.app ((ΓR).obj M)))
      (baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) i1 i3
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (baseChangeΓ φ (tilde ((ΓR).obj M)))
      ((ΓR).map (tilde.pullbackSpecIso φ ((ΓR).obj M)).hom) i2 i4

  have hnat := baseChangeΓ_naturality φ M.fromTildeΓ
  have j1 : IsIso ((ΓR).map ((pb φ).map M.fromTildeΓ)) := @isIso_map _ _ _ _ _ _ _ _ (isIso_map _ _)
  have j2 : IsIso ((ext φ).map ((ΓR).map M.fromTildeΓ)) := @isIso_map _ _ _ _ _ _ _ _ (isIso_map _ _)
  have j3 : IsIso (baseChangeΓ φ (tilde ((ΓR).obj M)) ≫ (ΓR).map ((pb φ).map M.fromTildeΓ)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 j1
  have j4 : IsIso ((ext φ).map ((ΓR).map M.fromTildeΓ) ≫ baseChangeΓ φ M) := hnat ▸ j3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ j2 j4

end AffineBC

end AlgebraicGeometry.Scheme.Modules


set_option autoImplicit false

noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace SectionsCI


variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U)

abbrev iU : Spec Γ(X, U) ⟶ X := hU.fromSpec

abbrev j : Spec Γ(Y, i ⁻¹ᵁ U) ⟶ Y := (hU.preimage i).fromSpec

theorem j_i' : j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec i hU (hU.preimage i) le_rfl).symm

theorem j_i : j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU :=
  (Classical.choice (⟨⟨j_i' i U hU⟩⟩ : Nonempty (PLift (j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU)))).down

theorem le_opensRange_j : i ⁻¹ᵁ U ≤ (j i U hU).opensRange := by
  rw [IsAffineOpen.opensRange_fromSpec]

theorem top_le_preimage_j : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U) := by
  rw [IsAffineOpen.fromSpec_preimage_self]

theorem top_le_preimage_iU : (⊤ : (Spec Γ(X, U)).Opens) ≤ (iU U hU) ⁻¹ᵁ U := by
  rw [IsAffineOpen.fromSpec_preimage_self]

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

namespace UnitCalculus

variable {X Y Z : Scheme.{u}}

theorem unit_app_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((pullbackPushforwardAdjunction g).unit.app ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

theorem unit_app_congr_res {p₁ p₂ : Z ⟶ X} (h : p₁ = p₂) (M : X.Modules) (U : X.Opens) (W : Z.Opens)
    (hW₁ : W ≤ p₁ ⁻¹ᵁ U) (hW₂ : W ≤ p₂ ⁻¹ᵁ U) :
    ((pullbackPushforwardAdjunction p₁).unit.app M).app U ≫ ((pullbackCongr h).hom.app M).app (p₁ ⁻¹ᵁ U) ≫
        ((Scheme.Modules.pullback p₂).obj M).presheaf.map (homOfLE hW₁).op =
      ((pullbackPushforwardAdjunction p₂).unit.app M).app U ≫
        ((Scheme.Modules.pullback p₂).obj M).presheaf.map (homOfLE hW₂).op := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Hom.id_app]
  erw [Category.id_comp]

theorem bijective_unit_app_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((pullbackPushforwardAdjunction j).unit.app N).app V) := by
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j) (pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Hom.app t V) hfac.symm

  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) := Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app
      (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]

  have hh : ((pullbackPushforwardAdjunction j).unit.app N).app V =
      N.presheaf.map (homOfLE (j.image_preimage_le V)).op ≫
        (((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app (j ⁻¹ᵁ V) := hfac'
  rw [hh]
  exact hiso

end UnitCalculus

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace SectionsCI


variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

abbrev M' : (Spec Γ(X, U)).Modules := (Scheme.Modules.pullback (iU U hU)).obj M

abbrev MY : Y.Modules := (Scheme.Modules.pullback i).obj M

def η : Γ(M, U) ⟶ Γ(MY i M, i ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction i).unit.app M).app U

def ρ : Γ(M, U) ⟶ Γ(M' U hU M, ⊤) :=
  ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U ≫
    (M' U hU M).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op

def θ : Γ(MY i M, i ⁻¹ᵁ U) ⟶
    Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), ⊤) :=
  ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) ≫
    ((Scheme.Modules.pullback (j i U hU)).obj (MY i M)).presheaf.map (homOfLE (top_le_preimage_j i U hU)).op

theorem isIso_presheaf_map_top_le {Y : Scheme.{u}} (N : Y.Modules) (V : Y.Opens) (h : (⊤ : Y.Opens) ≤ V) :
    IsIso (N.presheaf.map (homOfLE h).op) := by
  have hV : V = ⊤ := top_le_iff.mp h
  subst hV
  rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, N.presheaf.map_id]
  infer_instance

theorem bijective_ρ : Function.Bijective (ρ U hU M) := by
  unfold ρ
  rw [← ConcreteCategory.isIso_iff_bijective]
  have h1 : IsIso (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact UnitCalculus.bijective_unit_app_of_isOpenImmersion (iU U hU) M U (by rw [IsAffineOpen.opensRange_fromSpec])
  have h2 := isIso_presheaf_map_top_le (M' U hU M) _ (top_le_preimage_iU U hU)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

theorem bijective_θ : Function.Bijective (θ i U hU M) := by
  unfold θ
  rw [← ConcreteCategory.isIso_iff_bijective]
  have h1 : IsIso (((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact UnitCalculus.bijective_unit_app_of_isOpenImmersion (j i U hU) (MY i M) _ (le_opensRange_j i U hU)
  have h2 := isIso_presheaf_map_top_le ((Scheme.Modules.pullback (j i U hU)).obj (MY i M)) _
    (top_le_preimage_j i U hU)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

def σ : (Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M) ≅
    (Scheme.Modules.pullback (j i U hU)).obj (MY i M) :=
  (pullbackComp (Spec.map (i.app U)) (iU U hU)).app M ≪≫
    (pullbackCongr (j_i i U hU).symm).app M ≪≫
    ((pullbackComp (j i U hU) i).app M).symm

def ηφ : Γ(M' U hU M, ⊤) ⟶ Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) :=
  ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ⊤

theorem app_res {Y : Scheme.{u}} {N₁ N₂ : Y.Modules} (ψ : N₁ ⟶ N₂) {V W : Y.Opens} (h : W ≤ V) (x : Γ(N₁, V)) :
    ψ.app W (N₁.presheaf.map (homOfLE h).op x) = N₂.presheaf.map (homOfLE h).op (ψ.app V x) := by
  have := ψ.mapPresheaf.naturality (homOfLE h).op
  exact ConcreteCategory.congr_hom this x

theorem hom_inv_app_apply {Y : Scheme.{u}} {N₁ N₂ : Y.Modules} (e : N₁ ≅ N₂) (V : Y.Opens) (x : Γ(N₂, V)) :
    e.hom.app V (e.inv.app V x) = x := by
  have h : (e.inv ≫ e.hom).app V = 𝟙 _ := by rw [e.inv_hom_id]; rfl
  have := ConcreteCategory.congr_hom h x
  exact this

theorem σ_hom_app (V : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens)
    (x : Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), V)) :
    (σ i U hU M).hom.app V x =
      ((pullbackComp (j i U hU) i).inv.app M).app V
        (((pullbackCongr (j_i i U hU).symm).hom.app M).app V
          (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app V x)) := by
  rfl

theorem le1 : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ (Spec.map (i.app U)) ⁻¹ᵁ ((iU U hU) ⁻¹ᵁ U) :=
  fun _ _ => top_le_preimage_iU U hU (Set.mem_univ _)

theorem chase (m : Γ(M, U)) :
    ((σ i U hU M).hom.app ⊤) (ηφ i U hU M (ρ U hU M m)) = θ i U hU M (η i U M m) := by
  have le3 := top_le_preimage_j i U hU

  have e1 : ηφ i U hU M (ρ U hU M m)
      = ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M)).presheaf.map (homOfLE (le1 i U hU)).op
          (((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
            (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m)) :=
    app_res ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)) (top_le_preimage_iU U hU) _

  have hx2 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).inv.app M).app ((Spec.map (i.app U) ≫ iU U hU) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m)
      = ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
            (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m) :=
    ConcreteCategory.congr_hom (UnitCalculus.unit_app_comp (Spec.map (i.app U)) (iU U hU) M U) m
  have e2 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ((Spec.map (i.app U)) ⁻¹ᵁ ((iU U hU) ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m))
      = ((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m :=
    (congrArg _ hx2.symm).trans (hom_inv_app_apply ((pullbackComp (Spec.map (i.app U)) (iU U hU)).app M) _ _)

  have e3 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m))
      = ((Scheme.Modules.pullback (Spec.map (i.app U) ≫ iU U hU)).obj M).presheaf.map (homOfLE (le1 i U hU)).op
          (((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m) :=
    (congrArg _ e1).trans ((app_res ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M) (le1 i U hU) _).trans
      (congrArg _ e2))

  have hx4 := ConcreteCategory.congr_hom
    (UnitCalculus.unit_app_congr_res (j_i i U hU).symm M U ⊤ (le1 i U hU) le3) m
  have e4 : ((pullbackCongr (j_i i U hU).symm).hom.app M).app ⊤
        (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m)))
      = ((Scheme.Modules.pullback (j i U hU ≫ i)).obj M).presheaf.map (homOfLE le3).op
          (((pullbackPushforwardAdjunction (j i U hU ≫ i)).unit.app M).app U m) :=
    (congrArg _ e3).trans ((app_res ((pullbackCongr (j_i i U hU).symm).hom.app M) (le1 i U hU) _).trans hx4)

  have hx5 : ((pullbackComp (j i U hU) i).inv.app M).app ((j i U hU ≫ i) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (j i U hU ≫ i)).unit.app M).app U m)
      = ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction i).unit.app M).app U m) :=
    ConcreteCategory.congr_hom (UnitCalculus.unit_app_comp (j i U hU) i M U) m
  have e5 : ((pullbackComp (j i U hU) i).inv.app M).app ⊤
        (((pullbackCongr (j_i i U hU).symm).hom.app M).app ⊤
          (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m))))
      = θ i U hU M (η i U M m) :=
    (congrArg _ e4).trans ((app_res ((pullbackComp (j i U hU) i).inv.app M) le3 _).trans
      (congrArg _ hx5))
  exact (σ_hom_app i U hU M ⊤ _).trans e5

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace SectionsCI


variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

scoped instance opensMapFinal' {Y Z : Scheme.{u}} (f : Y ⟶ Z) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

def pullbackUnitIso' {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf := by
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ h

theorem locallyTrivial_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) (L : Z.Modules)
    (htriv : ∀ z : Z, ∃ (V : Z.Opens), z ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    ∀ y : Y, ∃ (V : Y.Opens), y ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj L) ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  intro y
  obtain ⟨V, hyV, ⟨eV⟩⟩ := htriv (f.base y)
  refine ⟨f ⁻¹ᵁ V, hyV, ⟨?_⟩⟩
  have hfact : (f ⁻¹ᵁ V).ι ≫ f = (f ∣_ V) ≫ V.ι := (morphismRestrict_ι f V).symm
  exact
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ V)).mapIso eV ≪≫
    pullbackUnitIso' (f ∣_ V)

abbrev N' : ModuleCat Γ(X, U) := (moduleSpecΓFunctor (R := Γ(X, U))).obj (M' U hU M)

theorem N'_smul_def (b : Γ(X, U)) (n : N' U hU M) :
    b • n = (((Spec Γ(X, U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso Γ(X, U)).hom.hom b)) • (show Γ(M' U hU M, ⊤) from n) := rfl

omit hU M in
theorem res_top_top' (s : Γ(Spec Γ(X, U), ⊤)) :
    ((Spec Γ(X, U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)).op).hom s = s := by
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

theorem iU_appLE (b : Γ(X, U)) :
    ((Spec Γ(X, U)).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op).hom (((iU U hU).app U).hom b)
      = (Scheme.ΓSpecIso Γ(X, U)).inv.hom b := by
  have h := IsAffineOpen.fromSpec_app_self hU

  have hb := congrArg (fun t => ((Spec Γ(X, U)).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op).hom
    ((CommRingCat.Hom.hom t) b)) h
  simp only [CommRingCat.comp_apply] at hb
  refine hb.trans ?_
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : ((eqToHom (hU.fromSpec_preimage_self)).op ≫ (homOfLE (top_le_preimage_iU U hU)).op :
      op (⊤ : (Spec Γ(X, U)).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  erw [this, CategoryTheory.Functor.map_id]
  rfl

theorem N'_smul_def' (b : Γ(X, U)) (n : N' U hU M) :
    b • n = ((Scheme.ΓSpecIso Γ(X, U)).inv.hom b) • (show Γ(M' U hU M, ⊤) from n) := by
  rw [N'_smul_def, res_top_top']
  rfl

theorem unit_iU_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U (b • m)
      = ((iU U hU).app U).hom b •
        (show Γ(M' U hU M, (iU U hU) ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m) :=
  Scheme.Modules.Hom.app_smul _ _ _

theorem ρ_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ρ U hU M (b • m) = (b • (show N' U hU M from ρ U hU M m) : N' U hU M) := by
  have h2 := congrArg ((M' U hU M).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op) (unit_iU_smul U hU M b m)
  have h3 := Scheme.Modules.map_smul (M' U hU M) (homOfLE (top_le_preimage_iU U hU)) (((iU U hU).app U).hom b)
    (show Γ(M' U hU M, (iU U hU) ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m)
  rw [iU_appLE] at h3
  exact (h2.trans h3).trans (N'_smul_def' U hU M b _).symm

def ρlin : Γ(M, U) →ₗ[Γ(X, U)] N' U hU M where
  toFun m := ρ U hU M m
  map_add' x y := map_add _ x y
  map_smul' b m := ρ_smul U hU M b m

theorem ρlin_apply (m : Γ(M, U)) : ρlin U hU M m = ρ U hU M m := rfl

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace SectionsCI


variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

def ρR : Γ(M, U) ≃ₗ[Γ(X, U)] N' U hU M :=
  { (ρlin U hU M : Γ(M, U) →ₗ[Γ(X, U)] N' U hU M) with
    invFun := (Equiv.ofBijective _ (bijective_ρ U hU M)).invFun
    left_inv := (Equiv.ofBijective _ (bijective_ρ U hU M)).left_inv
    right_inv := (Equiv.ofBijective _ (bijective_ρ U hU M)).right_inv }

theorem ρR_apply (m : Γ(M, U)) : ρR U hU M m = ρ U hU M m := rfl

abbrev T₁ : Type u := ((ModuleCat.extendScalars (i.app U).hom).obj (N' U hU M) : Type u)

abbrev S₁ : ModuleCat Γ(X, U) :=
  (ModuleCat.restrictScalars (i.app U).hom).obj (ModuleCat.of Γ(Y, i ⁻¹ᵁ U) Γ(Y, i ⁻¹ᵁ U))

def Kfwd : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) →+ T₁ i U hU M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  TensorProduct.liftAddHom
    { toFun := fun a =>
        (TensorProduct.mk Γ(X, U) (S₁ i U) (N' U hU M) (a : S₁ i U)).toAddMonoidHom.comp
          (ρlin U hU M).toAddMonoidHom
      map_zero' := by
        apply AddMonoidHom.ext; intro m
        change ((((0 : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m)) : T₁ i U hU M) = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun a a' => by
        apply AddMonoidHom.ext; intro m
        change ((((a + a' : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U)) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
          = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
            + ((a' : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
        exact TensorProduct.add_tmul _ _ _ }
    (fun b a m => by
      change (((b • a : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
        = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M (b • m)) : T₁ i U hU M)
      rw [LinearMap.map_smul, ← TensorProduct.smul_tmul]
      try rfl
      try congr 1)

theorem Kfwd_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kfwd i U hU M (a ⊗ₜ[Γ(X, U)] m)
      = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ a m

def Kbwd₀ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) →+ (N' U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  { toFun := fun a =>
      (TensorProduct.mk Γ(X, U) Γ(Y, i ⁻¹ᵁ U) Γ(M, U) a).toAddMonoidHom.comp
        ((ρR U hU M).symm : N' U hU M →ₗ[Γ(X, U)] Γ(M, U)).toAddMonoidHom
    map_zero' := by apply AddMonoidHom.ext; intro n; exact TensorProduct.zero_tmul _ _
    map_add' := fun a a' => by apply AddMonoidHom.ext; intro n; exact TensorProduct.add_tmul _ _ _ }

theorem Kbwd₀_apply (a : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kbwd₀ i U hU M a n = a ⊗ₜ[Γ(X, U)] (ρR U hU M).symm n := rfl

def Kbwd : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    T₁ i U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  TensorProduct.liftAddHom
    (show S₁ i U →+ (N' U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) from Kbwd₀ i U hU M)
    (fun b a n => by
      change Kbwd₀ i U hU M (b • a) n = Kbwd₀ i U hU M a (b • n)
      rw [Kbwd₀_apply, Kbwd₀_apply, LinearEquiv.map_smul, ← TensorProduct.smul_tmul]
      try rfl
      try congr 1)

theorem Kbwd_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kbwd i U hU M ((a : S₁ i U) ⊗ₜ[Γ(X, U)] n : T₁ i U hU M) = Kbwd₀ i U hU M a n := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ a n

def κ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃+ T₁ i U hU M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  { Kfwd i U hU M with
    invFun := Kbwd i U hU M
    left_inv := fun z => by
      change Kbwd i U hU M (Kfwd i U hU M z) = z
      induction z using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (Kbwd i U hU M) (map_zero (Kfwd i U hU M))).trans (map_zero (Kbwd i U hU M))
      | add x y hx hy =>
        exact (congrArg (Kbwd i U hU M) (map_add (Kfwd i U hU M) x y)).trans
          ((map_add (Kbwd i U hU M) _ _).trans (congrArg₂ (· + ·) hx hy))
      | tmul a m =>
        rw [Kfwd_tmul]
        refine (Kbwd_tmul i U hU M _ _).trans ?_
        rw [Kbwd₀_apply]
        congr 1
        exact (ρR U hU M).symm_apply_apply m
    right_inv := fun t => by
      change Kfwd i U hU M (Kbwd i U hU M t) = t
      induction t using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (Kfwd i U hU M) (map_zero (Kbwd i U hU M))).trans (map_zero (Kfwd i U hU M))
      | add x y hx hy =>
        exact (congrArg (Kfwd i U hU M) (map_add (Kbwd i U hU M) x y)).trans
          ((map_add (Kfwd i U hU M) _ _).trans (congrArg₂ (· + ·) hx hy))
      | tmul a n =>
        refine (congrArg (Kfwd i U hU M) (Kbwd_tmul i U hU M a n)).trans ?_
        refine (congrArg (Kfwd i U hU M) (Kbwd₀_apply i U hU M a n)).trans ?_
        refine (Kfwd_tmul i U hU M a ((ρR U hU M).symm n)).trans ?_
        congr 1
        exact (ρR U hU M).apply_symm_apply n }

theorem κ_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    κ i U hU M (a ⊗ₜ[Γ(X, U)] m) = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] ρ U hU M m : T₁ i U hU M) :=
  Kfwd_tmul i U hU M a m

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace SectionsCI


variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

abbrev Q : ModuleCat (Γ(Y, i ⁻¹ᵁ U)) :=
  (moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M))

def β : (ModuleCat.extendScalars (i.app U).hom).obj (N' U hU M) ⟶ Q i U hU M :=
  ((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv (N' U hU M) (Q i U hU M)).symm
    ((moduleSpecΓFunctor (R := Γ(X, U))).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
        ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M)))

theorem β_tmul (x : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    (β i U hU M).hom ((x : S₁ i U) ⊗ₜ[Γ(X, U)] n : T₁ i U hU M) = x • (show Q i U hU M from ηφ i U hU M n) := by
  unfold β
  rw [Adjunction.homEquiv_counit]
  rfl

theorem Q_smul_def (x : Γ(Y, i ⁻¹ᵁ U)) (q : Q i U hU M) :
    x • q = ((Scheme.ΓSpecIso (Γ(Y, i ⁻¹ᵁ U))).inv.hom x) •
      (show Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) from q) := by
  have h1 : x • q = (((Spec Γ(Y, i ⁻¹ᵁ U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso (Γ(Y, i ⁻¹ᵁ U))).hom.hom x)) •
      (show Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) from q) := rfl
  rw [h1]
  congr 1
  all_goals try (rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]; rfl)

theorem σ_smul (t : Γ(Spec Γ(Y, i ⁻¹ᵁ U), ⊤)) (q : Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤)) :
    (σ i U hU M).hom.app ⊤ (t • q) = t • (σ i U hU M).hom.app ⊤ q :=
  Scheme.Modules.Hom.app_smul _ _ _

theorem θ_smul (s : Γ(Y, i ⁻¹ᵁ U)) (y : Γ(MY i M, i ⁻¹ᵁ U)) :
    θ i U hU M (s • y) =
      ((j i U hU).appLE (i ⁻¹ᵁ U) ⊤ (top_le_preimage_j i U hU)).hom s • θ i U hU M y := by
  have h1 : ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) (s • y)
      = ((j i U hU).app (i ⁻¹ᵁ U)).hom s •
        (show Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U)) from
          ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) y) :=
    Scheme.Modules.Hom.app_smul _ _ _
  have h2 := congrArg (((Scheme.Modules.pullback (j i U hU)).obj (MY i M)).presheaf.map
    (homOfLE (top_le_preimage_j i U hU)).op) h1
  have h3 := Scheme.Modules.map_smul ((Scheme.Modules.pullback (j i U hU)).obj (MY i M))
    (homOfLE (top_le_preimage_j i U hU)) (((j i U hU).app (i ⁻¹ᵁ U)).hom s)
    (show Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U)) from
      ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) y)
  exact h2.trans h3

theorem scalar_key (a : Γ(Y, i ⁻¹ᵁ U)) :
    ((j i U hU).appLE (i ⁻¹ᵁ U) ⊤ (top_le_preimage_j i U hU)).hom a
      = (Scheme.ΓSpecIso Γ(Y, i ⁻¹ᵁ U)).inv.hom a := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  have h := IsAffineOpen.fromSpec_app_self (hU.preimage i)
  have hb := congrArg (fun t => ((Spec Γ(Y, i ⁻¹ᵁ U)).presheaf.map (homOfLE (top_le_preimage_j i U hU)).op).hom
    ((CommRingCat.Hom.hom t) a)) h
  simp only [CommRingCat.comp_apply] at hb
  refine hb.trans ?_
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : ((eqToHom ((hU.preimage i).fromSpec_preimage_self)).op ≫ (homOfLE (top_le_preimage_j i U hU)).op :
      op (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  erw [this, CategoryTheory.Functor.map_id]
  rfl

abbrev P : Type u := (Γ(MY i M, i ⁻¹ᵁ U) : Type u)

abbrev instRP : Module Γ(X, U) (P i U M) := Module.compHom (P i U M) (i.app U).hom

theorem isScalarTower_RSP : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    letI := instRP i U M; IsScalarTower Γ(X, U) Γ(Y, i ⁻¹ᵁ U) (P i U M) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem unit_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ((pullbackPushforwardAdjunction i).unit.app M).app U (b • m)
      = (i.app U).hom b • (show P i U M from ((pullbackPushforwardAdjunction i).unit.app M).app U m) :=
  Scheme.Modules.Hom.app_smul _ _ _

def ηR : letI := instRP i U M
    Γ(M, U) →ₗ[Γ(X, U)] P i U M :=
  letI := instRP i U M
  { toFun := fun m => η i U M m
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r m => by
      show η i U M (r • m) = ((i.app U).hom r) • η i U M m
      exact unit_smul i U M r m }

theorem ηR_apply (m : Γ(M, U)) : letI := instRP i U M
    ηR i U M m = η i U M m := rfl

def e₀ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(Y, i ⁻¹ᵁ U)] P i U M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  haveI := isScalarTower_RSP i U M
  LinearMap.liftBaseChange Γ(Y, i ⁻¹ᵁ U) (ηR i U M)

theorem e₀_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    e₀ i U M (a ⊗ₜ[Γ(X, U)] m) = a • η i U M m :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  haveI := isScalarTower_RSP i U M
  LinearMap.liftBaseChange_tmul Γ(Y, i ⁻¹ᵁ U) (ηR i U M) a m

theorem θ_e₀ (z : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
      Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    θ i U hU M (e₀ i U M z) = (σ i U hU M).hom.app ⊤ ((β i U hU M).hom (κ i U hU M z)) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]

  | add x y hx hy =>
    simp only [map_add, hx, hy]

  | tmul a m =>
    rw [e₀_tmul, κ_tmul, β_tmul, Q_smul_def, σ_smul, chase, θ_smul, scalar_key]

include hU in

theorem bijective_e₀
    (hM' : IsIso (M' U hU M).fromTildeΓ)
    (hC1 : ∀ (N : (Spec Γ(X, U)).Modules), IsIso N.fromTildeΓ →
      IsIso (((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj N)
        ((moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N))).symm
      ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app N) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
          ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N)))) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Function.Bijective (e₀ i U M) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  have hβ : IsIso (β i U hU M) := hC1 _ hM'
  have bβ : Function.Bijective (β i U hU M).hom := by
    have := ConcreteCategory.bijective_of_isIso (β i U hU M); exact this
  have bσ : Function.Bijective ((σ i U hU M).hom.app ⊤) := by
    rw [← ConcreteCategory.isIso_iff_bijective]; infer_instance
  have bθ := bijective_θ i U hU M
  have bκ : Function.Bijective (κ i U hU M) := (κ i U hU M).bijective
  have hcomp : Function.Bijective (fun z => θ i U hU M (e₀ i U M z)) := by
    have heq : (fun z => θ i U hU M (e₀ i U M z))
        = (fun z => (σ i U hU M).hom.app ⊤ ((β i U hU M).hom (κ i U hU M z))) := funext (θ_e₀ i U hU M)
    rw [heq]
    exact bσ.comp (bβ.comp bκ)
  constructor
  · exact Function.Injective.of_comp hcomp.1
  · intro p
    obtain ⟨z, hz⟩ := hcomp.2 (θ i U hU M p)
    exact ⟨z, bθ.1 hz⟩

include hU in
theorem main
    (hM' : IsIso (M' U hU M).fromTildeΓ)
    (hC1 : ∀ (N : (Spec Γ(X, U)).Modules), IsIso N.fromTildeΓ →
      IsIso (((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj N)
        ((moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N))).symm
      ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app N) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
          ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N)))) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, i ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e (1 ⊗ₜ m) = (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U).hom m := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  refine ⟨LinearEquiv.ofBijective (e₀ i U M) (bijective_e₀ i U hU M hM' hC1), fun m => ?_⟩
  rw [LinearEquiv.ofBijective_apply, e₀_tmul, one_smul]
  rfl

end AlgebraicGeometry.Scheme.Modules.SectionsCI


end
end
end

/- Checked affine and sheaf comparison support: BridgeUse. -/
section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
universe u
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaGlobalization.CoherentBridge

lemma affine_pullback_fromTilde {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((Scheme.Modules.pullback hU.fromSpec).obj M).fromTildeΓ := by
  have : ((Scheme.Modules.pullback hU.fromSpec).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X,U)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M) inferInstance
  infer_instance

lemma affine_baseChange {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X,U) Γ(Y,i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y,i ⁻¹ᵁ U) ⊗[Γ(X,U)] Γ(M,U) ≃ₗ[Γ(Y,i ⁻¹ᵁ U)]
      Γ((Scheme.Modules.pullback i).obj M,i ⁻¹ᵁ U),
    ∀ m : Γ(M,U), e (1 ⊗ₜ m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U m := by
  apply Scheme.Modules.SectionsCI.main i U hU M (affine_pullback_fromTilde M U hU)
  exact fun N h => Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma (i.app U) N h

end ArithmeticThetaGlobalization.CoherentBridge
end
end

/- Checked affine and sheaf comparison support: TensorKernel. -/
section
open TensorProduct
universe u
namespace ArithmeticThetaGlobalization.CoherentBridge
variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M]

lemma tensor_one_surjective (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (fun m : M => (1 : B) ⊗ₜ[A] m) := by
  intro z
  obtain ⟨w, rfl⟩ := LinearMap.rTensor_surjective M (g := Algebra.linearMap A B) h z
  refine ⟨TensorProduct.lid A M w, ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, tmul_add, hx, hy]
  | tmul a m => simpa only [LinearEquiv.coe_coe, TensorProduct.lid_tmul, LinearMap.rTensor_tmul, Algebra.linearMap_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

lemma tensor_one_eq_zero (h : Function.Surjective (algebraMap A B)) (m : M) :
    (1 : B) ⊗ₜ[A] m = 0 ↔ m ∈ RingHom.ker (algebraMap A B) • (⊤ : Submodule A M) := by
  let g := Algebra.linearMap A B
  have he : Function.Exact (RingHom.ker (algebraMap A B)).subtype g := by
    rw [LinearMap.exact_iff]
    ext a
    simp [g, RingHom.mem_ker]
  have hex := rTensor_exact M he h
  have hker := LinearMap.exact_iff.mp hex
  rw [← Ideal.subtype_rTensor_range M (RingHom.ker (algebraMap A B)), LinearMap.range_comp]
  change _ ↔ m ∈ Submodule.map (TensorProduct.lid A M).toLinearMap _
  rw [← hker, Submodule.mem_map]
  constructor
  · intro hm
    refine ⟨(1 : A) ⊗ₜ[A] m, ?_, by simp⟩
    simpa [LinearMap.mem_ker, g] using hm
  · rintro ⟨w, hw, rfl⟩
    have hw' : g.rTensor M w = 0 := hw
    have hh : (1 : B) ⊗ₜ[A] (TensorProduct.lid A M w) = g.rTensor M w := by
      clear hw hw'
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, tmul_add, hx, hy]
      | tmul a m => simpa only [g, TensorProduct.lid_tmul, LinearMap.rTensor_tmul, Algebra.linearMap_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    exact hh.trans hw'
end ArithmeticThetaGlobalization.CoherentBridge
end

/- Checked affine and sheaf comparison support: ReductionProbe. -/
section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
universe u
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization.CoherentBridge
variable {X : Scheme.{u}} (M : X.Modules)

def localMap {Y : Scheme.{u}} (i : Y ⟶ X) (U : X.Opens) :
    Γ(M,U) ⟶ Γ((Scheme.Modules.pullback i).obj M,i ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U

lemma reduction_surjective [M.IsQuasicoherent] (J : X.IdealSheafData) (U : X.affineOpens) :
    Function.Surjective (localMap M J.subschemeι U.1) := by
  letI : Algebra Γ(X,U.1) Γ(J.subscheme,J.subschemeι ⁻¹ᵁ U.1) := (J.subschemeι.app U.1).hom.toAlgebra
  obtain ⟨e, he⟩ := affine_baseChange J.subschemeι M U.1 U.2
  have h := tensor_one_surjective (M := Γ(M,U.1)) (J.subschemeι_app_surjective U)
  intro y
  obtain ⟨m, hm⟩ := h (e.symm y)
  refine ⟨m, ?_⟩
  change ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app M).app U.1 m = y
  exact (he m).symm.trans ((congrArg e hm).trans (e.apply_symm_apply y))

lemma reduction_kernel [M.IsQuasicoherent] (J : X.IdealSheafData) (U : X.affineOpens) (m : Γ(M,U.1)) :
    localMap M J.subschemeι U.1 m = 0 ↔ m ∈ J.ideal U • (⊤ : Submodule Γ(X,U.1) Γ(M,U.1)) := by
  letI : Algebra Γ(X,U.1) Γ(J.subscheme,J.subschemeι ⁻¹ᵁ U.1) := (J.subschemeι.app U.1).hom.toAlgebra
  obtain ⟨e, he⟩ := affine_baseChange J.subschemeι M U.1 U.2
  change ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app M).app U.1 m = 0 ↔ _
  rw [← he, e.map_eq_zero_iff]
  rw [tensor_one_eq_zero (J.subschemeι_app_surjective U)]
  rw [show RingHom.ker (algebraMap Γ(X,U.1) Γ(J.subscheme,J.subschemeι ⁻¹ᵁ U.1)) = J.ideal U from
    Scheme.IdealSheafData.ker_subschemeι_app J U]
end ArithmeticThetaGlobalization.CoherentBridge
end
end

/- Checked affine and sheaf comparison support: TransitionProbe. -/
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization.CoherentBridge
open Scheme.Modules
variable {X Y Z : Scheme.{u}} (M : X.Modules)

def transition (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ p = q) :
    (pushforward p).obj ((pullback p).obj M) ⟶ (pushforward q).obj ((pullback q).obj M) :=
  (pushforward p).map
    ((pullbackPushforwardAdjunction g).unit.app ((pullback p).obj M) ≫
      (pushforward g).map ((pullbackComp g p).hom.app M ≫ (pullbackCongr h).hom.app M)) ≫
    (pushforwardComp g p).hom.app ((pullback q).obj M) ≫
      (pushforwardCongr h).hom.app ((pullback q).obj M)

lemma transition_unit (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ p = q) :
    (pullbackPushforwardAdjunction p).unit.app M ≫ transition M p q g h =
      (pullbackPushforwardAdjunction q).unit.app M := by
  subst q
  ext U x
  simp only [transition, Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Hom.id_app, Category.comp_id, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  have hh := congrArg (fun f => f ≫ ((pullbackComp g p).hom.app M).app ((g ≫ p) ⁻¹ᵁ U))
    (UnitCalculus.unit_app_comp g p M U)
  simp only [Category.assoc, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app, Category.comp_id] at hh
  have hv := congrArg (fun f => f x) hh
  change ((pullbackPushforwardAdjunction (g ≫ p)).unit.app M).app U x =
    ((pullbackComp g p).hom.app M).app ((g ≫ p) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction g).unit.app ((pullback p).obj M)).app (p ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction p).unit.app M).app U x)) at hv
  exact hv.symm

lemma transition_top (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ p = q)
    (s : Γ((pullback p).obj M,⊤)) :
    (transition M p q g h).app ⊤ s = ArithmeticThetaRootTorsor.pullbackSectionOver p q M ⟨g,h⟩ s := by
  subst q
  simp only [transition, Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Hom.id_app, Category.comp_id, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma localMap_res (p : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(M,U)) :
    localMap M p V (M.presheaf.map (homOfLE h).op a) =
      ((pullback p).obj M).presheaf.map (homOfLE (p.preimage_mono h)).op (localMap M p U a) := by
  exact congrArg (fun f => f a) (((pullbackPushforwardAdjunction p).unit.app M).val.naturality (homOfLE h).op)

def resTop (U : X.Opens) : Γ(M,⊤) ⟶ Γ(M,U) := M.presheaf.map (homOfLE le_top).op

lemma res_resTop {U V : X.Opens} (h : V ≤ U) (a : Γ(M,⊤)) :
    M.presheaf.map (homOfLE h).op (resTop M U a) = resTop M V a := by
  change M.presheaf.map _ (M.presheaf.map _ a) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma lift_transition (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (h : g ≫ p = q)
    (U : X.Opens) (a : Γ(M,U)) (s : Γ((pullback p).obj M,⊤))
    (ha : localMap M p U a = resTop ((pullback p).obj M) (p ⁻¹ᵁ U) s) :
    localMap M q U a = resTop ((pullback q).obj M) (q ⁻¹ᵁ U)
      (ArithmeticThetaRootTorsor.pullbackSectionOver p q M ⟨g,h⟩ s) := by
  have hu := congrArg (fun v => v.app U a) (transition_unit M p q g h)
  change (transition M p q g h).app U (localMap M p U a) = localMap M q U a at hu
  rw [ha] at hu
  have hn := congrArg (fun v => v s) ((transition M p q g h).val.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change (transition M p q g h).app U (resTop ((pullback p).obj M) (p ⁻¹ᵁ U) s) =
    resTop ((pullback q).obj M) (q ⁻¹ᵁ U) ((transition M p q g h).app ⊤ s) at hn
  rw [transition_top] at hn
  exact hu.symm.trans hn
end ArithmeticThetaGlobalization.CoherentBridge
end
end

/- Checked affine and sheaf comparison support: QuasiProbe. -/
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization.CoherentBridge
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)

lemma image_top : hU.fromSpec ''ᵁ ⊤ = U := by simp [hU.opensRange_fromSpec]

def eTop : Γ(M.restrict hU.fromSpec,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso hU.fromSpec ⊤ ≪≫ M.presheaf.mapIso (eqToIso (image_top U hU).symm).op

def eBasic (a : Γ(X,U)) : Γ(M.restrict hU.fromSpec,PrimeSpectrum.basicOpen a) ≅ Γ(M,X.basicOpen a) :=
  M.restrictAppIso hU.fromSpec _ ≪≫ M.presheaf.mapIso (eqToIso (hU.fromSpec_image_basicOpen a).symm).op

lemma fromSpec_appLE (V : (Spec Γ(X,U)).Opens) (h : V ≤ hU.fromSpec ⁻¹ᵁ U) (b : Γ(X,U)) :
    hU.fromSpec.appLE U V h b =
      (Spec Γ(X,U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X,U)).inv b) := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, CommRingCat.comp_apply, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma eTop_smul (a : Γ(X,U)) (x : Γ(M.restrict hU.fromSpec,⊤)) :
    (eTop M U hU).hom (a • x) = a • (eTop M U hU).hom x := by
  change M.presheaf.map _ ((M.restrictAppIso hU.fromSpec ⊤).hom (a • x)) = _
  rw [Scheme.Modules.smul_Spec_def]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  simp only [Iso.op_hom]
  rw [Scheme.Modules.map_smul]
  congr 1
  erw [← fromSpec_appLE U hU ⊤ (by rw [hU.fromSpec_preimage_self])]
  simp only [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.appLE_appIso_inv, ← Functor.map_comp]
  change X.presheaf.map (𝟙 (op U)) a = a
  simp

lemma eBasic_smul (a b : Γ(X,U)) (x : Γ(M.restrict hU.fromSpec,PrimeSpectrum.basicOpen a)) :
    (eBasic M U hU a).hom (b • x) =
      X.presheaf.map (homOfLE (X.basicOpen_le a)).op b • (eBasic M U hU a).hom x := by
  change M.presheaf.map _ ((M.restrictAppIso hU.fromSpec _).hom (b • x)) = _
  rw [Scheme.Modules.smul_Spec_def]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  simp only [Iso.op_hom]
  rw [Scheme.Modules.map_smul]
  congr 1
  erw [← fromSpec_appLE U hU (PrimeSpectrum.basicOpen a) (by rw [hU.fromSpec_preimage_self]; exact le_top)]
  simp only [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.appLE_appIso_inv, ← Functor.map_comp]
  rfl

lemma eBasic_res (a : Γ(X,U)) (x : Γ(M.restrict hU.fromSpec,⊤)) :
    (eBasic M U hU a).hom ((M.restrict hU.fromSpec).presheaf.map (homOfLE le_top).op x) =
      M.presheaf.map (homOfLE (X.basicOpen_le a)).op ((eTop M U hU).hom x) := by
  simp only [eBasic,eTop,Iso.trans_hom,Functor.mapIso_hom,Iso.op_hom,ConcreteCategory.comp_apply]
  rw [Scheme.Modules.map_restrictAppIso_hom_apply]
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ (M.presheaf.map _ x)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma quasicoherent_ofModules {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    [M.IsQuasicoherent] : (OModulePresheaf.ofModules f M).IsQuasicoherent := by
  intro U a
  let N := M.restrict U.2.fromSpec
  haveI : N.IsQuasicoherent := inferInstance
  have hloc : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  haveI := hloc a
  constructor
  · intro x
    obtain ⟨n,y,hy⟩ := IsLocalizedModule.Away.surj
      ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom a
      ((eBasic M U.1 U.2 a).inv x)
    refine ⟨n,(eTop M U.1 U.2).hom y, ?_⟩
    have hh := congrArg ((eBasic M U.1 U.2 a).hom) hy.symm
    change (eBasic M U.1 U.2 a).hom ((M.restrict U.2.fromSpec).presheaf.map (homOfLE le_top).op y) =
      (eBasic M U.1 U.2 a).hom ((a^n) • (eBasic M U.1 U.2 a).inv x) at hh
    rw [eBasic_res, eBasic_smul, Iso.inv_hom_id_apply] at hh
    exact hh
  · intro y hy
    have hh : N.presheaf.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op ((eTop M U.1 U.2).inv y) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (eBasic M U.1 U.2 a).hom).1
      rw [map_zero, eBasic_res, Iso.inv_hom_id_apply]
      exact hy
    obtain ⟨⟨_,n,rfl⟩,hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
      ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom
      (m := (eTop M U.1 U.2).inv y)).mp hh
    refine ⟨n, ?_⟩
    change (a^n) • (eTop M U.1 U.2).inv y = 0 at hn
    have he := congrArg ((eTop M U.1 U.2).hom) hn
    rw [map_zero, eTop_smul, Iso.inv_hom_id_apply] at he
    exact he
end ArithmeticThetaGlobalization.CoherentBridge
end
end

/- Checked affine and sheaf comparison support: CechBridge. -/
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization.CoherentBridge
open ArithmeticThetaGeometricPrerequisites
open ArithmeticThetaGeometricPrerequisites.FormalBridge (parameter_ideal_affine powers_antitone properCover)
open P2MW.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.CechH0Sol (idx0 le_inter_idx0)
variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R) (M : X.Modules)

lemma cochain_mem_pow_iff (K : X.OrderedAffineCover) (i n : ℕ)
    (a : (OModulePresheaf.ofModules f M).cochain K i) :
    a ∈ (Ideal.span {t})^n • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain K i)) ↔
    ∀ s : K.Idx i, ∃ b : Γ(M,K.inter s),
      ((Scheme.TwoAffineOpenCover.algebraOfHom f (K.inter s)).algebraMap t)^n • b = a s := by
  classical
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b,_,hb⟩ s
    refine ⟨b s, ?_⟩
    have h := congrFun hb s
    simpa only [Pi.smul_apply, OModulePresheaf.ofModules_algebraMap_smul, map_pow] using h
  · intro h
    choose b hb using h
    refine ⟨b,Submodule.mem_top, funext fun s => ?_⟩
    change ((Scheme.TwoAffineOpenCover.algebraOfHom f (K.inter s)).algebraMap (t^n)) • b s = a s
    simpa only [map_pow] using hb s

lemma cochain_mem_pow_iff_kernel [IsSeparated f] [M.IsQuasicoherent]
    (K : X.OrderedAffineCover) (i n : ℕ) (a : (OModulePresheaf.ofModules f M).cochain K i) :
    a ∈ (Ideal.span {t})^n • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).cochain K i)) ↔
    ∀ s : K.Idx i, localMap M (parameterIdeal R X f t ^ n).subschemeι (K.inter s) (a s) = 0 := by
  rw [cochain_mem_pow_iff]
  apply forall_congr'
  intro s
  rw [reduction_kernel M _ ⟨K.inter s,K.isAffineOpen_inter f s⟩,
    parameter_ideal_affine, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

omit f t in
lemma sections_ext (K : X.OrderedAffineCover) (a b : Γ(M,⊤))
    (h : ∀ j : K.Idx 0, resTop M (K.inter j) a = resTop M (K.inter j) b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf,M.isSheaf⟩ K.U ⊤
    (fun _ => homOfLE le_top) K.iSup_eq_top.ge
  intro i
  have hh := congrArg (M.presheaf.map (homOfLE (le_inter_idx0 K i)).op) (h (idx0 K i))
  rw [res_resTop, res_resTop] at hh
  exact hh

lemma global_cocycle (K : X.OrderedAffineCover) (a : Γ(M,⊤)) :
    (OModulePresheaf.ofModules f M).d K 0 (fun j => resTop M (K.inter j) a) = 0 := by
  funext j
  rw [OModulePresheaf.d_apply]
  change (∑ k : Fin 2, ((-1 : ℤ)^(k:ℕ)) •
    M.presheaf.map (homOfLE (K.inter_le_inter_face j k)).op (resTop M (K.inter (K.face j k)) a)) = 0
  simp_rw [res_resTop]
  simp [Fin.sum_univ_two]

lemma d_lift_zero (K : X.OrderedAffineCover) (J : X.IdealSheafData)
    (s : Γ((Scheme.Modules.pullback J.subschemeι).obj M,⊤))
    (a : (OModulePresheaf.ofModules f M).cochain K 0)
    (ha : ∀ j : K.Idx 0, localMap M J.subschemeι (K.inter j) (a j) =
      resTop ((Scheme.Modules.pullback J.subschemeι).obj M) (J.subschemeι ⁻¹ᵁ K.inter j) s) :
    ∀ j : K.Idx 1, localMap M J.subschemeι (K.inter j) ((OModulePresheaf.ofModules f M).d K 0 a j) = 0 := by
  intro j
  rw [OModulePresheaf.d_apply]
  change localMap M J.subschemeι (K.inter j)
    (∑ k : Fin 2, ((-1 : ℤ)^(k:ℕ)) • M.presheaf.map (homOfLE (K.inter_le_inter_face j k)).op (a (K.face j k))) = 0
  rw [map_sum]
  simp_rw [map_zsmul, localMap_res, ha, res_resTop]
  simp [Fin.sum_univ_two]

lemma subscheme_sections_ext (K : X.OrderedAffineCover) (J : X.IdealSheafData)
    (a b : Γ((Scheme.Modules.pullback J.subschemeι).obj M,⊤))
    (h : ∀ j : K.Idx 0,
      resTop ((Scheme.Modules.pullback J.subschemeι).obj M) (J.subschemeι ⁻¹ᵁ K.inter j) a =
      resTop ((Scheme.Modules.pullback J.subschemeι).obj M) (J.subschemeι ⁻¹ᵁ K.inter j) b) : a = b := by
  apply sections_ext J.subscheme ((Scheme.Modules.pullback J.subschemeι).obj M) (K.comap J.subschemeι)
  intro j
  rw [K.comap_inter J.subschemeι j]
  exact h j
end ArithmeticThetaGlobalization.CoherentBridge
end
end

/- Checked affine and sheaf comparison support: AlgebraizeProbe. -/
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization.CoherentBridge
open ArithmeticThetaGeometricPrerequisites ArithmeticThetaRootTorsor
open ArithmeticThetaGeometricPrerequisites.FormalBridge (powers_antitone properCover)
lemma localMap_resTop {X Y : Scheme.{u}} (M : X.Modules) (p : Y ⟶ X) (U : X.Opens) (a : Γ(M,⊤)) :
    localMap M p U (resTop M U a) =
      resTop ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U)
        (ArithmeticThetaPullback.pullbackGlobalSection p M a) := localMap_res M p le_top a

lemma resTop_top {X : Scheme.{u}} (M : X.Modules) (a : Γ(M,⊤)) : resTop M ⊤ a = a := by
  change M.presheaf.map (𝟙 (op ⊤)) a = a
  rw [CategoryTheory.Functor.map_id]
  rfl

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (t : R) [IsAdicComplete (Ideal.span {t}) R]
  (M : X.Modules) [M.IsQuasicoherent]

theorem algebraize
    (hc : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X,U) Γ(M,U))
    (K : X.OrderedAffineCover)
    (s : FormalLineSections X (parameterIdeal R X f t) M)
    (hs : CompatibleFormalLineSections X (parameterIdeal R X f t) M s) :
    ∃! a : Γ(M,⊤), ∀ n : ℕ,
      ArithmeticThetaPullback.pullbackGlobalSection (parameterIdeal R X f t ^ n).subschemeι M a = s n := by
  classical
  let I := parameterIdeal R X f t
  let F := OModulePresheaf.ofModules f M
  have hLift (n : ℕ) (j : K.Idx 0) : ∃ a : Γ(M,K.inter j),
      localMap M (I^(n+1)).subschemeι (K.inter j) a =
        resTop ((Scheme.Modules.pullback (I^(n+1)).subschemeι).obj M)
          ((I^(n+1)).subschemeι ⁻¹ᵁ K.inter j) (s (n+1)) :=
    reduction_surjective M (I^(n+1)) ⟨K.inter j,K.isAffineOpen_inter f j⟩ _
  choose a ha using hLift
  have hd (n : ℕ) : F.d K 0 (a n) ∈
      (Ideal.span {t})^(n+1) • (⊤ : Submodule R (F.cochain K 1)) := by
    rw [cochain_mem_pow_iff_kernel]
    exact d_lift_zero R X f M K _ (s (n+1)) (a n) (ha n)
  have ht (n : ℕ) : a (n+1) - a n ∈
      (Ideal.span {t})^(n+1) • (⊤ : Submodule R (F.cochain K 0)) := by
    rw [cochain_mem_pow_iff_kernel]
    intro j
    change localMap M (I^(n+1)).subschemeι (K.inter j) (a (n+1) j - a n j) = 0
    rw [map_sub, sub_eq_zero, ha]
    have hle : I^(n+1+1) ≤ I^(n+1) := powers_antitone X I (Nat.le_succ _)
    have h := lift_transition M (I^(n+1+1)).subschemeι (I^(n+1)).subschemeι
      (Scheme.IdealSheafData.inclusion hle) (Scheme.IdealSheafData.inclusion_subschemeι hle)
      (K.inter j) (a (n+1) j) (s (n+1+1)) (ha (n+1) j)
    rw [hs (n+1) (n+1+1) hle] at h
    exact h
  have hcF : F.IsCoherent := fun U => hc U.1 U.2
  obtain ⟨b,⟨hdb,hb⟩,huniq⟩ :=
    OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
      (Ideal.span {t}) f F hcF (quasicoherent_ofModules M f) K a hd ht
  obtain ⟨z,hz,huz⟩ :=
    (P2MW.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.solution f M K b).mp hdb
  have hzpos (n : ℕ) : ArithmeticThetaPullback.pullbackGlobalSection (I^(n+1)).subschemeι M z = s (n+1) := by
    apply subscheme_sections_ext X M K (I^(n+1))
    intro j
    change resTop ((Scheme.Modules.pullback (I^(n+1)).subschemeι).obj M) _
      (localMap M (I^(n+1)).subschemeι ⊤ z) = _
    change resTop ((Scheme.Modules.pullback (I^(n+1)).subschemeι).obj M) _
      (ArithmeticThetaPullback.pullbackGlobalSection (I^(n+1)).subschemeι M z) = _
    rw [← localMap_resTop]
    have h := (cochain_mem_pow_iff_kernel R X f t M K 0 (n+1) (b - (show F.cochain K 0 from a n))).mp (hb n) j
    change localMap M (I^(n+1)).subschemeι (K.inter j) ((show Γ(M,K.inter j) from b j) - a n j) = 0 at h
    rw [map_sub, sub_eq_zero, ha] at h
    have hj : resTop M (K.inter j) z = b j := (hz j).symm
    rw [hj]
    exact h
  have hzall (n : ℕ) : ArithmeticThetaPullback.pullbackGlobalSection (I^n).subschemeι M z = s n := by
    cases n with
    | succ n => exact hzpos n
    | zero =>
      have hle : I^1 ≤ I^0 := powers_antitone X I (Nat.zero_le _)
      have h := lift_transition M (I^1).subschemeι (I^0).subschemeι
        (Scheme.IdealSheafData.inclusion hle) (Scheme.IdealSheafData.inclusion_subschemeι hle)
        ⊤ z (s 1) (by exact (hzpos 0).trans (resTop_top _ (s 1)).symm)
      rw [hs 0 1 hle] at h
      exact h.trans (resTop_top _ (s 0))
  refine ⟨z,hzall,?_⟩
  intro z' hz'
  have hzb : (fun j : K.Idx 0 => resTop M (K.inter j) z') = b := by
    apply huniq
    refine ⟨global_cocycle R X f M K z', fun n => ?_⟩
    rw [cochain_mem_pow_iff_kernel]
    intro j
    change localMap M (I^(n+1)).subschemeι (K.inter j) (resTop M (K.inter j) z' - a n j) = 0
    rw [map_sub,sub_eq_zero,ha,localMap_resTop]
    change resTop ((Scheme.Modules.pullback (I^(n+1)).subschemeι).obj M) _
      (ArithmeticThetaPullback.pullbackGlobalSection (I^(n+1)).subschemeι M z') = _
    rw [hz']
  apply sections_ext X M K
  intro j
  exact (congrFun hzb j).trans (hz j)
end ArithmeticThetaGlobalization.CoherentBridge
end
end

section
universe u
/-- Coherent formal sections on all actual infinitesimal thickenings. -/
theorem ArithmeticThetaGlobalization.proper_coherent_formal_sections :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R] (X : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom X (AlgebraicGeometry.Spec (CommRingCat.of R))) [AlgebraicGeometry.IsProper f] (H : X.Modules), H.IsQuasicoherent → (∀ U : X.Opens, AlgebraicGeometry.IsAffineOpen U → Module.Finite (X.presheaf.obj (Opposite.op U)) (H.presheaf.obj (Opposite.op U))) → ∀ s : ArithmeticThetaRootTorsor.FormalLineSections X (ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t) H, ArithmeticThetaRootTorsor.CompatibleFormalLineSections X (ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t) H s → ∃! a : H.presheaf.obj (Opposite.op ⊤), ∀ n : ℕ, ArithmeticThetaPullback.pullbackGlobalSection ((ArithmeticThetaGeometricPrerequisites.parameterIdeal R X f t ^ n).subschemeι) H a = s n := by
  intro R _ _ t _ X f _ H hq hc s hs
  letI := hq
  exact ArithmeticThetaGlobalization.CoherentBridge.algebraize R X f t H hc
    (ArithmeticThetaGeometricPrerequisites.FormalBridge.properCover R X f) s hs

#print axioms ArithmeticThetaGlobalization.proper_coherent_formal_sections
end
