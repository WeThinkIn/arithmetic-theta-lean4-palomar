module

public import IntegralHodgeDefinitionsR0149
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen

@[expose] public section

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaIntegralHodgeR0149
namespace GenericKaehlerComparisonR0149
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull

open scoped TensorProduct

lemma tensor_inclusion_bijective (C D P : Type u) [CommRing C] [CommRing D]
    [Algebra C D] [AddCommGroup P] [Module C P]
    (h : Function.Bijective (algebraMap C D)) :
    Function.Bijective (fun x : P => (1 : D) ⊗ₜ[C] x) := by
  let e : C ≃ₐ[C] D := AlgEquiv.ofBijective (Algebra.ofId C D) h
  let t : P ≃ₗ[C] D ⊗[C] P := (TensorProduct.lid C P).symm.trans
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl C P))
  have ht : (fun x : P => (1 : D) ⊗ₜ[C] x) = t := by
    funext x
    simp [t]
  rw [ht]
  exact t.bijective

lemma differential_map_bijective (A B C D : Type u)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A B C D]
    (h : Function.Bijective (algebraMap C D)) :
    Function.Bijective (KaehlerDifferential.map A B C D) := by
  have he : ∀ x : Ω[C⁄A],
      KaehlerDifferential.tensorKaehlerEquiv A B C D (1 ⊗ₜ[C] x) =
        KaehlerDifferential.map A B C D x := by
    intro x
    have hx : x ∈ Submodule.span C (Set.range (KaehlerDifferential.D A C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul,
        KaehlerDifferential.map_D]
    | zero => simp
    | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul D a,
        LinearEquiv.map_smul, hx, map_smul, IsScalarTower.algebraMap_smul]
  have hh := (KaehlerDifferential.tensorKaehlerEquiv A B C D).bijective.comp
    (tensor_inclusion_bijective C D Ω[C⁄A] h)
  simpa only [Function.comp_def, he] using hh

section General
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {X Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A))
  (g : X ⟶ Spec (CommRingCat.of B)) (j : X ⟶ Y)
  (h : j ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The map induced by the actual commuting square, via the two universal adjunctions. -/
def comparisonHom : (Scheme.Modules.pullback j).obj f.kaehler ⟶ g.kaehler :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm (k1 f g j h)

lemma comparisonHom_D (U : Y.Opens) (a : Γ(Y, U)) :
    (comparisonHom f g j h).app (j ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection j (relativeD f U a)) =
      relativeD g (j ⁻¹ᵁ U) (j.app U a) := by
  rw [comparisonHom, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  change (k1 f g j h).app U (f.kaehlerToSections U (dK f U a)) = _
  rw [k1_kaehlerToSections, k1app_dK]
  rfl

/-- Differential generators determine a map out of the pulled-back sheaf. -/
lemma hom_ext {N : X.Modules}
    (α β : (Scheme.Modules.pullback j).obj f.kaehler ⟶ N)
    (hab : ∀ (U : Y.Opens) (a : Γ(Y, U)),
      α.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j (relativeD f U a)) =
      β.app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j (relativeD f U a))) : α = β := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).injective
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  exact (Scheme.Modules.app_pullbackLocalSection j α (relativeD f U.unop a)).symm.trans
    ((hab U.unop a).trans (Scheme.Modules.app_pullbackLocalSection j β (relativeD f U.unop a)))

lemma pullbackSection_bijective [IsOpenImmersion j] (U : Y.Opens)
    (hU : U ≤ j.opensRange) :
    Function.Bijective (fun s : Γ(f.kaehler, U) => Scheme.Modules.pullbackLocalSection j s) := by
  have he : j ''ᵁ j ⁻¹ᵁ U = U := by
    rw [j.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hi : IsIso (homOfLE (j.image_preimage_le U)) := by
    rw [show homOfLE (j.image_preimage_le U) = eqToHom he from Subsingleton.elim _ _]
    infer_instance
  have hm := ConcreteCategory.bijective_of_isIso
    (f.kaehler.presheaf.map (homOfLE (j.image_preimage_le U)).op)
  have hn := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback j).hom.app f.kaehler).app (j ⁻¹ᵁ U))
  convert hn.comp hm using 1
  funext s
  exact P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.PicTanH.pullbackLocalSection_openImmersion j f.kaehler U s

lemma comparison_app_bijective [IsOpenImmersion j]
    (hp : CategoryTheory.IsPullback j g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) (hUr : U ≤ j.opensRange) :
    Function.Bijective ((comparisonHom f g j hp.w).app (j ⁻¹ᵁ U)) := by
  letI := f.sectionsAlgebra U
  letI := g.sectionsAlgebra (j ⁻¹ᵁ U)
  letI : Algebra Γ(Y, U) Γ(X, j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  letI : Algebra A Γ(X, j ⁻¹ᵁ U) :=
    (CommRingCat.ofHom (algebraMap A B) ≫ g.constToPresheaf.app (op (j ⁻¹ᵁ U))).hom.toAlgebra
  haveI : IsScalarTower A B Γ(X, j ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A Γ(Y, U) Γ(X, j ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (fac f g j hp.w U))
  obtain ⟨hV, hPO⟩ := f.isAffineOpen_preimage_and_isPushout_of_isPullback g j hp U hU
  have hAlg : (j.appLE U (j ⁻¹ᵁ U) le_rfl).hom.toAlgebra = (j.app U).hom.toAlgebra :=
    congrArg (fun q : Γ(Y, U) ⟶ Γ(X, j ⁻¹ᵁ U) => q.hom.toAlgebra) j.appLE_eq_app
  rw [hAlg] at hPO
  haveI : Algebra.IsPushout A B Γ(Y, U) Γ(X, j ⁻¹ᵁ U) := hPO
  haveI : IsIso (j.app U) := j.isIso_app U hUr
  have hd := differential_map_bijective A B Γ(Y, U) Γ(X, j ⁻¹ᵁ U)
    (ConcreteCategory.bijective_of_isIso (j.app U))
  have hk : Function.Bijective (fun x : f.kaehlerPresheaf.obj (op U) => k1app f g j hp.w U x) :=
    (g.kaehlerToSections_bijective_of_isAffineOpen hV).comp hd
  have hk1 : Function.Bijective ((k1 f g j hp.w).app U) := by
    apply (Function.Bijective.of_comp_iff _ (f.kaehlerToSections_bijective_of_isAffineOpen hU)).mp
    change Function.Bijective (fun x : f.kaehlerPresheaf.obj (op U) =>
      (k1 f g j hp.w).app U (f.kaehlerToSections U x))
    simpa only [k1_kaehlerToSections] using hk
  apply (Function.Bijective.of_comp_iff _ (pullbackSection_bijective f j U hUr)).mp
  change Function.Bijective (fun x : Γ(f.kaehler, U) =>
    (comparisonHom f g j hp.w).app (j ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection j x))
  simpa only [comparisonHom, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection] using hk1

lemma isIso_of_affine_app {P Q : X.Modules} (α : P ⟶ Q)
    (hα : ∀ (V : X.Opens), IsAffineOpen V → Function.Bijective (α.app V)) : IsIso α := by
  let αs : (⟨P.presheaf, P.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X.carrier) ⟶
      ⟨Q.presheaf, Q.isSheaf⟩ := ⟨α.mapPresheaf⟩
  have hs : IsIso αs := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun V : X.affineOpens => V.val)
    · simpa using X.isBasis_affineOpens
    · intro V
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact hα V.val V.property
  haveI : IsIso αs := hs
  haveI : IsIso αs.hom :=
    (inferInstance : IsIso ((sheafToPresheaf _ _).map αs))
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (αs.hom.app (op V))

lemma comparison_isIso [IsOpenImmersion j]
    (hp : CategoryTheory.IsPullback j g f (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    IsIso (comparisonHom f g j hp.w) := by
  apply isIso_of_affine_app
  intro V hV
  have hh := comparison_app_bijective f g j hp (j ''ᵁ V)
    (hV.image_of_isOpenImmersion j) (j.image_le_opensRange V)
  have he := j.preimage_image_eq V
  exact he ▸ hh

end General

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)

lemma square_commutes : genericInclusion k M ≫ M.p =
    genericStructure k M ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k))) :=
  CategoryTheory.Limits.pullback.condition

lemma comparison_unique (b c : GenericComparison k M)
    (hb : IsGenericComparison k M b) (hc : IsGenericComparison k M c) : b = c := by
  apply Iso.ext
  apply hom_ext M.p (genericInclusion k M)
  intro U a
  exact (hb U a).trans (hc U a).symm

end GenericKaehlerComparisonR0149
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140
open GenericKaehlerComparisonR0149

/-- The unique canonical generic base-change isomorphism, with all generator equations. -/
theorem generic_kaehler_comparison : ∀ (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (T : Tower k r hr) (M : Model k T),
    ∃! b : GenericComparison k M, IsGenericComparison k M b := by
  intro k _ _ r hr T M
  letI : IsOpenImmersion (genericInclusion k M) :=
    ArithmeticThetaProjectiveEffectivityR0135.AlgebraizedGenericSmoothnessR0135.generic_inclusion_open k M
  have hp : IsPullback (genericInclusion k M) (genericStructure k M) M.p
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) :=
    CategoryTheory.IsPullback.of_hasPullback M.p (genericBase k)
  letI := comparison_isIso M.p (genericStructure k M) (genericInclusion k M) hp
  let b : GenericComparison k M := asIso
    (comparisonHom M.p (genericStructure k M) (genericInclusion k M) hp.w)
  have hb : IsGenericComparison k M b := by
    intro U a
    exact comparisonHom_D M.p (genericStructure k M) (genericInclusion k M) hp.w U a
  exact ⟨b, hb, fun c hc => comparison_unique k M c b hc hb⟩

end ArithmeticThetaIntegralHodgeR0149
