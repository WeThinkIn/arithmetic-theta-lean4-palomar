import LocalWeierstrassDefinitionsR0203
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation

import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation

import Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso

import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback


import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth

import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_sections_pullback_obj_unit_eq
import Theorems.Thm_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
import Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaLocalWeierstrassR0203.FiniteTypeApproximation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

/-- Multiplication compatibility on all test schemes forces compatibility with
the actual origin sections, without passing to geometric points. -/
theorem origin_eq_of_mul_eq
    {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} {f : X ⟶ Base R} {g : Y ⟶ Base S}
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw S g)
    (b : Base R ⟶ Base S) (π : X ⟶ Y) (hπ : π ≫ g = f ≫ b)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Base R) (x y : SchemeHomOver t f),
      (L.mul t x y).val ≫ π =
        (M.mul (t ≫ b)
          ⟨x.val ≫ π, by rw [Category.assoc, hπ, ← Category.assoc, x.property]⟩
          ⟨y.val ≫ π, by rw [Category.assoc, hπ, ← Category.assoc, y.property]⟩).val) :
    (L.one (𝟙 _)).val ≫ π = b ≫ (M.one (𝟙 _)).val := by
  let z : SchemeHomOver ((𝟙 (Base R)) ≫ b) g :=
    ⟨(L.one (𝟙 _)).val ≫ π, by
      rw [Category.assoc, hπ, ← Category.assoc, (L.one (𝟙 _)).property]⟩
  have hz : M.mul _ z z = z := by
    apply Subtype.ext
    exact (hmul (𝟙 _) (L.one (𝟙 _)) (L.one (𝟙 _))).symm.trans
      (congrArg (fun x : SchemeHomOver (𝟙 _) f => x.val ≫ π) (L.one_mul _ _))
  have hz1 : z = M.one _ := by
    letI := M.pointGroup ((𝟙 (Base R)) ≫ b)
    apply mul_left_cancel (a := z)
    change M.mul _ z z = M.mul _ z (M.one _)
    rw [M.mul_one]
    exact hz
  have hn := congrArg Subtype.val (M.one_natural (𝟙 _) ((𝟙 (Base R)) ≫ b) b (by simp))
  exact (congrArg Subtype.val hz1).trans hn.symm

/-- Finite presentation follows from the actual smooth proper geometry. -/
theorem finite_presentation (R : Type u) [CommRing R] (Q : FramedCurve R) :
    LocallyOfFinitePresentation Q.structureMap ∧ QuasiCompact Q.structureMap ∧
      QuasiSeparated Q.structureMap := by
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : IsProper Q.structureMap := Q.geometry.proper
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Effective finite-type descent of the underlying scheme and structural map.
The group operations, geometric properties, dimension and Hodge frame remain
additional descent obligations for the final framed model. -/
theorem underlying_scheme_descent
    {A₀ : Type u} [CommRing A₀]
    (R : Type u) [CommRing R] [Algebra A₀ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra A₀ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.target ⟶ X),
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  obtain ⟨hlfp, hqc, hqs⟩ := finite_presentation R Q
  letI := hlfp
  letI := hqc
  letI := hqs
  obtain ⟨T, hT, _, X, f, π, hs⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := A₀) Q.structureMap ∅
  exact ⟨T, hT, X, f, π, hs⟩

/-- The underlying model can be chosen over a finitely generated rational
subalgebra, with no nontriviality, reducedness or domain hypothesis on `R`. -/
theorem rational_scheme_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.target ⟶ X),
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  letI : Algebra (ULift.{u} ℚ) R := ULift.algebra' ℚ R
  letI : IsScalarTower ℚ (ULift.{u} ℚ) R :=
    IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ULift.{u} ℚ) (A := R) fun r => rfl
  obtain ⟨T, hT, X, f, π, hs⟩ := underlying_scheme_descent (A₀ := ULift.{u} ℚ) R Q
  letI : Algebra.FiniteType ℚ (ULift.{u} ℚ) :=
    Algebra.FiniteType.equiv inferInstance (ULift.algEquiv : ULift.{u} ℚ ≃ₐ[ℚ] ℚ).symm
  letI : Algebra.FiniteType (ULift.{u} ℚ) T := T.fg_iff_finiteType.mp hT
  have hTQ : (T.restrictScalars ℚ).FG := by
    apply (T.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := ULift.{u} ℚ) (A := T)
      inferInstance inferInstance
  exact ⟨T.restrictScalars ℚ, hTQ, X, f, π, hs⟩

/-- Properness and flatness can be retained on the rational finite-type model.
The group law, relative dimension and Hodge frame are not asserted here. -/
theorem rational_proper_flat_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.target ⟶ X),
        IsProper f ∧ Flat f ∧
        IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  letI : Algebra (ULift.{u} ℚ) R := ULift.algebra' ℚ R
  letI : IsScalarTower ℚ (ULift.{u} ℚ) R :=
    IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ULift.{u} ℚ) (A := R) fun r => rfl
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : IsProper Q.structureMap := Q.geometry.proper
  obtain ⟨T, hT, _, X, f, π, hs⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := ULift.{u} ℚ) Q.structureMap ∅
  letI : Algebra.FiniteType ℚ (ULift.{u} ℚ) :=
    Algebra.FiniteType.equiv inferInstance (ULift.algEquiv : ULift.{u} ℚ ≃ₐ[ℚ] ℚ).symm
  letI : Algebra.FiniteType (ULift.{u} ℚ) T := T.fg_iff_finiteType.mp hT
  have hTQ : (T.restrictScalars ℚ).FG := by
    apply (T.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := ULift.{u} ℚ) (A := T)
      inferInstance inferInstance
  exact ⟨T.restrictScalars ℚ, hTQ, X, f, π, hs⟩

/-- Smoothness can also be retained after enlarging the finite rational stage.
The Cartesian comparison remains the map induced by the same structural maps. -/
theorem rational_smooth_proper_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (π : Q.target ⟶ X),
        IsProper f ∧ Smooth f ∧
        IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))) := by
  obtain ⟨T, hT, X, f, π, hp, hf, hπ⟩ := rational_proper_flat_descent R Q
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℚ T
  letI := hp
  letI := hf
  letI : Smooth Q.structureMap := Q.geometry.smooth
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  haveI : Smooth (pullback.snd f b) := by
    rw [← hπ.isoPullback_inv_snd]
    infer_instance
  obtain ⟨U, hU, _, hsm⟩ :=
    AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd f (A := R) ∅
  let v : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T U))
  let c : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  have hcv : c ≫ v = b := by
    dsimp [c, v, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let π' : Q.target ⟶ pullback f v :=
    pullback.lift π (Q.structureMap ≫ c) (by rw [Category.assoc, hcv, hπ.w])
  have hπ' : IsPullback π' Q.structureMap (pullback.snd f v) c := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f v) (h₂₂ := v) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f v)
    rw [pullback.lift_fst, hcv]
    exact hπ
  letI : Algebra.FiniteType T U := U.fg_iff_finiteType.mp hU
  have hUQ : (U.restrictScalars ℚ).FG := by
    apply (U.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := T) (A := U) inferInstance inferInstance
  exact ⟨U.restrictScalars ℚ, hUQ, pullback f v, pullback.snd f v, π',
    inferInstance, hsm, hπ'⟩

private theorem mul_val_congr
    {S : Type u} [CommRing S] {X Z : Scheme.{u}} {f : X ⟶ Base S}
    (L : RelativeGroupLaw S f) {t₁ t₂ : Z ⟶ Base S} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f)
    (hx : x₁.val = x₂.val) (hy : y₁.val = y₂.val) :
    (L.mul t₁ x₁ y₁).val = (L.mul t₂ x₂ y₂).val := by
  subst t₂
  cases Subtype.ext hx
  cases Subtype.ext hy
  rfl

/-- The actual group law descends on a smooth proper rational finite-type model,
with multiplication preserved on every scheme-valued point. -/
theorem rational_smooth_proper_group_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (L : RelativeGroupLaw T f)
        (π : Q.target ⟶ X)
        (hπ : IsPullback π Q.structureMap f
          (Spec.map (CommRingCat.ofHom (algebraMap T R)))),
        IsProper f ∧ Smooth f ∧
        ∀ (Z : Scheme.{u}) (t : Z ⟶ Base R) (x y : SchemeHomOver t Q.structureMap),
          (Q.law.mul t x y).val ≫ π =
            (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap T R)))
              ⟨x.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, x.property]⟩
              ⟨y.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, y.property]⟩).val := by
  obtain ⟨T, hT, X, f, π, hp, hs, hπ⟩ := rational_smooth_proper_descent R Q
  letI := hp
  letI := hs
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  let e : Q.target ≅ pullback f b := hπ.isoPullback
  have he : e.hom ≫ pullback.snd f b = Q.structureMap := hπ.isoPullback_hom_snd
  obtain ⟨LR, hLR, _⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso e he Q.law
  obtain ⟨U, hU, _, LU, c, hciso, hc, _, hmul, _⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      f LR ∅
  letI := hciso
  let v : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T U))
  let a : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  let fU := pullback.snd f v
  let π' : Q.target ⟶ pullback f v := (e.hom ≫ c) ≫ pullback.fst fU a
  have hc' : (e.hom ≫ c) ≫ pullback.snd fU a = Q.structureMap := by
    rw [Category.assoc, hc, he]
  have hpb : IsPullback (e.hom ≫ c) Q.structureMap (pullback.snd fU a) (𝟙 (Base R)) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hc'⟩
  have hπ' : IsPullback π' Q.structureMap fU a := by
    simpa only [Category.id_comp] using hpb.paste_horiz (IsPullback.of_hasPullback fU a)
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : Algebra.FiniteType T U := U.fg_iff_finiteType.mp hU
  have hUQ : (U.restrictScalars ℚ).FG := by
    apply (U.restrictScalars ℚ).fg_iff_finiteType.mpr
    exact Algebra.FiniteType.trans (R := ℚ) (S := T) (A := U) inferInstance inferInstance
  refine ⟨U.restrictScalars ℚ, hUQ, pullback f v, fU, LU, π', hπ', inferInstance,
    inferInstance, ?_⟩
  intro Z t x y
  let xe : SchemeHomOver t (pullback.snd f b) :=
    ⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩
  let ye : SchemeHomOver t (pullback.snd f b) :=
    ⟨y.val ≫ e.hom, by rw [Category.assoc, he, y.property]⟩
  have h1 : (LR.mul t xe ye).val = (Q.law.mul t x y).val ≫ e.hom := hLR t x y
  have h2 := congrArg (fun z => z ≫ pullback.fst fU a) (hmul t xe ye)
  rw [h1] at h2
  simp only [fU, a, v, RelativeGroupLaw.baseChange_mul,
    RelativeGroupLaw.baseChangePointOfBase_coe, RelativeGroupLaw.baseChangePointToBase,
    pullback.lift_fst] at h2
  refine (show (Q.law.mul t x y).val ≫ π' = _ from by
    simpa only [π', fU, a, v, Category.assoc] using h2).trans ?_
  apply mul_val_congr LU
  · rfl
  · simp only [xe, π', fU, a, v, Category.assoc]
  · simp only [ye, π', fU, a, v, Category.assoc]

/-- Relative smooth dimension is unique at an actual point, including over
nonreduced and disconnected affine bases. -/
theorem smooth_dimension_unique
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
    (n m : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f]
    (x : X) : n = m := by
  let α : R →+* X.presheaf.stalk x :=
    (Scheme.Spec.preimage (X.fromSpecStalk x ≫ f)).unop.hom
  letI : Algebra R (X.presheaf.stalk x) := α.toAlgebra
  have hα : X.fromSpecStalk x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk x))) := by
    exact (Scheme.Spec.map_preimage (X.fromSpecStalk x ≫ f)).symm
  obtain ⟨bn⟩ := SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    f n x hα
  obtain ⟨bm⟩ := SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    f m x hα
  simpa using Fintype.card_congr (bn.indexEquiv bm)

/-- Smooth relative dimension descends across a Cartesian comparison with dense
image. The argument compares stalk differential bases on nonempty open sets. -/
theorem smooth_dimension_of_dense_comparison
    {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (f : X ⟶ Base R) (g : Y ⟶ Base S)
    (π : Y ⟶ X) (b : Base S ⟶ Base R) (sq : IsPullback π g f b)
    [Smooth f] (n : ℕ) [SmoothOfRelativeDimension n g]
    (hdense : DenseRange π) : SmoothOfRelativeDimension n f := by
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    intro x
    obtain ⟨V, d, hx, hd⟩ := Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp f x
    letI := hd
    let U := π ⁻¹ᵁ V
    have sqV : IsPullback (π ∣_ V) (U.ι ≫ g) (V.ι ≫ f) b :=
      (isPullback_morphismRestrict π V).paste_vert sq
    letI := smoothOfRelativeDimension_isStableUnderBaseChange d
    haveI : SmoothOfRelativeDimension d (U.ι ≫ g) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sqV hd
    haveI : SmoothOfRelativeDimension n (U.ι ≫ g) :=
      IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension n) inferInstance U.ι
    obtain ⟨y, hy⟩ := hdense.exists_mem_open V.isOpen ⟨x, hx⟩
    have hdn : d = n := smooth_dimension_unique (U.ι ≫ g) d n ⟨y, hy⟩
    exact ⟨V, hx, hdn ▸ hd⟩
  choose V hx hV using hlocal
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) V ?_ hV
  apply le_antisymm le_top
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- Flat openness makes the comparison dense when the scalar map is injective.
No reducedness assumption is used. -/
theorem dense_comparison_of_injective
    {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (f : X ⟶ Base R) (g : Y ⟶ Base S)
    (π : Y ⟶ X) (α : R →+* S)
    (sq : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    [Smooth f] (hα : Function.Injective α) : DenseRange π := by
  let b := Spec.map (CommRingCat.ofHom α)
  have hb : DenseRange b := by
    change DenseRange (PrimeSpectrum.comap α)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot α).mp hα]
    exact bot_le
  have hpre : Dense (f ⁻¹' Set.range b) := hb.preimage f.isOpenMap
  rw [← Scheme.Pullback.range_fst f b] at hpre
  apply hpre.mono
  rintro z ⟨w, rfl⟩
  refine ⟨sq.isoPullback.inv w, ?_⟩
  exact congrArg (fun h => h w) sq.isoPullback_inv_fst

/-- Every smooth finite-stage group model constructed above has the original
relative dimension, since subalgebra inclusions induce dense comparisons. -/
theorem dimension_one_of_subalgebra_model
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R)
    (T : Subalgebra ℚ R) {X : Scheme.{u}} (f : X ⟶ Base T)
    (π : Q.target ⟶ X)
    (sq : IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))))
    [Smooth f] : SmoothOfRelativeDimension 1 f := by
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.dimension
  exact smooth_dimension_of_dense_comparison f Q.structureMap π _ sq 1
    (dense_comparison_of_injective f Q.structureMap π (algebraMap T R) sq Subtype.val_injective)

/-- The directed system includes every rational element, with injective
transition maps. Its definition does not require a nonzero base ring. -/
abbrev RationalStage (R : Type u) [CommRing R] [Algebra ℚ R] :=
  {T : Subalgebra ℚ R // T.FG}

instance rationalStage_nonempty (R : Type u) [CommRing R] [Algebra ℚ R] :
    Nonempty (RationalStage R) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance rationalStage_directed (R : Type u) [CommRing R] [Algebra ℚ R] :
    IsDirected (RationalStage R) (· ≤ ·) where
  directed i j := ⟨⟨i.val ⊔ j.val, i.property.sup j.property⟩, (show i.val ≤ i.val ⊔ j.val from le_sup_left),
      (show j.val ≤ i.val ⊔ j.val from le_sup_right)⟩

def stageTransition {R : Type u} [CommRing R] [Algebra ℚ R]
    (i j : RationalStage R) (h : i ≤ j) : i.val →+* j.val :=
  (Subalgebra.inclusion h).toRingHom

instance stageTransition_system (R : Type u) [CommRing R] [Algebra ℚ R] :
    DirectedSystem (fun i : RationalStage R => i.val)
      (fun i j h => ⇑(stageTransition i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The ambient rational algebra is the direct limit of its finite subalgebras. -/
theorem rationalStage_directLimit (R : Type u) [CommRing R] [Algebra ℚ R] :
    IsDirectLimit (fun i j h => ⇑(stageTransition (R := R) i j h))
      (fun i => ⇑i.val.val.toRingHom) where
  surj r := by
    classical
    let i : RationalStage R := ⟨Algebra.adjoin ℚ ({r} : Set R),
      by simpa using (Subalgebra.fg_adjoin_finset (R := ℚ) {r})⟩
    exact ⟨i, ⟨r, Algebra.subset_adjoin (Set.mem_singleton r)⟩, rfl⟩
  inj i j x y h := by
    refine ⟨⟨i.val ⊔ j.val, i.property.sup j.property⟩, (show i.val ≤ i.val ⊔ j.val from le_sup_left),
      (show j.val ≤ i.val ⊔ j.val from le_sup_right), ?_⟩
    exact Subtype.ext h
  compatibility _ _ _ _ := rfl

/-- An isomorphism of actual invertible sheaves over a rational finite stage
which exists over the ambient algebra already exists at a larger finite stage. -/
theorem invertible_iso_finite_stage
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (T : Subalgebra ℚ R) (hT : T.FG)
    (M N : (Base T).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N)
    (he : Nonempty
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap T R)))).obj M ≅
       (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap T R)))).obj N)) :
    ∃ (U : Subalgebra ℚ R) (_hU : U.FG) (hTU : T ≤ U), Nonempty
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion hTU).toRingHom))).obj M ≅
       (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion hTU).toRingHom))).obj N) := by
  let i : RationalStage R := ⟨T, hT⟩
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  let p := pullback.fst (𝟙 (Base T)) b
  let q := pullback.snd (𝟙 (Base T)) b
  have hp : p = q ≫ b := by simpa [p, q] using (pullback.condition (f := 𝟙 (Base T)) (g := b))
  obtain ⟨e⟩ := he
  have hep : Nonempty ((Scheme.Modules.pullback p).obj M ≅
      (Scheme.Modules.pullback p).obj N) := by
    exact ⟨ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso hp M ≪≫
      ((Scheme.Modules.pullbackComp q b).app M).symm ≪≫
      (Scheme.Modules.pullback q).mapIso e ≪≫
      (Scheme.Modules.pullbackComp q b).app N ≪≫
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso hp N).symm⟩
  obtain ⟨j, hij, ⟨ej⟩⟩ :=
    Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
      (stageTransition (R := R)) (fun i => i.val.val.toRingHom)
      (rationalStage_directLimit R) i (𝟙 (Base T)) M N hM hN hep
  let c : Base j.val ⟶ Base T := Spec.map (CommRingCat.ofHom (stageTransition i j hij))
  let s : Base j.val ⟶ pullback (𝟙 (Base T)) c :=
    pullback.lift c (𝟙 (Base j.val)) (by simp)
  have hs : s ≫ pullback.fst (𝟙 (Base T)) c = c := pullback.lift_fst _ _ _
  refine ⟨j.val, j.property, hij, ⟨?_⟩⟩
  exact (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso hs M).symm ≪≫
    ((Scheme.Modules.pullbackComp s _).app M).symm ≪≫
    (Scheme.Modules.pullback s).mapIso ej ≪≫
    (Scheme.Modules.pullbackComp s _).app N ≪≫
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso hs N

/-- The actual identity cotangent is invertible on a smooth group curve of
relative dimension one. -/
theorem identity_cotangent_invertible
    {T : Type u} [CommRing T] {X : Scheme.{u}} (f : X ⟶ Base T)
    (L : RelativeGroupLaw T f) [SmoothOfRelativeDimension 1 f] :
    Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (L.one (𝟙 _)).val).obj f.kaehler) := by
  apply (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
  exact Scheme.Modules.IsLocallyFreeOfRank.pullback _
    (Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension f 1).1

/-- A frame of the original identity cotangent descends to the actual identity
cotangent of a larger finite stage. This uses the Cartesian differential map. -/
theorem hodge_frame_finite_stage
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R)
    (T : Subalgebra ℚ R) (hT : T.FG) {X : Scheme.{u}}
    (f : X ⟶ Base T) (L : RelativeGroupLaw T f) (π : Q.target ⟶ X)
    (sq : IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))))
    [SmoothOfRelativeDimension 1 f]
    (hz : Q.zero ≫ π = Spec.map (CommRingCat.ofHom (algebraMap T R)) ≫ (L.one (𝟙 _)).val) :
    ∃ (U : Subalgebra ℚ R) (_hU : U.FG) (hTU : T ≤ U),
      let c := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
      Nonempty ((SheafOfModules.unit (Base U).ringCatSheaf : (Base U).Modules) ≅
        (Scheme.Modules.pullback ((L.baseChange c).one (𝟙 _)).val).obj
          (pullback.snd f c).kaehler) := by
  let M : (Base T).Modules := SheafOfModules.unit (Base T).ringCatSheaf
  let N := (Scheme.Modules.pullback (L.one (𝟙 _)).val).obj f.kaehler
  let b : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  have he : Nonempty ((Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N) := by
    obtain ⟨e⟩ := Q.hodge
    exact ⟨Scheme.Modules.pullbackUnitIso b ≪≫ e ≪≫
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso
        f Q.structureMap π sq (L.one (𝟙 _)).val Q.zero hz).symm⟩
  obtain ⟨U, hU, hTU, ⟨eU⟩⟩ := invertible_iso_finite_stage R T hT M N
    (Scheme.Modules.isInvertible_unit _) (identity_cotangent_invertible f L) he
  letI : Algebra T U := (Subalgebra.inclusion hTU).toRingHom.toAlgebra
  let c : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
  let LU := L.baseChange c
  have hzc : (LU.one (𝟙 _)).val ≫ pullback.fst f c = c ≫ (L.one (𝟙 _)).val := by
    have h := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 (Base U)) ≫ c) c (by simp))
    simpa only [LU, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, GoodReductionJacobian.schemeHomOverComp_coe] using h.symm
  refine ⟨U, hU, hTU, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackUnitIso c).symm ≪≫ eU ≪≫
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso
      f (pullback.snd f c) (pullback.fst f c) (IsPullback.of_hasPullback f c)
      (L.one (𝟙 _)).val (LU.one (𝟙 _)).val hzc

/-- Multiplication compatibility survives passage to a larger scalar stage,
with equality tested on the two projections of the actual pullback. -/
theorem multiplication_lift
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {X Y : Scheme.{u}} {f : X ⟶ Base R} {g : Y ⟶ Base T}
    (K : RelativeGroupLaw R f) (L : RelativeGroupLaw T g)
    (a : Base R ⟶ Base T) (b : Base R ⟶ Base S) (c : Base S ⟶ Base T)
    (hbc : b ≫ c = a) (π : X ⟶ Y) (hw : π ≫ g = f ≫ a)
    (π' : X ⟶ pullback g c) (hfst : π' ≫ pullback.fst g c = π)
    (hsnd : π' ≫ pullback.snd g c = f ≫ b)
    (hmul : ∀ (Z : Scheme.{u}) (t : Z ⟶ Base R) (x y : SchemeHomOver t f),
      (K.mul t x y).val ≫ π =
        (L.mul (t ≫ a)
          ⟨x.val ≫ π, by rw [Category.assoc, hw, ← Category.assoc, x.property]⟩
          ⟨y.val ≫ π, by rw [Category.assoc, hw, ← Category.assoc, y.property]⟩).val)
    (Z : Scheme.{u}) (t : Z ⟶ Base R) (x y : SchemeHomOver t f)
    (x' y' : SchemeHomOver (t ≫ b) (pullback.snd g c))
    (hx : x'.val = x.val ≫ π') (hy : y'.val = y.val ≫ π') :
    ((L.baseChange c).mul (t ≫ b) x' y').val = (K.mul t x y).val ≫ π' := by
  apply pullback.hom_ext
  · simp only [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, Category.assoc, hfst]
    refine (mul_val_congr L (by rw [Category.assoc, hbc]) _ _ _ _ ?_ ?_).trans
      (hmul Z t x y).symm
    · simp only [RelativeGroupLaw.baseChangePointToBase_coe, hx, Category.assoc, hfst]
    · simp only [RelativeGroupLaw.baseChangePointToBase_coe, hy, Category.assoc, hfst]
  · simp only [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_snd]
    rw [Category.assoc, hsnd, ← Category.assoc, (K.mul t x y).property]

/-- Simultaneous finite-stage descent of the smooth proper group curve,
relative dimension, and actual Hodge frame. Connected fibres are the remaining
geometric assertion required to form the frozen `FramedCurve` structure. -/
theorem rational_framed_group_descent
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    ∃ (T : Subalgebra ℚ R), T.FG ∧
      ∃ (X : Scheme.{u}) (f : X ⟶ Base T) (L : RelativeGroupLaw T f)
        (π : Q.target ⟶ X),
        IsProper f ∧ SmoothOfRelativeDimension 1 f ∧
        IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom (algebraMap T R))) ∧
        Nonempty ((SheafOfModules.unit (Base T).ringCatSheaf : (Base T).Modules) ≅
          (Scheme.Modules.pullback (L.one (𝟙 _)).val).obj f.kaehler) ∧
        (Q.zero ≫ π = Spec.map (CommRingCat.ofHom (algebraMap T R)) ≫ (L.one (𝟙 _)).val) ∧
        (∀ (Z : Scheme.{u}) (t : Z ⟶ Base R) (x y : SchemeHomOver t Q.structureMap)
          (x' y' : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap T R))) f),
          x'.val = x.val ≫ π → y'.val = y.val ≫ π →
          (L.mul _ x' y').val = (Q.law.mul t x y).val ≫ π) := by
  obtain ⟨T, hT, X, f, L, π, sq, hp, hsm, hm⟩ := rational_smooth_proper_group_descent R Q
  letI := hp
  letI := hsm
  haveI : SmoothOfRelativeDimension 1 f := dimension_one_of_subalgebra_model R Q T f π sq
  have hz := origin_eq_of_mul_eq Q.law L _ π sq.w (fun t x y => hm _ t x y)
  obtain ⟨U, hU, hTU, hframe⟩ := hodge_frame_finite_stage R Q T hT f L π sq hz
  let c : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
  let b : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  let a : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  have hbc : b ≫ c = a := by
    dsimp [b, c, a]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let π' : Q.target ⟶ pullback f c :=
    pullback.lift π (Q.structureMap ≫ b) (by rw [Category.assoc, hbc, sq.w])
  have sq' : IsPullback π' Q.structureMap (pullback.snd f c) b := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f c) (h₂₂ := c) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f c)
    rw [pullback.lift_fst, hbc]
    exact sq
  have hm' := multiplication_lift Q.law L a b c hbc π sq.w π'
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hm
  have hz' : Q.zero ≫ π' = b ≫ ((L.baseChange c).one (𝟙 _)).val := by
    apply origin_eq_of_mul_eq Q.law (L.baseChange c) b π' sq'.w
    intro Z t x y
    exact (hm' Z t x y _ _ rfl rfl).symm
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨U, hU, pullback f c, pullback.snd f c, L.baseChange c, π',
    inferInstance, inferInstance, sq', hframe, hz', hm'⟩

/-- The finite list of coefficients of a unit-ideal relation forces a larger
rational stage to factor through an open subset of the original spectrum. -/
theorem finite_stage_factors_open
    (R : Type u) [CommRing R] [Algebra ℚ R]
    (T : Subalgebra ℚ R) (hT : T.FG)
    (V : Set (PrimeSpectrum T)) (hV : IsOpen V)
    (hR : ∀ p : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap T R) p ∈ V) :
    ∃ (U : Subalgebra ℚ R) (hTU : T ≤ U), U.FG ∧
      ∀ p : PrimeSpectrum U, PrimeSpectrum.comap (Subalgebra.inclusion hTU).toRingHom p ∈ V := by
  classical
  have hx : ∀ p : PrimeSpectrum R, ∃ t : T,
      (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum T)) ⊆ V ∧
      (t : R) ∉ p.asIdeal := by
    intro p
    obtain ⟨_, ⟨t, rfl⟩, hpt, htV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hR p) hV
    exact ⟨t, htV, hpt⟩
  choose t htV hpt using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : PrimeSpectrum R => (PrimeSpectrum.basicOpen (t p : R) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (t p : R)).isOpen)
    (fun p _ => Set.mem_iUnion_of_mem p (hpt p))
  have hspan : Ideal.span (Set.range fun i : ↥s => (t i : R)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmem := hs (Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum R))
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨i, his, him⟩ := hmem
    exact him (hle (Ideal.subset_span ⟨⟨i, his⟩, rfl⟩))
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (hspan.symm ▸ (Submodule.mem_top : (1 : R) ∈ ⊤))
  let U := T ⊔ Algebra.adjoin ℚ (Set.range a)
  have hTU : T ≤ U := le_sup_left
  have haU : ∀ i, a i ∈ U := fun i =>
    (show Algebra.adjoin ℚ (Set.range a) ≤ U from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_range_self i))
  have haFG : (Algebra.adjoin ℚ (Set.range a)).FG := by
    simpa using (Subalgebra.fg_adjoin_finset (R := ℚ) (Finset.univ.image a))
  have hU : U.FG := hT.sup haFG
  refine ⟨U, hTU, hU, ?_⟩
  intro p
  let j := (Subalgebra.inclusion hTU).toRingHom
  have hsum : ∑ i, (⟨a i, haU i⟩ : U) * j (t i) = 1 := by
    apply Subtype.ext
    change (↑(∑ i, (⟨a i, haU i⟩ : U) * j (t i)) : R) = 1
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
    exact ha
  have hi : ∃ i : ↥s, j (t i) ∉ p.asIdeal := by
    by_contra hh
    push Not at hh
    apply p.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hh i)
  obtain ⟨i, hi⟩ := hi
  exact htV i hi

/-- Connectedness of every fibre over a point in the image of the actual scalar
map follows by descent along the induced extension of residue fields. -/
theorem connected_fibre_at_scalar_image
    (R : Type u) [CommRing R] (Q : FramedCurve R)
    {T : Type u} [CommRing T] (α : T →+* R)
    {X : Scheme.{u}} (f : X ⟶ Base T) (π : Q.target ⟶ X)
    (sq : IsPullback π Q.structureMap f (Spec.map (CommRingCat.ofHom α)))
    (p : Base R) :
    GeometricallyConnected
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom α)) p)) := by
  haveI : GeometricallyIntegral Q.structureMap := Q.geometry.geometricallyIntegral_of_commRing
  haveI : GeometricallyConnected Q.structureMap :=
    GeometricallyIrreducible.geometricallyConnected Q.structureMap
  let b := Spec.map (CommRingCat.ofHom α)
  letI : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      @Surjective := GeometricallyConnected.descendsAlong_surjective
  have hb : Surjective (Spec.map (b.residueFieldMap p)) := by
    refine ⟨fun x => ⟨IsLocalRing.closedPoint _, ?_⟩⟩
    exact Subsingleton.elim _ _
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected)
    (Q := @Surjective) (isPullback_fiberToSpecResidueField_of_isPullback sq p).flip hb inferInstance

/- The following cochain comparison is proved using the accepted cover
 definitions already in ProperFormalFunctions. The argument follows affine
 section base change and naturality, as in the library cochain-descent proof;
 no conflicting cover definition is imported or redefined. -/
namespace CechDescent
open Opposite TopologicalSpace TensorProduct Scheme.TwoAffineOpenCover

section EqRes
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {ρ : Y ⟶ Spec (.of R)} (G : OModulePresheaf ρ)

def eqRes {U U' : Y.Opens} (h : U = U') : G.obj U' ≃ₗ[R] G.obj U :=
  LinearEquiv.ofLinearMap (G.res h.le) (G.res h.ge)
    (by rw [← G.res_comp h.le h.ge]; exact G.res_refl U)
    (by rw [← G.res_comp h.ge h.le]; exact G.res_refl U')

theorem eqRes_apply {U U' : Y.Opens} (h : U = U') (x : G.obj U') : eqRes G h x = G.res h.le x := rfl

theorem res_res_eq_res_res {U V V' W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ V') (h₄ : V' ≤ W) (x : G.obj W) :
    G.res h₁ (G.res h₂ x) = G.res h₃ (G.res h₄ x) := by
  rw [G.res_res, G.res_res]

end EqRes

section Affine
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (𝒰 : X.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated' [IsSeparated π] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter' [IsSeparated π] {i : ℕ} (s : 𝒰.Idx i) : IsAffineOpen (𝒰.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → 𝒰.ι), IsAffineOpen (⨅ j, 𝒰.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, 𝒰.U (t j)) = 𝒰.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact 𝒰.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), 𝒰.U (t j)) = 𝒰.U (t 0) ⊓ (⨅ j : Fin (m + 1), 𝒰.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated' π (𝒰.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

end Affine

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (M : X.Modules)
  (A : Type u) [CommRing A] [Algebra R A]

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U' ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U)
    (m : (OModulePresheaf.ofModules π M).obj U) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U'
        (M.presheaf.map (homOfLE h).op m)
      = ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map (homOfLE h').op
          (show (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
              ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj
              ((Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst π (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)) = homOfLE h' :=
    Subsingleton.elim _ _
  show (((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst π (specMap R A)).base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [IsSeparated π] (𝒰 : X.OrderedAffineCover)
  (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

omit [IsSeparated π] in

def unitAt {i : ℕ} (s : 𝒰.Idx i) :
    (OModulePresheaf.ofModules π M).obj (𝒰.inter s) →+
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res
      (𝒰.baseChange_inter_le π A s)).toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
      (𝒰.inter s)).hom

omit [IsSeparated π] in
theorem unitAt_apply {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 s m
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
            (𝒰.inter s)).hom m) :=
  rfl

include htriv in
theorem exists_eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    ∃ e : A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s),
      ∀ m, e ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m := by
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial π M htriv
    (𝒰.inter s) (isAffineOpen_inter' π 𝒰 s) A
  refine ⟨e.trans (eqRes (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)) (𝒰.baseChange_inter π A s)),
    fun m => ?_⟩
  exact congrArg ((OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res (𝒰.baseChange_inter_le π A s))
    (he m)

def eSimplex {i : ℕ} (s : 𝒰.Idx i) :
    A ⊗[R] (OModulePresheaf.ofModules π M).obj (𝒰.inter s) ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).obj ((𝒰.baseChange π A).inter s) :=
  (exists_eSimplex π M A 𝒰 htriv s).choose

theorem eSimplex_one_tmul {i : ℕ} (s : 𝒰.Idx i) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s ((1 : A) ⊗ₜ[R] m) = unitAt π M A 𝒰 s m :=
  (exists_eSimplex π M A 𝒰 htriv s).choose_spec m

theorem eSimplex_tmul {i : ℕ} (s : 𝒰.Idx i) (a : A) (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    eSimplex π M A 𝒰 htriv s (a ⊗ₜ[R] m) = a • unitAt π M A 𝒰 s m := by
  rw [tmul_eq_smul_one_tmul (R := R) A a m, map_smul, eSimplex_one_tmul]

def E (i : ℕ) :
    A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
      (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).cochain (𝒰.baseChange π A) i :=
  (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))).trans
    (LinearEquiv.piCongrRight fun s : 𝒰.Idx i => eSimplex π M A 𝒰 htriv s)

theorem E_tmul (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i (a ⊗ₜ[R] c) s = a • unitAt π M A 𝒰 s (c s) := by
  change eSimplex π M A 𝒰 htriv s
      (TensorProduct.piRight R A A (fun s : 𝒰.Idx i => (OModulePresheaf.ofModules π M).obj (𝒰.inter s))
        (a ⊗ₜ[R] c) s) = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, eSimplex_tmul]

theorem E_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i) :
    E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c) s = unitAt π M A 𝒰 s (c s) := by
  rw [E_tmul, one_smul]

omit [IsSeparated π] in

theorem unitAt_res {i i' : ℕ} (s : 𝒰.Idx i) (t : 𝒰.Idx i') (h : 𝒰.inter t ≤ 𝒰.inter s)
    (hA : (𝒰.baseChange π A).inter t ≤ (𝒰.baseChange π A).inter s)
    (m : (OModulePresheaf.ofModules π M).obj (𝒰.inter s)) :
    unitAt π M A 𝒰 t ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res hA (unitAt π M A 𝒰 s m) := by
  rw [unitAt_apply, unitAt_apply, OModulePresheaf.res_res]
  have h' : (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter t ≤ (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒰.inter s :=
    Scheme.Hom.preimage_mono _ h
  have key := unit_res π M A h h' m

  have : (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
        (𝒰.inter t)).hom ((OModulePresheaf.ofModules π M).res h m)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).res h'
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst π (specMap R A))).unit.app M).app
              (𝒰.inter s)).hom m) := by
    exact key
  rw [this, OModulePresheaf.res_res]

theorem E_d_one_tmul (i : ℕ) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) :
    E π M A 𝒰 htriv (i + 1) ((1 : A) ⊗ₜ[R] (OModulePresheaf.ofModules π M).d 𝒰 i c)
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
          (E π M A 𝒰 htriv i ((1 : A) ⊗ₜ[R] c)) := by
  funext t
  rw [E_one_tmul, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, E_one_tmul]
  congr 1

  exact unitAt_res π M A 𝒰 (𝒰.face t j) t (𝒰.inter_le_inter_face t j)
    ((𝒰.baseChange π A).inter_le_inter_face t j) (c (𝒰.face t j))

theorem E_d (i : ℕ) :
    (E π M A 𝒰 htriv (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
      = (OModulePresheaf.ofModules (Limits.pullback.snd π (specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (specMap R A))).obj M)).d (𝒰.baseChange π A) i
        ∘ₗ (E π M A 𝒰 htriv i).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul]
    rw [tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a c, map_smul, map_smul, map_smul,
      E_d_one_tmul]

end Main


end CechDescent

/- Finite-module support and degree-zero sheaf gluing give the semicontinuity
 argument below. The source argument is adapted from the library semicontinuity
 proof, with the cochain comparison proved above against frozen cover definitions. -/
namespace FibreSemicontinuity
open Opposite TopologicalSpace TensorProduct Scheme.TwoAffineOpenCover

section FibreDim

variable {R : Type u} [CommRing R]

noncomputable abbrev fibreDim (Q : Type u) [AddCommGroup Q] [Module R Q]
    (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] Q)

variable {Q : Type u} [AddCommGroup Q] [Module R Q]

noncomputable def baseChangeCokerEquiv {P : Type u} [AddCommGroup P] [Module R P]
    (φ : P →ₗ[R] Q) (A : Type u) [CommRing A] [Algebra R A] :
    ((A ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange A)) ≃ₗ[A]
      A ⊗[R] (Q ⧸ LinearMap.range φ) := by
  have hex : Function.Exact φ (LinearMap.range φ).mkQ := LinearMap.exact_map_mkQ_range φ
  have hsurj : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hexA : Function.Exact (φ.baseChange A) ((LinearMap.range φ).mkQ.baseChange A) := by
    have h := lTensor_exact A hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  exact hexA.linearEquivOfSurjective (LinearMap.baseChange_surjective A hsurj)

theorem fibreDim_le_card {ι : Type u} [Fintype ι] (φ : (ι → R) →ₗ[R] Q) (𝔮 : PrimeSpectrum R)
    (h : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] (Q ⧸ LinearMap.range φ))) :
    fibreDim Q 𝔮 ≤ Fintype.card ι := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => 𝔮.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔮.asIdeal.zero_mem))⟩⟩
  set K := 𝔮.asIdeal.ResidueField
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    exact (baseChangeCokerEquiv φ K).toEquiv.subsingleton
  have hsurj : Function.Surjective (φ.baseChange K) := LinearMap.range_eq_top.mp hrange
  calc fibreDim Q 𝔮 ≤ Module.finrank K (K ⊗[R] (ι → R)) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Fintype.card ι := by
        rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]

theorem exists_family_card_eq (𝔭 : PrimeSpectrum R) [Module.Finite R Q] :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → Q),
      Fintype.card ι = fibreDim Q 𝔭 ∧
        Subsingleton (𝔭.asIdeal.ResidueField ⊗[R]
          (Q ⧸ LinearMap.range (Fintype.linearCombination R q))) := by
  set K := 𝔭.asIdeal.ResidueField

  have hspan : Submodule.span K (Set.range (TensorProduct.mk R K Q 1)) = ⊤ := by
    have h := (Submodule.baseChange_eq_span (p := (⊤ : Submodule R Q)) (A := K)).symm.trans
      (Submodule.baseChange_top (R := R) (M := Q) (A := K))
    rwa [Submodule.map_coe, Submodule.top_coe, Set.image_univ] at h
  obtain ⟨ι, a, -, hspan', hli⟩ := exists_linearIndependent' (K := K) (TensorProduct.mk R K Q 1)
  rw [hspan] at hspan'
  let b : Module.Basis ι K (K ⊗[R] Q) := Module.Basis.mk hli hspan'.ge
  haveI : IsNoetherian K (K ⊗[R] Q) := IsNoetherian.iff_fg.2 inferInstance
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  refine ⟨ι, inferInstance, a, (Module.finrank_eq_card_basis b).symm, ?_⟩
  classical
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R a
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨1 ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, Module.Basis.coe_mk]
    change (1 : K) ⊗ₜ[R] φ (Pi.single i 1) = (1 : K) ⊗ₜ[R] a i
    rw [Fintype.linearCombination_apply_single, one_smul]
  haveI : Subsingleton ((K ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange K)) :=
    Submodule.Quotient.subsingleton_iff.mpr hrange
  exact (baseChangeCokerEquiv φ K).symm.toEquiv.subsingleton

theorem isClosed_setOf_le_fibreDim [Module.Finite R Q] (m : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭} := by
  rw [← isOpen_compl_iff]
  have hset : {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭}ᶜ = {𝔭 | fibreDim Q 𝔭 < m} := by
    ext 𝔭; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hset, isOpen_iff_forall_mem_open]
  intro 𝔭 h𝔭
  obtain ⟨ι, _, q, hcard, hsub⟩ := exists_family_card_eq (Q := Q) 𝔭
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R q
  let Q' := Q ⧸ LinearMap.range φ
  refine ⟨(Module.support R Q')ᶜ, ?_, Module.isClosed_support.isOpen_compl, ?_⟩
  · intro 𝔮 h𝔮
    have h𝔮' : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] Q') := by
      rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
        not_nontrivial_iff_subsingleton] at h𝔮
      exact h𝔮
    calc fibreDim Q 𝔮 ≤ Fintype.card ι := fibreDim_le_card φ 𝔮 h𝔮'
      _ = fibreDim Q 𝔭 := hcard
      _ < m := h𝔭
  · rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    exact hsub

end FibreDim

section TwoTerm

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

theorem fibreH0_add_finrank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + Module.finrank R G.C1 =
      Module.finrank R G.C0 + fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => 𝔭.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔭.asIdeal.zero_mem))⟩⟩
  set K := 𝔭.asIdeal.ResidueField
  set dK := G.d.baseChange K
  have h1 : Module.finrank K (LinearMap.range dK) + Module.finrank K (LinearMap.ker dK) =
      Module.finrank K (K ⊗[R] G.C0) := LinearMap.finrank_range_add_finrank_ker dK
  have h2 : Module.finrank K (K ⊗[R] G.C0) = Module.finrank R G.C0 := Module.finrank_baseChange
  have h3 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) +
      Module.finrank K (LinearMap.range dK) = Module.finrank K (K ⊗[R] G.C1) :=
    Submodule.finrank_quotient_add_finrank _
  have h4 : Module.finrank K (K ⊗[R] G.C1) = Module.finrank R G.C1 := Module.finrank_baseChange
  have h5 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) =
      fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := (baseChangeCokerEquiv G.d K).finrank_eq
  have h0 : G.fibreH0 𝔭 = Module.finrank K (LinearMap.ker dK) := rfl
  omega

theorem isClosed_setOf_le_fibreH0 (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} := by
  have hset : {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} =
      {𝔭 | n + Module.finrank R G.C1 - Module.finrank R G.C0 ≤
        fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭} := by
    ext 𝔭
    simp only [Set.mem_ofPred_eq]
    have := fibreH0_add_finrank G 𝔭
    omega
  rw [hset]
  exact isClosed_setOf_le_fibreDim _

end TwoTerm

section Cover

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def H0Equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] Γ(M, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  (LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩).symm

end H0


theorem sections_semicontinuity
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤)} := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰

  have key : ∀ 𝔭 : PrimeSpectrum R,
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤))
        = G.fibreH0 𝔭 := by
    intro 𝔭
    let K := 𝔭.asIdeal.ResidueField
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj M) ⊤
    let e0 := CechDescent.E f M K 𝒰 htriv 0
    let e1' := CechDescent.E f M K 𝒰 htriv 1
    have hker : (LinearMap.ker ((OModulePresheaf.ofModules p₂
        ((Scheme.Modules.pullback p₁).obj M)).d (𝒰.baseChange f K) 0)).comap e0.toLinearMap =
        LinearMap.ker (((OModulePresheaf.ofModules f M).d 𝒰 0).baseChange K) := by
      ext z
      simp only [Submodule.mem_comap, LinearMap.mem_ker]
      have hz := LinearMap.congr_fun (CechDescent.E_d f M K 𝒰 htriv 0) z
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at hz
      have hz' : e1' ((((OModulePresheaf.ofModules f M).d 𝒰 0).baseChange K) z) =
          ((OModulePresheaf.ofModules p₂ ((Scheme.Modules.pullback p₁).obj M)).d
            (𝒰.baseChange f K) 0) (e0 z) := hz
      change ((OModulePresheaf.ofModules p₂ ((Scheme.Modules.pullback p₁).obj M)).d
        (𝒰.baseChange f K) 0) (e0 z) = 0 ↔ _
      rw [← hz']
      exact e1'.map_eq_zero_iff
    let e1 := (LinearEquiv.ofEq _ _ hker.symm).trans (e0.ofSubmodule' _)
    let e2 := H0Equiv p₂ ((Scheme.Modules.pullback p₁).obj M) (𝒰.baseChange f K)
    let e3 := LinearEquiv.ofBijective
      (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm K) (hbij K)
    exact (e2.symm.trans (e1.symm.trans e3.symm)).finrank_eq
  have hset : {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤)}
      = {𝔭 | n ≤ G.fibreH0 𝔭} := by
    ext 𝔭
    simp only [Set.mem_ofPred_eq]
    rw [← key 𝔭]
  rw [hset]
  exact isClosed_setOf_le_fibreH0 G n


end FibreSemicontinuity

/- Openness is deduced from the actual dimension of global functions on
 smooth proper fibres. This adapts the library argument to the freshly checked
 section semicontinuity theorem in this module. -/
namespace GoodFibreLocus
open Opposite TopologicalSpace

section aux

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) (𝔭 : ↥(Spec (CommRingCat.of S)))

theorem geometricallyIrreducible_fiber_iff :
    GeometricallyIrreducible (f.fiberToSpecResidueField 𝔭) ↔
      GeometricallyIrreducible (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) := by
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of S) 𝔭
  let y : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S 𝔭.asIdeal.ResidueField))
  let y' := (Spec (CommRingCat.of S)).fromSpecResidueField 𝔭
  have hy' : Spec.map e.inv ≫ y = y' := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _
  have hy : Spec.map e.hom ≫ y' = y := by
    rw [← hy', ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  constructor
  · intro h

    have houter : IsPullback (pullback.fst f y) (pullback.snd f y) f (Spec.map e.hom ≫ y') := by
      rw [hy]; exact IsPullback.of_hasPullback f y
    let t := pullback.lift (f := f) (g := y') (pullback.fst f y) (pullback.snd f y ≫ Spec.map e.hom)
      (by rw [houter.w, Category.assoc])
    have hsq : IsPullback t (pullback.snd f y) (f.fiberToSpecResidueField 𝔭) (Spec.map e.hom) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact houter) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f y')
    exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hsq h
  · intro h
    have houter : IsPullback (pullback.fst f y') (pullback.snd f y') f (Spec.map e.inv ≫ y) := by
      rw [hy']; exact IsPullback.of_hasPullback f y'
    let t := pullback.lift (f := f) (g := y) (pullback.fst f y') (pullback.snd f y' ≫ Spec.map e.inv)
      (by rw [houter.w, Category.assoc])
    have hsq : IsPullback t (pullback.snd f y') (pullback.snd f y) (Spec.map e.inv) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact houter) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f y)
    exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hsq h

theorem specMap_residueField_base (p : ↥(Spec (CommRingCat.of 𝔭.asIdeal.ResidueField))) :
    (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  show (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap S 𝔭.asIdeal.ResidueField)).hom p).asIdeal = 𝔭.asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
  exact Ideal.ker_algebraMap_residueField _

theorem nonempty_pullback_iff :
    Nonempty ↥(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ↔ 𝔭 ∈ Set.range f.base := by
  constructor
  · rintro ⟨z⟩
    refine ⟨(pullback.fst f _).base z, ?_⟩
    have hc := congrArg (fun φ => φ.base z) (pullback.condition (f := f) (g := Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
    rw [hc]; exact specMap_residueField_base 𝔭 _
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
      (g := Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField) z
      (IsLocalRing.closedPoint _) (by rw [hz, specMap_residueField_base])
    exact ⟨w⟩

end aux

theorem bijective_algebraMap_iff_finrank_le_one {κ A : Type u} [Field κ] [CommRing A] [Algebra κ A] [Nontrivial A]
    [Module.Finite κ A] : Function.Bijective (algebraMap κ A) ↔ Module.finrank κ A ≤ 1 := by
  constructor
  · intro hb
    have e : κ ≃ₗ[κ] A := LinearEquiv.ofBijective (Algebra.linearMap κ A) hb
    rw [← e.finrank_eq, Module.finrank_self]
  · intro h1
    have hpos : 0 < Module.finrank κ A := Module.finrank_pos
    have heq : Module.finrank κ κ = Module.finrank κ A := by rw [Module.finrank_self]; omega
    have hinj : Function.Injective (Algebra.linearMap κ A) := (algebraMap κ A).injective
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj⟩

theorem mem_iff_finrank_le_one
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f]
    (𝔭 : ↥(Spec (CommRingCat.of S))) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = 𝔭.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) ↔
      (𝔭 ∈ Set.range f.base ∧
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ⊤
        Module.finrank 𝔭.asIdeal.ResidueField
          Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField), ⊤) ≤ 1) := by
  let κ := 𝔭.asIdeal.ResidueField
  let y := Scheme.TwoAffineOpenCover.specMap S κ
  let fκ := pullback.snd f y
  letI instA := Scheme.TwoAffineOpenCover.algebraOfHom fκ ⊤
  rw [AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField f 𝔭,
    geometricallyIrreducible_fiber_iff f 𝔭]

  haveI : Module.Finite κ Γ(pullback f y, ⊤) := by
    have h0 := AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing fκ
    dsimp only [Scheme.Hom.appTop] at h0
    rw [Scheme.Hom.app_eq_appLE] at h0
    have h1 : ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ fκ.appLE ⊤ ⊤ le_top).hom.Finite := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Finite.comp h0
        (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of κ)).inv).2)
    exact h1

  have hN1 : ∀ [Nonempty ↥(pullback f y)], GeometricallyIrreducible fκ ↔ Function.Bijective (algebraMap κ Γ(pullback f y, ⊤)) := by
    intro _
    have h := AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth fκ
    dsimp only [Scheme.Hom.appTop] at h
    rw [Scheme.Hom.app_eq_appLE] at h
    exact h
  constructor
  · intro h
    haveI := h
    haveI : Nonempty ↥(pullback f y) := by
      obtain ⟨z, -⟩ := (inferInstance : Surjective fκ).1 (IsLocalRing.closedPoint κ)
      exact ⟨z⟩
    haveI : Nontrivial Γ(pullback f y, ⊤) :=
      ((pullback f y).presheaf.germ ⊤ (Classical.arbitrary _) trivial).hom.domain_nontrivial
    refine ⟨(nonempty_pullback_iff f 𝔭).mp inferInstance, ?_⟩
    exact (bijective_algebraMap_iff_finrank_le_one).mp (hN1.mp h)
  · rintro ⟨hmem, hle⟩
    haveI : Nonempty ↥(pullback f y) := (nonempty_pullback_iff f 𝔭).mpr hmem
    haveI : Nontrivial Γ(pullback f y, ⊤) :=
      ((pullback f y).presheaf.germ ⊤ (Classical.arbitrary _) trivial).hom.domain_nontrivial
    exact hN1.mpr ((bijective_algebraMap_iff_finrank_le_one).mpr hle)

theorem isClosed_setOf_two_le_finrank
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Flat f] :
    IsClosed {𝔭 : ↥(Spec (CommRingCat.of S)) |
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ⊤
      2 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField), ⊤)} := by
  have htriv : ∀ x : Z, ∃ (U : Z.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit Z.ringCatSheaf) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    fun x => ⟨⊤, trivial, AlgebraicGeometry.Scheme.Modules.nonempty_pullback_obj_unit_iso_unit (⊤ : Z.Opens).ι⟩
  have h := FibreSemicontinuity.sections_semicontinuity f
    (SheafOfModules.unit Z.ringCatSheaf) htriv 2
  have hB : ∀ 𝔭 : ↥(Spec (CommRingCat.of S)),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⊤
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField Γ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))).obj
          (SheafOfModules.unit Z.ringCatSheaf), ⊤)
        = Module.finrank 𝔭.asIdeal.ResidueField Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField), ⊤) := by
    intro 𝔭
    obtain ⟨-, h2⟩ := AlgebraicGeometry.Scheme.Modules.finrank_sections_pullback_obj_unit_eq f 𝔭.asIdeal.ResidueField
    exact h2
  have hset : {𝔭 : ↥(Spec (CommRingCat.of S)) |
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ⊤
      2 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField), ⊤)}
      = {𝔭 : ↥(Spec (CommRingCat.of S)) |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⊤
      2 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField))).obj
          (SheafOfModules.unit Z.ringCatSheaf), ⊤)} := by
    ext 𝔭; simp only [Set.mem_ofPred_eq]; rw [hB 𝔭]
  rw [hset]; exact h

theorem good_fibre_locus_open
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} := by
  have hEq : {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))}
      = Set.range f.base ∩ {𝔭 : ↥(Spec (CommRingCat.of S)) |
          letI := Scheme.TwoAffineOpenCover.algebraOfHom
            (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField)) ⊤
          2 ≤ Module.finrank 𝔭.asIdeal.ResidueField
            Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S 𝔭.asIdeal.ResidueField), ⊤)}ᶜ := by
    ext 𝔭
    rw [Set.mem_ofPred_eq, mem_iff_finrank_le_one f 𝔭, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
      Nat.lt_succ_iff]
  rw [hEq]
  exact f.isOpenMap.isOpen_range.inter (isClosed_setOf_two_le_finrank f).isOpen_compl


end GoodFibreLocus

/-- An already finite-type rational base is its own full framed approximation.
This is a boundary case, not the arbitrary-base target. -/
def selfApproximation
    (R : Type u) [CommRing R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (Q : FramedCurve R) : FramedApproximation R Q where
  ring := R
  finiteType := inferInstance
  scalar := AlgHom.id ℚ R
  model := Q
  comparison := 𝟙 Q.target
  cartesian := by
    simpa using IsPullback.id_horiz Q.structureMap
  zero_eq := by simp
  mul_eq := by
    intro T t x y x' y' hx hy
    have hm : ∀ (t₁ t₂ : T ⟶ Base R), t₁ = t₂ →
        ∀ (a b : SchemeHomOver t₁ Q.structureMap) (c d : SchemeHomOver t₂ Q.structureMap),
          a.val = c.val → b.val = d.val → (Q.law.mul t₁ a b).val = (Q.law.mul t₂ c d).val := by
      intro t₁ t₂ ht
      subst t₂
      intro a b c d ha hb
      cases Subtype.ext ha
      cases Subtype.ext hb
      rfl
    simpa using hm _ t (by simp) x' y' x y (by simpa using hx) (by simpa using hy)

#print axioms GoodFibreLocus.good_fibre_locus_open
#print axioms FibreSemicontinuity.sections_semicontinuity
#print axioms FibreSemicontinuity.isClosed_setOf_le_fibreH0
#print axioms FibreSemicontinuity.H0Equiv
#print axioms CechDescent.E_d
#print axioms finite_stage_factors_open
#print axioms connected_fibre_at_scalar_image
#print axioms multiplication_lift
#print axioms rational_framed_group_descent
#print axioms identity_cotangent_invertible
#print axioms hodge_frame_finite_stage
#print axioms rationalStage_directLimit
#print axioms invertible_iso_finite_stage
#print axioms origin_eq_of_mul_eq
#print axioms finite_presentation
#print axioms underlying_scheme_descent
#print axioms rational_scheme_descent
#print axioms selfApproximation
#print axioms rational_proper_flat_descent
#print axioms rational_smooth_proper_descent
#print axioms rational_smooth_proper_group_descent
#print axioms smooth_dimension_unique
#print axioms smooth_dimension_of_dense_comparison
#print axioms dense_comparison_of_injective
#print axioms dimension_one_of_subalgebra_model

end ArithmeticThetaLocalWeierstrassR0203.FiniteTypeApproximation

namespace ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open FiniteTypeApproximation

/-- Every actual framed smooth proper group curve over an arbitrary rational
algebra has a finite-type rational approximation, with a Cartesian comparison
preserving the origin and multiplication on all test schemes. -/
theorem framed_finite_type_approximation
    (R : Type u) [CommRing R] [Algebra ℚ R] (Q : FramedCurve R) :
    Nonempty (FramedApproximation R Q) := by
  obtain ⟨T, hT, X, f, L, π, hp, hd, sq, ⟨frame⟩, hz, hm⟩ :=
    rational_framed_group_descent R Q
  letI := hp
  letI := hd
  letI : Algebra.FiniteType ℚ T := T.fg_iff_finiteType.mp hT
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℚ T
  let V : Set (PrimeSpectrum T) := {p | GeometricallyIrreducible (f.fiberToSpecResidueField p)}
  have hV : IsOpen V := by
    have heq : V = {p : Base T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : T →+* k),
        RingHom.ker x = p.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} := by
      ext p
      exact (AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
        f p).symm
    rw [heq]
    exact GoodFibreLocus.good_fibre_locus_open f
  have hRV : ∀ p : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap T R) p ∈ V := by
    intro p
    haveI := connected_fibre_at_scalar_image R Q (algebraMap T R) f π sq p
    haveI := AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom (algebraMap T R))) p))
    exact inferInstanceAs (GeometricallyIrreducible
      (f.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom (algebraMap T R))) p)))
  obtain ⟨U, hTU, hU, hUV⟩ := finite_stage_factors_open R T hT V hV hRV
  letI : Algebra T U := (Subalgebra.inclusion hTU).toRingHom.toAlgebra
  let c : Base U ⟶ Base T := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hTU).toRingHom)
  let b : Base R ⟶ Base U := Spec.map (CommRingCat.ofHom (algebraMap U R))
  let a : Base R ⟶ Base T := Spec.map (CommRingCat.ofHom (algebraMap T R))
  have hbc : b ≫ c = a := by
    dsimp [b, c, a]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let fU := pullback.snd f c
  let LU := L.baseChange c
  haveI : GeometricallyIrreducible fU := by
    rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
    intro q
    haveI : GeometricallyIrreducible (f.fiberToSpecResidueField (c q)) := hUV q
    exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
      (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f c) q) inferInstance
  haveI : GeometricallyConnected fU := GeometricallyIrreducible.geometricallyConnected fU
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 fU := inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd f c))
  have hzU : (LU.one (𝟙 _)).val ≫ pullback.fst f c = c ≫ (L.one (𝟙 _)).val := by
    have h := congrArg Subtype.val (L.one_natural (𝟙 _) ((𝟙 (Base U)) ≫ c) c (by simp))
    simpa only [LU, RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, GoodReductionJacobian.schemeHomOverComp_coe] using h.symm
  have frameU : Nonempty ((SheafOfModules.unit (Base U).ringCatSheaf : (Base U).Modules) ≅
      (Scheme.Modules.pullback (LU.one (𝟙 _)).val).obj fU.kaehler) := by
    exact ⟨(Scheme.Modules.pullbackUnitIso c).symm ≪≫ (Scheme.Modules.pullback c).mapIso frame ≪≫
      ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso
        f fU (pullback.fst f c) (IsPullback.of_hasPullback f c)
        (L.one (𝟙 _)).val (LU.one (𝟙 _)).val hzU⟩
  let π' : Q.target ⟶ pullback f c :=
    pullback.lift π (Q.structureMap ≫ b) (by rw [Category.assoc, hbc, sq.w])
  have sq' : IsPullback π' Q.structureMap fU b := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f c) (h₂₂ := c) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f c)
    rw [pullback.lift_fst, hbc]
    exact sq
  have hm' := multiplication_lift Q.law L a b c hbc π sq.w π'
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (fun Z t x y => (hm Z t x y _ _ rfl rfl).symm)
  have hz' : Q.zero ≫ π' = b ≫ (LU.one (𝟙 _)).val := by
    apply origin_eq_of_mul_eq Q.law LU b π' sq'.w
    intro Z t x y
    exact (hm' Z t x y _ _ rfl rfl).symm
  let model : FramedCurve U := {
    target := pullback f c
    structureMap := fU
    law := LU
    geometry := {
      smooth := inferInstance
      proper := inferInstanceAs (IsProper (pullback.snd f c))
      connectedFibres := fun q => fU.isConnected_preimage_singleton q
      hasGroupLaw := ⟨LU⟩ }
    dimension := inferInstance
    hodge := frameU }
  exact ⟨{
    ring := U
    finiteType := U.fg_iff_finiteType.mp hU
    scalar := U.val
    model := model
    comparison := π'
    cartesian := sq'
    zero_eq := hz'
    mul_eq := hm' }⟩

#print axioms framed_finite_type_approximation
end ArithmeticThetaLocalWeierstrassR0203
