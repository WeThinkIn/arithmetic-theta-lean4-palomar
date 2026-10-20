module

public import GlobalMarkedIdealChartsR0133
public import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

@[expose] public section
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Affine charts of the actual marked complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCartierR0133
namespace AffineMarkedComplementR0133
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

lemma support_on_spec {S : Type u} [CommRing S]
    (I : (Spec (CommRingCat.of S)).IdealSheafData) :
    (I.support : Set (Spec (CommRingCat.of S))) =
      PrimeSpectrum.zeroLocus (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (I.ideal ⟨⊤, isAffineOpen_top _⟩)) := by
  ext x
  change x ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem
    (U := ⟨⊤, isAffineOpen_top _⟩) (by trivial)]
  rw [Spec_zeroLocus]
  let e := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
  change x ∈ PrimeSpectrum.zeroLocus ((I.ideal ⟨⊤, isAffineOpen_top _⟩).comap e.symm.toRingHom) ↔ _
  change x ∈ PrimeSpectrum.zeroLocus ((I.ideal ⟨⊤, isAffineOpen_top _⟩).comap e.symm.toRingHom) ↔
    x ∈ PrimeSpectrum.zeroLocus ((I.ideal ⟨⊤, isAffineOpen_top _⟩).map e.toRingHom)
  simp only [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv]
  rfl


/- The two-closed-subscheme argument is adapted from the local FLT library's
S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range.
Its public theorem is restricted to universe zero; the following version and
its quotient-ring helper preserve arbitrary universes required by this task. -/
namespace ClosedAffineCover
open CategoryTheory.Limits TopologicalSpace Opposite
lemma quotient_pair_glue
    (A : Type u) [CommRing A] (I₁ I₂ : Ideal A) (h : I₁ ⊓ I₂ = ⊥) :
    Function.Injective (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) ∧
    ∀ (x₁ : A ⧸ I₁) (x₂ : A ⧸ I₂),
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) x₁ = Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) x₂ →
      ∃ a : A, Ideal.Quotient.mk I₁ a = x₁ ∧ Ideal.Quotient.mk I₂ a = x₂ := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq, Ideal.Quotient.eq] at hab
    have : a - b ∈ I₁ ⊓ I₂ := ⟨hab.1, hab.2⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · intro x₁ x₂ hx
    obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨a₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, Submodule.mem_sup] at hx
    obtain ⟨i₁, hi₁, i₂, hi₂, hsum⟩ := hx
    refine ⟨a₁ - i₁, ?_, ?_⟩
    · rw [Ideal.Quotient.eq, sub_sub_cancel_left]; exact I₁.neg_mem hi₁
    · rw [Ideal.Quotient.eq, show a₁ - i₁ - a₂ = i₂ by rw [sub_right_comm, ← hsum]; ring]
      exact hi₂


theorem exists_basicOpen_of_isClosed_of_notMem {Z : Scheme.{u}} [IsAffine Z]
    (C : Set Z) (hC : IsClosed C) (z : Z) (hz : z ∉ C) :
    ∃ a : Γ(Z, ⊤), z ∈ Z.basicOpen a ∧ ∀ c ∈ C, c ∉ Z.basicOpen a := by
  obtain ⟨I, rfl⟩ := (Z.eq_zeroLocus_of_isClosed_of_isAffine C).mp hC
  rw [Scheme.mem_zeroLocus_iff] at hz
  push Not at hz
  obtain ⟨a, haI, hza⟩ := hz
  exact ⟨a, hza, fun c hc => (Scheme.mem_zeroLocus_iff _ _ _).mp hc a haI⟩

theorem exists_appTop_eq_zero_and_mem_basicOpen {W Z : Scheme.{u}} [IsAffine Z] (ι : W ⟶ Z)
    [IsClosedImmersion ι] (z : Z) (hz : z ∉ Set.range ι.base) :
    ∃ a : Γ(Z, ⊤), ι.appTop a = 0 ∧ z ∈ Z.basicOpen a := by
  have hz' : z ∉ (ι.ker.support : Set Z) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact hz
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top Z⟩) (Set.mem_univ z),
    Scheme.Hom.ker_apply, Scheme.mem_zeroLocus_iff] at hz'
  push Not at hz'
  obtain ⟨a, ha, hza⟩ := hz'
  exact ⟨a, (RingHom.mem_ker).mp ha, hza⟩

theorem exists_forall_mem_basicOpen_iff {Z : Scheme.{u}} [IsAffine Z] (p : PrimeSpectrum Γ(Z, ⊤)) :
    ∃ z : Z, ∀ a : Γ(Z, ⊤), z ∈ Z.basicOpen a ↔ a ∉ p.asIdeal := by
  refine ⟨Z.isoSpec.inv.base p, fun a => ?_⟩
  have hp : Z.toSpecΓ.base (Z.isoSpec.inv.base p) = p := by
    change (Z.isoSpec.inv ≫ Z.toSpecΓ).base p = p
    rw [Scheme.isoSpec_inv_toSpecΓ]
    rfl
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  change Z.toSpecΓ.base (Z.isoSpec.inv.base p) ∈ PrimeSpectrum.basicOpen a ↔ _
  rw [hp]
  exact PrimeSpectrum.mem_basicOpen a p

theorem eq_zero_of_app_eq_zero {X Z₁ Z₂ : Scheme.{u}} [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {V : X.Opens} (s : Γ(X, V))
    (h₁ : i₁.app V s = 0) (h₂ : i₂.app V s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx' : x ∈ Set.range i₁.base ∪ Set.range i₂.base := hcov.symm ▸ Set.mem_univ x
  rcases hx' with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · have hz : z ∈ i₁ ⁻¹ᵁ X.basicOpen s := hx
    rw [Scheme.preimage_basicOpen, h₁, Scheme.basicOpen_zero] at hz
    exact hz
  · have hz : z ∈ i₂ ⁻¹ᵁ X.basicOpen s := hx
    rw [Scheme.preimage_basicOpen, h₂, Scheme.basicOpen_zero] at hz
    exact hz

theorem ker_inf_ker_eq_bot {X Z₁ Z₂ : Scheme.{u}} [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) (V : X.Opens) :
    RingHom.ker (i₁.app V).hom ⊓ RingHom.ker (i₂.app V).hom = ⊥ := by
  rw [eq_bot_iff]
  rintro s ⟨h₁, h₂⟩
  exact eq_zero_of_app_eq_zero i₁ i₂ hcov s h₁ h₂

theorem exists_ringHom_comp_eq_of_surjective {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (π : A →+* B) (hπ : Function.Surjective π) (g : A →+* C) (hle : RingHom.ker π ≤ RingHom.ker g) :
    ∃ ρ : B →+* C, ρ.comp π = g := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) g fun a ha => hle ha).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [this, Ideal.Quotient.lift_mk]

theorem app_map_apply {X Z : Scheme.{u}} (i : Z ⟶ X) {U V : X.Opens} (ι : V ⟶ U) (s : Γ(X, U)) :
    i.app V (X.presheaf.map ι.op s) =
      Z.presheaf.map ((Opens.map i.base).map ι).op (i.app U s) := by
  rw [← CommRingCat.comp_apply, i.naturality]
  rfl

theorem appTop_SpecMap_comp_fromSpec {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    {R : CommRingCat.{u}} (φ : Γ(Z, V) ⟶ R) (a : Γ(Z, ⊤)) :
    (Spec.map φ ≫ hV.fromSpec).appTop a =
      (Scheme.ΓSpecIso R).inv (φ (Z.presheaf.map (homOfLE le_top).op a)) := by
  have nat := congrArg (fun ψ => ψ (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a))
    (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Spec.map φ).appTop (hV.fromSpec.app ⊤ a) = _
  rw [hV.fromSpec_app_of_le ⊤ le_top, CommRingCat.comp_apply, CommRingCat.comp_apply]
  congr 1

section Glue

variable {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
  (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)

omit [IsReduced X] in

theorem sub_mem_ker_sup_ker (U : X.Opens) (hU : IsAffineOpen U) (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂)
    (t₁ t₂ : Γ(X, U))
    (ht₁ : i₁.app U t₁ = Z₁.presheaf.map (homOfLE le_top).op a₁)
    (ht₂ : i₂.app U t₂ = Z₂.presheaf.map (homOfLE le_top).op a₂) :
    t₁ - t₂ ∈ RingHom.ker (i₁.app U).hom ⊔ RingHom.ker (i₂.app U).hom := by
  set J : Ideal Γ(X, U) := RingHom.ker (i₁.app U).hom ⊔ RingHom.ker (i₂.app U).hom with hJ
  obtain ⟨ρ₁, hρ₁⟩ := exists_ringHom_comp_eq_of_surjective (i₁.app U).hom (i₁.app_surjective U hU)
    (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact le_sup_left)
  obtain ⟨ρ₂, hρ₂⟩ := exists_ringHom_comp_eq_of_surjective (i₂.app U).hom (i₂.app_surjective U hU)
    (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact le_sup_right)
  have hV₁ : IsAffineOpen (i₁ ⁻¹ᵁ U) := hU.preimage i₁
  have hV₂ : IsAffineOpen (i₂ ⁻¹ᵁ U) := hU.preimage i₂
  let Q : CommRingCat.{u} := CommRingCat.of (Γ(X, U) ⧸ J)
  let g₁ : Spec Q ⟶ Z₁ := Spec.map (CommRingCat.ofHom ρ₁) ≫ hV₁.fromSpec
  let g₂ : Spec Q ⟶ Z₂ := Spec.map (CommRingCat.ofHom ρ₂) ≫ hV₂.fromSpec
  have hπρ : i₁.appLE U (i₁ ⁻¹ᵁ U) le_rfl ≫ CommRingCat.ofHom ρ₁ =
      i₂.appLE U (i₂ ⁻¹ᵁ U) le_rfl ≫ CommRingCat.ofHom ρ₂ := by
    ext x
    rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]
    change (ρ₁.comp (i₁.app U).hom) x = (ρ₂.comp (i₂.app U).hom) x
    rw [hρ₁, hρ₂]
  have comm : g₁ ≫ i₁ = g₂ ≫ i₂ := by
    simp only [g₁, g₂, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec i₁ hU hV₁ le_rfl,
      ← IsAffineOpen.SpecMap_appLE_fromSpec i₂ hU hV₂ le_rfl,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hπρ]
  have e : g₁.appTop a₁ = g₂.appTop a₂ := by
    have := congrArg (fun y => (pullback.lift g₁ g₂ comm).appTop y) h
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      pullback.lift_snd] at this
    exact this
  simp only [g₁, g₂, appTop_SpecMap_comp_fromSpec] at e
  have inj : Function.Injective (Scheme.ΓSpecIso Q).inv := (ConcreteCategory.bijective_of_isIso _).1
  have e' := inj e
  change ρ₁ (Z₁.presheaf.map (homOfLE le_top).op a₁) = ρ₂ (Z₂.presheaf.map (homOfLE le_top).op a₂) at e'
  rw [← ht₁, ← ht₂] at e'
  change (ρ₁.comp (i₁.app U).hom) t₁ = (ρ₂.comp (i₂.app U).hom) t₂ at e'
  rw [hρ₁, hρ₂] at e'
  exact Ideal.Quotient.eq.mp e'

include hcov in

theorem exists_section_local (U : X.Opens) (hU : IsAffineOpen U) (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂) :
    ∃ s : Γ(X, U), i₁.app U s = Z₁.presheaf.map (homOfLE le_top).op a₁ ∧
      i₂.app U s = Z₂.presheaf.map (homOfLE le_top).op a₂ := by
  obtain ⟨t₁, ht₁⟩ := i₁.app_surjective U hU (Z₁.presheaf.map (homOfLE le_top).op a₁)
  obtain ⟨t₂, ht₂⟩ := i₂.app_surjective U hU (Z₂.presheaf.map (homOfLE le_top).op a₂)
  have key := sub_mem_ker_sup_ker i₁ i₂ U hU a₁ a₂ h t₁ t₂ ht₁ ht₂
  obtain ⟨-, hF1⟩ := quotient_pair_glue
    Γ(X, U) (RingHom.ker (i₁.app U).hom) (RingHom.ker (i₂.app U).hom)
    (ker_inf_ker_eq_bot i₁ i₂ hcov U)
  obtain ⟨s, hs₁, hs₂⟩ := hF1 (Ideal.Quotient.mk _ t₁) (Ideal.Quotient.mk _ t₂) (by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq.mpr key)
  refine ⟨s, ?_, ?_⟩
  · rw [← ht₁]
    exact (RingHom.sub_mem_ker_iff _).mp (Ideal.Quotient.eq.mp hs₁)
  · rw [← ht₂]
    exact (RingHom.sub_mem_ker_iff _).mp (Ideal.Quotient.eq.mp hs₂)

include hcov in

theorem exists_section (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂) :
    ∃ s : Γ(X, ⊤), i₁.appTop s = a₁ ∧ i₂.appTop s = a₂ := by
  choose sf hsf₁ hsf₂ using fun U : X.affineOpens => exists_section_local i₁ i₂ hcov U.1 U.2 a₁ a₂ h
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf
      (fun U : X.affineOpens => (U : X.Opens)) sf := by
    intro U V
    change X.presheaf.map (Opens.infLELeft U.1 V.1).op (sf U) =
      X.presheaf.map (Opens.infLERight U.1 V.1).op (sf V)
    rw [← sub_eq_zero]
    apply eq_zero_of_app_eq_zero i₁ i₂ hcov
    · rw [map_sub, sub_eq_zero, app_map_apply, app_map_apply, hsf₁, hsf₁, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [map_sub, sub_eq_zero, app_map_apply, app_map_apply, hsf₂, hsf₂, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun U : X.affineOpens => (U : X.Opens)) ⊤
    (fun U => homOfLE le_top) (by rw [iSup_affineOpens_eq_top X]) sf hcompat
  have cover : ∀ {Z : Scheme.{u}} (i : Z ⟶ X),
      (⊤ : Z.Opens) ≤ ⨆ U : X.affineOpens, i ⁻¹ᵁ (U : X.Opens) := by
    intro Z i z _
    rw [Opens.mem_iSup]
    obtain ⟨U, hU, hzU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := i.base z) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, hzU⟩
  refine ⟨s, ?_, ?_⟩
  · refine Z₁.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => i₁ ⁻¹ᵁ (U : X.Opens)) ⊤
      (fun U => homOfLE le_top) (cover i₁) _ _ fun U => ?_
    change Z₁.presheaf.map (homOfLE le_top).op (i₁.app ⊤ s) =
      Z₁.presheaf.map (homOfLE le_top).op a₁
    rw [← hsf₁ U, ← hs U]
    change _ = i₁.app U.1 (X.presheaf.map (homOfLE le_top).op s)
    rw [app_map_apply]
    rfl
  · refine Z₂.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => i₂ ⁻¹ᵁ (U : X.Opens)) ⊤
      (fun U => homOfLE le_top) (cover i₂) _ _ fun U => ?_
    change Z₂.presheaf.map (homOfLE le_top).op (i₂.app ⊤ s) =
      Z₂.presheaf.map (homOfLE le_top).op a₂
    rw [← hsf₂ U, ← hs U]
    change _ = i₂.app U.1 (X.presheaf.map (homOfLE le_top).op s)
    rw [app_map_apply]
    rfl

include hcov in
theorem appTop_surjective_left [IsAffine Z₂] : Function.Surjective i₁.appTop := by
  intro a₁
  obtain ⟨a₂, ha₂⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.snd i₁ i₂)).2
    ((pullback.fst i₁ i₂).appTop a₁)
  obtain ⟨s, hs, -⟩ := exists_section i₁ i₂ hcov a₁ a₂ ha₂.symm
  exact ⟨s, hs⟩

include hcov in
theorem appTop_surjective_right [IsAffine Z₁] : Function.Surjective i₂.appTop := by
  intro a₂
  obtain ⟨a₁, ha₁⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst i₁ i₂)).2
    ((pullback.snd i₁ i₂).appTop a₂)
  obtain ⟨s, -, hs⟩ := exists_section i₁ i₂ hcov a₁ a₂ ha₁
  exact ⟨s, hs⟩

include hcov in
theorem exists_appTop_eq_zero_left [IsAffine Z₁] (w : Z₁)
    (hw : w ∉ i₁.base ⁻¹' Set.range i₂.base) :
    ∃ f : Γ(X, ⊤), i₂.appTop f = 0 ∧ w ∈ Z₁.basicOpen (i₁.appTop f) := by
  rw [← Scheme.Pullback.range_fst] at hw
  obtain ⟨a, ha, hwa⟩ := exists_appTop_eq_zero_and_mem_basicOpen (pullback.fst i₁ i₂) w hw
  obtain ⟨f, hf₁, hf₂⟩ := exists_section i₁ i₂ hcov a 0 (by rw [ha, map_zero])
  exact ⟨f, hf₂, hf₁ ▸ hwa⟩

include hcov in
theorem exists_appTop_eq_zero_right [IsAffine Z₂] (w : Z₂)
    (hw : w ∉ i₂.base ⁻¹' Set.range i₁.base) :
    ∃ f : Γ(X, ⊤), i₁.appTop f = 0 ∧ w ∈ Z₂.basicOpen (i₂.appTop f) := by
  rw [← Scheme.Pullback.range_snd] at hw
  obtain ⟨a, ha, hwa⟩ := exists_appTop_eq_zero_and_mem_basicOpen (pullback.snd i₁ i₂) w hw
  obtain ⟨f, hf₁, hf₂⟩ := exists_section i₁ i₂ hcov 0 a (by rw [ha, map_zero])
  exact ⟨f, hf₁, hf₂ ▸ hwa⟩

end Glue

theorem exists_basicOpen_oneSided {X Z Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) [IsAffine Z]
    (hcov : ∀ x : X, x ∈ Set.range i.base ∨ x ∈ Set.range i'.base)
    (hsurj : Function.Surjective i.appTop)
    (hker : ∀ w : Z', w ∉ i'.base ⁻¹' Set.range i.base →
      ∃ f : Γ(X, ⊤), i.appTop f = 0 ∧ w ∈ Z'.basicOpen (i'.appTop f))
    (x : X) (U : X.Opens) (hxU : x ∈ U) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ ∀ z : Z, i.base z ∈ X.basicOpen f → i.base z ∈ U := by
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨a, hza, hCa⟩ := exists_basicOpen_of_isClosed_of_notMem ((i ⁻¹ᵁ U : Set Z)ᶜ)
      (i ⁻¹ᵁ U).isOpen.isClosed_compl z (by simpa using hxU)
    obtain ⟨f, rfl⟩ := hsurj a
    refine ⟨f, ?_, fun z' hz' => ?_⟩
    · have : z ∈ i ⁻¹ᵁ X.basicOpen f := by rwa [Scheme.preimage_basicOpen]
      exact this
    · have hz'' : z' ∈ i ⁻¹ᵁ X.basicOpen f := hz'
      rw [Scheme.preimage_basicOpen] at hz''
      have := hCa z'
      simp only [Set.mem_compl_iff, SetLike.mem_coe] at this
      by_contra hU
      exact this hU hz''
  · obtain ⟨w, rfl⟩ := (hcov x).resolve_left hx
    obtain ⟨f, hf0, hwf⟩ := hker w hx
    refine ⟨f, ?_, fun z hz => ?_⟩
    · have : w ∈ i' ⁻¹ᵁ X.basicOpen f := by rwa [Scheme.preimage_basicOpen]
      exact this
    · have hz' : z ∈ i ⁻¹ᵁ X.basicOpen f := hz
      rw [Scheme.preimage_basicOpen] at hz'
      change z ∈ Z.basicOpen (i.appTop f) at hz'
      rw [hf0, Scheme.basicOpen_zero] at hz'
      exact hz'.elim

section Cover

variable {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsAffine Z₁] [IsAffine Z₂] [IsReduced X]
  (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)

include hcov in

theorem exists_mem_basicOpen_and_isAffineOpen (x : X) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  have hcov' : ∀ x : X, x ∈ Set.range i₁.base ∨ x ∈ Set.range i₂.base := fun x =>
    (Set.mem_union _ _ _).mp (hcov.symm ▸ Set.mem_univ x)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨f₁, hx₁, hU₁⟩ := exists_basicOpen_oneSided i₁ i₂ hcov'
    (appTop_surjective_left i₁ i₂ hcov) (exists_appTop_eq_zero_right i₁ i₂ hcov) x U hxU
  obtain ⟨f₂, hx₂, hU₂⟩ := exists_basicOpen_oneSided i₂ i₁ (fun x => (hcov' x).symm)
    (appTop_surjective_right i₁ i₂ hcov) (exists_appTop_eq_zero_left i₁ i₂ hcov) x U hxU
  refine ⟨f₁ * f₂, ?_, ?_⟩
  · rw [Scheme.basicOpen_mul]; exact ⟨hx₁, hx₂⟩
  · have hle : X.basicOpen (f₁ * f₂) ≤ U := by
      intro y hy
      rw [Scheme.basicOpen_mul] at hy
      rcases hcov' y with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact hU₁ z hy.1
      · exact hU₂ z hy.2
    have : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f₁ * f₂)) =
        X.basicOpen (f₁ * f₂) := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hle
    rw [← this]
    exact hU.basicOpen _

end Cover

theorem not_subset_of_ker_le {X Z : Scheme.{u}} [IsAffine Z] (i : Z ⟶ X)
    (hsurj : Function.Surjective i.appTop) (𝔪 : Ideal Γ(X, ⊤)) [h𝔪 : 𝔪.IsMaximal]
    (hker : RingHom.ker i.appTop.hom ≤ 𝔪) (S : Set Γ(X, ⊤))
    (hL : ∀ z : Z, ∃ f ∈ S, i.base z ∈ X.basicOpen f) : ¬ S ⊆ 𝔪 := by
  intro hS
  have hne : 𝔪.map i.appTop.hom ≠ ⊤ := by
    intro htop
    have := congr_arg (Ideal.comap i.appTop.hom) htop
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker] at this
    exact h𝔪.ne_top this
  obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨z, hz⟩ := exists_forall_mem_basicOpen_iff (Z := Z) ⟨𝔭, h𝔭.isPrime⟩
  obtain ⟨f, hfS, hzf⟩ := hL z
  have h1 : i.appTop f ∉ 𝔭 := by
    rw [← hz]
    have : z ∈ i ⁻¹ᵁ X.basicOpen f := hzf
    rwa [Scheme.preimage_basicOpen] at this
  exact h1 (hle (Ideal.mem_map_of_mem _ (hS hfS)))

lemma affine_of_two_closed
    (X Z₁ Z₂ : Scheme.{u}) (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (h₁ : IsClosedImmersion i₁) (h₂ : IsClosedImmersion i₂)
    (hZ₁ : IsAffine Z₁) (hZ₂ : IsAffine Z₂)
    (hred : IsReduced X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X := by
  let S : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  refine isAffine_of_isAffineOpen_basicOpen S ?_ (fun f hf => hf)
  by_contra hne
  obtain ⟨𝔪, h𝔪, hS𝔪⟩ := Ideal.exists_le_maximal _ hne
  have hS : S ⊆ 𝔪 := fun f hf => hS𝔪 (Ideal.subset_span hf)
  have hL := exists_mem_basicOpen_and_isAffineOpen i₁ i₂ hcov
  have hbot := ker_inf_ker_eq_bot i₁ i₂ hcov ⊤
  have hI : RingHom.ker (i₁.appTop).hom ≤ 𝔪 ∨ RingHom.ker (i₂.appTop).hom ≤ 𝔪 := by
    refine h𝔪.isPrime.mul_le.mp (le_trans Ideal.mul_le_inf ?_)
    change RingHom.ker (i₁.app ⊤).hom ⊓ RingHom.ker (i₂.app ⊤).hom ≤ 𝔪
    rw [hbot]; exact bot_le
  rcases hI with hI | hI
  · exact not_subset_of_ker_le i₁ (appTop_surjective_left i₁ i₂ hcov) 𝔪 hI S
      (fun z => let ⟨f, hf, hfa⟩ := hL (i₁.base z); ⟨f, hfa, hf⟩) hS
  · exact not_subset_of_ker_le i₂ (appTop_surjective_right i₁ i₂ hcov) 𝔪 hI S
      (fun z => let ⟨f, hf, hfa⟩ := hL (i₂.base z); ⟨f, hfa, hf⟩) hS

open AlgebraicGeometry.Scheme.IdealSheafData
noncomputable abbrev red (Z : Scheme.{u}) : Scheme.{u} := (vanishingIdeal (⊤ : Closeds ↥Z)).subscheme

noncomputable abbrev redι (Z : Scheme.{u}) : red Z ⟶ Z := (vanishingIdeal (⊤ : Closeds ↥Z)).subschemeι

theorem range_redι (Z : Scheme.{u}) : Set.range (redι Z).base = Set.univ := by
  rw [redι, range_subschemeι, coe_support_vanishingIdeal]; rfl

local instance (Z : Scheme.{u}) : IsReduced (red Z) := (isReduced_subscheme_vanishingIdeal_and_le_ker _).1

lemma affine_of_finite_closed_reduced : ∀ (n : ℕ) (X : Scheme.{u}) (Z : Fin n → Scheme.{u}) (i : ∀ j : Fin n, Z j ⟶ X),
    (∀ j, IsClosedImmersion (i j)) → (∀ j, IsAffine (Z j)) → IsReduced X →
    (⋃ j, Set.range (i j).base = Set.univ) → IsAffine X := by
  intro n
  induction n with
  | zero =>
    intro X Z i hci haff hred hcov
    have : IsEmpty ↥X := ⟨fun x => by
      have hx := hcov.symm ▸ Set.mem_univ x
      simp at hx⟩
    infer_instance
  | succ n ih =>
    intro X Z i hci haff hred hcov
    have := hred
    have := hci

    let W : Closeds ↥X := ⟨⋃ j : Fin n, Set.range (i j.castSucc).base,
      isClosed_iUnion_of_finite fun j => (i j.castSucc).isClosedEmbedding.isClosed_range⟩
    obtain ⟨hX'red, hker⟩ := isReduced_subscheme_vanishingIdeal_and_le_ker W
    have := hX'red
    have hrangeι : Set.range (vanishingIdeal W).subschemeι.base = (W : Set ↥X) := by
      rw [range_subschemeι, coe_support_vanishingIdeal]

    have hle : ∀ j : Fin n, (vanishingIdeal W).subschemeι.ker ≤ (redι (Z j.castSucc) ≫ i j.castSucc).ker := by
      intro j
      rw [ker_subschemeι]
      refine hker _ ?_
      rintro _ ⟨t, rfl⟩
      exact Set.mem_iUnion.mpr ⟨j, (redι (Z j.castSucc)).base t, rfl⟩
    let i' : ∀ j : Fin n, red (Z j.castSucc) ⟶ (vanishingIdeal W).subscheme := fun j =>
      IsClosedImmersion.lift (vanishingIdeal W).subschemeι (redι (Z j.castSucc) ≫ i j.castSucc) (hle j)
    have hi'fac : ∀ j, i' j ≫ (vanishingIdeal W).subschemeι = redι (Z j.castSucc) ≫ i j.castSucc := fun j =>
      IsClosedImmersion.lift_fac _ _ _
    have hci' : ∀ j, IsClosedImmersion (i' j) := by
      intro j
      have : IsClosedImmersion (i' j ≫ (vanishingIdeal W).subschemeι) := by rw [hi'fac]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion (i' j) (vanishingIdeal W).subschemeι
    have haff' : ∀ j : Fin n, IsAffine (red (Z j.castSucc)) := by
      intro j; have := haff j.castSucc
      exact isAffine_of_isAffineHom (redι (Z j.castSucc))
    have hcov' : ⋃ j, Set.range (i' j).base = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => Set.mem_iUnion.mpr ?_
      have hx : (vanishingIdeal W).subschemeι.base x' ∈ (W : Set ↥X) := hrangeι ▸ ⟨x', rfl⟩
      obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, rfl⟩ : y ∈ Set.range (redι (Z j.castSucc)).base := by rw [range_redι]; trivial
      refine ⟨j, t, (vanishingIdeal W).subschemeι.isClosedEmbedding.injective ?_⟩
      rw [← hy]
      change (i' j ≫ (vanishingIdeal W).subschemeι).base t = (redι (Z j.castSucc) ≫ i j.castSucc).base t
      rw [hi'fac]
    have hX' : IsAffine (vanishingIdeal W).subscheme := ih _ _ i' hci' haff' hX'red hcov'

    refine affine_of_two_closed X
      (vanishingIdeal W).subscheme (Z (Fin.last n)) (vanishingIdeal W).subschemeι (i (Fin.last n))
      inferInstance (hci _) hX' (haff _) hred ?_
    rw [hrangeι]
    refine Set.eq_univ_of_forall fun x => ?_
    have hx := hcov.symm ▸ Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j', hj⟩)
    · exact Or.inr hj

/-- A finite cover by closed affine subschemes forces affineness, even when
the ambient scheme has nilpotents. -/
lemma affine_of_finite_closed (X : Scheme.{u}) (m : ℕ) (Z : Fin m → Scheme.{u})
    (i : ∀ j, Z j ⟶ X) (hci : ∀ j, IsClosedImmersion (i j))
    (haff : ∀ j, IsAffine (Z j)) (hcov : ⋃ j, Set.range (i j) = Set.univ) :
    IsAffine X := by
  have := hci
  let R := red X
  let ι := redι X
  have hle (j : Fin m) : ι.ker ≤ (redι (Z j) ≫ i j).ker := by
    change (vanishingIdeal (⊤ : Closeds X)).subschemeι.ker ≤ _
    rw [ker_subschemeι]
    exact (isReduced_subscheme_vanishingIdeal_and_le_ker (⊤ : Closeds X)).2 _
      (Set.subset_univ _)
  let f : ∀ j, red (Z j) ⟶ R := fun j =>
    IsClosedImmersion.lift ι (redι (Z j) ≫ i j) (hle j)
  have hf (j) : f j ≫ ι = redι (Z j) ≫ i j := IsClosedImmersion.lift_fac _ _ _
  have hcf (j) : IsClosedImmersion (f j) := by
    have : IsClosedImmersion (f j ≫ ι) := by rw [hf]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion (f j) ι
  have haf (j) : IsAffine (red (Z j)) := by
    have := haff j
    exact isAffine_of_isAffineHom (redι (Z j))
  have hcover : ⋃ j, Set.range (f j).base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp (hcov.symm ▸ Set.mem_univ (ι x))
    obtain ⟨z, hz⟩ : y ∈ Set.range (redι (Z j)) := by rw [range_redι]; trivial
    refine Set.mem_iUnion.mpr ⟨j, z, ι.isClosedEmbedding.injective ?_⟩
    change (f j ≫ ι) z = ι x
    rw [hf, Scheme.Hom.comp_apply, hz, hy]
  have : IsAffine R := affine_of_finite_closed_reduced m R (fun j => red (Z j)) f
    hcf haf inferInstance hcover
  have : Surjective ι := (surjective_iff _).mpr (Set.range_eq_univ.mp (range_redι X))
  exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective ι

end ClosedAffineCover

variable (k : Type u) [Field k] [CharZero k] (r n : ℕ) (hr : 0 < r)
  {E : B k n false ≃+* B k n true}

/-- The actual marked complement is principal on each of the specified charts. -/
lemma chart_preimage_complement (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    (D.chart i) ⁻¹ᵁ (divisorComplement k r n hr D a) =
      PrimeSpectrum.basicOpen (pairEquation k n (a i) (a (next r hr i))) := by
  have hs := support_on_spec ((markedIdeal k r n hr D a).comap (D.chart i))
  change (((markedIdeal k r n hr D a).comap (D.chart i)).support : Set (specA k n)) =
    PrimeSpectrum.zeroLocus (chartIdeal k r n hr D a i) at hs
  rw [global_marked_ideal_charts k r n hr hr3 E hE D a i,
    PrimeSpectrum.zeroLocus_span] at hs
  rw [Scheme.IdealSheafData.support_comap] at hs
  apply TopologicalSpace.Opens.ext
  change ((D.chart i) ⁻¹' (markedIdeal k r n hr D a).supportᶜ) = _
  rw [Set.preimage_compl]
  exact (congrArg Set.compl hs).trans (PrimeSpectrum.basicOpen_eq_zeroLocus_compl _).symm

lemma chart_complement_affine (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    IsAffineOpen ((D.chart i) ⁻¹ᵁ (divisorComplement k r n hr D a)) := by
  rw [chart_preimage_complement k r n hr hr3 hE D a i]
  exact IsAffineOpen.Spec_basicOpen _

open ArithmeticThetaPolygonCohomologyR0131

omit [CharZero k] in
lemma pair_equation_reduction (N : ℕ) (h : n ≤ N) (a b : kˣ) :
    truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
      (pairEquation k N a b) = pairEquation k n a b := by
  simp only [pairEquation, map_mul, markedEquation, map_sub]
  rfl

lemma complement_reduction_preimage (N : ℕ) (h : n ≤ N) (hr3 : 3 ≤ r)
    (hE : IsAdjacent k n E) {F : B k N false ≃+* B k N true}
    (hF : IsAdjacent k N F) (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i) (a : Fin r → kˣ) :
    i ⁻¹ᵁ divisorComplement k r N hr T a = divisorComplement k r n hr D a := by
  ext x
  obtain ⟨j, p, rfl⟩ := D.covers x
  change i (D.chart j p) ∈ divisorComplement k r N hr T a ↔ _
  rw [← Scheme.Hom.comp_apply, hi.2 j, Scheme.Hom.comp_apply]
  change chartReduction k n N h p ∈ (T.chart j) ⁻¹ᵁ divisorComplement k r N hr T a ↔
    p ∈ (D.chart j) ⁻¹ᵁ divisorComplement k r n hr D a
  rw [chart_preimage_complement k r N hr hr3 hF T a j,
    chart_preimage_complement k r n hr hr3 hE D a j]
  change truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h
    (pairEquation k N (a j) (a (next r hr j))) ∉ p.asIdeal ↔ _
  rw [pair_equation_reduction]
  rfl

/-- Affineness of the marked complement ascends along the actual nilpotent
reduction map; no flatness hypothesis is used. -/
lemma complement_affine_of_reduction (N : ℕ) (h : n ≤ N) (hr3 : 3 ≤ r)
    (hE : IsAdjacent k n E) {F : B k N false ≃+* B k N true}
    (hF : IsAdjacent k N F) (D : Atlas k r n hr E) (T : Atlas k r N hr F)
    (i : D.X ⟶ T.X) (hi : IsReduction k r n N hr h D T i)
    [IsClosedImmersion i] (a : Fin r → kˣ)
    (ha : IsAffine (divisorComplement k r n hr D a).toScheme) :
    IsAffine (divisorComplement k r N hr T a).toScheme := by
  have : Surjective i := (surjective_iff i).mpr (reduction_surjective k r n N hr h D T i hi)
  have : IsAffine (i ⁻¹ᵁ divisorComplement k r N hr T a).toScheme := by
    rw [complement_reduction_preimage k r n hr N h hr3 hE hF D T i hi a]
    exact ha
  have : Surjective (i ∣_ divisorComplement k r N hr T a) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i _).flip inferInstance
  exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective
    (i ∣_ divisorComplement k r N hr T a)

/-- For a fixed cycle and field, the universal thickness-zero case suffices
for the full frozen affineness assertion at every thickness. -/
lemma complement_affine_of_zero (hr3 : 3 ≤ r)
    (hzero : ∀ (E₀ : B k 0 false ≃+* B k 0 true), IsAdjacent k 0 E₀ →
      ∀ (D₀ : Atlas k r 0 hr E₀) (a : Fin r → kˣ),
        IsAffine (divisorComplement k r 0 hr D₀ a).toScheme)
    (hE : IsAdjacent k n E) (D : Atlas k r n hr E) (a : Fin r → kˣ) :
    IsAffine (divisorComplement k r n hr D a).toScheme := by
  obtain ⟨E₀, hE₀, _⟩ := finite_stage_adjacent k 0
  obtain ⟨D₀⟩ := infinitesimal_polygon_atlas k r hr hr3 0 E₀ hE₀
  obtain ⟨i, ⟨hi, hclosed, _⟩, _⟩ := polygon_thickening_transition
    k r hr hr3 0 n (Nat.zero_le n) E₀ E hE₀ hE D₀ D
  let := hclosed
  exact complement_affine_of_reduction k r 0 hr n (Nat.zero_le n) hr3 hE₀ hE
    D₀ D i hi a (hzero E₀ hE₀ D₀ a)

/-- Glue two morphisms along the actual intersection of a two-open cover. -/
lemma glue_two_opens {X Y : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (f : U.toScheme ⟶ Y) (g : V.toScheme ⟶ Y)
    (hfg : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ f =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ g) :
    ∃ h : X ⟶ Y, U.ι ≫ h = f ∧ V.ι ≫ h = g := by
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : TopologicalSpace.IsOpenCover W := by
    change (⨆ b, W b) = ⊤
    simpa [W, iSup_bool_eq, sup_comm] using hUV
  let C := X.openCoverOfIsOpenCover W hW
  let F : ∀ b, C.X b ⟶ Y := fun b => by
    cases b
    · exact g
    · exact f
  have hF : ∀ b c, CategoryTheory.Limits.pullback.fst (C.f b) (C.f c) ≫ F b =
      CategoryTheory.Limits.pullback.snd (C.f b) (C.f c) ≫ F c := by
    intro b c
    cases b <;> cases c
    · change CategoryTheory.Limits.pullback.fst V.ι V.ι ≫ g =
        CategoryTheory.Limits.pullback.snd V.ι V.ι ≫ g
      congr 1
      exact (cancel_mono V.ι).mp CategoryTheory.Limits.pullback.condition
    · change CategoryTheory.Limits.pullback.fst V.ι U.ι ≫ g =
        CategoryTheory.Limits.pullback.snd V.ι U.ι ≫ f
      rw [← cancel_epi (isPullback_opens_inf U V).flip.isoPullback.hom]
      simpa using hfg.symm
    · change CategoryTheory.Limits.pullback.fst U.ι V.ι ≫ f =
        CategoryTheory.Limits.pullback.snd U.ι V.ι ≫ g
      rw [← cancel_epi (isPullback_opens_inf U V).isoPullback.hom]
      simpa using hfg
    · change CategoryTheory.Limits.pullback.fst U.ι U.ι ≫ f =
        CategoryTheory.Limits.pullback.snd U.ι U.ι ≫ f
      congr 1
      exact (cancel_mono U.ι).mp CategoryTheory.Limits.pullback.condition
  exact ⟨C.glueMorphisms F hF, C.ι_glueMorphisms F hF true, C.ι_glueMorphisms F hF false⟩

namespace ComponentParametrization
open ArithmeticThetaPolygonCohomologyR0131

/-- The actual constant-coefficient map of the truncated power-series base. -/
def residueBase : R k n →+* k :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
    intro f hf
    have hf' : f ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k)) :=
      Ideal.pow_le_self (Nat.succ_ne_zero n) hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf'
    simp)

omit [CharZero k] in
@[simp] lemma residueBase_parameter : residueBase k n (parameter k n) = 0 := by
  simp [residueBase, parameter, trunc]

omit [CharZero k] in
@[simp] lemma residueBase_markedUnit (a : kˣ) :
    residueBase k n (markedUnit k n a : R k n) = a := by
  simp [residueBase, markedUnit, trunc]

variable {S : Type u} [CommRing S] [Algebra k S]

/-- The right branch in the affine coordinate whose two node values are zero
and one. The removed marking corresponds to the pole of this coordinate. -/
def rightPoint (a : kˣ) (z : S) (d : Sˣ) : A k n →+* S :=
  mkPoint ((algebraMap k S).comp (residueBase k n))
    (algebraMap k S (a : k) * z * ↑d⁻¹) 0 (by simp)

/-- The left branch in the same coordinate. -/
def leftPoint (b : kˣ) (z : S) (v : Sˣ) : A k n →+* S :=
  mkPoint ((algebraMap k S).comp (residueBase k n))
    0 (algebraMap k S (↑b⁻¹ : k) * (z - 1) * ↑v⁻¹) (by simp)

@[simp] lemma rightPoint_x (a : kˣ) (z : S) (d : Sˣ) :
    rightPoint k n a z d (coordX k n) = algebraMap k S (a : k) * z * ↑d⁻¹ :=
  mkPoint_x _ _ _ _
@[simp] lemma rightPoint_y (a : kˣ) (z : S) (d : Sˣ) :
    rightPoint k n a z d (coordY k n) = 0 := mkPoint_y _ _ _ _
@[simp] lemma leftPoint_x (b : kˣ) (z : S) (v : Sˣ) :
    leftPoint k n b z v (coordX k n) = 0 := mkPoint_x _ _ _ _
@[simp] lemma leftPoint_y (b : kˣ) (z : S) (v : Sˣ) :
    leftPoint k n b z v (coordY k n) =
      algebraMap k S (↑b⁻¹ : k) * (z - 1) * ↑v⁻¹ := mkPoint_y _ _ _ _

@[simp] lemma rightPoint_base (a : kˣ) (z : S) (d : Sˣ) (c : R k n) :
    rightPoint k n a z d (base k n c) = algebraMap k S (residueBase k n c) :=
  RingHom.congr_fun (mkPoint_base _ _ _ (by simp)) c
@[simp] lemma leftPoint_base (b : kˣ) (z : S) (v : Sˣ) (c : R k n) :
    leftPoint k n b z v (base k n c) = algebraMap k S (residueBase k n c) :=
  RingHom.congr_fun (mkPoint_base _ _ _ (by simp)) c

lemma right_equation_unit (a : kˣ) (z : S) (d : Sˣ) (hd : (d : S) = z - 1) :
    IsUnit (rightPoint k n a z d (markedEquation k n a)) := by
  have hz : z = (d : S) + 1 := by rw [hd]; ring
  have he : rightPoint k n a z d (markedEquation k n a) =
      algebraMap k S (a : k) * ↑d⁻¹ := by
    simp only [markedEquation, map_sub, rightPoint_x, rightPoint_base, residueBase_markedUnit]
    rw [hz, mul_add, add_mul]
    simp [mul_assoc]
  rw [he]
  exact (a.isUnit.map (algebraMap k S)).mul d⁻¹.isUnit

lemma left_equation_unit (b : kˣ) (z : S) (v : Sˣ) (hv : (v : S) = z) :
    IsUnit (leftPoint k n b z v
      (coordY k n - base k n (↑((markedUnit k n b)⁻¹)))) := by
  have he : leftPoint k n b z v
      (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) =
      -(algebraMap k S (↑b⁻¹ : k) * ↑v⁻¹) := by
    have hb : (↑((markedUnit k n b)⁻¹) : R k n) = markedUnit k n b⁻¹ := by simp [markedUnit]
    simp only [map_sub, leftPoint_y, leftPoint_base, hb, residueBase_markedUnit]
    rw [← hv, mul_sub, sub_mul]
    simp [mul_assoc]
  rw [he]
  exact ((b⁻¹.isUnit.map (algebraMap k S)).mul v⁻¹.isUnit).neg

lemma right_pair_unit (a b : kˣ) (z : S) (d : Sˣ) (hd : (d : S) = z - 1) :
    IsUnit (rightPoint k n a z d (pairEquation k n a b)) := by
  rw [pairEquation, map_mul]
  apply (right_equation_unit k n a z d hd).mul
  have hb : (↑((markedUnit k n b)⁻¹) : R k n) = markedUnit k n b⁻¹ := by simp [markedUnit]
  simpa only [map_sub, rightPoint_y, rightPoint_base, hb, residueBase_markedUnit,
    zero_sub] using (b⁻¹.isUnit.map (algebraMap k S)).neg

lemma left_pair_unit (a b : kˣ) (z : S) (v : Sˣ) (hv : (v : S) = z) :
    IsUnit (leftPoint k n b z v (pairEquation k n a b)) := by
  rw [pairEquation, map_mul]
  apply IsUnit.mul _ (left_equation_unit k n b z v hv)
  simpa only [markedEquation, map_sub, leftPoint_x, leftPoint_base,
    residueBase_markedUnit, zero_sub] using (a.isUnit.map (algebraMap k S)).neg

omit [Algebra k S] in
/-- The two branch parametrizations agree through the actual adjacent atlas
map. This statement works for any commutative target ring, including the
rings of sections on intersections of affine opens. -/
lemma adjacent_branch_points (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (b : R k n →+* S) (hb : b (parameter k n) = 0) (v : Sˣ) :
    Spec.map (CommRingCat.ofHom (mkPoint b 0 (↑v⁻¹) (by simp [hb]))) ≫ D.chart j =
      Spec.map (CommRingCat.ofHom (mkPoint b (↑v) 0 (by simp [hb]))) ≫
        D.chart (next r hr j) := by
  let f := mkPoint b (↑v) 0 (by simp [hb])
  let q := openPoint f true (by simp [f])
  have hq : q.comp (restriction k n true) = f := openPoint_restriction f true _
  let g := q.comp (E.toRingHom.comp (restriction k n false))
  have hbase : g.comp (base k n) = b := by
    dsimp only [g]
    rw [RingHom.comp_assoc, RingHom.comp_assoc, adjacent_base hE,
      ← RingHom.comp_assoc, hq]
    exact mkPoint_base _ _ _ _
  have hprod : g (coordY k n) * (v : S) = 1 := by
    have he := congrArg q (adjacent_y_mul_x hE)
    simp only [map_mul, map_one] at he
    have hv : q (restriction k n true (coordX k n)) = v := by
      change (q.comp (restriction k n true)) (coordX k n) = _
      rw [hq]
      exact mkPoint_x _ _ _ _
    rwa [hv] at he
  have hy : g (coordY k n) = ↑v⁻¹ := by
    calc
      _ = (g (coordY k n) * (v : S)) * ↑v⁻¹ := by simp [mul_assoc]
      _ = _ := by rw [hprod, one_mul]
  have hx : g (coordX k n) = 0 := by
    have he := congrArg g (coordX_mul_coordY k n)
    have hb' : g (base k n (parameter k n)) = 0 :=
      (RingHom.congr_fun hbase (parameter k n)).trans hb
    rw [map_mul, hy, hb'] at he
    calc
      _ = (g (coordX k n) * ↑v⁻¹) * (v : S) := by simp [mul_assoc]
      _ = 0 := by rw [he, zero_mul]
  have hg : g = mkPoint b 0 (↑v⁻¹) (by simp [hb]) := by
    apply point_ext
    · exact hbase.trans (mkPoint_base _ _ _ _).symm
    · exact hx.trans (mkPoint_x _ _ _ _).symm
    · exact hy.trans (mkPoint_y _ _ _ _).symm
  have hl : Spec.map (CommRingCat.ofHom q) ≫ leftLeg k n E =
      Spec.map (CommRingCat.ofHom (mkPoint b 0 (↑v⁻¹) (by simp [hb]))) := by
    rw [leftLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hg
  have hh : Spec.map (CommRingCat.ofHom q) ≫ rightLeg k n =
      Spec.map (CommRingCat.ofHom f) := by
    rw [rightLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hq
  rw [← hl, Category.assoc, (D.adjacent j).w, ← Category.assoc, hh]

lemma right_branch_in_complement (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r)
    (z : S) (d : Sˣ) (hd : (d : S) = z - 1) :
    Set.range (Spec.map (CommRingCat.ofHom (rightPoint k n (a j) z d)) ≫ D.chart j) ⊆
      divisorComplement k r n hr D a := by
  rintro x ⟨p, rfl⟩
  change Spec.map (CommRingCat.ofHom (rightPoint k n (a j) z d)) p ∈
    (D.chart j) ⁻¹ᵁ divisorComplement k r n hr D a
  rw [chart_preimage_complement k r n hr hr3 hE D a j]
  change rightPoint k n (a j) z d (pairEquation k n (a j) (a (next r hr j))) ∉ p.asIdeal
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (right_pair_unit k n (a j) (a (next r hr j)) z d hd))

lemma left_branch_in_complement (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r)
    (z : S) (v : Sˣ) (hv : (v : S) = z) :
    Set.range (Spec.map (CommRingCat.ofHom (leftPoint k n (a (next r hr j)) z v)) ≫ D.chart j) ⊆
      divisorComplement k r n hr D a := by
  rintro x ⟨p, rfl⟩
  change Spec.map (CommRingCat.ofHom (leftPoint k n (a (next r hr j)) z v)) p ∈
    (D.chart j) ⁻¹ᵁ divisorComplement k r n hr D a
  rw [chart_preimage_complement k r n hr hr3 hE D a j]
  change leftPoint k n (a (next r hr j)) z v
    (pairEquation k n (a j) (a (next r hr j))) ∉ p.asIdeal
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (left_pair_unit k n (a j) (a (next r hr j)) z v hv))

variable {T : Type u} [CommRing T] [Algebra k T]

lemma rightPoint_naturality (f : S →ₐ[k] T) (a : kˣ) (z : S) (d : Sˣ) :
    f.toRingHom.comp (rightPoint k n a z d) =
      rightPoint k n a (f z) (d.map f.toMonoidHom) := by
  apply point_ext
  · ext c
    simp only [RingHom.comp_apply, rightPoint_base]
    exact f.commutes _
  · simp [rightPoint_x]
  · simp [rightPoint_y]

lemma leftPoint_naturality (f : S →ₐ[k] T) (a : kˣ) (z : S) (v : Sˣ) :
    f.toRingHom.comp (leftPoint k n a z v) =
      leftPoint k n a (f z) (v.map f.toMonoidHom) := by
  apply point_ext
  · ext c
    simp only [RingHom.comp_apply, leftPoint_base]
    exact f.commutes _
  · simp [leftPoint_x]
  · simp [leftPoint_y]

lemma branch_agreement (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) (z : S) (v d : Sˣ)
    (hv : (v : S) = z) (hd : (d : S) = z - 1) :
    Spec.map (CommRingCat.ofHom (leftPoint k n a z v)) ≫ D.chart j =
      Spec.map (CommRingCat.ofHom (rightPoint k n a z d)) ≫
        D.chart (next r hr j) := by
  let w : Sˣ := a.map (algebraMap k S) * v * d⁻¹
  have hw : (w : S) = algebraMap k S (a : k) * z * ↑d⁻¹ := by
    simp [w, hv]
  have hwi : (↑w⁻¹ : S) = algebraMap k S (↑a⁻¹ : k) * (z - 1) * ↑v⁻¹ := by
    simp only [w, mul_inv_rev, inv_inv, Units.val_mul, Units.coe_map_inv]
    change (d : S) * (↑v⁻¹ * algebraMap k S (↑a⁻¹ : k)) = _
    rw [hd]
    ring
  have hright : rightPoint k n a z d =
      mkPoint ((algebraMap k S).comp (residueBase k n)) (↑w) 0 (by simp) := by
    apply point_ext
    · exact (mkPoint_base _ _ _ _).trans (mkPoint_base _ _ _ _).symm
    · simp [hw]
    · simp
  have hleft : leftPoint k n a z v =
      mkPoint ((algebraMap k S).comp (residueBase k n)) 0 (↑w⁻¹) (by simp) := by
    apply point_ext
    · exact (mkPoint_base _ _ _ _).trans (mkPoint_base _ _ _ _).symm
    · simp
    · simp [hwi]
  rw [hleft, hright]
  exact adjacent_branch_points k r n hr hE D j _ (by simp) w

/-- The parameter line for one component of the reduced complement. -/
def line : Scheme.{u} := Spec (CommRingCat.of (Polynomial k))

def sectionMap (U : (line k).Opens) : Polynomial k →+* Γ(line k, U) :=
  ((line k).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom

instance sectionAlgebra (U : (line k).Opens) : Algebra k Γ(line k, U) :=
  ((sectionMap k U).comp Polynomial.C).toAlgebra

lemma sectionMap_restrict {U V : (line k).Opens} (h : U ≤ V) (p : Polynomial k) :
    (line k).presheaf.map (homOfLE h).op (sectionMap k V p) = sectionMap k U p := by
  simp only [sectionMap, RingHom.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def sectionRestrict {U V : (line k).Opens} (h : U ≤ V) :
    Γ(line k, V) →ₐ[k] Γ(line k, U) :=
  { ((line k).presheaf.map (homOfLE h).op).hom with
    commutes' := fun c => sectionMap_restrict k h (Polynomial.C c) }

lemma sectionMap_basicOpen_unit (p : Polynomial k) :
    IsUnit (sectionMap k (PrimeSpectrum.basicOpen p) p) := by
  let f := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv p
  have he : PrimeSpectrum.basicOpen p ≤ (line k).basicOpen f :=
    (basicOpen_eq_of_affine (R := CommRingCat.of (Polynomial k)) p).symm.le
  have h := ((line k).toRingedSpace.isUnit_res_basicOpen f).map
    (((line k).presheaf.map (homOfLE he).op).hom)
  change IsUnit (((line k).presheaf.map (homOfLE he).op)
    (((line k).presheaf.map (homOfLE ((line k).basicOpen_le f)).op) f)) at h
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h


def rightOpen : (line k).Opens := PrimeSpectrum.basicOpen (Polynomial.X - 1)
def leftOpen : (line k).Opens := PrimeSpectrum.basicOpen Polynomial.X

def rightDenominator : Γ(line k, rightOpen k)ˣ :=
  (sectionMap_basicOpen_unit k (Polynomial.X - 1)).unit

def leftDenominator : Γ(line k, leftOpen k)ˣ :=
  (sectionMap_basicOpen_unit k Polynomial.X).unit

lemma rightDenominator_val : (rightDenominator k : Γ(line k, rightOpen k)) =
    sectionMap k (rightOpen k) Polynomial.X - 1 := by
  simp [rightDenominator, rightOpen, IsUnit.unit_spec, map_sub, map_one]

lemma leftDenominator_val : (leftDenominator k : Γ(line k, leftOpen k)) =
    sectionMap k (leftOpen k) Polynomial.X := by
  exact IsUnit.unit_spec _

lemma line_cover : rightOpen k ⊔ leftOpen k = ⊤ := by
  apply top_unique
  intro p hp
  change Polynomial.X - 1 ∉ p.asIdeal ∨ Polynomial.X ∉ p.asIdeal
  by_contra h
  push Not at h
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    (show (1 : Polynomial k) ∈ p.asIdeal by
      convert p.asIdeal.sub_mem h.2 h.1 using 1 <;> ring) isUnit_one)

def rightMap (D : Atlas k r n hr E) (j : Fin r) (a : kˣ) :
    (rightOpen k).toScheme ⟶ D.X :=
  (rightOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (rightPoint k n (S := Γ(line k, rightOpen k)) a (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k))) ≫
      D.chart (next r hr j)

def leftMap (D : Atlas k r n hr E) (j : Fin r) (a : kˣ) :
    (leftOpen k).toScheme ⟶ D.X :=
  (leftOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (leftPoint k n (S := Γ(line k, leftOpen k)) a (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k))) ≫
      D.chart j

lemma maps_agree (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) :
    (line k).homOfLE (inf_le_left : rightOpen k ⊓ leftOpen k ≤ rightOpen k) ≫
      rightMap k r n hr D j a =
    (line k).homOfLE (inf_le_right : rightOpen k ⊓ leftOpen k ≤ leftOpen k) ≫
      leftMap k r n hr D j a := by
  let W := rightOpen k ⊓ leftOpen k
  let ρ := sectionRestrict k (inf_le_left : W ≤ rightOpen k)
  let σ := sectionRestrict k (inf_le_right : W ≤ leftOpen k)
  let z := sectionMap k W Polynomial.X
  let d := (rightDenominator k).map ρ.toMonoidHom
  let v := (leftDenominator k).map σ.toMonoidHom
  have hd : (d : Γ(line k, W)) = z - 1 := by
    change ρ (rightDenominator k : Γ(line k, rightOpen k)) = _
    rw [rightDenominator_val, map_sub, map_one]
    exact congrArg (fun x => x - 1) (sectionMap_restrict k inf_le_left Polynomial.X)
  have hv : (v : Γ(line k, W)) = z := by
    change σ (leftDenominator k : Γ(line k, leftOpen k)) = _
    rw [leftDenominator_val]
    exact sectionMap_restrict k inf_le_right Polynomial.X
  have hrho : ρ (sectionMap k (rightOpen k) Polynomial.X) = z :=
    sectionMap_restrict k inf_le_left Polynomial.X
  have hsigma : σ (sectionMap k (leftOpen k) Polynomial.X) = z :=
    sectionMap_restrict k inf_le_right Polynomial.X
  have hnR := rightPoint_naturality k n ρ a
    (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)
  have hnL := leftPoint_naturality k n σ a
    (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)
  rw [hrho] at hnR
  rw [hsigma] at hnL
  simp only [rightMap, leftMap, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  have hR : CommRingCat.ofHom (rightPoint k n (S := Γ(line k, rightOpen k)) a
      (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)) ≫
      (line k).presheaf.map (homOfLE (inf_le_left : W ≤ rightOpen k)).op =
        CommRingCat.ofHom (rightPoint k n a z d) := by
    exact congrArg CommRingCat.ofHom hnR
  have hL : CommRingCat.ofHom (leftPoint k n (S := Γ(line k, leftOpen k)) a
      (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)) ≫
      (line k).presheaf.map (homOfLE (inf_le_right : W ≤ leftOpen k)).op =
        CommRingCat.ofHom (leftPoint k n a z v) := by
    exact congrArg CommRingCat.ofHom hnL
  rw [hR, hL, branch_agreement k r n hr hE D j a z v d hv hd]

/-- A parametrized component in the actual atlas realization. -/
def component (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) : line k ⟶ D.X :=
  (glue_two_opens (rightOpen k) (leftOpen k) (line_cover k)
    (rightMap k r n hr D j a) (leftMap k r n hr D j a)
    (maps_agree k r n hr hE D j a)).choose

lemma right_component (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) :
    (rightOpen k).ι ≫ component k r n hr hE D j a = rightMap k r n hr D j a :=
  (glue_two_opens (rightOpen k) (leftOpen k) (line_cover k)
    (rightMap k r n hr D j a) (leftMap k r n hr D j a)
    (maps_agree k r n hr hE D j a)).choose_spec.1

lemma left_component (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) :
    (leftOpen k).ι ≫ component k r n hr hE D j a = leftMap k r n hr D j a :=
  (glue_two_opens (rightOpen k) (leftOpen k) (line_cover k)
    (rightMap k r n hr D j a) (leftMap k r n hr D j a)
    (maps_agree k r n hr hE D j a)).choose_spec.2

lemma component_range_complement (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    Set.range (component k r n hr hE D j (a (next r hr j))) ⊆
      divisorComplement k r n hr D a := by
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ rightOpen k ⊔ leftOpen k := (line_cover k).symm ▸ trivial
  rcases hp with hp | hp
  · have he := congrArg (fun f : (rightOpen k).toScheme ⟶ D.X => f ⟨p, hp⟩)
      (right_component k r n hr hE D j (a (next r hr j)))
    change component k r n hr hE D j (a (next r hr j)) p = _ at he
    rw [he]
    exact right_branch_in_complement k r n hr hr3 hE D a (next r hr j)
      (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)
      (rightDenominator_val k) ⟨(rightOpen k).toSpecΓ ⟨p, hp⟩, rfl⟩
  · have he := congrArg (fun f : (leftOpen k).toScheme ⟶ D.X => f ⟨p, hp⟩)
      (left_component k r n hr hE D j (a (next r hr j)))
    change component k r n hr hE D j (a (next r hr j)) p = _ at he
    rw [he]
    exact left_branch_in_complement k r n hr hr3 hE D a j
      (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)
      (leftDenominator_val k) ⟨(leftOpen k).toSpecΓ ⟨p, hp⟩, rfl⟩

/-- The component morphism lands in the actual marked complement. -/
def complementComponent (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    line k ⟶ (divisorComplement k r n hr D a).toScheme :=
  IsOpenImmersion.lift (divisorComplement k r n hr D a).ι
    (component k r n hr hE D j (a (next r hr j)))
    (by rw [Scheme.Opens.range_ι]; exact component_range_complement k r n hr hr3 hE D a j)

lemma complementComponent_fac (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    complementComponent k r n hr hr3 hE D a j ≫ (divisorComplement k r n hr D a).ι =
      component k r n hr hE D j (a (next r hr j)) :=
  IsOpenImmersion.lift_fac _ _ _

lemma sectionMap_spec (U : (line k).Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionMap k U)) = U.ι := by
  change U.toSpecΓ ≫ Spec.map
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
      (line k).presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
    Category.assoc]
  exact (congrArg (fun g => U.ι ≫ g)
    (toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of (Polynomial k)))).trans (Category.comp_id _)

lemma sectionMap_mem (U : (line k).Opens) (p : U.toScheme) (f : Polynomial k) :
    sectionMap k U f ∈ (U.toSpecΓ p).asIdeal ↔ f ∈ (U.ι p).asIdeal := by
  have h := congrArg (fun g : U.toScheme ⟶ line k => g p) (sectionMap_spec k U)
  change Spec.map (CommRingCat.ofHom (sectionMap k U)) (U.toSpecΓ p) = U.ι p at h
  change f ∈ (Spec.map (CommRingCat.ofHom (sectionMap k U)) (U.toSpecΓ p)).asIdeal ↔ _
  rw [h]

lemma rightLeg_coord_not_mem (p : specB k n true) :
    coordX k n ∉ (rightLeg k n p).asIdeal := by
  have hu : IsUnit (restriction k n true (coordX k n)) :=
    (IsLocalization.Away.algebraMap_isUnit
      (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k true)).map
      (trunc _ (openParameter k true) n)
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

lemma leftLeg_coord_not_mem (p : specB k n true) :
    coordY k n ∉ (leftLeg k n E p).asIdeal := by
  have hu : IsUnit (restriction k n false (coordY k n)) :=
    (IsLocalization.Away.algebraMap_isUnit
      (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k false)).map
      (trunc _ (openParameter k false) n)
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map E.toRingHom))

lemma left_branch_charts (D : Atlas k r n hr E) (i j : Fin r)
    (f : A k n →+* S) (hx : f (coordX k n) = 0) (p : PrimeSpectrum S)
    (hp : D.chart j (Spec.map (CommRingCat.ofHom f) p) ∈ Set.range (D.chart i)) :
    i = j ∨ i = next r hr j := by
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hn : i = next r hr j
  · exact Or.inr hn
  obtain ⟨q, hq⟩ := hp
  by_cases hi : next r hr i = j
  · obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i) q
      (Spec.map (CommRingCat.ofHom f) p) (by simpa [hi] using hq)
    have hz : coordX k n ∈ (Spec.map (CommRingCat.ofHom f) p).asIdeal := by
      change f (coordX k n) ∈ p.asIdeal
      rw [hx]; exact p.asIdeal.zero_mem
    rw [← ht] at hz
    exact False.elim (rightLeg_coord_not_mem k n t hz)
  · exact False.elim (Set.disjoint_left.mp (D.disjoint i j hij hi (Ne.symm hn))
      ⟨q, hq⟩ ⟨Spec.map (CommRingCat.ofHom f) p, rfl⟩)

lemma right_branch_charts (D : Atlas k r n hr E) (i j : Fin r)
    (f : A k n →+* S) (hy : f (coordY k n) = 0) (p : PrimeSpectrum S)
    (hp : D.chart j (Spec.map (CommRingCat.ofHom f) p) ∈ Set.range (D.chart i)) :
    i = j ∨ next r hr i = j := by
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hn : next r hr i = j
  · exact Or.inr hn
  obtain ⟨q, hq⟩ := hp
  by_cases hj : next r hr j = i
  · obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j)
      (Spec.map (CommRingCat.ofHom f) p) q (by simpa [hj] using hq.symm)
    have hz : coordY k n ∈ (Spec.map (CommRingCat.ofHom f) p).asIdeal := by
      change f (coordY k n) ∈ p.asIdeal
      rw [hy]; exact p.asIdeal.zero_mem
    rw [← ht] at hz
    exact False.elim (leftLeg_coord_not_mem k n t hz)
  · exact False.elim (Set.disjoint_left.mp (D.disjoint i j hij hn hj)
      ⟨q, hq⟩ ⟨Spec.map (CommRingCat.ofHom f) p, rfl⟩)

lemma component_charts (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (i j : Fin r) (a : kˣ) (p : line k)
    (hp : component k r n hr hE D j a p ∈ Set.range (D.chart i)) :
    i = j ∨ i = next r hr j := by
  have hcover : p ∈ rightOpen k ⊔ leftOpen k := (line_cover k).symm ▸ trivial
  rcases hcover with h | h
  · have he := congrArg (fun f : (rightOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (right_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he] at hp
    obtain hi | hi := right_branch_charts k r n hr D i (next r hr j) _
      (rightPoint_y k n a _ _) ((rightOpen k).toSpecΓ ⟨p, h⟩) hp
    · exact Or.inr hi
    · exact Or.inl ((Finite.injective_iff_surjective.mpr (next_surjective r hr)) hi)
  · have he := congrArg (fun f : (leftOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (left_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he] at hp
    exact left_branch_charts k r n hr D i j _
      (leftPoint_x k n a _ _) ((leftOpen k).toSpecΓ ⟨p, h⟩) hp

lemma component_mem_left_chart (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) (p : line k) :
    component k r n hr hE D j a p ∈ Set.range (D.chart j) ↔ p ∈ leftOpen k := by
  constructor
  · intro hp
    by_contra hnot
    have hcov : p ∈ rightOpen k ⊔ leftOpen k := (line_cover k).symm ▸ trivial
    have h : p ∈ rightOpen k := hcov.resolve_right hnot
    have he := congrArg (fun f : (rightOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (right_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he] at hp
    obtain ⟨q, hq⟩ := hp
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j) q
      (Spec.map (CommRingCat.ofHom (rightPoint k n (S := Γ(line k, rightOpen k)) a
        (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)))
        ((rightOpen k).toSpecΓ ⟨p, h⟩)) hq
    apply rightLeg_coord_not_mem k n t
    rw [ht]
    change rightPoint k n a (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)
      (coordX k n) ∈ ((rightOpen k).toSpecΓ ⟨p, h⟩).asIdeal
    rw [rightPoint_x]
    have hz : sectionMap k (rightOpen k) Polynomial.X ∈
        ((rightOpen k).toSpecΓ ⟨p, h⟩).asIdeal :=
      (sectionMap_mem k (rightOpen k) ⟨p, h⟩ Polynomial.X).mpr (not_not.mp hnot)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hz)
  · intro h
    have he := congrArg (fun f : (leftOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (left_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he]
    exact ⟨_, rfl⟩

lemma component_mem_right_chart (hE : IsAdjacent k n E) (D : Atlas k r n hr E)
    (j : Fin r) (a : kˣ) (p : line k) :
    component k r n hr hE D j a p ∈ Set.range (D.chart (next r hr j)) ↔
      p ∈ rightOpen k := by
  constructor
  · intro hp
    by_contra hnot
    have hcov : p ∈ rightOpen k ⊔ leftOpen k := (line_cover k).symm ▸ trivial
    have h : p ∈ leftOpen k := hcov.resolve_left hnot
    have he := congrArg (fun f : (leftOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (left_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he] at hp
    obtain ⟨q, hq⟩ := hp
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent j)
      (Spec.map (CommRingCat.ofHom (leftPoint k n (S := Γ(line k, leftOpen k)) a
        (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)))
        ((leftOpen k).toSpecΓ ⟨p, h⟩)) q hq.symm
    apply leftLeg_coord_not_mem k n t
    rw [ht]
    change leftPoint k n a (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)
      (coordY k n) ∈ ((leftOpen k).toSpecΓ ⟨p, h⟩).asIdeal
    rw [leftPoint_y]
    have hz : sectionMap k (leftOpen k) Polynomial.X - 1 ∈
        ((leftOpen k).toSpecΓ ⟨p, h⟩).asIdeal := by
      simpa only [map_sub, map_one] using
        (sectionMap_mem k (leftOpen k) ⟨p, h⟩ (Polynomial.X - 1)).mpr (not_not.mp hnot)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hz)
  · intro h
    have he := congrArg (fun f : (rightOpen k).toScheme ⟶ D.X => f ⟨p, h⟩)
      (right_component k r n hr hE D j a)
    change component k r n hr hE D j a p = _ at he
    rw [he]
    exact ⟨_, rfl⟩

instance polynomialSectionAlgebra (U : (line k).Opens) :
    Algebra (Polynomial k) Γ(line k, U) :=
  StructureSheaf.openAlgebra (Polynomial k) (Opposite.op U)

lemma sectionMap_eq_algebraMap (U : (line k).Opens) :
    sectionMap k U = algebraMap (Polynomial k) Γ(line k, U) := by
  rfl

lemma localization_subring_eq_top {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    [Algebra R₀ S₀] (x : R₀) [IsLocalization.Away x S₀] (V : Subring S₀)
    (hR : ∀ c, algebraMap R₀ S₀ c ∈ V) (v : S₀)
    (hv : v * algebraMap R₀ S₀ x = 1) (hV : v ∈ V) : V = ⊤ := by
  apply top_unique
  intro s hs
  obtain ⟨⟨c, m, hm⟩, he⟩ := IsLocalization.surj (Submonoid.powers x) s
  obtain ⟨d, rfl⟩ := hm
  have hid : v ^ d * algebraMap R₀ S₀ (x ^ d) = 1 := by
    rw [map_pow, ← mul_pow, hv, one_pow]
  have he' : s = algebraMap R₀ S₀ c * v ^ d := by
    calc
      s = s * (v ^ d * algebraMap R₀ S₀ (x ^ d)) := by rw [hid, mul_one]
      _ = (s * algebraMap R₀ S₀ (x ^ d)) * v ^ d := by ring
      _ = _ := by rw [he]
  rw [he']
  exact V.mul_mem (hR c) (V.pow_mem hV d)

lemma polynomial_mem_subring (V : Subring S) (f : Polynomial k →+* S)
    (hC : ∀ c, f (Polynomial.C c) ∈ V) (hX : f Polynomial.X ∈ V) :
    ∀ p, f p ∈ V := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using V.add_mem hp hq
  | monomial m c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact V.mul_mem (hC c) (V.pow_mem hX m)

lemma residueBase_constant (c : k) :
    residueBase k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C c)) = c := by
  simp [residueBase, trunc]

/-- Surjectivity on a localization can be checked using the polynomial
coordinate and the inverse of the designated denominator. -/
lemma section_subring_eq_top (p : Polynomial k)
    (V : Subring Γ(line k, PrimeSpectrum.basicOpen p))
    (hC : ∀ c, sectionMap k _ (Polynomial.C c) ∈ V)
    (hX : sectionMap k _ Polynomial.X ∈ V)
    (v : Γ(line k, PrimeSpectrum.basicOpen p))
    (hv : v * sectionMap k _ p = 1) (hV : v ∈ V) : V = ⊤ := by
  have : IsLocalization.Away p Γ(line k, PrimeSpectrum.basicOpen p) :=
    StructureSheaf.IsLocalization.to_basicOpen (Polynomial k) p
  apply localization_subring_eq_top p V
    (fun c => (sectionMap_eq_algebraMap k _ ▸ polynomial_mem_subring k V
      (sectionMap k _) hC hX c)) v _ hV
  simpa only [sectionMap_eq_algebraMap] using hv

def rightLocalRingMap (a b : kˣ) :
    Localization.Away (pairEquation k n a b) →+* Γ(line k, rightOpen k) :=
  IsLocalization.Away.lift (pairEquation k n a b)
    (right_pair_unit k n (S := Γ(line k, rightOpen k)) a b
      (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k) (rightDenominator_val k))

lemma rightLocalRingMap_algebraMap (a b : kˣ) (c : A k n) :
    rightLocalRingMap k n a b (algebraMap (A k n) _ c) =
      rightPoint k n (S := Γ(line k, rightOpen k)) a
        (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k) c :=
  IsLocalization.Away.lift_eq _ _ c

set_option maxHeartbeats 800000 in
lemma rightLocalRingMap_surjective (a b : kˣ) :
    Function.Surjective (rightLocalRingMap k n a b) := by
  let L := Localization.Away (pairEquation k n a b)
  let φ := rightLocalRingMap k n a b
  let q := sectionMap k (rightOpen k)
  let d := rightDenominator k
  let α : k →+* Γ(line k, rightOpen k) := algebraMap k _
  have hconst (c : k) : α c ∈ φ.range := by
    refine ⟨algebraMap (A k n) L (base k n
      (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C c))), ?_⟩
    change rightLocalRingMap k n a b _ = _
    rw [rightLocalRingMap_algebraMap, rightPoint_base, residueBase_constant]
  have he : φ (algebraMap (A k n) L (markedEquation k n a)) = α (a : k) * ↑d⁻¹ := by
    rw [rightLocalRingMap_algebraMap]
    simp only [markedEquation, map_sub, rightPoint_x, rightPoint_base, residueBase_markedUnit]
    have hz : q Polynomial.X = (d : Γ(line k, rightOpen k)) + 1 := by
      rw [rightDenominator_val]; ring
    change α (a : k) * q Polynomial.X * ↑d⁻¹ - α (a : k) = _
    rw [hz, mul_add, add_mul]
    simp [mul_assoc]
  have hunit : IsUnit (algebraMap (A k n) L (markedEquation k n a)) := by
    apply isUnit_of_mul_isUnit_left (y := algebraMap (A k n) L
      (coordY k n - base k n (↑((markedUnit k n b)⁻¹))))
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (pairEquation k n a b)
  let w := hunit.unit
  have hw : φ (↑w⁻¹) * (α (a : k) * ↑d⁻¹) = 1 := by
    calc
      _ = φ (↑w⁻¹) * φ (↑w) := by rw [hunit.unit_spec, he]
      _ = 1 := by simp only [← map_mul, Units.inv_mul, map_one]
  have hd : (d : Γ(line k, rightOpen k)) ∈ φ.range := by
    have heq : (d : Γ(line k, rightOpen k)) = α (a : k) * φ (↑w⁻¹) := by
      calc
        _ = (φ (↑w⁻¹) * (α (a : k) * ↑d⁻¹)) * ↑d := by rw [hw, one_mul]
        _ = (φ (↑w⁻¹) * α (a : k)) * (↑d⁻¹ * ↑d) := by ring
        _ = _ := by rw [Units.inv_mul, mul_one, mul_comm]
    rw [heq]
    exact φ.range.mul_mem (hconst a) ⟨_, rfl⟩
  have hdinv : (↑d⁻¹ : Γ(line k, rightOpen k)) ∈ φ.range := by
    have heq : (↑d⁻¹ : Γ(line k, rightOpen k)) =
        α (↑a⁻¹ : k) * φ (algebraMap (A k n) L (markedEquation k n a)) := by
      rw [he, ← mul_assoc, ← map_mul]
      simp
    rw [heq]
    exact φ.range.mul_mem (hconst _) ⟨_, rfl⟩
  apply RingHom.range_eq_top.mp
  refine section_subring_eq_top k (Polynomial.X - 1) φ.range
    (fun c => hconst c) ?_ (↑d⁻¹ : Γ(line k, rightOpen k)) ?_ hdinv
  · have hz : q Polynomial.X = (d : Γ(line k, rightOpen k)) + 1 := by
      rw [rightDenominator_val]; ring
    change q Polynomial.X ∈ φ.range
    rw [hz]
    exact φ.range.add_mem hd φ.range.one_mem
  · change (↑d⁻¹ : Γ(line k, rightOpen k)) * q (Polynomial.X - 1) = 1
    have hden : q (Polynomial.X - 1) = (d : Γ(line k, rightOpen k)) := by
      rw [map_sub, map_one, rightDenominator_val]
    rw [hden]; exact d.inv_val

def leftLocalRingMap (a b : kˣ) :
    Localization.Away (pairEquation k n a b) →+* Γ(line k, leftOpen k) :=
  IsLocalization.Away.lift (pairEquation k n a b)
    (left_pair_unit k n (S := Γ(line k, leftOpen k)) a b
      (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k) (leftDenominator_val k))

lemma leftLocalRingMap_algebraMap (a b : kˣ) (c : A k n) :
    leftLocalRingMap k n a b (algebraMap (A k n) _ c) =
      leftPoint k n (S := Γ(line k, leftOpen k)) b
        (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k) c :=
  IsLocalization.Away.lift_eq _ _ c

set_option maxHeartbeats 800000 in
lemma leftLocalRingMap_surjective (a b : kˣ) :
    Function.Surjective (leftLocalRingMap k n a b) := by
  let L := Localization.Away (pairEquation k n a b)
  let φ := leftLocalRingMap k n a b
  let q := sectionMap k (leftOpen k)
  let v := leftDenominator k
  let α : k →+* Γ(line k, leftOpen k) := algebraMap k _
  let c : kˣ := -b⁻¹
  let e := coordY k n - base k n (↑((markedUnit k n b)⁻¹))
  have hconst (t : k) : α t ∈ φ.range := by
    refine ⟨algebraMap (A k n) L (base k n
      (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C t))), ?_⟩
    change leftLocalRingMap k n a b _ = _
    rw [leftLocalRingMap_algebraMap, leftPoint_base, residueBase_constant]
  have he : φ (algebraMap (A k n) L e) = α (c : k) * ↑v⁻¹ := by
    rw [leftLocalRingMap_algebraMap]
    have hb : (↑((markedUnit k n b)⁻¹) : R k n) = markedUnit k n b⁻¹ := by simp [markedUnit]
    simp only [e, map_sub, leftPoint_y, leftPoint_base, hb, residueBase_markedUnit]
    have hz : q Polynomial.X = (v : Γ(line k, leftOpen k)) := (leftDenominator_val k).symm
    change α (↑b⁻¹ : k) * (q Polynomial.X - 1) * ↑v⁻¹ - α (↑b⁻¹ : k) = _
    rw [hz, mul_sub, sub_mul]
    simp only [mul_one, mul_assoc, Units.mul_inv, c, Units.val_neg, map_neg, neg_mul]
    ring
  have hunit : IsUnit (algebraMap (A k n) L e) := by
    apply isUnit_of_mul_isUnit_right (x := algebraMap (A k n) L (markedEquation k n a))
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (pairEquation k n a b)
  let w := hunit.unit
  have hw : φ (↑w⁻¹) * (α (c : k) * ↑v⁻¹) = 1 := by
    calc
      _ = φ (↑w⁻¹) * φ (↑w) := by rw [hunit.unit_spec, he]
      _ = 1 := by simp only [← map_mul, Units.inv_mul, map_one]
  have hv : (v : Γ(line k, leftOpen k)) ∈ φ.range := by
    have heq : (v : Γ(line k, leftOpen k)) = α (c : k) * φ (↑w⁻¹) := by
      calc
        _ = (φ (↑w⁻¹) * (α (c : k) * ↑v⁻¹)) * ↑v := by rw [hw, one_mul]
        _ = (φ (↑w⁻¹) * α (c : k)) * (↑v⁻¹ * ↑v) := by ring
        _ = _ := by rw [Units.inv_mul, mul_one, mul_comm]
    rw [heq]
    exact φ.range.mul_mem (hconst c) ⟨_, rfl⟩
  have hvinv : (↑v⁻¹ : Γ(line k, leftOpen k)) ∈ φ.range := by
    have heq : (↑v⁻¹ : Γ(line k, leftOpen k)) =
        α (↑c⁻¹ : k) * φ (algebraMap (A k n) L e) := by
      rw [he, ← mul_assoc, ← map_mul]
      simp only [Units.inv_mul, map_one, one_mul]
    rw [heq]
    exact φ.range.mul_mem (hconst _) ⟨_, rfl⟩
  apply RingHom.range_eq_top.mp
  refine section_subring_eq_top k Polynomial.X φ.range (fun t => hconst t)
    ?_ (↑v⁻¹ : Γ(line k, leftOpen k)) ?_ hvinv
  · change q Polynomial.X ∈ φ.range
    rwa [← leftDenominator_val]
  · change (↑v⁻¹ : Γ(line k, leftOpen k)) * q Polynomial.X = 1
    rw [← leftDenominator_val]
    exact v.inv_mul

def pairOpen (a b : kˣ) : (specA k n).Opens :=
  PrimeSpectrum.basicOpen (pairEquation k n a b)

/-- A branch is a closed subscheme of the principal marked-complement chart. -/
def rightClosedMap (a b : kˣ) :
    (rightOpen k).toScheme ⟶ (pairOpen k n a b).toScheme :=
  (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k))
    (Polynomial.X - 1)).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (rightLocalRingMap k n a b)) ≫
      (basicOpenIsoSpecAway (R := CommRingCat.of (A k n)) (pairEquation k n a b)).inv

def leftClosedMap (a b : kˣ) :
    (leftOpen k).toScheme ⟶ (pairOpen k n a b).toScheme :=
  (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k)) Polynomial.X).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (leftLocalRingMap k n a b)) ≫
      (basicOpenIsoSpecAway (R := CommRingCat.of (A k n)) (pairEquation k n a b)).inv

instance rightClosedMap_isClosedImmersion (a b : kˣ) :
    IsClosedImmersion (rightClosedMap k n a b) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (rightLocalRingMap k n a b)) (rightLocalRingMap_surjective k n a b)
  unfold rightClosedMap
  infer_instance

instance leftClosedMap_isClosedImmersion (a b : kˣ) :
    IsClosedImmersion (leftClosedMap k n a b) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (leftLocalRingMap k n a b)) (leftLocalRingMap_surjective k n a b)
  unfold leftClosedMap
  infer_instance

lemma basicOpenIsoSpecAway_inv_ι {R₀ : CommRingCat.{u}} (f : R₀) :
    (basicOpenIsoSpecAway f).inv ≫ Scheme.Opens.ι (X := Spec R₀) (PrimeSpectrum.basicOpen f) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (Localization.Away f))) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap f, Iso.inv_hom_id_assoc]

lemma rightClosedMap_fac (a b : kˣ) :
    rightClosedMap k n a b ≫ (pairOpen k n a b).ι =
      (rightOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (rightPoint k n (S := Γ(line k, rightOpen k)) a
          (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k))) := by
  have hι : (basicOpenIsoSpecAway (R := CommRingCat.of (A k n))
      (pairEquation k n a b)).inv ≫ (pairOpen k n a b).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (A k n) (Localization.Away (pairEquation k n a b)))) :=
    basicOpenIsoSpecAway_inv_ι (R₀ := CommRingCat.of (A k n)) (pairEquation k n a b)
  change ((rightOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rightLocalRingMap k n a b)) ≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (A k n)) (pairEquation k n a b)).inv) ≫
      (pairOpen k n a b).ι = _
  rw [Category.assoc, Category.assoc, hι, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact rightLocalRingMap_algebraMap k n a b c

lemma leftClosedMap_fac (a b : kˣ) :
    leftClosedMap k n a b ≫ (pairOpen k n a b).ι =
      (leftOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (leftPoint k n (S := Γ(line k, leftOpen k)) b
          (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k))) := by
  have hι : (basicOpenIsoSpecAway (R := CommRingCat.of (A k n))
      (pairEquation k n a b)).inv ≫ (pairOpen k n a b).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (A k n) (Localization.Away (pairEquation k n a b)))) :=
    basicOpenIsoSpecAway_inv_ι (R₀ := CommRingCat.of (A k n)) (pairEquation k n a b)
  change ((leftOpen k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (leftLocalRingMap k n a b)) ≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (A k n)) (pairEquation k n a b)).inv) ≫
      (pairOpen k n a b).ι = _
  rw [Category.assoc, Category.assoc, hι, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact leftLocalRingMap_algebraMap k n a b c

def complementChart (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    (pairOpen k n (a i) (a (next r hr i))).toScheme ⟶
      (divisorComplement k r n hr D a).toScheme :=
  IsOpenImmersion.lift (divisorComplement k r n hr D a).ι
    ((pairOpen k n (a i) (a (next r hr i))).ι ≫ D.chart i) (by
      rw [Scheme.Opens.range_ι]
      rintro x ⟨p, rfl⟩
      change (pairOpen k n (a i) (a (next r hr i))).ι p ∈
        (D.chart i) ⁻¹ᵁ divisorComplement k r n hr D a
      rw [chart_preimage_complement k r n hr hr3 hE D a i]
      exact p.property)

lemma complementChart_fac (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    complementChart k r n hr hr3 hE D a i ≫ (divisorComplement k r n hr D a).ι =
      (pairOpen k n (a i) (a (next r hr i))).ι ≫ D.chart i :=
  IsOpenImmersion.lift_fac _ _ _

instance complementChart_open (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r) :
    IsOpenImmersion (complementChart k r n hr hr3 hE D a i) := by
  let := D.chart_open i
  have : IsOpenImmersion (complementChart k r n hr hr3 hE D a i ≫
      (divisorComplement k r n hr D a).ι) := by
    rw [complementChart_fac]
    infer_instance
  exact IsOpenImmersion.of_comp _ (divisorComplement k r n hr D a).ι

lemma complementChart_range (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (i : Fin r)
    (x : (divisorComplement k r n hr D a).toScheme) :
    x ∈ Set.range (complementChart k r n hr hr3 hE D a i) ↔
      (divisorComplement k r n hr D a).ι x ∈ Set.range (D.chart i) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, congrArg (fun f => f p) (complementChart_fac k r n hr hr3 hE D a i).symm⟩
  · rintro ⟨p, hp⟩
    have hpmem : p ∈ pairOpen k n (a i) (a (next r hr i)) := by
      change p ∈ PrimeSpectrum.basicOpen (pairEquation k n (a i) (a (next r hr i)))
      rw [← chart_preimage_complement k r n hr hr3 hE D a i]
      change D.chart i p ∈ divisorComplement k r n hr D a
      rw [hp]
      exact x.property
    refine ⟨⟨p, hpmem⟩, (divisorComplement k r n hr D a).ι.isOpenEmbedding.injective ?_⟩
    change (complementChart k r n hr hr3 hE D a i ≫ (divisorComplement k r n hr D a).ι)
      ⟨p, hpmem⟩ = _
    rw [complementChart_fac]
    exact hp

def complementCover (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) :
    (divisorComplement k r n hr D a).toScheme.OpenCover where
  I₀ := Fin r
  X i := (pairOpen k n (a i) (a (next r hr i))).toScheme
  f := complementChart k r n hr hr3 hE D a
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro x
    obtain ⟨i, p, hp⟩ := D.covers ((divisorComplement k r n hr D a).ι x)
    obtain ⟨q, hq⟩ := (complementChart_range k r n hr hr3 hE D a i x).mpr ⟨p, hp⟩
    exact ⟨i, q, hq⟩

lemma left_component_pullback (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    CategoryTheory.IsPullback (leftClosedMap k n (a j) (a (next r hr j)))
      (leftOpen k).ι (complementChart k r n hr hr3 hE D a j)
      (complementComponent k r n hr hr3 hE D a j) := by
  apply IsOpenImmersion.isPullback
  · apply (cancel_mono (divisorComplement k r n hr D a).ι).mp
    simp only [Category.assoc, complementComponent_fac, complementChart_fac]
    rw [← Category.assoc, leftClosedMap_fac]
    exact left_component k r n hr hE D j (a (next r hr j))
  · rw [Scheme.Opens.opensRange_ι]
    ext p
    change complementComponent k r n hr hr3 hE D a j p ∈
      Set.range (complementChart k r n hr hr3 hE D a j) ↔ p ∈ leftOpen k
    rw [complementChart_range]
    change (complementComponent k r n hr hr3 hE D a j ≫
      (divisorComplement k r n hr D a).ι) p ∈ Set.range (D.chart j) ↔ _
    rw [complementComponent_fac]
    exact component_mem_left_chart k r n hr hE D j (a (next r hr j)) p

lemma right_component_pullback (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    CategoryTheory.IsPullback
      (rightClosedMap k n (a (next r hr j)) (a (next r hr (next r hr j))))
      (rightOpen k).ι (complementChart k r n hr hr3 hE D a (next r hr j))
      (complementComponent k r n hr hr3 hE D a j) := by
  apply IsOpenImmersion.isPullback
  · apply (cancel_mono (divisorComplement k r n hr D a).ι).mp
    simp only [Category.assoc, complementComponent_fac, complementChart_fac]
    rw [← Category.assoc, rightClosedMap_fac]
    exact right_component k r n hr hE D j (a (next r hr j))
  · rw [Scheme.Opens.opensRange_ι]
    ext p
    change complementComponent k r n hr hr3 hE D a j p ∈
      Set.range (complementChart k r n hr hr3 hE D a (next r hr j)) ↔ p ∈ rightOpen k
    rw [complementChart_range]
    change (complementComponent k r n hr hr3 hE D a j ≫
      (divisorComplement k r n hr D a).ι) p ∈ Set.range (D.chart (next r hr j)) ↔ _
    rw [complementComponent_fac]
    exact component_mem_right_chart k r n hr hE D j (a (next r hr j)) p

/-- Each parametrized affine line is a closed subscheme of the marked complement. -/
lemma complementComponent_closed (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) (j : Fin r) :
    IsClosedImmersion (complementComponent k r n hr hr3 hE D a j) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (complementCover k r n hr hr3 hE D a)
  intro i
  change IsClosedImmersion (CategoryTheory.Limits.pullback.snd
    (complementComponent k r n hr hr3 hE D a j) (complementChart k r n hr hr3 hE D a i))
  by_cases hi : i = j
  · subst i
    rw [← (left_component_pullback k r n hr hr3 hE D a j).flip.isoPullback_inv_snd]
    infer_instance
  by_cases hn : i = next r hr j
  · subst i
    rw [← (right_component_pullback k r n hr hr3 hE D a j).flip.isoPullback_inv_snd]
    infer_instance
  let f := complementComponent k r n hr hr3 hE D a j
  let c := complementChart k r n hr hr3 hE D a i
  have hempty : IsEmpty (CategoryTheory.Limits.pullback f c : Scheme.{u}) := by
    constructor
    intro z
    have h := congrArg (fun g => g z) (CategoryTheory.Limits.pullback.condition (f := f) (g := c))
    change f (CategoryTheory.Limits.pullback.fst f c z) =
      c (CategoryTheory.Limits.pullback.snd f c z) at h
    have hx := (complementChart_range k r n hr hr3 hE D a i
      (f (CategoryTheory.Limits.pullback.fst f c z))).mp
        ⟨CategoryTheory.Limits.pullback.snd f c z, h.symm⟩
    change (f ≫ (divisorComplement k r n hr D a).ι)
      (CategoryTheory.Limits.pullback.fst f c z) ∈ Set.range (D.chart i) at hx
    rw [complementComponent_fac] at hx
    exact (component_charts k r n hr hE D i j (a (next r hr j)) _ hx).elim hi hn
  apply IsClosedImmersion.of_isPreimmersion
  simp only [Set.range_eq_empty, isClosed_empty]

def constantBase : k →+* R k n :=
  (trunc (PowerSeries k) PowerSeries.X n).comp PowerSeries.C

lemma residueBase_factor {F : Type u} [Field F] (g : R k n →+* F) :
    g = (g.comp (constantBase k n)).comp (residueBase k n) := by
  apply RingHom.ext
  intro c
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hzero : g (trunc (PowerSeries k) PowerSeries.X n PowerSeries.X) = 0 :=
    parameter_map_eq_zero g
  have he := congrArg (g.comp (trunc (PowerSeries k) PowerSeries.X n))
    (PowerSeries.eq_X_mul_shift_add_const s)
  simp only [map_add, map_mul, RingHom.comp_apply, hzero, zero_mul, zero_add] at he
  exact he

lemma section_evaluation (p : Polynomial k) {F : Type u} [Field F] [Algebra k F]
    (z : F) (hu : IsUnit (Polynomial.eval₂RingHom (algebraMap k F) z p)) :
    ∃ ρ : Γ(line k, PrimeSpectrum.basicOpen p) →ₐ[k] F,
      ∀ q, ρ (sectionMap k _ q) = Polynomial.eval₂RingHom (algebraMap k F) z q := by
  let f := Polynomial.eval₂RingHom (algebraMap k F) z
  letI : IsLocalization.Away p Γ(line k, PrimeSpectrum.basicOpen p) :=
    StructureSheaf.IsLocalization.to_basicOpen (Polynomial k) p
  let ρ : Γ(line k, PrimeSpectrum.basicOpen p) →+* F :=
    IsLocalization.Away.lift p hu
  have hρ (q : Polynomial k) : ρ (sectionMap k _ q) = f q := by
    rw [sectionMap_eq_algebraMap]
    exact IsLocalization.Away.lift_eq _ hu q
  refine ⟨{ ρ with commutes' := ?_ }, hρ⟩
  intro c
  change ρ (sectionMap k _ (Polynomial.C c)) = _
  rw [hρ]
  simp [f]

lemma right_field_factor {F : Type u} [Field F] [Algebra k F]
    (g : A k n →+* F) (a : kˣ)
    (hb : g.comp (base k n) = (algebraMap k F).comp (residueBase k n))
    (hy : g (coordY k n) = 0) (ha : g (markedEquation k n a) ≠ 0) :
    ∃ ρ : Γ(line k, rightOpen k) →ₐ[k] F,
      ρ.toRingHom.comp (rightPoint k n (S := Γ(line k, rightOpen k)) a
        (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)) = g := by
  let x := g (coordX k n)
  let c := algebraMap k F (a : k)
  have hc : c ≠ 0 := (a.isUnit.map (algebraMap k F)).ne_zero
  have he : g (markedEquation k n a) = x - c := by
    rw [markedEquation, map_sub]
    have h := RingHom.congr_fun hb (markedUnit k n a)
    simpa [x, c, residueBase_markedUnit] using congrArg (fun y => g (coordX k n) - y) h
  have hxc : x - c ≠ 0 := he ▸ ha
  let z := x / (x - c)
  have hz : z - 1 = c / (x - c) := by dsimp [z]; field_simp; ring
  obtain ⟨ρ, hρ⟩ := section_evaluation k (Polynomial.X - 1) z
    (by simpa only [map_sub, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_one, hz] using
      (isUnit_iff_ne_zero.mpr (div_ne_zero hc hxc)))
  refine ⟨ρ, ?_⟩
  have hZ : ρ (sectionMap k (rightOpen k) Polynomial.X) = z := by
    exact (hρ Polynomial.X).trans (Polynomial.eval₂_X _ _)
  have hd : ρ (rightDenominator k : Γ(line k, rightOpen k)) = z - 1 := by
    rw [rightDenominator_val, map_sub, map_one, hZ]
  have hdi : ρ (↑(rightDenominator k)⁻¹ : Γ(line k, rightOpen k)) = (z - 1)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hd, ← map_mul, Units.inv_mul, map_one]
  apply point_ext
  · apply RingHom.ext
    intro t
    simp only [RingHom.comp_apply, rightPoint_base]
    exact (ρ.commutes _).trans (RingHom.congr_fun hb t).symm
  · change ρ (rightPoint k n (S := Γ(line k, rightOpen k)) a
      (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k) (coordX k n)) = x
    have hC : ρ (algebraMap k Γ(line k, rightOpen k) (a : k)) = c := ρ.commutes _
    rw [rightPoint_x, map_mul, map_mul, hC, hZ, hdi]
    change c * z * (z - 1)⁻¹ = x
    rw [hz]
    dsimp [z]
    field_simp
  · simp only [RingHom.comp_apply, rightPoint_y, map_zero, hy]

lemma left_field_factor {F : Type u} [Field F] [Algebra k F]
    (g : A k n →+* F) (b : kˣ)
    (hb : g.comp (base k n) = (algebraMap k F).comp (residueBase k n))
    (hx : g (coordX k n) = 0)
    (ha : g (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) ≠ 0) :
    ∃ ρ : Γ(line k, leftOpen k) →ₐ[k] F,
      ρ.toRingHom.comp (leftPoint k n (S := Γ(line k, leftOpen k)) b
        (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)) = g := by
  let y := g (coordY k n)
  let c := algebraMap k F (↑b⁻¹ : k)
  have hc : c ≠ 0 := (b⁻¹.isUnit.map (algebraMap k F)).ne_zero
  have he : g (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) = y - c := by
    have hb' : (↑((markedUnit k n b)⁻¹) : R k n) = markedUnit k n b⁻¹ := by simp [markedUnit]
    rw [map_sub, hb']
    have h := RingHom.congr_fun hb (markedUnit k n b⁻¹)
    simpa [y, c, residueBase_markedUnit] using congrArg (fun t => g (coordY k n) - t) h
  have hyc : y - c ≠ 0 := he ▸ ha
  let z := -c / (y - c)
  have hz : z ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc) hyc
  obtain ⟨ρ, hρ⟩ := section_evaluation k Polynomial.X z
    (by simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using isUnit_iff_ne_zero.mpr hz)
  refine ⟨ρ, ?_⟩
  have hZ : ρ (sectionMap k (leftOpen k) Polynomial.X) = z :=
    (hρ Polynomial.X).trans (Polynomial.eval₂_X _ _)
  have hv : ρ (leftDenominator k : Γ(line k, leftOpen k)) = z := by
    rw [leftDenominator_val, hZ]
  have hvi : ρ (↑(leftDenominator k)⁻¹ : Γ(line k, leftOpen k)) = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hv, ← map_mul, Units.inv_mul, map_one]
  apply point_ext
  · apply RingHom.ext
    intro t
    simp only [RingHom.comp_apply, leftPoint_base]
    exact (ρ.commutes _).trans (RingHom.congr_fun hb t).symm
  · simp only [RingHom.comp_apply, leftPoint_x, map_zero, hx]
  · change ρ (leftPoint k n (S := Γ(line k, leftOpen k)) b
      (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k) (coordY k n)) = y
    have hC : ρ (algebraMap k Γ(line k, leftOpen k) (↑b⁻¹ : k)) = c := ρ.commutes _
    rw [leftPoint_y, map_mul, map_mul, map_sub, map_one, hC, hZ, hvi]
    dsimp [z]
    field_simp
    ring

lemma right_field_component_factor {F : Type u} [Field F] [Algebra k F]
    (hE : IsAdjacent k n E) (D : Atlas k r n hr E) (j : Fin r) (a : kˣ)
    (g : A k n →+* F)
    (hb : g.comp (base k n) = (algebraMap k F).comp (residueBase k n))
    (hy : g (coordY k n) = 0) (ha : g (markedEquation k n a) ≠ 0) :
    ∃ f : Spec (CommRingCat.of F) ⟶ line k,
      f ≫ component k r n hr hE D j a = Spec.map (CommRingCat.ofHom g) ≫
        D.chart (next r hr j) := by
  obtain ⟨ρ, hρ⟩ := right_field_factor k n g a hb hy ha
  let e := (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k))
    (Polynomial.X - 1)).isoSpec
  refine ⟨Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ e.inv ≫ (rightOpen k).ι, ?_⟩
  rw [Category.assoc, Category.assoc, right_component]
  change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ e.inv ≫
    (rightOpen k).toSpecΓ ≫ _ = _
  have hei : e.inv ≫ (rightOpen k).toSpecΓ = 𝟙 _ := e.inv_hom_id
  rw [← Category.assoc e.inv, hei, Category.id_comp,
    ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (rightPoint k n (S := Γ(line k, rightOpen k)) a
      (sectionMap k (rightOpen k) Polynomial.X) (rightDenominator k)) ≫
      CommRingCat.ofHom ρ.toRingHom = CommRingCat.ofHom g :=
    congrArg CommRingCat.ofHom hρ
  rw [he]

lemma left_field_component_factor {F : Type u} [Field F] [Algebra k F]
    (hE : IsAdjacent k n E) (D : Atlas k r n hr E) (j : Fin r) (b : kˣ)
    (g : A k n →+* F)
    (hb : g.comp (base k n) = (algebraMap k F).comp (residueBase k n))
    (hx : g (coordX k n) = 0)
    (ha : g (coordY k n - base k n (↑((markedUnit k n b)⁻¹))) ≠ 0) :
    ∃ f : Spec (CommRingCat.of F) ⟶ line k,
      f ≫ component k r n hr hE D j b = Spec.map (CommRingCat.ofHom g) ≫ D.chart j := by
  obtain ⟨ρ, hρ⟩ := left_field_factor k n g b hb hx ha
  let e := (IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k)) Polynomial.X).isoSpec
  refine ⟨Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ e.inv ≫ (leftOpen k).ι, ?_⟩
  rw [Category.assoc, Category.assoc, left_component]
  change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ e.inv ≫
    (leftOpen k).toSpecΓ ≫ _ = _
  have hei : e.inv ≫ (leftOpen k).toSpecΓ = 𝟙 _ := e.inv_hom_id
  rw [← Category.assoc e.inv, hei, Category.id_comp,
    ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (leftPoint k n (S := Γ(line k, leftOpen k)) b
      (sectionMap k (leftOpen k) Polynomial.X) (leftDenominator k)) ≫
      CommRingCat.ofHom ρ.toRingHom = CommRingCat.ofHom g :=
    congrArg CommRingCat.ofHom hρ
  rw [he]

/-- All points of the complement are contained in one of the closed affine lines. -/
lemma complementComponent_covers (hr3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (D : Atlas k r n hr E) (a : Fin r → kˣ) :
    ⋃ j, Set.range (complementComponent k r n hr hr3 hE D a j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, p, hp⟩ := D.covers ((divisorComplement k r n hr D a).ι x)
  have hpcomp : p ∈ PrimeSpectrum.basicOpen (pairEquation k n (a i) (a (next r hr i))) := by
    rw [← chart_preimage_complement k r n hr hr3 hE D a i]
    change D.chart i p ∈ divisorComplement k r n hr D a
    rw [hp]
    exact x.property
  let F := p.asIdeal.ResidueField
  let g : A k n →+* F := algebraMap (A k n) F
  let α := (g.comp (base k n)).comp (constantBase k n)
  letI : Algebra k F := α.toAlgebra
  have hb : g.comp (base k n) = (algebraMap k F).comp (residueBase k n) :=
    residueBase_factor k n (g.comp (base k n))
  have hpair : g (pairEquation k n (a i) (a (next r hr i))) ≠ 0 := by
    exact fun h => hpcomp (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hprod := point_coordinates_mul_eq_zero g
  have hpoint : ∃ t : Spec (CommRingCat.of F), Spec.map (CommRingCat.ofHom g) t = p := by
    have h := PrimeSpectrum.residueField_comap p
    have hmem : p ∈ Set.range (PrimeSpectrum.comap g) := by rw [h]; exact Set.mem_singleton p
    exact hmem
  obtain ⟨t, ht⟩ := hpoint
  have finish (j : Fin r) (f : Spec (CommRingCat.of F) ⟶ line k)
      (hf : f ≫ component k r n hr hE D j (a (next r hr j)) =
        Spec.map (CommRingCat.ofHom g) ≫ D.chart i) :
      x ∈ ⋃ j, Set.range (complementComponent k r n hr hr3 hE D a j) := by
    refine Set.mem_iUnion.mpr ⟨j, f t, (divisorComplement k r n hr D a).ι.isOpenEmbedding.injective ?_⟩
    change (complementComponent k r n hr hr3 hE D a j ≫
      (divisorComplement k r n hr D a).ι) (f t) = _
    rw [complementComponent_fac, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply, ht]
    exact hp
  rcases mul_eq_zero.mp hprod with hx | hy
  · have ha : g (coordY k n - base k n (↑((markedUnit k n (a (next r hr i)))⁻¹))) ≠ 0 := by
      intro h
      apply hpair
      rw [pairEquation, map_mul, h, mul_zero]
    obtain ⟨f, hf⟩ := left_field_component_factor k r n hr hE D i (a (next r hr i)) g hb hx ha
    exact finish i f hf
  · have ha : g (markedEquation k n (a i)) ≠ 0 := by
      intro h
      apply hpair
      rw [pairEquation, map_mul, h, zero_mul]
    obtain ⟨j, hj⟩ := next_surjective r hr i
    obtain ⟨f, hf⟩ := right_field_component_factor k r n hr hE D j (a i) g hb hy ha
    exact finish j f (by simpa [hj] using hf)

end ComponentParametrization

end AffineMarkedComplementR0133

/-- The complement of one unit-valued marking in every component position of
an infinitesimal Tate polygon is affine, at every thickness. -/
theorem affine_marked_complement :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
        ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
      ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
      ∀ (D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E) (a : Fin r → kˣ),
      AlgebraicGeometry.IsAffine ((ArithmeticThetaPolygonCartierR0133.divisorComplement
        k r n hr D a).toScheme) := by
  intro k _ _ r n hr hr3 E hE D a
  exact AffineMarkedComplementR0133.ClosedAffineCover.affine_of_finite_closed _ r
    (fun _ => AffineMarkedComplementR0133.ComponentParametrization.line k)
    (AffineMarkedComplementR0133.ComponentParametrization.complementComponent k r n hr hr3 hE D a)
    (AffineMarkedComplementR0133.ComponentParametrization.complementComponent_closed k r n hr hr3 hE D a)
    (fun _ => by unfold AffineMarkedComplementR0133.ComponentParametrization.line; infer_instance)
    (AffineMarkedComplementR0133.ComponentParametrization.complementComponent_covers k r n hr hr3 hE D a)

end ArithmeticThetaPolygonCartierR0133

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.chart_preimage_complement

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.complement_affine_of_zero

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ClosedAffineCover.affine_of_finite_closed

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.adjacent_branch_points

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.right_branch_in_complement

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.left_branch_in_complement

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.complementComponent_fac

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.rightClosedMap_isClosedImmersion
#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.leftClosedMap_isClosedImmersion

#print axioms ArithmeticThetaPolygonCartierR0133.AffineMarkedComplementR0133.ComponentParametrization.complementComponent_closed

#print axioms ArithmeticThetaPolygonCartierR0133.affine_marked_complement
