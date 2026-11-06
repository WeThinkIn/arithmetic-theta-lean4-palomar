module

public import NoetherianPositiveCohomologyR0203

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaLocalWeierstrassR0203.NoetherianPoleFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open Conormal SectionExact

lemma origin_conormal_trivial (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R) :
    Nonempty ((SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules) ≅
      (Scheme.Modules.pullback (Q.zero)).obj (Q.zero).ker.module) := by
  let c := Q.structureMap
  let e := Q.zero
  have he : e ≫ c = 𝟙 _ := Q.zero_over
  letI : IsProper c := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 c := Q.smooth_dimension_one
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ c) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e c
  have hΩ : Scheme.Modules.IsInvertible c.kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (c.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  haveI : IsIso (conormalMap c e) :=
    section_conormal_isIso c e he (Q.zero_ideal_invertible) hΩ
  obtain ⟨η⟩ := Q.hodge_trivial
  exact ⟨η ≪≫ (asIso (conormalMap c e)).symm⟩

lemma origin_power_restriction_trivial (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    Nonempty ((Scheme.Modules.pullback (Q.zero)).obj
      ((Q.zero).ker ^ m).invModule ≅ 𝟙_ (Spec (.of R)).Modules) := by
  obtain ⟨η⟩ := origin_conormal_trivial R Q
  exact pullback_pow_invModule_trivial (Q.zero) _
    (Q.zero_ideal_invertible) ⟨η.symm⟩ m hm

lemma origin_shortExact (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) :
    ∃ S : ShortComplex Q.target.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ ((Q.zero).ker ^ m).invModule) ∧
      Nonempty (S.X₂ ≅ ((Q.zero).ker ^ (m+1)).invModule) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (Q.zero)).obj
        (𝟙_ (Spec (.of R)).Modules)) := by
  let e := Q.zero
  let I := e.ker
  let M := (I ^ (m+1)).invModule
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ Q.structureMap) := by
      rw [Q.zero_over]; infer_instance
    exact IsClosedImmersion.of_comp e Q.structureMap
  have hI : I.IsInvertible := Q.zero_ideal_invertible
  have hM : Scheme.Modules.IsInvertible M := (hI.pow (m+1)).isInvertible_invModule
  obtain ⟨S,hS,⟨α⟩,h₂,⟨γ⟩⟩ := Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
    e M ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible M).mpr hM)
  obtain ⟨β⟩ := ideal_tensor_succ_inv I hI m
  obtain ⟨η⟩ := origin_power_restriction_trivial R Q (m+1) (Nat.succ_pos _)
  exact ⟨S,hS,⟨α ≪≫ β⟩,h₂,⟨γ ≪≫ (Scheme.Modules.pushforward e).mapIso η⟩⟩

lemma origin_global_shortExact (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    ∃ S : ShortComplex Q.target.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ ((Q.zero).ker ^ m).invModule) ∧
      Nonempty (S.X₂ ≅ ((Q.zero).ker ^ (m+1)).invModule) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward (Q.zero)).obj
        (𝟙_ (Spec (.of R)).Modules)) ∧ Function.Surjective (S.g.app ⊤) := by
  obtain ⟨S,hS,⟨α⟩,h₂,h₃⟩ := origin_shortExact R Q m
  have hM : Scheme.Modules.IsInvertible S.X₁ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨η⟩⟩ := ((Q.zero_ideal_invertible).pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso α ≪≫ η⟩⟩
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : CompactSpace Q.target := QuasiCompact.compactSpace_of_compactSpace Q.structureMap
  let K := PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact Q.target
  have hH := (noetherian_positive_cohomology R Q m hm).2.2.1 K 0
  exact ⟨S,hS,⟨α⟩,h₂,h₃,surjective_global_sections Q.structureMap S hS hM K
    (subsingleton_higher_of_iso Q.structureMap α K 0 hH)⟩

lemma origin_sections_succ_split (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let M := ((Q.zero).ker ^ m).invModule
    let N := ((Q.zero).ker ^ (m+1)).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
    Nonempty (Γ(N,⊤) ≃ₗ[R] Γ(M,⊤) × R) := by
  let M := ((Q.zero).ker ^ m).invModule
  let N := ((Q.zero).ker ^ (m+1)).invModule
  let T := (Scheme.Modules.pushforward (Q.zero)).obj (𝟙_ (Spec (.of R)).Modules)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap T ⊤
  obtain ⟨S,hS,⟨α⟩,⟨β⟩,⟨γ⟩,hsurj⟩ := origin_global_shortExact R Q m hm
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₁ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₂ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₃ ⊤
  let e₁ := FibreCohomology.sectionsIsoLinear Q.structureMap α ⊤
  let e₂ := FibreCohomology.sectionsIsoLinear Q.structureMap β ⊤
  let e₃ := (FibreCohomology.sectionsIsoLinear Q.structureMap γ ⊤) ≪≫ₗ
    pushforward_unit_sections Q.structureMap (Q.zero) (Q.zero_over)
  letI : Module.Projective R Γ(S.X₃,⊤) := Module.Projective.of_equiv e₃.symm
  let f : Γ(S.X₁,⊤) →ₗ[R] Γ(S.X₂,⊤) := (ofModulesHom Q.structureMap S.f).app ⊤
  let g : Γ(S.X₂,⊤) →ₗ[R] Γ(S.X₃,⊤) := (ofModulesHom Q.structureMap S.g).app ⊤
  haveI := hS.mono_f
  have hf : Function.Injective f := (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f ⊤
  have hex : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      change S.g.app ⊤ (S.f.app ⊤ x) = 0
      exact congrArg (fun φ => φ.app ⊤ x) S.zero
    · intro x hx
      exact Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact ⊤ x hx
  obtain ⟨ε⟩ := split_linear_sequence f g hf hsurj hex
  exact ⟨e₂.symm ≪≫ₗ ε ≪≫ₗ e₁.prodCongr e₃⟩

lemma surjective_origin_restriction (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLocalWeierstrassR0203.FramedCurve R) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction Q.zero.ker.subschemeι).unit.app
      (Q.zero.ker ^ (m+1)).invModule).app ⊤) := by
  let I := Q.zero.ker
  let M := (I ^ m).invModule
  let N := (I ^ (m+1)).invModule
  have hI := Q.zero_ideal_invertible
  have hN : Scheme.Modules.IsLocallyFreeOfRank 1 N :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
      (hI.pow (m+1)).isInvertible_invModule
  obtain ⟨w,hS⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.Ws31IdealSES.exists_shortExact_unit I N hN
  let S := ShortComplex.mk ((N ◁ I.moduleι) ≫ (ρ_ N).hom) _ w
  obtain ⟨α⟩ := ideal_tensor_succ_inv I hI m
  let δ : N ⊗ I.module ≅ M := (β_ N I.module) ≪≫ α
  have hM : Scheme.Modules.IsInvertible (N ⊗ I.module) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U,hx,⟨η⟩⟩ := (hI.pow m).isInvertible_invModule.1 x
    exact ⟨U,hx,⟨(Scheme.Modules.pullback U.ι).mapIso δ ≪≫ η⟩⟩
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : CompactSpace Q.target := QuasiCompact.compactSpace_of_compactSpace Q.structureMap
  let K := PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact Q.target
  have hH := (noetherian_positive_cohomology R Q m hm).2.2.1 K 0
  exact surjective_global_sections Q.structureMap S hS hM K
    (subsingleton_higher_of_iso Q.structureMap δ K 0 hH)

lemma surjective_identity_restriction (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLocalWeierstrassR0203.FramedCurve R) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (Scheme.Modules.pullbackLocalSection Q.zero
      (L := (Q.zero.ker ^ (m+1)).invModule) (U := ⊤)) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  haveI : IsClosedImmersion (Q.zero ≫ Q.structureMap) := by
    rw [Q.zero_over]; infer_instance
  haveI : IsClosedImmersion Q.zero := IsClosedImmersion.of_comp _ Q.structureMap
  intro y
  exact Scheme.Modules.exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
    Q.zero.ker.subschemeι (asIso Q.zero.toImage) Q.zero Q.zero.toImage_imageι
    _ (surjective_origin_restriction R Q m hm) y

open scoped TensorProduct

/-- In a rank-one free module every linear functional obeys the scalar interchange law. -/
lemma rank_one_interchange {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (e : R ≃ₗ[R] M) (g : M →ₗ[R] R) (x y : M) : g x • y = g y • x := by
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  have he (a : R) : e a = a • e 1 := by simpa using e.map_smul a (1 : R)
  rw [he a, he b, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  simp only [smul_eq_mul]
  ring

lemma functional_zero_of_rank_one {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (e : R ≃ₗ[R] M)
    (f : R →ₗ[R] M) (g : M →ₗ[R] R) (hf : Function.Injective f)
    (hgf : g ∘ₗ f = 0) : g = 0 := by
  ext x
  apply hf
  calc
    f (g x) = g x • f 1 := by simpa using f.map_smul (g x) (1 : R)
    _ = g (f 1) • x := rank_one_interchange e g x (f 1)
    _ = f 0 := by simp [show g (f 1) = 0 from LinearMap.congr_fun hgf 1]

/-- Exactness and constant projective rank one replace the fraction-field argument. -/
lemma exact_projective_rank_one (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (f : R →ₗ[R] M) (g : M →ₗ[R] R) (hf : Function.Injective f)
    (hex : LinearMap.range f = LinearMap.ker g) : Function.Bijective f := by
  have hgf : g ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro r
    change g (f r) = 0
    exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f r)
  have hg : g = 0 := by
    ext x
    apply eq_zero_of_localization
    intro p hp
    letI := hp
    let A := Localization.AtPrime p
    letI : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
    have hrA : Module.finrank A (A ⊗[R] M) = 1 :=
      (Module.rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨p, inferInstance⟩).symm.trans (hr _)
    obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrA
    let ε := TensorProduct.AlgebraTensorModule.rid R A A
    let fA := (f.baseChange A) ∘ₗ ε.symm.toLinearMap
    let gA := ε.toLinearMap ∘ₗ (g.baseChange A)
    have hfA : Function.Injective fA :=
      (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp ε.symm.injective
    have hgfA : gA ∘ₗ fA = 0 := by
      apply LinearMap.ext
      intro a
      change ε ((g.baseChange A) ((f.baseChange A) (ε.symm a))) = 0
      have hh := LinearMap.congr_fun (congrArg (fun t => t.baseChange A) hgf) (ε.symm a)
      simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply,
        LinearMap.baseChange_zero, LinearMap.zero_apply, map_zero] using congrArg ε hh
    have hgA := functional_zero_of_rank_one e fA gA hfA hgfA
    have hh := LinearMap.congr_fun hgA ((1 : A) ⊗ₜ[R] x)
    simpa [gA, ε, LinearMap.baseChange_tmul, Algebra.smul_def] using hh
  exact ⟨hf, LinearMap.range_eq_top.mp (by rw [hex, hg, LinearMap.ker_zero])⟩

#print axioms exact_projective_rank_one

lemma rankAtStalk_one_of_geometric_rank (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (hr : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = 1) (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = 1 := by
  let F := p.asIdeal.ResidueField
  let K := AlgebraicClosure F
  let e : K ⊗[F] (F ⊗[R] M) ≃ₗ[K] K ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R F K K M
  rw [Module.rankAtStalk_eq]
  change Module.finrank F (F ⊗[R] M) = 1
  rw [← Module.finrank_baseChange (R := K) (S := F) (M' := F ⊗[R] M)]
  exact e.finrank_eq.trans (hr K)

lemma structure_app_bijective (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : ArithmeticThetaLocalWeierstrassR0203.FramedCurve R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Bijective (Q.structureMap.app U) := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : Smooth Q.structureMap := Q.geometry.smooth
  letI : GeometricallyIntegral Q.structureMap := Q.geometry.geometricallyIntegral_of_commRing
  letI : GeometricallyConnected Q.structureMap := ⟨by
    intro K _ y Z fst snd hpb
    letI : IsIntegral Z :=
      (Q.geometry.geometricallyIntegral_of_commRing).1 y fst snd hpb
    infer_instance⟩
  exact bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
    Q.structureMap U

lemma origin_first_sections (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R) :
    let M := ((Q.zero).ker ^ 1).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Nonempty (Γ(M,⊤) ≃ₗ[R] R) := by
  let I := (Q.zero).ker
  let M := (I ^ 1).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  obtain ⟨S,hS,⟨α⟩,⟨β⟩,⟨γ⟩⟩ := origin_shortExact R Q 0
  obtain ⟨δ⟩ := zero_power_inv_trivial I (Q.zero_ideal_invertible)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₁ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₂ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap S.X₃ ⊤
  let e₁ := (FibreCohomology.sectionsIsoLinear Q.structureMap (α ≪≫ δ) ⊤) ≪≫ₗ
    (unit_sections Q.structureMap (structure_app_bijective R Q ⊤)).symm
  let e₂ : Γ(S.X₂,⊤) ≃ₗ[R] Γ(M,⊤) := FibreCohomology.sectionsIsoLinear Q.structureMap β ⊤
  let e₃ := (FibreCohomology.sectionsIsoLinear Q.structureMap γ ⊤) ≪≫ₗ
    pushforward_unit_sections Q.structureMap (Q.zero) (Q.zero_over)
  let f₀ : Γ(S.X₁,⊤) →ₗ[R] Γ(S.X₂,⊤) := (ofModulesHom Q.structureMap S.f).app ⊤
  let g₀ : Γ(S.X₂,⊤) →ₗ[R] Γ(S.X₃,⊤) := (ofModulesHom Q.structureMap S.g).app ⊤
  let f := f₀ ∘ₗ e₁.symm.toLinearMap
  let g := e₃.toLinearMap ∘ₗ g₀
  haveI := hS.mono_f
  have hf₀ : Function.Injective f₀ := (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f ⊤
  have hex : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨r,rfl⟩
      change e₃ (S.g.app ⊤ (S.f.app ⊤ (e₁.symm r))) = 0
      rw [show S.g.app ⊤ (S.f.app ⊤ (e₁.symm r)) = 0 from
        congrArg (fun φ => φ.app ⊤ (e₁.symm r)) S.zero, map_zero]
    · intro x hx
      change e₃ (S.g.app ⊤ x) = 0 at hx
      have hx₀ : S.g.app ⊤ x = 0 := e₃.injective (by simpa only [map_zero] using hx)
      obtain ⟨y,hy⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact ⊤ x hx₀
      refine ⟨e₁ y, ?_⟩
      change S.f.app ⊤ (e₁.symm (e₁ y)) = x
      rw [e₁.symm_apply_apply]
      exact hy
  haveI : Module.Finite R Γ(M,⊤) :=
    (noetherian_positive_cohomology R Q 1 (by omega)).1.1
  letI : Module.Finite R Γ(S.X₂,⊤) := Module.Finite.equiv e₂.symm
  haveI : Module.Projective R Γ(M,⊤) :=
    (noetherian_positive_cohomology R Q 1 (by omega)).1.2
  letI : Module.Projective R Γ(S.X₂,⊤) := Module.Projective.of_equiv e₂.symm
  have hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(S.X₂,⊤) p = 1 := by
    apply rankAtStalk_one_of_geometric_rank R Γ(S.X₂,⊤)
    intro K _ _ _
    exact (e₂.baseChange R K _ _).finrank_eq.trans
      ((noetherian_positive_cohomology R Q 1 (by omega)).2.2.2 K).2
  have hf := exact_projective_rank_one R Γ(S.X₂,⊤) hr f g (hf₀.comp e₁.symm.injective) hex
  exact ⟨e₂.symm ≪≫ₗ (LinearEquiv.ofBijective f hf).symm⟩

#print axioms origin_first_sections

/-- The recursive bases use a singleton basis even when the base is the zero ring. -/
lemma origin_positive_sections_basis (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLocalWeierstrassR0203.FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let M := (Q.zero.ker ^ m).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Nonempty (Module.Basis (Fin m) R Γ(M,⊤)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    let M := (Q.zero.ker ^ 1).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    obtain ⟨e⟩ := origin_first_sections R Q
    exact ⟨(Module.Basis.singleton (Fin 1) R).map e.symm⟩
  | succ m hm ih =>
    let M := (Q.zero.ker ^ m).invModule
    let N := (Q.zero.ker ^ (m+1)).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap N ⊤
    obtain ⟨b⟩ := ih
    obtain ⟨e⟩ := origin_sections_succ_split R Q m hm
    exact ⟨((b.prod (Module.Basis.singleton (Fin 1) R)).reindex finSumFinEquiv).map e.symm⟩

end ArithmeticThetaLocalWeierstrassR0203.NoetherianPoleFiltration

namespace ArithmeticThetaLocalWeierstrassR0203
/-- Positive pole bases and the actual surjective restriction maps over every
Noetherian rational base, including nonreduced bases and the zero ring. -/
theorem noetherian_pole_filtration (R : Type u) [CommRing R] [Algebra ℚ R]
    [IsNoetherianRing R] (Q : FramedCurve R) : PositiveFiltration R Q := by
  intro m hm
  exact ⟨NoetherianPoleFiltration.origin_positive_sections_basis R Q m hm,
    NoetherianPoleFiltration.surjective_identity_restriction R Q m hm⟩

#print axioms noetherian_pole_filtration
end ArithmeticThetaLocalWeierstrassR0203
