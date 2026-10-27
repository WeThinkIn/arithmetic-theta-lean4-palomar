import LocalWeierstrassDefinitionsR0203

/-! Positive identity-ideal cohomology over arbitrary Noetherian rational rings.
The geometric fibre arguments generalize the r0174 wrappers; the accepted
field, Cech, and finite-projective base-change engines are reused unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaLocalWeierstrassR0203
namespace NoetherianPositiveCohomology
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.FibreCohomology
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Vanishing
open scoped TensorProduct

lemma origin_geometric_genus (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ Spec (.of R)) (L : Type u) [Field L] [Algebra K L]
    (M : CurveModel K L) (e : M.C ≅ pullback Q.structureMap s)
    (he : e.hom ≫ pullback.snd Q.structureMap s = M.toBase) (Kc : Divisor K L) (g' : ℕ)
    (hRR : ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') :
    g' = 1 := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one
  letI : GeometricallyIntegral Q.structureMap := Q.geometry.geometricallyIntegral_of_commRing
  let QK := Q.geometry.baseChange_of_field s
  obtain ⟨LG⟩ := QK.hasGroupLaw
  exact group_curveModel_genus (pullback.snd Q.structureMap s) LG L M e he Kc g' hRR

open AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory

/-- Positive origin powers have vanishing H¹ and rank equal to the pole bound
on every field fibre, with its actual structural map. -/
lemma origin_fibre_positive_cohomology (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] (sK : Spec (.of K) ⟶ Spec (.of R))
    (𝒱 : (pullback Q.structureMap sK).TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).H1 ∧
    Module.finrank K (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).H0 = m := by
  let c := Q.structureMap
  let C := Q.target
  let ε := Q.law.one (𝟙 _)
  letI : IsProper c := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 c := Q.smooth_dimension_one
  letI : GeometricallyIntegral c := Q.geometry.geometricallyIntegral_of_commRing
  have hg := origin_geometric_genus R Q

  let S : Scheme.{u} := Spec (CommRingCat.of R)
  let ψ : SchemeHomOver sK (𝟙 S) := ⟨sK, Category.comp_id _⟩
  let g' : pullback c sK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg'π : g' ≫ π = pullback.fst c sK := by
    simp only [g', π, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c (𝟙 S) = pullback.snd c sK ≫ sK := by
    simp only [g', baseChangeSnd, pullback.lift_snd]
    rfl

  have hcart : IsPullback g' (pullback.snd c sK) (pullback.snd c (𝟙 S)) sK := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c (𝟙 S))
    rw [hg'π, Category.comp_id]
    exact IsPullback.of_hasPullback c sK

  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hI : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 hεc
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσ : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S := by
    simp only [rigSection, pullback.lift_snd]
  have hI' : (rigSection c (𝟙 S) ε).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ
  have hσπ : rigSection c (𝟙 S) ε ≫ π = ε.1 := by
    simp only [rigSection, π, pullback.lift_fst, Category.id_comp]

  obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
    (rigSection c (𝟙 S) ε) hσπ hI hI' m).1

  let N : C.Modules := (ε.1.ker ^ m).invModule
  let M : (pullback c (𝟙 S)).Modules :=
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)).L ⊗ sectionTwist c ε (𝟙 S) m
  have eS : (Scheme.Modules.pullback π).obj N ≅ M :=
    eπ ≪≫ (λ_ (sectionTwist c ε (𝟙 S) m)).symm
  have e : (Scheme.Modules.pullback (pullback.fst c sK)).obj N ≅ (Scheme.Modules.pullback g').obj M :=
    (Scheme.Modules.pullbackCongr hg'π.symm).app N ≪≫ ((Scheme.Modules.pullbackComp g' π).app N).symm ≪≫
      (Scheme.Modules.pullback g').mapIso eS

  obtain ⟨𝒲, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c (𝟙 S) M sK
      (pullback.snd c sK) g' hcart ((Scheme.Modules.pullback (pullback.fst c sK)).obj N) e 𝒱

  obtain ⟨h1, h0⟩ :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
      R c ε 1 hg (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)) (fibrewiseAlgEquivZero_unit (𝟙 S)) m (by omega) K sK 𝒲
  haveI := h1
  exact ⟨eH1.toEquiv.subsingleton, eH0.finrank_eq.trans (by simpa using h0)⟩

/-- On every geometric fibre the two-chart cover is constructed, and the
positive-degree cohomology statements hold for every pole bound. -/
lemma origin_exists_fibre_positive_cohomology_cover
    (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (K : Type u) [Field K] [IsAlgClosed K] (sK : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ 𝒱 : (pullback Q.structureMap sK).TwoAffineOpenCover, ∀ m : ℕ, 0 < m →
      Subsingleton (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
        ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
          (((Q.zero).ker ^ m).invModule))).H1 ∧
      Module.finrank K (𝒱.sectionsOf (pullback.snd Q.structureMap sK)
        ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
          (((Q.zero).ker ^ m).invModule))).H0 = m := by
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : SmoothOfRelativeDimension 1 Q.structureMap := Q.smooth_dimension_one
  letI : GeometricallyIntegral Q.structureMap := Q.geometry.geometricallyIntegral_of_commRing
  obtain ⟨LG⟩ := (Q.geometry.baseChange_of_field sK).hasGroupLaw
  obtain ⟨𝒱,-⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed K
    (pullback.snd Q.structureMap sK) ((LG.one (𝟙 _)).val (IsLocalRing.closedPoint K))
  exact ⟨𝒱, fun m hm => origin_fibre_positive_cohomology R Q m hm K sK 𝒱⟩

lemma fibre_vanishing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] (sK : Spec (.of K) ⟶ Spec (.of R))
    (𝒰 : (pullback Q.structureMap sK).OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules (pullback.snd Q.structureMap sK)
      ((Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj
        (((Q.zero).ker ^ m).invModule))).HSucc 𝒰 i) := by
  let c := Q.structureMap
  let M := ((Q.zero).ker ^ m).invModule
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  letI : IsProper c := Q.geometry.proper
  let π := pullback.snd c sK
  let MK := (Scheme.Modules.pullback (pullback.fst c sK)).obj M
  let s : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Scheme.TwoAffineOpenCover.specMap K (AlgebraicClosure K)
  apply descend_field_vanishing π MK (hM.pullback _) 𝒰 (AlgebraicClosure K) ?_ i
  intro j
  let ψ : SchemeHomOver (s ≫ sK) sK := ⟨s, rfl⟩
  let g' : pullback c (s ≫ sK) ⟶ pullback c sK := RelPicard.baseChangeSnd c ψ
  let y := pullback.snd c (s ≫ sK)
  have hgf : g' ≫ pullback.fst c sK = pullback.fst c (s ≫ sK) := by
    simp only [g', RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hgs : g' ≫ π = y ≫ s := by
    simp only [g', π, RelPicard.baseChangeSnd, pullback.lift_snd]
    rfl
  have hcart : IsPullback g' y π s := by
    refine IsPullback.of_right ?_ hgs (IsPullback.of_hasPullback c sK)
    rw [hgf]
    exact IsPullback.of_hasPullback c (s ≫ sK)
  let F := (Scheme.Modules.pullback (pullback.fst c (s ≫ sK))).obj M
  let e : F ≅ (Scheme.Modules.pullback g').obj MK :=
    (Scheme.Modules.pullbackCongr hgf.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp g' (pullback.fst c sK)).app M).symm
  obtain ⟨𝒱,h𝒱⟩ := origin_exists_fibre_positive_cohomology_cover
    R Q (AlgebraicClosure K) (s ≫ sK)
  obtain ⟨𝒲,-,⟨eH⟩⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    c sK MK s y g' hcart F e 𝒱
  haveI : Subsingleton (𝒱.sectionsOf y F).H1 := (h𝒱 m hm).1
  have hW : Subsingleton (𝒲.sectionsOf (pullback.snd π s)
      ((Scheme.Modules.pullback (pullback.fst π s)).obj MK)).H1 :=
    eH.symm.toEquiv.subsingleton
  exact all_covers_of_two_chart (pullback.snd π s) _
    ((hM.pullback (pullback.fst c sK)).pullback (pullback.fst π s)) 𝒲 hW
    (𝒰.baseChange π (AlgebraicClosure K)) j


/-- Positive origin-power sections are finite projective and commute with
arbitrary ring base change, by the actual pullback of local sections. -/
lemma positive_sections_baseChange (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) :
    let f := Q.structureMap
    let M := ((Q.zero).ker ^ m).invModule
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (x : Γ(M, ⊤)),
          e (a ⊗ₜ[R] x) = a • Scheme.Modules.pullbackLocalSection
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) x := by
  let M := ((Q.zero).ker ^ m).invModule
  letI : IsProper Q.structureMap := Q.geometry.proper
  letI : Smooth Q.structureMap := Q.geometry.smooth
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  apply ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.solution Q.structureMap M hM.1
  intro K _ _
  let sK := Scheme.TwoAffineOpenCover.specMap R K
  haveI : CompactSpace (pullback Q.structureMap sK : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Q.structureMap sK)
  let 𝒰 := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections.Sections.P2mSectionsBaseChangeH0.coverOfCompact
    (pullback Q.structureMap sK)
  exact ⟨𝒰, fun i => fibre_vanishing R Q m hm K sK 𝒰 i⟩

#print axioms positive_sections_baseChange

#print axioms fibre_vanishing

open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections

lemma positive_higher_cohomology (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (𝒰 : Q.target.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules Q.structureMap
      (((Q.zero).ker ^ m).invModule)).HSucc 𝒰 i) := by
  let f := Q.structureMap
  let M := ((Q.zero).ker ^ m).invModule
  let F := OModulePresheaf.ofModules f M
  letI : IsProper f := Q.geometry.proper
  letI : Smooth f := Q.geometry.smooth
  have hM : Scheme.Modules.IsInvertible M :=
    ((Q.zero_ideal_invertible).pow m).isInvertible_invModule
  haveI : ∀ j, Module.Flat R (F.cochain 𝒰 j) := fun j =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M hM.1 𝒰 j
  have hdd : ∀ j, F.d 𝒰 (j + 1) ∘ₗ F.d 𝒰 j = 0 := fun j => OModulePresheaf.d_comp_d F 𝒰 j
  have hbd : ∀ j, Fintype.card 𝒰.ι ≤ j → Subsingleton (F.cochain 𝒰 j) :=
    fun j hj => Sections.Engine19.subsingleton_cochain F 𝒰 j hj
  have hCF : F.CechFinite 𝒰 :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M hM.1 𝒰
  have hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      LinearMap.ker ((F.d 𝒰 (j + 1)).baseChange K) ≤ LinearMap.range ((F.d 𝒰 j).baseChange K) := by
    intro K _ _ j
    let sK := Scheme.TwoAffineOpenCover.specMap R K
    haveI : Subsingleton ((OModulePresheaf.ofModules (pullback.snd f sK)
        ((Scheme.Modules.pullback (pullback.fst f sK)).obj M)).HSucc (𝒰.baseChange f K) j) :=
      fibre_vanishing R Q m hm K sK (𝒰.baseChange f K) j
    obtain ⟨φ,-,hφ⟩ := (Homology.solution f 𝒰 M hM.1 K).1.2 j
    exact Sections.Engine19.ker_le_range_of_subsingleton _ _ φ hφ
  obtain ⟨-,-,hAll⟩ :=
    Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
      (fun j => F.cochain 𝒰 j) (fun j => F.d 𝒰 j) hdd (Fintype.card 𝒰.ι) hbd hCF.1 hCF.2 hfib
  have hker : LinearMap.ker (F.d 𝒰 (i + 1)) ≤ LinearMap.range (F.d 𝒰 i) := by
    intro x hx
    have hxR : (1 : R) ⊗ₜ[R] x ∈ LinearMap.ker ((F.d 𝒰 (i + 1)).baseChange R) := by
      rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hx,
        TensorProduct.tmul_zero]
    obtain ⟨z,hz⟩ := hAll R i hxR
    refine ⟨TensorProduct.lid R _ z, ?_⟩
    have h := congrArg (TensorProduct.lid R _) hz
    rw [Sections.P2mSectionsBaseChangeH0.lid_baseChange_apply, TensorProduct.lid_tmul,
      one_smul] at h
    exact h
  have htop : (LinearMap.range (F.d 𝒰 i)).comap (LinearMap.ker (F.d 𝒰 (i + 1))).subtype = ⊤ := by
    apply top_unique
    intro x _
    exact hker x.property
  change Subsingleton (LinearMap.ker (F.d 𝒰 (i + 1)) ⧸ _)
  rw [htop]
  infer_instance

#print axioms positive_higher_cohomology


lemma positive_sections_geometric_rank (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra ℚ R]
    (Q : FramedCurve R)
    (m : ℕ) (hm : 0 < m) (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
    let M := ((Q.zero).ker ^ m).invModule
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
    Module.finrank K (K ⊗[R] Γ(M,⊤)) = m := by
  let M := ((Q.zero).ker ^ m).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  let sK := Scheme.TwoAffineOpenCover.specMap R K
  let MK := (Scheme.Modules.pullback (pullback.fst Q.structureMap sK)).obj M
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd Q.structureMap sK) MK ⊤
  obtain ⟨e,-⟩ := (positive_sections_baseChange R Q m hm).2 K
  obtain ⟨𝒱,h𝒱⟩ := origin_exists_fibre_positive_cohomology_cover R Q K sK
  obtain ⟨eH,-⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 (pullback.snd Q.structureMap sK) MK
  let e' : K ⊗[R] Γ(M,⊤) ≃ₗ[K] Γ(MK,⊤) := e
  exact e'.finrank_eq.trans (eH.finrank_eq.trans (h𝒱 m hm).2)

#print axioms positive_sections_geometric_rank
end NoetherianPositiveCohomology

open AlgebraicGeometry

/-- Finite projectivity, actual arbitrary base change, positive Cech vanishing,
and finite-dimensional geometric rank over every Noetherian rational base. -/
theorem noetherian_positive_cohomology
    (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    (Q : FramedCurve R) : PositiveCohomology R Q := by
  intro m hm
  obtain ⟨hfinite, hbase⟩ := NoetherianPositiveCohomology.positive_sections_baseChange R Q m hm
  refine ⟨hfinite, hbase, NoetherianPositiveCohomology.positive_higher_cohomology R Q m hm, ?_⟩
  intro K _ _ _
  let M := (Q.zero.ker ^ m).invModule
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
  letI : Module.Finite R Γ(M, ⊤) := hfinite.1
  exact ⟨inferInstance, NoetherianPositiveCohomology.positive_sections_geometric_rank R Q m hm K⟩

#print axioms noetherian_positive_cohomology
end ArithmeticThetaLocalWeierstrassR0203
