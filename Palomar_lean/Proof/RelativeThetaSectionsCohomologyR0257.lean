module

public import RelativeSchrodingerDefinitionsR0257

@[expose] public section

/-! Cohomology and canonical scalar extension for the unframed theta line. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u

namespace ArithmeticThetaRelativeSchrodingerR0257
namespace RelativeThetaSectionsCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.PositiveSections
open Vanishing
open scoped TensorProduct

/-- The actual pulled-back theta line has positive cohomology on a geometric
fibre. Only a line over the field is trivialized here. -/
lemma geometric_fibre_cover {R K : Type u} [CommRing R] [Field K]
    [IsAlgClosed K] [Algebra ℚ K] (E : EllipticFamily R)
    (s : Spec (.of K) ⟶ Spec (.of R)) (m : ℕ) (hm : 0 < m) :
    ∃ 𝒱 : (pullback E.projection s).TwoAffineOpenCover,
      Subsingleton (𝒱.sectionsOf (pullback.snd E.projection s)
        ((Scheme.Modules.pullback (pullback.fst E.projection s)).obj (thetaLine E m))).H1 ∧
      Module.finrank K (𝒱.sectionsOf (pullback.snd E.projection s)
        ((Scheme.Modules.pullback (pullback.fst E.projection s)).obj (thetaLine E m))).H0 = m := by
  let F := baseChangedFamily E s
  letI : IsProper F.projection := F.proper
  letI : SmoothOfRelativeDimension 1 F.projection := F.smooth
  letI : GeometricallyIntegral F.projection :=
    (fieldFrame F).geometry.geometricallyIntegral_of_commRing
  obtain ⟨𝒱, _⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed K
    F.projection ((zero F) (IsLocalRing.closedPoint K))
  exact ⟨𝒱, field_line_cohomology F m hm _ (fibreLineIso E s m) 𝒱⟩

/-- All positive Cech cohomology vanishes on every field fibre. Descent from
the algebraic closure uses the existing faithfully flat cohomology comparison. -/
lemma fibre_vanishing {R K : Type u} [CommRing R] [Field K] [Algebra ℚ K]
    (E : EllipticFamily R) (sK : Spec (.of K) ⟶ Spec (.of R))
    (m : ℕ) (hm : 0 < m) (𝒰 : (pullback E.projection sK).OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules (pullback.snd E.projection sK)
      ((Scheme.Modules.pullback (pullback.fst E.projection sK)).obj (thetaLine E m))).HSucc 𝒰 i) := by
  let c := E.projection
  let M := thetaLine E m
  have hM := RelativeNormalizedThetaInversion.line_invertible E m
  letI : IsProper c := E.proper
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
  obtain ⟨𝒱, h𝒱, _⟩ := geometric_fibre_cover E (s ≫ sK) m hm
  obtain ⟨𝒲, _, ⟨eH⟩⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
    c sK MK s y g' hcart F e 𝒱
  letI : Subsingleton (𝒱.sectionsOf y F).H1 := h𝒱
  have hW : Subsingleton (𝒲.sectionsOf (pullback.snd π s)
      ((Scheme.Modules.pullback (pullback.fst π s)).obj MK)).H1 :=
    eH.symm.toEquiv.subsingleton
  exact all_covers_of_two_chart (pullback.snd π s) _
    ((hM.pullback (pullback.fst c sK)).pullback (pullback.fst π s)) 𝒲 hW
    (𝒰.baseChange π (AlgebraicClosure K)) j

/-- The proper flat cohomology engine applies to genuine local trivializations
of the theta line, without a global Hodge frame. -/
lemma sections_baseChange {R : Type u} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    (E : EllipticFamily R) (m : ℕ) (hm : 0 < m) :
    (letI := sectionModule E m
     Module.Finite R (sections E m) ∧ Module.Projective R (sections E m)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      let f := E.projection
      let t := Scheme.TwoAffineOpenCover.specMap R S
      let M := thetaLine E m
      letI := sectionModule E m
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f t)
        ((Scheme.Modules.pullback (pullback.fst f t)).obj M) ((pullback.fst f t) ⁻¹ᵁ ⊤)
      ∃ e : S ⊗[R] sections E m ≃ₗ[S]
          Γ((Scheme.Modules.pullback (pullback.fst f t)).obj M, (pullback.fst f t) ⁻¹ᵁ ⊤),
        ∀ (s : S) (w : sections E m),
          e (s ⊗ₜ[R] w) = s • Scheme.Modules.pullbackLocalSection (pullback.fst f t) w := by
  letI : IsProper E.projection := E.proper
  letI : SmoothOfRelativeDimension 1 E.projection := E.smooth
  apply Sections.solution E.projection (thetaLine E m)
    (RelativeNormalizedThetaInversion.line_invertible E m).1
  intro K _ _
  letI : Algebra ℚ K := ((algebraMap R K).comp (algebraMap ℚ R)).toAlgebra
  let sK := Scheme.TwoAffineOpenCover.specMap R K
  letI : CompactSpace (pullback E.projection sK : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd E.projection sK)
  let 𝒰 := Sections.P2mSectionsBaseChangeH0.coverOfCompact (pullback E.projection sK)
  exact ⟨𝒰, fun i => fibre_vanishing E sK m hm 𝒰 i⟩

end RelativeThetaSectionsCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator
open scoped TensorProduct

/-- The actual unframed theta sections are finite projective of geometric rank
m, and their canonical pullback map is an isomorphism after any ring extension. -/
theorem relative_theta_sections_cohomology :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : EllipticFamily R) (m : ℕ), 0 < m → SectionFacts E m := by
  intro R _ _ _ E m hm
  letI := sectionModule E m
  obtain ⟨hfinite, hbase⟩ := RelativeThetaSectionsCohomology.sections_baseChange E m hm
  refine ⟨⟨hfinite.1, hfinite.2, ?_⟩, hbase⟩
  intro K _ _ _
  letI : Module.Finite R (sections E m) := hfinite.1
  refine ⟨inferInstance, ?_⟩
  letI : Algebra ℚ K := ((algebraMap R K).comp (algebraMap ℚ R)).toAlgebra
  let t := Scheme.TwoAffineOpenCover.specMap R K
  let MK := (Scheme.Modules.pullback (pullback.fst E.projection t)).obj (thetaLine E m)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd E.projection t) MK ⊤
  obtain ⟨e, _⟩ := hbase K
  obtain ⟨𝒱, _, h𝒱⟩ := RelativeThetaSectionsCohomology.geometric_fibre_cover E t m hm
  obtain ⟨eH, _⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 (pullback.snd E.projection t) MK
  let e' : K ⊗[R] sections E m ≃ₗ[K] Γ(MK, ⊤) := e
  exact e'.finrank_eq.trans (eH.finrank_eq.trans h𝒱)

#print axioms relative_theta_sections_cohomology
end ArithmeticThetaRelativeSchrodingerR0257
