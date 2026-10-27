import ProjectiveEffectivityDefinitionsR0135
import Theorems.Thm_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Local projective maps of the prescribed cubic numerator basis.
All implementation helpers belong to this module's namespace. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaProjectiveEffectivityR0135.SpecialFiberCubicEmbeddingR0135
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [CharZero k]
variable {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
variable {a : Fin r → kˣ}

/-- Spanning by the supplied basis transports generation by all sections to
generation by its actual chart numerators. -/
lemma basis_generates_chart
    (b : Fin (3*r) → Sections k r n hr E a 3)
    (hb : IsBasis k r n hr E a 3 b)
    (hg : GloballyGenerated k r n hr E a 3) (i : Fin r) :
    Ideal.span (Set.range (fun j => (b j).val i)) = ⊤ := by
  classical
  apply top_unique
  rw [← hg i]
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  obtain ⟨c, hc, _⟩ := hb s
  change s.val i ∈ Ideal.span (Set.range (fun j => (b j).val i))
  rw [hc i]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- The irrelevant-ideal hypothesis in the frozen realization predicate is
proved from the accepted generation theorem, for each supplied basis. -/
lemma coefficientChartMap_irrelevant
    (h3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (b : Fin (3*r) → Sections k r n hr E a 3)
    (hb : IsBasis k r n hr E a 3 b) (i : Fin r) :
    Ideal.map (coefficientChartMap k b i)
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k))).toIdeal = ⊤ := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
  have hg := basis_generates_chart k b hb
    (positive_global_generation k r n hr h3 E hE a 3 (by omega)) i
  have htop : Ideal.map e (Ideal.span (Set.range (fun j => (b j).val i))) = ⊤ := by
    rw [hg, Ideal.map_top]
  apply top_unique
  rw [← htop, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have hX : MvPolynomial.X j ∈
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k))).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X _ j)
  have hh := Ideal.mem_map_of_mem (coefficientChartMap k b i) hX
  change e ((MvPolynomial.eval₂Hom
    ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
      (fun j => (b j).val i)) (MvPolynomial.X j)) ∈ _ at hh
  rw [MvPolynomial.eval₂Hom_X'] at hh
  exact hh

/-- The exact local morphism required by `RealizesEmbedding`. -/
def chartMorphism (h3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (b : Fin (3*r) → Sections k r n hr E a 3)
    (hb : IsBasis k r n hr E a 3 b) (i : Fin r) :
    specA k n ⟶ projectiveSpace (PowerSeries k) (3*r) :=
  Proj.fromOfGlobalSections _ (coefficientChartMap k b i)
    (coefficientChartMap_irrelevant k h3 hE b hb i)

/-- The prescribed coefficient homomorphism fixes the base structural map. -/
lemma chartMorphism_over (h3 : 3 ≤ r) (hE : IsAdjacent k n E)
    (b : Fin (3*r) → Sections k r n hr E a 3)
    (hb : IsBasis k r n hr E a 3 b) (i : Fin r) :
    chartMorphism k h3 hE b hb i ≫ projectiveStructure (PowerSeries k) (3*r) =
      structureMap k n ≫ baseInclusion k n := by
  rw [chartMorphism, projectiveStructure, ← Category.assoc,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have he : ((coefficientChartMap k b i).comp (algebraMap _ _)).comp
      (algebraMap (PowerSeries k)
        ((MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) 0)) =
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom.comp
        ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n)) := by
    ext c
    change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C c)) = _
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  change ((Spec (CommRingCat.of (A k n))).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv) ≫ _ = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]
  simp only [structureMap, baseInclusion, CommRingCat.ofHom_comp, Spec.map_comp]

open ArithmeticThetaPolygonCohomologyR0131
open PositiveSectionMultiplicationR0134

/-- Every cubic section is a linear polynomial in the supplied basis, with
coefficients lifted along the prescribed power-series quotient. -/
lemma section_linear_polynomial
    (b : Fin (3*r) → Sections k r n hr E a 3)
    (hb : IsBasis k r n hr E a 3 b) (s : Sections k r n hr E a 3) :
    ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), p.IsHomogeneous 1 ∧
      ∀ i, (MvPolynomial.eval₂Hom
        ((base k n).comp (trunc (PowerSeries k) PowerSeries.X n))
        (fun j => (b j).val i)) p = s.val i := by
  classical
  obtain ⟨c, hc, _⟩ := hb s
  choose v hv using fun j => Ideal.Quotient.mk_surjective (c j)
  refine ⟨∑ j, MvPolynomial.C (v j) * MvPolynomial.X j, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro j _
    simpa using (MvPolynomial.isHomogeneous_C (Fin (3*r)) (v j)).mul
      (MvPolynomial.isHomogeneous_X (PowerSeries k) j)
  · intro i
    rw [map_sum, hc i]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.comp_apply]
    change base k n (Ideal.Quotient.mk _ (v j)) * _ = _
    rw [hv j]

section Special
variable {E : B k 0 false ≃+* B k 0 true}

/-- A section whose numerator is one on the specified nodal chart. Its other
numerators are exactly the already proved cubic vertex sections. -/
lemma exists_vertex_section (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (i : Fin r) :
    ∃ s : Sections k r 0 hr E a 3,
      s.val = vertex hr (ratio k r hr a) 3 i ∧ s.val i = 1 := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k 0
  refine ⟨⟨_, vertex_compatible hr h3 E hE L hL a 3 (by omega) i⟩, rfl, ?_⟩
  simp [vertex, PositiveGlobalGenerationR0134.next_ne r hr h3 i,
    (PositiveGlobalGenerationR0134.next_ne r hr h3 i).symm]

/-- Both nodal coordinates occur as actual cubic-section numerators on
any given chart; this is stronger than generation of the unit ideal. -/
lemma exists_coordinate_sections (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (i : Fin r) :
    (∃ s : Sections k r 0 hr E a 3, s.val i = coordX k 0) ∧
    (∃ s : Sections k r 0 hr E a 3, s.val i = coordY k 0) := by
  classical
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k 0
  constructor
  · obtain ⟨j, hj⟩ := (PolygonCechObstructionR0131.shift r hr).surjective i
    change next r hr j = i at hj
    refine ⟨⟨_, edge_compatible hr E hE L hL a 3 2 (by omega) (by omega) j⟩, ?_⟩
    have hij : i ≠ j := by rw [← hj]; exact PositiveGlobalGenerationR0134.next_ne r hr h3 j
    simp [edge, hj, hij]
  · let q := ratio k r hr a i
    let s := edge hr (ratio k r hr a) 3 1 i
    let c : R k 0 := (↑(q⁻¹) : R k 0)^3
    refine ⟨⟨fun j => base k 0 c * s j,
      PositiveSectionsReductionR0134.compatible_base_mul k r 0 hr E hE a 3 c s
        (edge_compatible hr E hE L hL a 3 1 (by omega) (by omega) i)⟩, ?_⟩
    change base k 0 c * s i = _
    simp only [s, edge, if_true, (PositiveGlobalGenerationR0134.next_ne r hr h3 i).symm,
      if_false, add_zero, pow_one]
    rw [← mul_assoc, ← map_mul]
    have hc : c * (↑(ratio k r hr a i) : R k 0)^3 = 1 := by
      change (↑(q⁻¹) : R k 0)^3 * (q : R k 0)^3 = 1
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [hc, map_one, one_mul]

/-- Evaluation of the supplied basis is onto the complete nodal chart ring,
not only onto either of its two branches. -/
lemma chart_evaluation_surjective (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r) :
    Function.Surjective (MvPolynomial.eval₂Hom
      ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
      (fun j => (b j).val i)) := by
  classical
  let f := MvPolynomial.eval₂Hom
    ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
    (fun j => (b j).val i)
  obtain ⟨⟨sx, hx⟩, ⟨sy, hy⟩⟩ := exists_coordinate_sections k h3 hE (a := a) i
  obtain ⟨px, _, hpx⟩ := section_linear_polynomial k b hb sx
  obtain ⟨py, _, hpy⟩ := section_linear_polynomial k b hb sy
  have hxr : coordX k 0 ∈ f.range := ⟨px, (hpx i).trans hx⟩
  have hyr : coordY k 0 ∈ f.range := ⟨py, (hpy i).trans hy⟩
  have hbase (c : R k 0) : base k 0 c ∈ f.range := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨MvPolynomial.C z, MvPolynomial.eval₂Hom_C _ _ _⟩
  intro z
  change z ∈ f.range
  obtain ⟨c, hc⟩ := PolygonCechKernelR0131.exists_expansion k 0 z
  rw [hc]
  apply Subring.sum_mem
  intro j _
  apply Subring.mul_mem _ (hbase _)
  cases j with
  | ofNat d =>
      change PolygonCechKernelR0131.monomial k 0 (d : ℤ) ∈ f.range
      rw [PolygonCechKernelR0131.monomial_nat]
      exact Subring.pow_mem _ hxr d
  | negSucc d =>
      rw [show Int.negSucc d = -((d+1 : ℕ) : ℤ) by omega,
        PolygonCechKernelR0131.monomial_neg]
      exact Subring.pow_mem _ hyr (d+1)

/-- The linear polynomial for a vertex section is a denominator evaluating to
one on its own chart, uniformly for every supplied basis. -/
lemma exists_vertex_polynomial (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r) :
    ∃ p : MvPolynomial (Fin (3*r)) (PowerSeries k), p.IsHomogeneous 1 ∧
      (∀ j, (MvPolynomial.eval₂Hom
        ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
        (fun l => (b l).val j)) p = vertex hr (ratio k r hr a) 3 i j) ∧
      (MvPolynomial.eval₂Hom
        ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
        (fun l => (b l).val i)) p = 1 := by
  obtain ⟨s, hs, hi⟩ := exists_vertex_section k h3 hE (a := a) i
  obtain ⟨p, hp, he⟩ := section_linear_polynomial k b hb s
  exact ⟨p, hp, fun j => (he j).trans (congrFun hs j), (he i).trans hi⟩

end Special

section AffineProjectiveChart
variable {S : Type u} [CommRing S] {N : ℕ} {X : Scheme.{u}}
variable (f : MvPolynomial (Fin N) S →+* Γ(X, ⊤))
variable (hf : Ideal.map f
  (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin N) S)).toIdeal = ⊤)
variable (v : MvPolynomial (Fin N) S) (hv : v.IsHomogeneous 1) (hfv : f v = 1)

include hv hfv in
lemma projective_map_preimage_vertex :
    Proj.fromOfGlobalSections _ f hf ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) S) v = ⊤ := by
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hv,
    hfv, Scheme.basicOpen_one]

/-- The local projective map factors into the affine open cut out by a linear
form whose value is one. -/
def projectiveChartLift : X ⟶
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) S) v).toScheme :=
  (Scheme.topIso X).inv ≫ (Proj.fromOfGlobalSections _ f hf).resLE _ ⊤
    (projective_map_preimage_vertex f hf v hv hfv).ge

lemma projectiveChartLift_ι : projectiveChartLift f hf v hv hfv ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) S) v).ι =
    Proj.fromOfGlobalSections _ f hf := by
  rw [projectiveChartLift, Category.assoc, Scheme.Hom.resLE_comp_ι]
  simp

/-- A surjective polynomial evaluation with a degree-one element evaluating to
one induces a scheme-theoretic closed immersion into its projective chart.
The homogeneous fractions retain all elements of the target affine ring. -/
lemma projectiveChartLift_closed [IsAffine X] (hs : Function.Surjective f) :
    IsClosedImmersion (projectiveChartLift f hf v hv hfv) := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin N) S
  haveI hvι : IsIso (X.basicOpen (f v)).ι := by
    rw [hfv, Scheme.basicOpen_one]
    exact inferInstanceAs (IsIso (Scheme.topIso X).hom)
  have hfac : projectiveChartLift f hf v hv hfv =
      inv (X.basicOpen (f v)).ι ≫ Proj.toBasicOpenOfGlobalSections 𝒜 f rfl one_pos hv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 v).ι, Category.assoc,
      projectiveChartLift_ι,
      ← Proj.fromOfGlobalSections_resLE 𝒜 f hf one_pos hv,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac]
  haveI : IsIso X.toSpecΓ := IsAffine.affine
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  unfold Proj.toBasicOpenOfGlobalSections
  simp only [Category.assoc]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  refine IsClosedImmersion.spec_of_surjective _ ?_
  intro z
  obtain ⟨y, hy⟩ : ∃ y, algebraMap Γ(X, ⊤) _ y = z := by
    obtain ⟨⟨y, s⟩, hz⟩ := IsLocalization.surj (M := Submonoid.powers (f v)) z
    have hs1 : (s : Γ(X, ⊤)) = 1 := by
      obtain ⟨m, hm⟩ := s.2
      simp only [← hm, hfv, one_pow]
    exact ⟨y, by rw [← hz, hs1, map_one, mul_one]⟩
  obtain ⟨p, rfl⟩ := hs y
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    HomogeneousLocalization.mk ⟨d, ⟨MvPolynomial.homogeneousComponent d p,
      (MvPolynomial.mem_homogeneousSubmodule d _).mpr
        (MvPolynomial.homogeneousComponent_mem d p)⟩,
      ⟨v^d, by simpa using SetLike.pow_mem_graded d (show v ∈ 𝒜 1 from hv)⟩, d, rfl⟩, ?_⟩
  rw [← hy, map_sum]
  trans ∑ d ∈ Finset.range (p.totalDegree + 1),
    algebraMap Γ(X, ⊤) _ (f (MvPolynomial.homogeneousComponent d p))
  · refine Finset.sum_congr rfl fun d _ => ?_
    show ((IsLocalization.map _ f _).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 v) (Localization.Away v)))
      (HomogeneousLocalization.mk _) = _
    rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
    refine Eq.trans ?_ (IsLocalization.mk'_one
      (M := Submonoid.powers (f v)) (Localization.Away (f v))
      (f (MvPolynomial.homogeneousComponent d p)))
    congr 1
    exact Subtype.ext (by simp [hfv])
  · rw [← map_sum, ← map_sum, MvPolynomial.sum_homogeneousComponent]

end AffineProjectiveChart


/-- Each prescribed nodal chart is a closed subscheme of the projective affine
open defined by its vertex linear form. No tangent direction is discarded. -/
lemma local_closed_embedding {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r) :
    ∃ (v : MvPolynomial (Fin (3*r)) (PowerSeries k))
      (g : specA k 0 ⟶ (Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) v).toScheme),
      v.IsHomogeneous 1 ∧ IsClosedImmersion g ∧
      g ≫ (Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) v).ι =
        chartMorphism k h3 hE b hb i ∧
      ∀ j, (MvPolynomial.eval₂Hom
        ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
        (fun l => (b l).val j)) v = vertex hr (ratio k r hr a) 3 i j := by
  letI : IsAffine (specA k 0) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k 0))))
  obtain ⟨v, hv, he, hi⟩ := exists_vertex_polynomial k h3 hE b hb i
  have hfv : coefficientChartMap k b i v = 1 := by
    change (Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
      ((MvPolynomial.eval₂Hom _ _) v) = 1
    rw [hi, map_one]
  have hs : Function.Surjective (coefficientChartMap k b i) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv).2.comp
      (chart_evaluation_surjective k h3 hE b hb i)
  exact ⟨v, projectiveChartLift _ (coefficientChartMap_irrelevant k h3 hE b hb i) v hv hfv,
    hv, projectiveChartLift_closed _ _ v hv hfv hs, projectiveChartLift_ι _ _ v hv hfv, he⟩


section ProjectiveOverlap
open HomogeneousLocalization
variable {S : Type u} [CommRing S] {N : ℕ}
variable {X Z : Scheme.{u}} (α : Z ⟶ X)
variable (f : MvPolynomial (Fin N) S →+* Γ(X, ⊤))
variable (hf : Ideal.map f
  (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin N) S)).toIdeal = ⊤)
variable (v : MvPolynomial (Fin N) S) (hv : v.IsHomogeneous 1)

include hv in
lemma comp_preimage_vertex (hu : IsUnit (α.appTop (f v))) :
    (α ≫ Proj.fromOfGlobalSections _ f hf) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) S) v = ⊤ := by
  rw [Scheme.Hom.comp_preimage,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hv,
    Scheme.preimage_basicOpen_top, Z.basicOpen_of_isUnit hu]

/-- Explicit homogeneous-fraction formula after pulling the local map to an
overlap where the chosen denominator becomes invertible. -/
lemma comp_fraction (hu : IsUnit (α.appTop (f v))) (m : ℕ)
    (p : MvPolynomial (Fin N) S) (hp : p ∈
      (MvPolynomial.homogeneousSubmodule (Fin N) S) (m • 1)) :
    (α ≫ Proj.fromOfGlobalSections _ f hf).appLE
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) S) v) ⊤
      (comp_preimage_vertex α f hf v hv hu).ge
      (Proj.awayToSection _ v (Away.mk _ hv m p hp)) * α.appTop (f v)^m =
    α.appTop (f p) := by
  have hU : (⊤ : Z.Opens) ≤ α ⁻¹ᵁ X.basicOpen (f v) := by
    rw [Scheme.preimage_basicOpen_top, Z.basicOpen_of_isUnit hu]
  have h := Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
    (MvPolynomial.homogeneousSubmodule (Fin N) S) f hf one_pos hv m p hp
  have hh := congrArg (α.appLE (X.basicOpen (f v)) ⊤ hU) h
  simp only [map_mul, map_pow] at hh
  have heval (z) : α.appLE (X.basicOpen (f v)) ⊤ hU
      ((Proj.fromOfGlobalSections _ f hf).appLE _ _
        (Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hv).ge z) =
      (α ≫ Proj.fromOfGlobalSections _ f hf).appLE _ ⊤
        (comp_preimage_vertex α f hf v hv hu).ge z :=
    ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE α
      (Proj.fromOfGlobalSections _ f hf) _ _ _ _ _) z
  have hres (z : Γ(X, ⊤)) : α.appLE (X.basicOpen (f v)) ⊤ hU
      (X.presheaf.map (homOfLE (X.basicOpen_le (f v))).op z) = α.appTop z := by
    have hnat := ConcreteCategory.congr_hom
      (Scheme.Hom.map_appLE α hU (homOfLE (X.basicOpen_le (f v))).op) z
    have htop : α.appLE ⊤ ⊤ le_top = α.appTop := by
      change α.appTop ≫ Z.presheaf.map (𝟙 _) = α.appTop
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    change α.appLE (X.basicOpen (f v)) ⊤ hU
      (X.presheaf.map (homOfLE (X.basicOpen_le (f v))).op z) = α.appLE ⊤ ⊤ le_top z at hnat
    rw [htop] at hnat
    exact hnat
  simpa only [heval, hres] using hh


include hv in
/-- Agreement of homogeneous values up to one unit gives agreement of the
actual projective morphisms on an overlap. -/
lemma comp_eq_of_homogeneous_scale {Y : Scheme.{u}} (β : Z ⟶ Y)
    (g : MvPolynomial (Fin N) S →+* Γ(Y, ⊤))
    (hg : Ideal.map g
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin N) S)).toIdeal = ⊤)
    (c : Γ(Z, ⊤)ˣ) (hscale : ∀ d p, p.IsHomogeneous d →
      α.appTop (f p) = β.appTop (g p) * (c : Γ(Z, ⊤))^d)
    (hu : IsUnit (α.appTop (f v))) :
    α ≫ Proj.fromOfGlobalSections _ f hf = β ≫ Proj.fromOfGlobalSections _ g hg := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin N) S
  have he : α.appTop (f v) = β.appTop (g v) * (c : Γ(Z, ⊤)) := by
    simpa using hscale 1 v hv
  have hu' : IsUnit (β.appTop (g v)) := by
    rw [he] at hu
    exact isUnit_of_mul_isUnit_left hu
  have ha := comp_preimage_vertex α f hf v hv hu
  have hb := comp_preimage_vertex β g hg v hv hu'
  have happ : (α ≫ Proj.fromOfGlobalSections _ f hf).appLE (Proj.basicOpen 𝒜 v) ⊤ ha.ge =
      (β ≫ Proj.fromOfGlobalSections _ g hg).appLE (Proj.basicOpen 𝒜 v) ⊤ hb.ge := by
    ext x
    have hsurj : Function.Surjective (Proj.awayToSection 𝒜 v) := by
      rw [← Proj.basicOpenIsoAway_hom 𝒜 v hv one_pos]
      exact (ConcreteCategory.bijective_of_isIso _).2
    obtain ⟨z, rfl⟩ := hsurj x
    obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective (𝒜 := 𝒜) hv z
    apply (hu.pow m).mul_right_cancel
    rw [comp_fraction α f hf v hv hu m p hp]
    have hp' : p.IsHomogeneous m := by simpa [𝒜, MvPolynomial.mem_homogeneousSubmodule] using hp
    rw [hscale m p hp', he, mul_pow, ← mul_assoc,
      comp_fraction β g hg v hv hu' m p hp]
  haveI : IsAffine (Proj.basicOpen 𝒜 v).toScheme := Proj.isAffineOpen_basicOpen 𝒜 v hv one_pos
  have hres : (α ≫ Proj.fromOfGlobalSections _ f hf).resLE (Proj.basicOpen 𝒜 v) ⊤ ha.ge =
      (β ≫ Proj.fromOfGlobalSections _ g hg).resLE (Proj.basicOpen 𝒜 v) ⊤ hb.ge := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]
  have h := congrArg (fun q => q ≫ (Proj.basicOpen 𝒜 v).ι) hres
  rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι] at h
  change (Scheme.topIso Z).hom ≫ _ = (Scheme.topIso Z).hom ≫ _ at h
  exact (cancel_epi (Scheme.topIso Z).hom).mp h

end ProjectiveOverlap


/-- Polynomial evaluation respects a common scaling of the degree-one
coordinates. This equality is about actual ring homomorphisms. -/
lemma homogeneous_scale {S T : Type u} [CommRing S] [CommRing T] {N : ℕ}
    (f g : MvPolynomial (Fin N) S →+* T) (c : T)
    (hC : ∀ s, f (MvPolynomial.C s) = g (MvPolynomial.C s))
    (hX : ∀ j, f (MvPolynomial.X j) = g (MvPolynomial.X j) * c)
    (d : ℕ) (p : MvPolynomial (Fin N) S) (hp : p.IsHomogeneous d) :
    f p = g p * c^d := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add p q _ _ hp hq => rw [map_add, map_add, hp, hq, add_mul]
  | monomial m a hm =>
    rw [MvPolynomial.monomial_eq]
    simp only [map_mul, Finsupp.prod, map_prod, map_pow, hC, hX,
      mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hdeg : ∑ j ∈ m.support, m j = d := by
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] using hm
    rw [hdeg, mul_assoc]


lemma spec_pullback_value {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (z : S) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv z) =
      (Scheme.ΓSpecIso (CommRingCat.of T)).inv (f z) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) z).symm

lemma adjacent_chartMorphism {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r) :
    leftLeg k 0 E ≫ chartMorphism k h3 hE b hb i =
      rightLeg k 0 ≫ chartMorphism k h3 hE b hb (next r hr i) := by
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k 0
  let F : MvPolynomial (Fin (3*r)) (PowerSeries k) →+* Γ(specB k 0 true, ⊤) :=
    (leftLeg k 0 E).appTop.hom.comp (coefficientChartMap k b i)
  let G : MvPolynomial (Fin (3*r)) (PowerSeries k) →+* Γ(specB k 0 true, ⊤) :=
    (rightLeg k 0).appTop.hom.comp (coefficientChartMap k b (next r hr i))
  let e : B k 0 true →+* Γ(specB k 0 true, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (B k 0 true))).inv.hom
  let w : B k 0 true := L.symm
    (LaurentPolynomial.C ((ratio k r hr a i : R k 0)^3) * LaurentPolynomial.T (-3))
  have hw : IsUnit w := by
    apply IsUnit.map L.symm
    exact (((ratio k r hr a i).isUnit.pow 3).map LaurentPolynomial.C).mul
      (LaurentPolynomial.isUnit_T _)
  obtain ⟨c, hc⟩ := hw.map e
  have hC (z : PowerSeries k) : F (MvPolynomial.C z) = G (MvPolynomial.C z) := by
    change (leftLeg k 0 E).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C z))) =
      (rightLeg k 0).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C z)))
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, leftLeg, rightLeg,
      ]
    erw [spec_pullback_value, spec_pullback_value]
    congr 1
    exact RingHom.congr_fun (adjacent_base hE) (trunc (PowerSeries k) PowerSeries.X 0 z)
  have hX (j : Fin (3*r)) : F (MvPolynomial.X j) = G (MvPolynomial.X j) * (c : Γ(specB k 0 true, ⊤)) := by
    change (leftLeg k 0 E).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j))) =
      (rightLeg k 0).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
        ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j))) * _
    simp only [MvPolynomial.eval₂Hom_X', leftLeg, rightLeg]
    erw [spec_pullback_value, spec_pullback_value]
    rw [hc]
    change e (E (restriction k 0 false ((b j).val i))) =
      e (restriction k 0 true ((b j).val (next r hr i))) * e w
    rw [← map_mul]
    congr 1
    apply L.injective
    rw [map_mul]
    change _ = _ * L (L.symm _)
    rw [L.apply_symm_apply]
    exact (special_compatible_iff k r hr E hE L hL a 3 (b j).val).mp (b j).property i
  obtain ⟨v, hv, he, hi⟩ := exists_vertex_polynomial k h3 hE b hb i
  have huv : IsUnit ((leftLeg k 0 E).appTop (coefficientChartMap k b i v)) := by
    have heq : coefficientChartMap k b i v = 1 := by
      change (Scheme.ΓSpecIso (CommRingCat.of (A k 0))).inv
        ((MvPolynomial.eval₂Hom _ _) v) = 1
      rw [hi, map_one]
    rw [heq, map_one]
    exact isUnit_one
  exact comp_eq_of_homogeneous_scale (leftLeg k 0 E) (coefficientChartMap k b i)
    (coefficientChartMap_irrelevant k h3 hE b hb i) v hv (rightLeg k 0)
    (coefficientChartMap k b (next r hr i))
    (coefficientChartMap_irrelevant k h3 hE b hb (next r hr i)) c
    (homogeneous_scale F G c hC hX) huv

/-- The numerator maps glue on every prescribed adjacent overlap. -/
def globalMorphism {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    D.X ⟶ projectiveSpace (PowerSeries k) (3*r) :=
  D.desc (chartMorphism k h3 hE b hb) (adjacent_chartMorphism k h3 hE b hb)

lemma globalMorphism_realizes {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    RealizesEmbedding k D b (globalMorphism k h3 hE D b hb) := by
  intro i
  exact ⟨coefficientChartMap_irrelevant k h3 hE b hb i, D.chart_desc _ _ i⟩

lemma globalMorphism_over {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    globalMorphism k h3 hE D b hb ≫ projectiveStructure (PowerSeries k) (3*r) =
      D.p ≫ baseInclusion k 0 := by
  apply D.hom_ext
  intro i
  rw [← Category.assoc, globalMorphism, D.chart_desc, chartMorphism_over,
    ← D.chart_over i, Category.assoc]


/-- A prime avoiding the chosen coordinate lifts to the actual overlap ring.
This uses the accepted universal extension map, not a replacement atlas. -/
lemma mem_range_restriction (side : Bool) (z : PrimeSpectrum (A k 0))
    (hz : (if side then coordX k 0 else coordY k 0) ∉ z.asIdeal) :
    z ∈ Set.range (Spec.map (CommRingCat.ofHom (restriction k 0 side))) := by
  let f : A k 0 →+* z.asIdeal.ResidueField := algebraMap _ _
  have hu : IsUnit (f (if side then coordX k 0 else coordY k 0)) := by
    apply isUnit_iff_ne_zero.mpr
    exact fun he => hz (Ideal.algebraMap_residueField_eq_zero.mp he)
  let g := openPoint f side hu
  have hrange := PrimeSpectrum.residueField_comap z
  have hz' : z ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [hrange]
    exact Set.mem_singleton z
  obtain ⟨q, hq⟩ := hz'
  refine ⟨Spec.map (CommRingCat.ofHom g) q, ?_⟩
  change PrimeSpectrum.comap (restriction k 0 side) (PrimeSpectrum.comap g q) = z
  rw [← PrimeSpectrum.comap_comp_apply, openPoint_restriction]
  exact hq

lemma mem_range_rightLeg (z : PrimeSpectrum (A k 0)) (hz : coordX k 0 ∉ z.asIdeal) :
    z ∈ Set.range (rightLeg k 0) := mem_range_restriction k true z hz

lemma mem_range_leftLeg (E : B k 0 false ≃+* B k 0 true)
    (z : PrimeSpectrum (A k 0)) (hz : coordY k 0 ∉ z.asIdeal) :
    z ∈ Set.range (leftLeg k 0 E) := by
  obtain ⟨q, hq⟩ := mem_range_restriction k false z hz
  have hs : Function.Surjective (Spec.map (CommRingCat.ofHom E.toRingHom)) := by
    letI : IsIso (CommRingCat.ofHom E.toRingHom) :=
      inferInstanceAs (IsIso E.toCommRingCatIso.hom)
    exact (Spec.map (CommRingCat.ofHom E.toRingHom)).homeomorph.surjective
  obtain ⟨w, hw⟩ := hs q
  refine ⟨w, ?_⟩
  rw [leftLeg, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
  exact (congrArg (Spec.map (CommRingCat.ofHom (restriction k 0 false))) hw).trans hq

/-- Nonvanishing of a vertex numerator forces a point to lie in its nodal
chart. This supplies the global point-separation step. -/
lemma vertex_nonzero_in_chart {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (D : Atlas k r 0 hr E) (i j : Fin r)
    (z : PrimeSpectrum (A k 0))
    (hz : vertex hr (ratio k r hr a) 3 i j ∉ z.asIdeal) :
    D.chart j z ∈ Set.range (D.chart i) := by
  classical
  by_cases hji : j = i
  · subst j
    exact ⟨z, rfl⟩
  have hn := PositiveGlobalGenerationR0134.next_ne r hr h3 i
  have hnn : next r hr (next r hr i) ≠ i := by
    intro he
    have hi : ((i.val + 1) % r + 1) % r = i.val := congrArg Fin.val he
    have hilt := i.isLt
    have hmod : (i.val + 1) % r = if i.val + 1 < r then i.val + 1 else 0 := by
      split_ifs with hh
      · exact Nat.mod_eq_of_lt hh
      · have heq : i.val + 1 = r := by omega
        rw [heq, Nat.mod_self]
    rw [hmod] at hi
    split_ifs at hi with hh
    · by_cases hhi : i.val + 2 < r
      · rw [show i.val + 1 + 1 = i.val + 2 by omega, Nat.mod_eq_of_lt hhi] at hi
        omega
      · have heq : i.val + 1 + 1 = r := by omega
        rw [heq, Nat.mod_self] at hi
        omega
    · rw [zero_add, Nat.mod_eq_of_lt (by omega : 1 < r)] at hi
      omega
  by_cases hjn : next r hr j = i
  · have hnj : j ≠ next r hr i := by
      intro he
      subst j
      exact hnn hjn
    have hy : coordY k 0 ∉ z.asIdeal := by
      intro hy
      apply hz
      simp only [vertex, hji, if_false, hjn, if_true, hnj, add_zero, zero_add]
      exact z.asIdeal.mul_mem_left _ (Ideal.pow_mem_of_mem z.asIdeal hy 3 (by omega))
    obtain ⟨w, hw⟩ := mem_range_leftLeg k E z hy
    refine ⟨rightLeg k 0 w, ?_⟩
    rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hjn, (D.adjacent j).w]
  · by_cases hnj : j = next r hr i
    · have hx : coordX k 0 ∉ z.asIdeal := by
        intro hx
        apply hz
        simp only [vertex, hnj, hn, hnn, if_false, if_true, zero_add]
        exact z.asIdeal.mul_mem_left _ (Ideal.pow_mem_of_mem z.asIdeal hx 3 (by omega))
      obtain ⟨w, hw⟩ := mem_range_rightLeg k z hx
      refine ⟨leftLeg k 0 E w, ?_⟩
      rw [← hw, ← Scheme.Hom.comp_apply, (D.adjacent i).w, Scheme.Hom.comp_apply, hnj]
    · exfalso
      apply hz
      simp only [vertex, hji, hjn, hnj, if_false, add_zero]
      exact z.asIdeal.zero_mem


lemma chartMorphism_preimage {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r)
    (v : MvPolynomial (Fin (3*r)) (PowerSeries k)) (hv : v.IsHomogeneous 1) :
    chartMorphism k h3 hE b hb i ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) v =
    PrimeSpectrum.basicOpen ((MvPolynomial.eval₂Hom
        ((base k 0).comp (trunc (PowerSeries k) PowerSeries.X 0))
        (fun l => (b l).val i)) v) := by
  rw [chartMorphism, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hv]
  exact basicOpen_eq_of_affine _

lemma chartMorphism_injective {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) (i : Fin r) :
    Function.Injective (chartMorphism k h3 hE b hb i) := by
  obtain ⟨v, g, _, hg, he, _⟩ := local_closed_embedding k h3 hE b hb i
  letI := hg
  rw [← he]
  exact (Proj.basicOpen _ v).ι.isOpenEmbedding.injective.comp g.isClosedEmbedding.injective

lemma globalMorphism_injective {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    Function.Injective (globalMorphism k h3 hE D b hb) := by
  intro x y hxy
  obtain ⟨i, z, rfl⟩ := D.covers x
  obtain ⟨j, w, rfl⟩ := D.covers y
  obtain ⟨v, hv, he, hi⟩ := exists_vertex_polynomial k h3 hE b hb i
  have hmaps (l : Fin r) (t : specA k 0) :
      globalMorphism k h3 hE D b hb (D.chart l t) = chartMorphism k h3 hE b hb l t :=
    congrArg (fun f : specA k 0 ⟶ _ => f t) (D.chart_desc _ (adjacent_chartMorphism k h3 hE b hb) l)
  rw [hmaps, hmaps] at hxy
  have hz : chartMorphism k h3 hE b hb i z ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) v := by
    change z ∈ chartMorphism k h3 hE b hb i ⁻¹ᵁ Proj.basicOpen _ v
    rw [chartMorphism_preimage k h3 hE b hb i v hv, hi]
    exact z.isPrime.one_notMem
  rw [hxy] at hz
  change w ∈ chartMorphism k h3 hE b hb j ⁻¹ᵁ Proj.basicOpen _ v at hz
  rw [chartMorphism_preimage k h3 hE b hb j v hv, he j] at hz
  obtain ⟨w', hw'⟩ := vertex_nonzero_in_chart k h3 D i j w hz
  rw [← hw']
  apply congrArg (D.chart i)
  apply chartMorphism_injective k h3 hE b hb i
  rw [← hmaps, ← hmaps, hw', hmaps, hmaps]
  exact hxy

lemma globalMorphism_surjectiveOnStalks {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    SurjectiveOnStalks (globalMorphism k h3 hE D b hb) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks) D.openCover
  intro i
  change SurjectiveOnStalks (D.chart i ≫ globalMorphism k h3 hE D b hb)
  rw [globalMorphism, D.chart_desc]
  obtain ⟨v, g, _, hg, he, _⟩ := local_closed_embedding k h3 hE b hb i
  letI := hg
  rw [← he]
  infer_instance

lemma globalMorphism_closed {E : B k 0 false ≃+* B k 0 true}
    (h3 : 3 ≤ r) (hE : IsAdjacent k 0 E) (D : Atlas k r 0 hr E)
    (b : Fin (3*r) → Sections k r 0 hr E a 3)
    (hb : IsBasis k r 0 hr E a 3 b) :
    IsClosedImmersion (globalMorphism k h3 hE D b hb) := by
  letI := globalMorphism_surjectiveOnStalks k h3 hE D b hb
  letI := SurjectiveOnStalks.mono_of_injective (globalMorphism_injective k h3 hE D b hb)
  apply (IsClosedImmersion.iff_isProper_and_mono _).mpr
  refine ⟨?_, inferInstance⟩
  letI : IsProper D.p := infinitesimal_polygon_proper k r hr h3 0 E hE D
  letI : IsClosedImmersion (baseInclusion k 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsProper (globalMorphism k h3 hE D b hb ≫ projectiveStructure (PowerSeries k) (3*r)) := by
    rw [globalMorphism_over]
    infer_instance
  haveI : IsSeparated (projectiveStructure (PowerSeries k) (3*r)) := by
    unfold projectiveStructure
    infer_instance
  exact IsProper.of_comp _ (projectiveStructure (PowerSeries k) (3*r))

end ArithmeticThetaProjectiveEffectivityR0135.SpecialFiberCubicEmbeddingR0135

namespace ArithmeticThetaProjectiveEffectivityR0135
open CategoryTheory AlgebraicGeometry
open SpecialFiberCubicEmbeddingR0135

/-- The complete cubic marked-divisor system embeds the special polygon, with
exactly the prescribed numerator maps and power-series structure map. -/
theorem special_fiber_cubic_embedding :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r → ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k 0 false ≃+* ArithmeticThetaInfinitesimalPolygonR0129.B k 0 true), ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k 0 E → ∀ (a : Fin r → kˣ) (D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r 0 hr E) (b : Fin (3*r) → ArithmeticThetaPositiveLineR0134.Sections k r 0 hr E a 3), ArithmeticThetaPositiveLineR0134.IsBasis k r 0 hr E a 3 b → ∃ j : D.X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace (PowerSeries k) (3*r), AlgebraicGeometry.IsClosedImmersion j ∧ ArithmeticThetaProjectiveEffectivityR0135.RealizesEmbedding k D b j ∧ CategoryTheory.CategoryStruct.comp j (ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure (PowerSeries k) (3*r)) = CategoryTheory.CategoryStruct.comp D.p (ArithmeticThetaProjectiveEffectivityR0135.baseInclusion k 0) := by
  intro k _ _ r hr h3 E hE a D b hb
  exact ⟨globalMorphism k h3 hE D b hb,
    globalMorphism_closed k h3 hE D b hb,
    globalMorphism_realizes k h3 hE D b hb,
    globalMorphism_over k h3 hE D b hb⟩

end ArithmeticThetaProjectiveEffectivityR0135

#print axioms ArithmeticThetaProjectiveEffectivityR0135.special_fiber_cubic_embedding
