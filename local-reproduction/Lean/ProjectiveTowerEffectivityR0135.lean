import FormalRelationsEffectivityR0135
import CompatibleProjectiveEmbeddingsR0135
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! Projective effectivity of the prescribed infinitesimal polygon tower.
Implementation lemmas belong to this module's namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134

open FormalRelationsEffectivityR0135 PositiveSectionsReductionR0134
open FormalHomogeneousPresentationR0135 MvPolynomial
section ProjectiveMaps
variable {S Q σ τ : Type u} [CommRing S] [CommRing Q]
variable [SetLike σ S] [AddSubgroupClass σ S] [SetLike τ Q] [AddSubgroupClass τ Q]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

lemma proj_chart_pullback (d : ℕ) (hd : 0 < d) (p : S) (hp : p ∈ 𝒜 d) :
    IsPullback (Proj.awayι ℬ (f p) (f.map_mem hp) hd)
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f p)))
      (Proj.map f hf) (Proj.awayι 𝒜 p hp hd) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback _ _ _ _
  · exact Proj.awayι_comp_map f hf hd p hp
  · simp only [Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

lemma projMap_closed_of_piece_surjective
    (hs : ∀ d p, p ∈ 𝒜 d → Function.Surjective (HomogeneousLocalization.Away.map f p)) :
    IsClosedImmersion (Proj.map f hf) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (Proj.affineOpenCover 𝒜).openCover
  intro s
  have hpb := proj_chart_pullback f hf s.1.val s.1.2 s.2 s.2.2
  have hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map f s.2))) :=
    IsClosedImmersion.spec_of_surjective _ (hs s.1.val s.2 s.2.2)
  rw [← hpb.isoPullback_hom_snd] at hclosed
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hpb.isoPullback.hom _).mp hclosed

end ProjectiveMaps

section GradedFlatness
variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
variable [CommRing S] [Algebra R S] [Module.Flat R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

lemma homogeneousLocalization_flat (p : S) :
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers p)).comp
      (algebraMap R (𝒜 0))).Flat := by
  let H := HomogeneousLocalization.Away 𝒜 p
  let L := Localization.Away p
  let g : R →+* H := (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers p)).comp
    (algebraMap R (𝒜 0))
  let : Algebra R H := g.toAlgebra
  let : Module R H := g.toAlgebra.toModule
  let : SMul R H := ⟨fun c z => g c * z⟩
  let : Module.IsTorsionFree R H := by
    apply Function.Injective.moduleIsTorsionFree (R := R) (M := H) (N := L) HomogeneousLocalization.val
      (HomogeneousLocalization.val_injective _)
    intro c z
    change HomogeneousLocalization.val (g c * z) = c • HomogeneousLocalization.val z
    rw [HomogeneousLocalization.val_mul, Algebra.smul_def]
    congr 1
  change Module.Flat R H
  infer_instance

lemma gradedStructure_flat : Flat (Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (Proj.affineOpenCover 𝒜).openCover
  intro s
  change Flat (Proj.awayι 𝒜 (s.2 : S) s.2.2 s.1.2 ≫ _)
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  exact Flat.SpecMap_iff.mpr (homogeneousLocalization_flat 𝒜 (s.2 : S))

end GradedFlatness

namespace GradedQuotient
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (J : HomogeneousIdeal 𝒜)

def grading : ℕ → Submodule R (S ⧸ J.toIdeal) :=
  HomogeneousIdealQuotientGrading.quotGradingSubmodule 𝒜 J.toIdeal

local instance graded : GradedAlgebra (grading 𝒜 J) :=
  HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous

def scheme : Scheme.{u} := Proj (grading 𝒜 J)

def quotientMap : 𝒜 →+*ᵍ grading 𝒜 J where
  __ := Ideal.Quotient.mk J.toIdeal
  map_mem := fun hp => HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hp

lemma irrelevant : HomogeneousIdeal.irrelevant (grading 𝒜 J) ≤
    (HomogeneousIdeal.irrelevant 𝒜).map (quotientMap 𝒜 J) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd p hp
  obtain ⟨q, hq, rfl⟩ :=
    (HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff _ _).mp hp
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hd hq)

def embedding : scheme 𝒜 J ⟶ Proj 𝒜 :=
  Proj.map (quotientMap 𝒜 J) (irrelevant 𝒜 J)

lemma away_surjective (d : ℕ) (p : S) (hp : p ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map
      (𝒜 := 𝒜) (ℬ := grading 𝒜 J) (quotientMap 𝒜 J) p) := by
  intro z
  obtain ⟨m, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading 𝒜 J) ((quotientMap 𝒜 J).map_mem hp) z
  obtain ⟨v, hv, rfl⟩ :=
    (HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff _ _).mp hq
  refine ⟨HomogeneousLocalization.Away.mk _ hp m v hv, ?_⟩
  exact HomogeneousLocalization.Away.map_mk _ _ _ _ _ _

lemma embedding_closed : IsClosedImmersion (embedding 𝒜 J) := by
  exact projMap_closed_of_piece_surjective (𝒜 := 𝒜) (ℬ := grading 𝒜 J)
    (quotientMap 𝒜 J) (irrelevant 𝒜 J) (away_surjective 𝒜 J)

def structureMap : scheme 𝒜 J ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading 𝒜 J) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((grading 𝒜 J) 0)))

lemma embedding_over : embedding 𝒜 J ≫
    (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) =
    structureMap 𝒜 J := by
  apply (Proj.mapAffineOpenCover (quotientMap 𝒜 J) (irrelevant 𝒜 J)).openCover.hom_ext
  intro s
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    embedding, structureMap,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rw [Proj.awayι_comp_map_assoc _ _ s.1.2 _ s.2.2,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

lemma structureMap_flat [IsDedekindDomain R] [Module.Flat R (S ⧸ J.toIdeal)] :
    Flat (structureMap 𝒜 J) := gradedStructure_flat (grading 𝒜 J)

end GradedQuotient

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

/-- Multiplication by the parameter can be cancelled after passing down one
thickness. Cancellation takes place in the untruncated regular node ring. -/
lemma parameter_cancel_to_previous (n : ℕ) (z : A k (1+n))
    (hz : base k (1+n) (parameter k (1+n)) * z = 0) :
    truncReduce _ (ArithmeticThetaNodeCharts.t k) n (1+n) (Nat.le_add_left n 1) z = 0 := by
  apply (trunc_pow_mul_eq_zero_iff _ (node_parameter_regular k) 1 n z).mp
  rw [node_parameter_power, pow_one]
  exact hz

/-- Homogeneous parameter saturation of the actual relation ideal. -/
lemma homogeneous_parameter_saturated (hb : CompatibleBases k T a b)
    {d : ℕ} {p : MvPolynomial (Fin (3*r)) (PowerSeries k)} (hp : p.IsHomogeneous d)
    (htp : C PowerSeries.X * p ∈ formalRelations k b) : p ∈ formalRelations k b := by
  apply (homogeneous_formal_iff k b hp).mpr
  have htp' : (C PowerSeries.X * p).IsHomogeneous d := by
    simpa using (isHomogeneous_C (Fin (3*r)) (PowerSeries.X : PowerSeries k)).mul hp
  have hz := (homogeneous_formal_iff k b htp').mp htp
  intro n i
  have hz' : base k (1+n) (parameter k (1+n)) * evaluate k b (1+n) i p = 0 := by
    simpa only [map_mul, FormalHomogeneousPresentationR0135.eval_C, parameter] using hz (1+n) i
  have hred := parameter_cancel_to_previous k n _ hz'
  rw [eval_reduce k b hb] at hred
  exact hred

/-- The degree tag permits cancellation for arbitrary polynomials degree by degree. -/
lemma parameter_saturated (hb : CompatibleBases k T a b)
    {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (htp : C PowerSeries.X * p ∈ formalRelations k b) : p ∈ formalRelations k b := by
  rw [← sum_homogeneousComponent p]
  apply Ideal.sum_mem
  intro d hd
  apply homogeneous_parameter_saturated k b hb (homogeneousComponent_isHomogeneous d p)
  have h := formal_component k b d htp
  simpa only [homogeneousComponent_C_mul] using h

lemma parameter_pow_saturated (hb : CompatibleBases k T a b)
    (m : ℕ) {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (htp : C (PowerSeries.X ^ m) * p ∈ formalRelations k b) : p ∈ formalRelations k b := by
  induction m with
  | zero => simpa using htp
  | succ m ih =>
    apply ih
    apply parameter_saturated k b hb
    simpa only [pow_succ', map_mul, mul_assoc] using htp

/-- Every nonzero base scalar is a parameter power times a unit. -/
lemma scalar_saturated (hb : CompatibleBases k T a b)
    (c : PowerSeries k) (hc : c ≠ 0)
    {p : MvPolynomial (Fin (3*r)) (PowerSeries k)}
    (hcp : C c * p ∈ formalRelations k b) : p ∈ formalRelations k b := by
  have hfactor := PowerSeries.X_pow_order_mul_divXPowOrder (f := c)
  obtain ⟨v, hv⟩ := PowerSeries.isUnit_divided_by_X_pow_order hc
  apply parameter_pow_saturated k b hb c.order.toNat
  have hm := (formalRelations k b).mul_mem_left (C (↑v⁻¹ : PowerSeries k)) hcp
  rw [← hfactor, ← hv, map_mul] at hm
  simpa only [← mul_assoc, ← map_mul, mul_left_comm (↑v⁻¹ : PowerSeries k),
    Units.inv_mul, mul_one] using hm

/-- Torsion-freeness concerns the prescribed power-series scalar structure. -/
lemma quotient_torsionFree (hb : CompatibleBases k T a b) :
    Module.IsTorsionFree (PowerSeries k)
      (MvPolynomial (Fin (3*r)) (PowerSeries k) ⧸ formalRelations k b) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro c z hz
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply scalar_saturated k b hb c hc
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (formalRelations k b) (c • p) = 0 at hz
  simpa only [MvPolynomial.smul_eq_C_mul] using hz

/-- The full graded coordinate ring is flat over the actual power-series base. -/
lemma quotient_flat (hb : CompatibleBases k T a b) :
    Module.Flat (PowerSeries k)
      (MvPolynomial (Fin (3*r)) (PowerSeries k) ⧸ formalRelations k b) := by
  let := quotient_torsionFree k b hb
  infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra

lemma relations_homogeneous :
    (formalRelations k b).IsHomogeneous (homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) := by
  obtain ⟨l, f, d, hd, hspan⟩ := finite_homogeneous_generators k b
  rw [← hspan]
  apply Ideal.homogeneous_span
  rintro p ⟨j, rfl⟩
  exact ⟨d j, hd j⟩

def formalHomogeneousIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) :=
  ⟨formalRelations k b, relations_homogeneous k b⟩

/-- The projective scheme of the actual formal relation quotient. -/
def candidate : Scheme.{u} :=
  GradedQuotient.scheme (homogeneousSubmodule (Fin (3*r)) (PowerSeries k))
    (formalHomogeneousIdeal k b)

def candidateEmbedding : candidate k b ⟶ projectiveSpace (PowerSeries k) (3*r) :=
  GradedQuotient.embedding _ (formalHomogeneousIdeal k b)

lemma candidateEmbedding_closed : IsClosedImmersion (candidateEmbedding k b) :=
  GradedQuotient.embedding_closed _ (formalHomogeneousIdeal k b)

lemma projectiveStructure_proper (R : Type u) [CommRing R] (N : ℕ) :
    IsProper (projectiveStructure R N) := by
  let 𝒜 := homogeneousSubmodule (Fin N) R
  let : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin N) R) := by
    classical
    refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
    induction p using MvPolynomial.induction_on with
    | C c => exact Subalgebra.algebraMap_mem _ (⟨C c, isHomogeneous_C _ c⟩ : 𝒜 0)
    | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
    | mul_X p j hp =>
      exact Subalgebra.mul_mem _ (hp trivial)
        (Algebra.subset_adjoin (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hb : Function.Bijective (algebraMap R (𝒜 0)) := by
    constructor
    · intro x y h
      apply MvPolynomial.C_injective
      exact congrArg Subtype.val h
    · intro p
      refine ⟨p.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (homogeneousComponent_zero p.val).symm.trans
        (homogeneousComponent_eq_self p.property)
  let : IsIso (CommRingCat.ofHom (algebraMap R (𝒜 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  unfold projectiveStructure
  infer_instance

def candidateStructure : candidate k b ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  candidateEmbedding k b ≫ projectiveStructure (PowerSeries k) (3*r)

lemma candidateStructure_proper : IsProper (candidateStructure k b) := by
  let := candidateEmbedding_closed k b
  let := projectiveStructure_proper (PowerSeries k) (3*r)
  unfold candidateStructure
  infer_instance

lemma candidateStructure_flat (hb : CompatibleBases k T a b) : Flat (candidateStructure k b) := by
  let : Module.Flat (PowerSeries k)
      (MvPolynomial (Fin (3*r)) (PowerSeries k) ⧸ (formalHomogeneousIdeal k b).toIdeal) :=
    quotient_flat k b hb
  rw [candidateStructure, candidateEmbedding, projectiveStructure, GradedQuotient.embedding_over]
  exact GradedQuotient.structureMap_flat _ (formalHomogeneousIdeal k b)

end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135


namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
section
variable {S Q σ τ : Type u} [CommRing S] [CommRing Q]
variable [SetLike σ S] [AddSubgroupClass σ S] [SetLike τ Q] [AddSubgroupClass τ Q]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable {X : Scheme.{u}} (g : Q →+* Γ(X, ⊤))

lemma toBasicOpen_comp_map (d : ℕ) (hd : 0 < d) (p : S) (hp : p ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections ℬ g (t := f p) rfl hd (f.map_mem hp) ≫
      (Proj.basicOpen ℬ (f p)).ι ≫ Proj.map f hf =
    Proj.toBasicOpenOfGlobalSections 𝒜 (g.comp f.toRingHom) (t := p) rfl hd hp ≫
      (Proj.basicOpen 𝒜 p).ι := by
  simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι_assoc, Proj.basicOpenIsoSpec_inv_ι]
  rw [Proj.awayι_comp_map f hf hd p hp]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  obtain ⟨m, q, hq, rfl⟩ := Away.mk_surjective 𝒜 hp z
  simp only [CommRingCat.hom_ofHom, GradedRingHom.coe_toRingHom, RingHom.comp_apply, Away.map_mk,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk', map_pow]

lemma fromGlobal_comp_map
    (hg : Ideal.map g (HomogeneousIdeal.irrelevant ℬ).toIdeal = ⊤)
    (hgf : Ideal.map (g.comp f.toRingHom) (HomogeneousIdeal.irrelevant 𝒜).toIdeal = ⊤) :
    Proj.fromOfGlobalSections ℬ g hg ≫ Proj.map f hf =
      Proj.fromOfGlobalSections 𝒜 (g.comp f.toRingHom) hgf := by
  apply (Proj.openCoverOfMapIrrelevantEqTop 𝒜 (g.comp f.toRingHom) hgf).hom_ext
  rintro ⟨d, p, hd, hp⟩
  have h₁ := Scheme.Hom.resLE_comp_ι (Proj.fromOfGlobalSections ℬ g hg)
    (Proj.fromOfGlobalSections_preimage_basicOpen ℬ g hg hd (f.map_mem hp)).ge
  rw [Proj.fromOfGlobalSections_resLE ℬ g hg hd (f.map_mem hp)] at h₁
  have h₂ := Scheme.Hom.resLE_comp_ι (Proj.fromOfGlobalSections 𝒜 (g.comp f.toRingHom) hgf)
    (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 (g.comp f.toRingHom) hgf hd hp).ge
  rw [Proj.fromOfGlobalSections_resLE 𝒜 (g.comp f.toRingHom) hgf hd hp] at h₂
  simp only [GradedRingHom.coe_toRingHom] at h₁ h₂
  change (X.basicOpen (g (f p))).ι ≫ _ = (X.basicOpen (g (f p))).ι ≫ _
  rw [← Category.assoc, ← h₁, Category.assoc, toBasicOpen_comp_map f hf g d hd p hp, h₂]
  rfl
end
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry
namespace GradedQuotient
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (J : HomogeneousIdeal 𝒜)
local instance graded' : GradedAlgebra (grading 𝒜 J) :=
  HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous

lemma exists_lift_fromGlobal {X : Scheme.{u}} (g : S →+* Γ(X, ⊤))
    (hg : Ideal.map g (HomogeneousIdeal.irrelevant 𝒜).toIdeal = ⊤)
    (hJ : J.toIdeal ≤ RingHom.ker g) :
    ∃ l : X ⟶ scheme 𝒜 J, l ≫ embedding 𝒜 J = Proj.fromOfGlobalSections 𝒜 g hg := by
  let g' := Ideal.Quotient.lift J.toIdeal g hJ
  have hc : g'.comp (quotientMap 𝒜 J).toRingHom = g := by
    ext x
    exact Ideal.Quotient.lift_mk J.toIdeal g hJ
  have hi : Ideal.map (quotientMap 𝒜 J).toRingHom (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (HomogeneousIdeal.irrelevant (grading 𝒜 J)).toIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro d hd p hp
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ hd ((quotientMap 𝒜 J).map_mem hp)
  have hg' : Ideal.map g' (HomogeneousIdeal.irrelevant (grading 𝒜 J)).toIdeal = ⊤ := by
    apply top_unique
    rw [← hg, ← hc, ← Ideal.map_map]
    exact Ideal.map_mono hi
  refine ⟨Proj.fromOfGlobalSections (grading 𝒜 J) g' hg', ?_⟩
  have hgf : Ideal.map (g'.comp (quotientMap 𝒜 J).toRingHom)
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal = ⊤ := by rw [hc]; exact hg
  exact (fromGlobal_comp_map (quotientMap 𝒜 J) (irrelevant 𝒜 J) g' hg' hgf).trans
    (by congr 1)
end GradedQuotient

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalRelationsEffectivityR0135 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

lemma formalRelations_le_chart_kernel (n : ℕ) (i : Fin r) :
    formalRelations k b ≤ RingHom.ker (coefficientChartMap k (b n) i) := by
  intro p hp
  change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (evaluate k b n i p) = 0
  suffices evaluate k b n i p = 0 by rw [this, map_zero]
  rw [← sum_homogeneousComponent p, map_sum]
  apply Finset.sum_eq_zero
  intro d _
  exact (homogeneous_formal_iff k b (homogeneousComponent_isHomogeneous d p)).mp
    (formal_component k b d hp) n i

lemma exists_chartLift (n : ℕ)
    (j : (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : RealizesEmbedding k (T.atlas n) (b n) j) (i : Fin r) :
    ∃ l : specA k n ⟶ candidate k b,
      l ≫ candidateEmbedding k b = (T.atlas n).chart i ≫ j := by
  obtain ⟨hi, he⟩ := hj i
  rw [he]
  exact GradedQuotient.exists_lift_fromGlobal _ (formalHomogeneousIdeal k b)
    (coefficientChartMap k (b n) i) hi (formalRelations_le_chart_kernel k b n i)

lemma exists_stageLift (n : ℕ)
    (j : (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : RealizesEmbedding k (T.atlas n) (b n) j) :
    ∃ l : (T.atlas n).X ⟶ candidate k b, l ≫ candidateEmbedding k b = j := by
  let : IsClosedImmersion (candidateEmbedding k b) := candidateEmbedding_closed k b
  let : SurjectiveOnStalks (candidateEmbedding k b) :=
    (candidateEmbedding_closed k b).toSurjectiveOnStalks
  let : Mono (candidateEmbedding k b) := SurjectiveOnStalks.mono_of_injective
    (candidateEmbedding k b).isClosedEmbedding.injective
  choose l hl using exists_chartLift k b n j hj
  have hcompat (i : Fin r) :
      leftLeg k n (T.overlap n) ≫ l i = rightLeg k n ≫ l (next r hr i) := by
    apply (cancel_mono (candidateEmbedding k b)).mp
    rw [Category.assoc, Category.assoc, hl, hl, ← Category.assoc, ← Category.assoc,
      ((T.atlas n).adjacent i).w]
  refine ⟨(T.atlas n).desc l hcompat, ?_⟩
  apply (T.atlas n).hom_ext
  intro i
  rw [← Category.assoc, (T.atlas n).chart_desc, hl]
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalRelationsEffectivityR0135 MvPolynomial
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

lemma candidateEmbedding_mono : Mono (candidateEmbedding k b) := by
  let : SurjectiveOnStalks (candidateEmbedding k b) :=
    (candidateEmbedding_closed k b).toSurjectiveOnStalks
  exact SurjectiveOnStalks.mono_of_injective
    (candidateEmbedding_closed k b).isClosedEmbedding.injective

variable (j : ∀ n, (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
variable (hj : ProjectiveSystem k T a b j)

def stageInclusion (n : ℕ) : (T.atlas n).X ⟶ candidate k b :=
  (exists_stageLift k b n (j n) (hj.1 n).2.1).choose

lemma stageInclusion_embedding (n : ℕ) :
    stageInclusion k b j hj n ≫ candidateEmbedding k b = j n :=
  (exists_stageLift k b n (j n) (hj.1 n).2.1).choose_spec

lemma stageInclusion_over (n : ℕ) :
    stageInclusion k b j hj n ≫ candidateStructure k b =
      (T.atlas n).p ≫ baseInclusion k n := by
  rw [candidateStructure, ← Category.assoc, stageInclusion_embedding]
  exact (hj.1 n).2.2

lemma stageInclusion_transition (n N : ℕ) (h : n ≤ N) :
    T.transition n N h ≫ stageInclusion k b j hj N = stageInclusion k b j hj n := by
  let := candidateEmbedding_mono k b
  apply (cancel_mono (candidateEmbedding k b)).mp
  rw [Category.assoc, stageInclusion_embedding, stageInclusion_embedding]
  exact hj.2 n N h

lemma stageInclusion_closed (n : ℕ) : IsClosedImmersion (stageInclusion k b j hj n) := by
  let := candidateEmbedding_closed k b
  let : IsClosedImmersion (stageInclusion k b j hj n ≫ candidateEmbedding k b) := by
    rw [stageInclusion_embedding]
    exact (hj.1 n).1
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (candidateEmbedding k b)

def candidateModel : Model k T where
  X := candidate k b
  p := candidateStructure k b
  inclusion := stageInclusion k b j hj

omit [CharZero k] in
lemma coefficientReduction_kernel (n : ℕ) :
    RingHom.ker (coefficientReduction k r n) =
      Ideal.span {C (PowerSeries.X ^ (n+1) : PowerSeries k)} := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (C_dvd_iff_map_hom_eq_zero (trunc (PowerSeries k) PowerSeries.X n)
    (PowerSeries.X ^ (n+1)) (fun c => by
      change Ideal.Quotient.mk _ c = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]) p).symm

lemma stageRelations_comap (h3 : 3 ≤ r) (hb : CompatibleBases k T a b) (n : ℕ) :
    Ideal.comap (coefficientReduction k r n) (relationsAt k b n) =
      formalRelations k b ⊔ Ideal.span {C (PowerSeries.X ^ (n+1) : PowerSeries k)} := by
  rw [← exact_reduction k b h3 hb n, Ideal.comap_map_of_surjective (coefficientReduction k r n)
    (MvPolynomial.map_surjective (trunc (PowerSeries k) PowerSeries.X n) Ideal.Quotient.mk_surjective),
    ← RingHom.ker_eq_comap_bot, coefficientReduction_kernel]
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace GradedQuotient
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (J : HomogeneousIdeal 𝒜)
local instance gradedKernel : GradedAlgebra (grading 𝒜 J) :=
  HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
lemma away_map_mk_eq_zero_iff {d : ℕ} (p : S) (hp : p ∈ 𝒜 d)
    (m : ℕ) (q : S) (hq : q ∈ 𝒜 (m • d)) :
    Away.map (quotientMap 𝒜 J) p (Away.mk 𝒜 hp m q hq) = 0 ↔
      ∃ l : ℕ, p^l * q ∈ J.toIdeal := by
  rw [Away.map_mk, ← (HomogeneousLocalization.val_injective _).eq_iff,
    Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_, l, rfl⟩, hl⟩
    refine ⟨l, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa only [quotientMap, GradedRingHom.coe_mk, map_mul, map_pow] using hl
  · rintro ⟨l, hl⟩
    refine ⟨⟨(quotientMap 𝒜 J p)^l, l, rfl⟩, ?_⟩
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hl
    simpa only [quotientMap, GradedRingHom.coe_mk, map_mul, map_pow] using hz
end GradedQuotient
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalRelationsEffectivityR0135 MvPolynomial
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

lemma homogeneous_stage_mem_iff {d : ℕ}
    (q : MvPolynomial (Fin (3*r)) (PowerSeries k)) (hq : q.IsHomogeneous d) (n : ℕ) :
    q ∈ Ideal.comap (coefficientReduction k r n) (relationsAt k b n) ↔
      ∀ i, evaluate k b n i q = 0 := by
  change coefficientReduction k r n q ∈ relationsAt k b n ↔ _
  rw [homogeneous_relation_iff k b n d _ (show (coefficientReduction k r n q).IsHomogeneous d from hq.map _)]
  simp only [← eval_reduction]

lemma simultaneous_localized_kernel {d e : ℕ}
    (v q : MvPolynomial (Fin (3*r)) (PowerSeries k))
    (hv : v.IsHomogeneous d) (hq : q.IsHomogeneous e) (n : ℕ) :
    (∀ i : Fin r, ∃ l : ℕ, (evaluate k b n i v)^l * evaluate k b n i q = 0) ↔
      ∃ l : ℕ, v^l * q ∈ Ideal.comap (coefficientReduction k r n) (relationsAt k b n) := by
  classical
  constructor
  · intro h
    choose l hl using h
    let L := ∑ i : Fin r, l i
    refine ⟨L, (homogeneous_stage_mem_iff k b _ ((hv.pow L).mul hq) n).mpr ?_⟩
    intro i
    have hi : l i ≤ L := Finset.single_le_sum (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
    rw [map_mul, map_pow]
    calc
      _ = (evaluate k b n i v)^(L-l i) * ((evaluate k b n i v)^l i * evaluate k b n i q) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
      _ = 0 := by rw [hl, mul_zero]
  · rintro ⟨l, hl⟩ i
    refine ⟨l, ?_⟩
    have hz := (homogeneous_stage_mem_iff k b _ ((hv.pow l).mul hq) n).mp hl i
    simpa only [map_mul, map_pow] using hz

lemma simultaneous_localized_formal_kernel (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    {d e : ℕ} (v q : MvPolynomial (Fin (3*r)) (PowerSeries k))
    (hv : v.IsHomogeneous d) (hq : q.IsHomogeneous e) (n : ℕ) :
    (∀ i : Fin r, ∃ l : ℕ, (evaluate k b n i v)^l * evaluate k b n i q = 0) ↔
      ∃ l : ℕ, v^l * q ∈ formalRelations k b ⊔
        Ideal.span {C (PowerSeries.X ^ (n+1) : PowerSeries k)} := by
  rw [simultaneous_localized_kernel k b v q hv hq n, stageRelations_comap k b h3 hb]
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
section
variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} [IsAffine X]
variable (g : S →+* Γ(X, ⊤))
variable (hg : Ideal.map g (HomogeneousIdeal.irrelevant 𝒜).toIdeal = ⊤)
lemma fromGlobal_fraction_eq_zero_iff {d : ℕ} (hd : 0 < d) (v : S) (hv : v ∈ 𝒜 d)
    (m : ℕ) (q : S) (hq : q ∈ 𝒜 (m • d)) :
    (Proj.fromOfGlobalSections 𝒜 g hg).appLE (Proj.basicOpen 𝒜 v) (X.basicOpen (g v))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 g hg hd hv).ge
      (Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv m q hq)) = 0 ↔
      ∃ l : ℕ, (g v)^l * g q = 0 := by
  let ρ := X.presheaf.map (homOfLE (X.basicOpen_le (g v))).op
  have hu : IsUnit (ρ (g v)) := X.toRingedSpace.isUnit_res_basicOpen (g v)
  have he := Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul_pow 𝒜 g hg hd hv m q hq
  constructor
  · intro hz
    rw [hz, zero_mul] at he
    exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X
      (isAffineOpen_top X) (g q) (g v) he.symm
  · rintro ⟨l, hl⟩
    have hz : ρ (g q) = 0 := by
      apply (hu.pow l).mul_left_cancel
      rw [mul_zero, ← map_pow, ← map_mul, hl, map_zero]
    apply (hu.pow m).mul_right_cancel
    rw [zero_mul, he]
    exact hz
lemma fromGlobal_kernel_fraction_iff [QuasiCompact (Proj.fromOfGlobalSections 𝒜 g hg)]
    {d : ℕ} (hd : 0 < d) (v : S) (hv : v ∈ 𝒜 d)
    (m : ℕ) (q : S) (hq : q ∈ 𝒜 (m • d)) :
    Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv m q hq) ∈
      (Proj.fromOfGlobalSections 𝒜 g hg).ker.ideal
        ⟨Proj.basicOpen 𝒜 v, Proj.isAffineOpen_basicOpen 𝒜 v hv hd⟩ ↔
      ∃ l : ℕ, (g v)^l * g q = 0 := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← fromGlobal_fraction_eq_zero_iff 𝒜 g hg hd v hv m q hq]
  have he := Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 g hg hd hv
  let ρ := X.presheaf.map (homOfLE he.ge).op
  have : IsIso ρ := by
    change IsIso (X.presheaf.map (eqToHom he.symm).op)
    infer_instance
  exact (map_eq_zero_iff ρ.hom (ConcreteCategory.bijective_of_isIso ρ).1).symm

end
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace GradedQuotient
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (J : HomogeneousIdeal 𝒜)
local instance gradedSheaf : GradedAlgebra (grading 𝒜 J) :=
  HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
lemma embedding_kernel_fraction_iff {d : ℕ} (hd : 0 < d) (v : S) (hv : v ∈ 𝒜 d)
    (m : ℕ) (q : S) (hq : q ∈ 𝒜 (m • d)) :
    Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv m q hq) ∈
      (embedding 𝒜 J).ker.ideal
        ⟨Proj.basicOpen 𝒜 v, Proj.isAffineOpen_basicOpen 𝒜 v hv hd⟩ ↔
      ∃ l : ℕ, v^l * q ∈ J.toIdeal := by
  let : IsClosedImmersion (embedding 𝒜 J) := embedding_closed 𝒜 J
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← away_map_mk_eq_zero_iff 𝒜 J v hv m q hq]
  let ℬ := grading 𝒜 J
  let f := quotientMap 𝒜 J
  have he := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f (irrelevant 𝒜 J) hv)
    (Away.mk 𝒜 hv m q hq)
  have he' : (embedding 𝒜 J).app (Proj.basicOpen 𝒜 v)
      (Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv m q hq)) =
      Proj.awayToSection ℬ (f v) (Away.map f v (Away.mk 𝒜 hv m q hq)) := by
    change ((embedding 𝒜 J).app (Proj.basicOpen 𝒜 v) ≫
      (Proj ℬ).presheaf.map (𝟙 _)) (Proj.awayToSection 𝒜 v (Away.mk 𝒜 hv m q hq)) = _ at he
    erw [CategoryTheory.Functor.map_id] at he
    exact he

  rw [he']
  have hi : Function.Injective (Proj.awayToSection ℬ (f v)) := by
    rw [← Proj.basicOpenIsoAway_hom ℬ (f v) (f.map_mem hv) hd]
    exact (ConcreteCategory.bijective_of_isIso _).1
  exact map_eq_zero_iff (Proj.awayToSection ℬ (f v)).hom hi
end GradedQuotient
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalRelationsEffectivityR0135 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

lemma stage_kernel_fraction_iff (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (n : ℕ) (j : (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : RealizesEmbedding k (T.atlas n) (b n) j) [IsClosedImmersion j]
    {d : ℕ} (hd : 0 < d) (v : MvPolynomial (Fin (3*r)) (PowerSeries k)) (hv : v.IsHomogeneous d)
    (m : ℕ) (q : MvPolynomial (Fin (3*r)) (PowerSeries k)) (hq : q.IsHomogeneous (m*d)) :
    Proj.awayToSection _ v (Away.mk _ hv m q hq) ∈
      j.ker.ideal ⟨Proj.basicOpen _ v, Proj.isAffineOpen_basicOpen _ v hv hd⟩ ↔
      ∃ l : ℕ, v^l * q ∈ formalRelations k b ⊔
        Ideal.span {C (PowerSeries.X ^ (n+1) : PowerSeries k)} := by
  rw [← simultaneous_localized_formal_kernel k b h3 hb v q hv hq n]
  rw [← j.iInf_ker_openCover_map_comp_apply (T.atlas n).openCover]
  simp only [Ideal.mem_iInf]
  apply forall_congr'
  intro i
  obtain ⟨hi, he⟩ := hj i
  change _ ∈ ((T.atlas n).chart i ≫ j).ker.ideal _ ↔ _
  rw [he]
  let : IsAffine (specA k n) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (A k n))))
  let : QuasiSeparatedSpace (projectiveSpace (PowerSeries k) (3*r)) := by
    unfold projectiveSpace
    infer_instance
  rw [fromGlobal_kernel_fraction_iff _ _ hi hd v hv m q hq]
  apply exists_congr
  intro l
  change ((Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (evaluate k b n i v))^l *
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv (evaluate k b n i q) = 0 ↔ _
  rw [← map_pow, ← map_mul]
  exact map_eq_zero_iff (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
    (ConcreteCategory.bijective_of_isIso _).1
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
open FormalRelationsEffectivityR0135 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

def stageHomogeneousIdeal (n : ℕ) :
    HomogeneousIdeal (homogeneousSubmodule (Fin (3*r)) (PowerSeries k)) :=
  ⟨formalRelations k b ⊔ Ideal.span {C (PowerSeries.X ^ (n+1) : PowerSeries k)},
    (relations_homogeneous k b).sup (by
      apply Ideal.homogeneous_span
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact ⟨0, isHomogeneous_C _ _⟩)⟩

lemma stage_kernel_eq_quotient (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (n : ℕ) (j : (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : RealizesEmbedding k (T.atlas n) (b n) j) [IsClosedImmersion j] :
    j.ker = (GradedQuotient.embedding _ (stageHomogeneousIdeal k b n)).ker := by
  let 𝒜 := homogeneousSubmodule (Fin (3*r)) (PowerSeries k)
  let U : (Proj.affineOpenCover 𝒜).I₀ → (Proj 𝒜).affineOpens :=
    fun s => ⟨Proj.basicOpen 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)), Proj.isAffineOpen_basicOpen 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 s.1.2⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · have h := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
    convert! h using 1
    congr 1
    funext s
    exact (Proj.opensRange_awayι 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 s.1.2).symm
  intro s
  ext x
  have hs : Function.Surjective (Proj.awayToSection 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k))) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 s.1.2]
    exact (ConcreteCategory.bijective_of_isIso _).2
  obtain ⟨z, rfl⟩ := hs x
  obtain ⟨m, q, hq, rfl⟩ := Away.mk_surjective 𝒜 s.2.2 z
  change Proj.awayToSection 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) (Away.mk 𝒜 s.2.2 m q hq) ∈
    j.ker.ideal ⟨_, Proj.isAffineOpen_basicOpen 𝒜 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 s.1.2⟩ ↔ _
  rw [stage_kernel_fraction_iff k b h3 hb n j hj s.1.2 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 m q hq,
    GradedQuotient.embedding_kernel_fraction_iff 𝒜 (stageHomogeneousIdeal k b n)
      s.1.2 (s.2 : MvPolynomial (Fin (3*r)) (PowerSeries k)) s.2.2 m q hq]
  rfl

lemma stage_iso_quotient (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (n : ℕ) (j : (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : RealizesEmbedding k (T.atlas n) (b n) j) [IsClosedImmersion j] :
    ∃ e : (T.atlas n).X ≅ GradedQuotient.scheme _ (stageHomogeneousIdeal k b n),
      e.hom ≫ GradedQuotient.embedding _ (stageHomogeneousIdeal k b n) = j := by
  let f := GradedQuotient.embedding _ (stageHomogeneousIdeal k b n)
  let : IsClosedImmersion f := GradedQuotient.embedding_closed _ _
  have he := stage_kernel_eq_quotient k b h3 hb n j hj
  let l := IsClosedImmersion.lift f j he.symm.le
  let : IsIso l := IsClosedImmersion.isIso_lift f j he.symm
  exact ⟨asIso l, IsClosedImmersion.lift_fac f j he.symm.le⟩
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace GradedQuotient
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (J K : HomogeneousIdeal 𝒜) (h : J.toIdeal ≤ K.toIdeal)
attribute [local instance] graded

def transition : grading 𝒜 J →+*ᵍ grading 𝒜 K where
  __ := Ideal.Quotient.factor h
  map_mem := by
    intro d q hq
    obtain ⟨p, hp, rfl⟩ :=
      (HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff _ _).mp hq
    exact HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hp

lemma transition_piece_surjective (d : ℕ) (q : S ⧸ K.toIdeal)
    (hq : q ∈ grading 𝒜 K d) :
    ∃ p : S ⧸ J.toIdeal, p ∈ grading 𝒜 J d ∧ transition 𝒜 J K h p = q := by
  obtain ⟨p, hp, rfl⟩ :=
    (HomogeneousIdealQuotientGrading.mem_quotGradingSubmodule_iff _ _).mp hq
  exact ⟨Ideal.Quotient.mk J.toIdeal p,
    HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hp, rfl⟩

lemma transition_irrelevant : HomogeneousIdeal.irrelevant (grading 𝒜 K) ≤
    (HomogeneousIdeal.irrelevant (grading 𝒜 J)).map (transition 𝒜 J K h) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd q hq
  obtain ⟨p, hp, rfl⟩ := transition_piece_surjective 𝒜 J K h d q hq
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hd hp)

def transitionEmbedding : scheme 𝒜 K ⟶ scheme 𝒜 J :=
  Proj.map (transition 𝒜 J K h) (transition_irrelevant 𝒜 J K h)

lemma transitionEmbedding_embedding :
    transitionEmbedding 𝒜 J K h ≫ embedding 𝒜 J = embedding 𝒜 K := by
  unfold transitionEmbedding embedding
  rw [← Proj.map_comp]
  rfl

lemma transition_away_surjective (d : ℕ) (p : S ⧸ J.toIdeal) (hp : p ∈ grading 𝒜 J d) :
    Function.Surjective (Away.map (transition 𝒜 J K h) p) := by
  intro z
  obtain ⟨m, q, hq, rfl⟩ := Away.mk_surjective (grading 𝒜 K)
    ((transition 𝒜 J K h).map_mem hp) z
  obtain ⟨q', hq', rfl⟩ := transition_piece_surjective 𝒜 J K h _ q hq
  exact ⟨Away.mk _ hp m q' hq', Away.map_mk _ _ _ _ _ _⟩

lemma transitionEmbedding_closed : IsClosedImmersion (transitionEmbedding 𝒜 J K h) :=
  projMap_closed_of_piece_surjective (transition 𝒜 J K h) (transition_irrelevant 𝒜 J K h)
    (transition_away_surjective 𝒜 J K h)
end GradedQuotient
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {N : ℕ}
local notation "𝒜" => homogeneousSubmodule (Fin N) R

def awayScalar (v : MvPolynomial (Fin N) R) : R →+* Away 𝒜 v :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers v)).comp (algebraMap R (𝒜 0))

lemma awayScalar_val (v : MvPolynomial (Fin N) R) (c : R) :
    (awayScalar v c).val = algebraMap (MvPolynomial (Fin N) R) (Localization.Away v) (C c) := rfl

lemma away_add {d : ℕ} {v : MvPolynomial (Fin N) R} (hv : v.IsHomogeneous d)
    (m : ℕ) (p q : MvPolynomial (Fin N) R) (hp : p.IsHomogeneous (m*d))
    (hq : q.IsHomogeneous (m*d)) :
    Away.mk 𝒜 hv m (p+q) (hp.add hq) = Away.mk 𝒜 hv m p hp + Away.mk 𝒜 hv m q hq := by
  apply HomogeneousLocalization.val_injective
  simp only [val_add, Away.val_mk, Localization.add_mk_self]

lemma away_scalar_mul {d : ℕ} {v : MvPolynomial (Fin N) R} (hv : v.IsHomogeneous d)
    (m : ℕ) (c : R) (p : MvPolynomial (Fin N) R) (hp : p.IsHomogeneous (m*d)) :
    awayScalar v c * Away.mk 𝒜 hv m p hp =
      Away.mk 𝒜 hv m (C c * p) (by simpa using (isHomogeneous_C _ c).mul hp) := by
  apply HomogeneousLocalization.val_injective
  simp only [val_mul, awayScalar_val, Away.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _

lemma away_extend {d : ℕ} {v : MvPolynomial (Fin N) R} (hv : v.IsHomogeneous d)
    (m l : ℕ) (p : MvPolynomial (Fin N) R) (hp : p.IsHomogeneous (m*d)) :
    Away.mk 𝒜 hv m p hp =
      Away.mk 𝒜 hv (l+m) (v^l*p) (by simpa [add_mul, mul_comm d l] using (hv.pow l).mul hp) := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  dsimp
  rw [pow_add]
  ring

lemma homogeneous_split_principal (I : Ideal (MvPolynomial (Fin N) R))
    (hI : I.IsHomogeneous 𝒜) (c : R) {d : ℕ} (p : MvPolynomial (Fin N) R)
    (hp : p.IsHomogeneous d) (h : p ∈ I ⊔ Ideal.span {C c}) :
    ∃ a b : MvPolynomial (Fin N) R, a.IsHomogeneous d ∧ b.IsHomogeneous d ∧
      a ∈ I ∧ p = a + C c * b := by
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp h
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨homogeneousComponent d a, homogeneousComponent d b,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
  · exact homogeneousComponent_mem_of_mem hI ha d
  · rw [← homogeneousComponent_C_mul, ← map_add, he,
      homogeneousComponent_eq_self hp]
attribute [local instance] GradedQuotient.graded

lemma awayScalar_eq_mk {d : ℕ} {v : MvPolynomial (Fin N) R} (hv : v.IsHomogeneous d) (c : R) :
    awayScalar v c = Away.mk 𝒜 hv 0 (C c) (by simp) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayScalar_val, Away.val_mk, pow_zero]
  exact (Localization.mk_one_eq_algebraMap _).symm

lemma away_quotient_kernel_sup (J K : HomogeneousIdeal 𝒜) (c : R)
    (hK : K.toIdeal = J.toIdeal ⊔ Ideal.span {C c})
    {d : ℕ} (v : MvPolynomial (Fin N) R) (hv : v.IsHomogeneous d) :
    RingHom.ker (Away.map (GradedQuotient.quotientMap 𝒜 K) v) =
      RingHom.ker (Away.map (GradedQuotient.quotientMap 𝒜 J) v) ⊔ Ideal.span {awayScalar v c} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective 𝒜 hv z
    obtain ⟨l, hl⟩ := (GradedQuotient.away_map_mk_eq_zero_iff 𝒜 K v hv m p hp).mp hz
    rw [hK] at hl
    have hdeg : (v^l*p).IsHomogeneous ((l+m)*d) := by
      simpa [add_mul, mul_comm d l] using (hv.pow l).mul hp
    obtain ⟨a, b, ha, hb, haI, he⟩ := homogeneous_split_principal J.toIdeal J.isHomogeneous c _ hdeg hl
    have hfrac : Away.mk 𝒜 hv m p hp = Away.mk 𝒜 hv (l+m) a ha +
        awayScalar v c * Away.mk 𝒜 hv (l+m) b hb := by
      rw [away_scalar_mul, ← away_add]
      trans Away.mk 𝒜 hv (l+m) (v^l*p) hdeg
      · exact away_extend hv m l p hp
      · congr 1
    rw [hfrac]
    apply Ideal.add_mem
    · apply Ideal.mem_sup_left
      apply (GradedQuotient.away_map_mk_eq_zero_iff 𝒜 J v hv (l+m) a ha).mpr
      exact ⟨0, by simpa using haI⟩
    · apply Ideal.mem_sup_right
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply sup_le
    · intro z hz
      obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective 𝒜 hv z
      obtain ⟨l, hl⟩ := (GradedQuotient.away_map_mk_eq_zero_iff 𝒜 J v hv m p hp).mp hz
      apply (GradedQuotient.away_map_mk_eq_zero_iff 𝒜 K v hv m p hp).mpr
      exact ⟨l, hK ▸ Ideal.mem_sup_left hl⟩
    · apply Ideal.span_le.mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      rw [awayScalar_eq_mk hv c]
      apply (GradedQuotient.away_map_mk_eq_zero_iff 𝒜 K v hv 0 (C c) _).mpr
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, hK]
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
lemma ring_pushout_of_surjective_kernel {R A B D : CommRingCat.{u}}
    (f : R ⟶ A) (g : R ⟶ B) (i : A ⟶ D) (j : B ⟶ D)
    (hcomm : f ≫ i = g ≫ j) (hg : Function.Surjective g) (hi : Function.Surjective i)
    (hk : RingHom.ker i.hom = Ideal.map f.hom (RingHom.ker g.hom)) : IsPushout f g i j := by
  have hkill (s : PushoutCocone f g) : RingHom.ker i.hom ≤ RingHom.ker s.inl.hom := by
    rw [hk, Ideal.map_le_iff_le_comap]
    intro x hx
    change s.inl (f x) = 0
    rw [← CommRingCat.comp_apply, s.condition, CommRingCat.comp_apply]
    rw [show g x = 0 from hx, map_zero]
  let l (s : PushoutCocone f g) : D ⟶ s.pt :=
    CommRingCat.ofHom (RingHom.liftOfSurjective i.hom hi ⟨s.inl.hom, hkill s⟩)
  have hl (s : PushoutCocone f g) : i ≫ l s = s.inl := by
    ext x
    simp [l, RingHom.liftOfRightInverse_comp_apply]
  refine ⟨⟨hcomm⟩, ⟨PushoutCocone.IsColimit.mk _ l hl ?_ ?_⟩⟩
  · intro s
    ext x
    obtain ⟨x, rfl⟩ := hg x
    have he : g ≫ j ≫ l s = g ≫ s.inr := by
      rw [← Category.assoc, ← hcomm, Category.assoc, hl, s.condition]
    exact ConcreteCategory.congr_hom he x

  · intro s m hm _
    ext x
    obtain ⟨x, rfl⟩ := hi x
    exact ConcreteCategory.congr_hom (hm.trans (hl s).symm) x
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
namespace ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra GradedQuotient.graded
variable {R : Type u} [CommRing R] {N : ℕ}
local notation "𝒜" => homogeneousSubmodule (Fin N) R
open GradedQuotient

def quotientChartScalar (J : HomogeneousIdeal 𝒜) (v : MvPolynomial (Fin N) R) :
    R →+* Away (grading 𝒜 J) (quotientMap 𝒜 J v) :=
  (fromZeroRingHom (grading 𝒜 J) (Submonoid.powers (quotientMap 𝒜 J v))).comp
    (algebraMap R ((grading 𝒜 J) 0))

lemma quotientChartScalar_eq (J : HomogeneousIdeal 𝒜) {d : ℕ}
    (v : MvPolynomial (Fin N) R) (hv : v.IsHomogeneous d) :
    (Away.map (quotientMap 𝒜 J) v).comp (awayScalar v) = quotientChartScalar J v := by
  ext c
  simp only [RingHom.comp_apply, awayScalar_eq_mk hv c, Away.map_mk]
  simp only [Away.val_mk, pow_zero]
  rfl

lemma relative_away_kernel (J K : HomogeneousIdeal 𝒜) (h : J.toIdeal ≤ K.toIdeal)
    (c : R) (hK : K.toIdeal = J.toIdeal ⊔ Ideal.span {C c})
    {d : ℕ} (v : MvPolynomial (Fin N) R) (hv : v.IsHomogeneous d) :
    RingHom.ker (Away.map (transition 𝒜 J K h) (quotientMap 𝒜 J v)) =
      Ideal.map (quotientChartScalar J v) (Ideal.span {c}) := by
  let F := Away.map (quotientMap 𝒜 J) v
  let G := Away.map (quotientMap 𝒜 K) v
  let H := Away.map (transition 𝒜 J K h) (quotientMap 𝒜 J v)
  have hcomp : H.comp F = G := by
    rw [← Away.map_comp]
    rfl
  have hsur : Function.Surjective F := away_surjective 𝒜 J d v hv
  have he : Ideal.map F (RingHom.ker G) = RingHom.ker H := by
    rw [← hcomp, ← RingHom.comap_ker, Ideal.map_comap_of_surjective F hsur]
  have hz : Ideal.map F (RingHom.ker F) = ⊥ := (Ideal.map_eq_bot_iff_le_ker F).mpr le_rfl
  rw [← he, away_quotient_kernel_sup J K c hK v hv,
    Ideal.map_sup, hz, bot_sup_eq, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton]
  congr 1

lemma principal_quotient_pullback (J K : HomogeneousIdeal 𝒜) (h : J.toIdeal ≤ K.toIdeal)
    (c : R) (hK : K.toIdeal = J.toIdeal ⊔ Ideal.span {C c})
    (R' : Type u) [CommRing R'] (red : R →+* R') (hred : Function.Surjective red)
    (hker : RingHom.ker red = Ideal.span {c})
    (β : scheme 𝒜 K ⟶ Spec (CommRingCat.of R'))
    (hcomm : transitionEmbedding 𝒜 J K h ≫ structureMap 𝒜 J =
      β ≫ Spec.map (CommRingCat.ofHom red)) :
    IsPullback (transitionEmbedding 𝒜 J K h) β (structureMap 𝒜 J)
      (Spec.map (CommRingCat.ofHom red)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (Proj.mapAffineOpenCover (quotientMap 𝒜 J) (irrelevant 𝒜 J)).openCover
  rintro ⟨⟨d, hd⟩, ⟨v, hv⟩⟩
  let qJ := quotientMap 𝒜 J
  let qK := quotientMap 𝒜 K
  let f := transition 𝒜 J K h
  let iJ := Proj.awayι (grading 𝒜 J) (qJ v) (qJ.map_mem hv) hd
  let iK := Proj.awayι (grading 𝒜 K) (qK v) (qK.map_mem hv) hd
  let H := Away.map f (qJ v)
  let B := Spec.preimage (iK ≫ β)
  have hchart : iJ ≫ structureMap 𝒜 J = Spec.map (CommRingCat.ofHom (quotientChartScalar J v)) := by
    rw [structureMap, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hsquare := (proj_chart_pullback f (transition_irrelevant 𝒜 J K h) d hd (qJ v)
    (qJ.map_mem hv)).flip
  have hring : CommRingCat.ofHom (quotientChartScalar J v) ≫ CommRingCat.ofHom H =
      CommRingCat.ofHom red ≫ B := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    rw [← hchart, ← Category.assoc, hsquare.w, Category.assoc]
    change iK ≫ (transitionEmbedding 𝒜 J K h ≫ structureMap 𝒜 J) =
      (iK ≫ β) ≫ Spec.map (CommRingCat.ofHom red)
    rw [hcomm, Category.assoc]
  have hp := ring_pushout_of_surjective_kernel
    (CommRingCat.ofHom (quotientChartScalar J v)) (CommRingCat.ofHom red)
    (CommRingCat.ofHom H) B hring hred
    (transition_away_surjective 𝒜 J K h d (qJ v) (qJ.map_mem hv)) (by
      change RingHom.ker H = Ideal.map (quotientChartScalar J v) (RingHom.ker red)
      rw [hker]
      exact relative_away_kernel J K h c hK v hv)
  have hp' := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ hp
  rw [Spec.map_preimage] at hp'
  have h₁ := hsquare.flip.isoPullback_hom_fst
  have h₂ := hsquare.flip.isoPullback_hom_snd
  refine hp'.of_iso hsquare.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans h₂.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ β) h₁) |>.symm
  · simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact hchart.symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPositiveLineR0134
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} {a : Fin r → kˣ}
variable (b : CubicBases k r hr T a)

lemma candidateStructure_eq : candidateStructure k b =
    GradedQuotient.structureMap (homogeneousSubmodule (Fin (3*r)) (PowerSeries k))
      (formalHomogeneousIdeal k b) := by
  rw [candidateStructure, candidateEmbedding, projectiveStructure, GradedQuotient.embedding_over]

lemma stageInclusion_isPullback (h3 : 3 ≤ r) (hb : CompatibleBases k T a b)
    (j : ∀ n, (T.atlas n).X ⟶ projectiveSpace (PowerSeries k) (3*r))
    (hj : ProjectiveSystem k T a b j) (n : ℕ) :
    IsPullback (stageInclusion k b j hj n) (T.atlas n).p (candidateStructure k b)
      (baseInclusion k n) := by
  let : IsClosedImmersion (j n) := (hj.1 n).1
  obtain ⟨e, he⟩ := stage_iso_quotient k b h3 hb n (j n) (hj.1 n).2.1
  let 𝒜₀ := homogeneousSubmodule (Fin (3*r)) (PowerSeries k)
  let J := formalHomogeneousIdeal k b
  let K := stageHomogeneousIdeal k b n
  have hJK : J.toIdeal ≤ K.toIdeal := le_sup_left
  let i := GradedQuotient.transitionEmbedding 𝒜₀ J K hJK
  have hi : e.hom ≫ i = stageInclusion k b j hj n := by
    let := candidateEmbedding_mono k b
    apply (cancel_mono (candidateEmbedding k b)).mp
    rw [Category.assoc]
    change e.hom ≫ (GradedQuotient.transitionEmbedding 𝒜₀ J K hJK ≫
      GradedQuotient.embedding 𝒜₀ J) = _
    rw [GradedQuotient.transitionEmbedding_embedding, he, stageInclusion_embedding]
  let β := e.inv ≫ (T.atlas n).p
  have hc : i ≫ GradedQuotient.structureMap 𝒜₀ J = β ≫ baseInclusion k n := by
    rw [← candidateStructure_eq k b]
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, hi, stageInclusion_over]
    simp [β]
  have hk : RingHom.ker (trunc (PowerSeries k) PowerSeries.X n) =
      Ideal.span {(PowerSeries.X ^ (n+1) : PowerSeries k)} := by
    change RingHom.ker (Ideal.Quotient.mk _) = _
    rw [Ideal.mk_ker, Ideal.span_singleton_pow]
  have hp := principal_quotient_pullback J K hJK (PowerSeries.X ^ (n+1)) rfl
    (ArithmeticThetaInfinitesimalPolygonR0129.R k n) (trunc (PowerSeries k) PowerSeries.X n)
    Ideal.Quotient.mk_surjective hk β hc
  refine hp.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [← hi, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (candidateStructure_eq k b).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
end ArithmeticThetaProjectiveEffectivityR0135.ProjectiveTowerEffectivityR0135

namespace ArithmeticThetaProjectiveEffectivityR0135
open CategoryTheory AlgebraicGeometry ProjectiveTowerEffectivityR0135

theorem projective_tower_effectivity :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r → ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ) (b : ArithmeticThetaProjectiveEffectivityR0135.CubicBases k r hr T a), ArithmeticThetaProjectiveEffectivityR0135.CompatibleBases k T a b → ∀ (j : ∀ n, (T.atlas n).X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace (PowerSeries k) (3*r)), ArithmeticThetaProjectiveEffectivityR0135.ProjectiveSystem k T a b j → ∃ M : ArithmeticThetaProjectiveEffectivityR0135.Model k T, ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M ∧ ∃ e : M.X ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace (PowerSeries k) (3*r), AlgebraicGeometry.IsClosedImmersion e ∧ CategoryTheory.CategoryStruct.comp e (ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure (PowerSeries k) (3*r)) = M.p ∧ ∀ n, CategoryTheory.CategoryStruct.comp (M.inclusion n) e = j n := by
  intro k _ _ r hr h3 T a b hb j hj
  refine ⟨candidateModel k b j hj, ?_, candidateEmbedding k b,
    candidateEmbedding_closed k b, rfl, stageInclusion_embedding k b j hj⟩
  exact ⟨candidateStructure_proper k b, candidateStructure_flat k b hb,
    stageInclusion_isPullback k b h3 hb j hj, stageInclusion_transition k b j hj⟩
end ArithmeticThetaProjectiveEffectivityR0135
#print axioms ArithmeticThetaProjectiveEffectivityR0135.projective_tower_effectivity
