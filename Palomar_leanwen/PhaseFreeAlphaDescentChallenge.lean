module
public import Mathlib
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace NeronModelInfra
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
namespace HomogeneousIdealQuotientGrading
open DirectSum
section Engine
variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)
def pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) : 𝒜 i →+ ℬ i :=
  AddMonoidHom.codRestrict
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i)
    (fun a => hmem i a a.2)
@[simp] lemma pieceHom_coe (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (i : ι) (a : 𝒜 i) :
    (pieceHom 𝒜 I ℬ hmem i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := rfl
lemma pieceHom_surjective (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (i : ι) : Function.Surjective (pieceHom 𝒜 I ℬ hmem i) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := hsurj i b hb
  exact ⟨⟨a, ha⟩, rfl⟩
omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in
theorem gradedMonoidOfImages [AddMonoid ι] [SetLike.GradedMonoid 𝒜] (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) : SetLike.GradedMonoid ℬ where
  one_mem := by
    have h1 : (1 : A ⧸ I) = Ideal.Quotient.mk I 1 := (map_one _).symm
    rw [h1]
    exact hmem 0 1 (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := hsurj i x hx
    obtain ⟨b, hb, rfl⟩ := hsurj j y hy
    rw [← map_mul]
    exact hmem _ _ (SetLike.mul_mem_graded ha hb)
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (y : ⨁ i, 𝒜 i) : DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y) = Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 y) := by
  refine DirectSum.induction_on y ?_ ?_ ?_
  · simp
  · intro i x
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of,
      pieceHom_coe]
  · intro x y hx hy
    rw [map_add, map_add, map_add, map_add, hx, hy]
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) : A →+ ⨁ i, ℬ i :=
  (DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : preDecompose 𝒜 I ℬ hmem a = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (decompose 𝒜 a) := rfl
lemma preDecompose_apply_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) (i : ι) : preDecompose 𝒜 I ℬ hmem a i = pieceHom 𝒜 I ℬ hmem i (decompose 𝒜 a i) := by
  rw [preDecompose_apply, DirectSum.map_apply]
lemma preDecompose_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) {i : ι} {a : A} (ha : a ∈ 𝒜 i) : preDecompose 𝒜 I ℬ hmem a = DirectSum.of (fun j => ℬ j) i ⟨Ideal.Quotient.mk I a, hmem i a ha⟩ := by
  rw [preDecompose_apply, decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl
lemma coeAddMonoidHom_preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = Ideal.Quotient.mk I a := by
  rw [preDecompose_apply, coeAddMonoidHom_map_pieceHom]
  congr 1
  exact (DirectSum.decompose 𝒜).symm_apply_apply a
lemma preDecompose_eq_zero_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) : preDecompose 𝒜 I ℬ hmem a = 0 := by
  ext i
  rw [preDecompose_apply_apply, DirectSum.zero_apply, pieceHom_coe, ZeroMemClass.coe_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hI i ha
def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem)
    (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
@[simp] lemma quotDecompose_mk
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hI : I.IsHomogeneous 𝒜) (a : A) :
    quotDecompose 𝒜 I ℬ hmem hI (Ideal.Quotient.mk I a) = preDecompose 𝒜 I ℬ hmem a := rfl
@[reducible] def decompositionOfImages
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b)
    (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition ℬ :=
  DirectSum.Decomposition.ofAddHom ℬ (quotDecompose 𝒜 I ℬ hmem hI)
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotDecompose_mk,
        coeAddMonoidHom_preDecompose])
    (by
      refine DirectSum.addHom_ext fun i b => ?_
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
      obtain ⟨a, ha, hab⟩ := hsurj i (b : A ⧸ I) b.2
      rw [← hab, quotDecompose_mk, preDecompose_of_mem 𝒜 I ℬ hmem ha]
      exact congrArg _ (Subtype.ext hab))
@[reducible] def gradedRingOfImages
    (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b)
    (hI : I.IsHomogeneous 𝒜) : GradedRing ℬ where
  toGradedMonoid := gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition := decompositionOfImages 𝒜 I ℬ hmem hsurj hI
theorem decompose_mk (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) [DirectSum.Decomposition ℬ] (a : A) : DirectSum.decompose ℬ (Ideal.Quotient.mk I a) = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (DirectSum.decompose 𝒜 a) := by
  apply (DirectSum.decompose ℬ).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [show ⇑(DirectSum.decompose ℬ).symm = ⇑(DirectSum.coeAddMonoidHom ℬ) from rfl]
  rw [coeAddMonoidHom_map_pieceHom]
  congr 1
  exact ((DirectSum.decompose 𝒜).symm_apply_apply a).symm
theorem decompose_mk_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) [DirectSum.Decomposition ℬ] (a : A) (i : ι) : (DirectSum.decompose ℬ (Ideal.Quotient.mk I a) i : A ⧸ I) = Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a i) := by
  rw [decompose_mk 𝒜 I ℬ hmem, DirectSum.map_apply, pieceHom_coe]
end Engine
section QuotGradingDef
variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
def quotGrading (i : ι) : AddSubgroup (A ⧸ I) :=
  (AddSubgroup.ofClass (𝒜 i)).map (Ideal.Quotient.mk I).toAddMonoidHom
lemma mem_quotGrading_iff {i : ι} {x : A ⧸ I} : x ∈ quotGrading 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
lemma mk_mem_quotGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) : Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I i :=
  (mem_quotGrading_iff 𝒜 I).mpr ⟨a, ha, rfl⟩
def quotGradingPieceHom (i : ι) : 𝒜 i →+ quotGrading 𝒜 I i :=
  pieceHom 𝒜 I (quotGrading 𝒜 I) (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha) i
@[simp] lemma quotGradingPieceHom_coe (i : ι) (a : 𝒜 i) :
    (quotGradingPieceHom 𝒜 I i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := rfl
lemma quotGradingPieceHom_surjective (i : ι) : Function.Surjective (quotGradingPieceHom 𝒜 I i) :=
  pieceHom_surjective 𝒜 I (quotGrading 𝒜 I) (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb) i
instance quotGradingGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotGrading 𝒜 I) :=
  gradedMonoidOfImages 𝒜 I (quotGrading 𝒜 I)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb)
end QuotGradingDef
section QuotGradingGraded
variable {ι A σ : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommRing A]
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)
@[reducible] def quotGradingGradedRing (hI : I.IsHomogeneous 𝒜) :
    GradedRing (quotGrading 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGrading 𝒜 I)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 I ha)
    (fun _ _ hb => (mem_quotGrading_iff 𝒜 I).mp hb)
    hI
instance quotGradingGradedRingOfHomogeneous (J : HomogeneousIdeal 𝒜) : GradedRing (quotGrading 𝒜 J.toIdeal) :=
  quotGradingGradedRing 𝒜 J.toIdeal J.isHomogeneous
theorem decompose_quotGrading_mk_apply (J : HomogeneousIdeal 𝒜) (a : A) (i : ι) : (DirectSum.decompose (quotGrading 𝒜 J.toIdeal) (Ideal.Quotient.mk J.toIdeal a) i : A ⧸ J.toIdeal) = Ideal.Quotient.mk J.toIdeal (DirectSum.decompose 𝒜 a i) :=
  decompose_mk_apply 𝒜 J.toIdeal (quotGrading 𝒜 J.toIdeal)
    (fun _ _ ha => mk_mem_quotGrading 𝒜 J.toIdeal ha) a i
end QuotGradingGraded
section SubmoduleVersion
variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)
def quotGradingSubmodule (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff {i : ι} {x : A ⧸ I} : x ∈ quotGradingSubmodule 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
lemma mk_mem_quotGradingSubmodule {i : ι} {a : A} (ha : a ∈ 𝒜 i) : Ideal.Quotient.mk I a ∈ quotGradingSubmodule 𝒜 I i :=
  (mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a, ha, rfl⟩
instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotGradingSubmodule 𝒜 I) :=
  gradedMonoidOfImages 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb)
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotGradingSubmodule 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb)
    hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J : HomogeneousIdeal 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal) :=
  quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
theorem decompose_quotGradingSubmodule_mk_apply (J : HomogeneousIdeal 𝒜) (a : A) (i : ι) : (DirectSum.decompose (quotGradingSubmodule 𝒜 J.toIdeal) (Ideal.Quotient.mk J.toIdeal a) i : A ⧸ J.toIdeal) = Ideal.Quotient.mk J.toIdeal (DirectSum.decompose 𝒜 a i) :=
  decompose_mk_apply 𝒜 J.toIdeal (quotGradingSubmodule 𝒜 J.toIdeal)
    (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 J.toIdeal ha) a i
end SubmoduleVersion
end HomogeneousIdealQuotientGrading
namespace ProjWeierstrassCubicPrime
open MvPolynomial
variable {F : Type*} [CommRing F]
theorem isHomogeneous_polynomial (V : WeierstrassCurve.Projective F) : V.polynomial.IsHomogeneous 3 := by
  have hA : (X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) F).IsHomogeneous 3 := by
    have h := (isHomogeneous_X_pow (R := F) (1 : Fin 3) 2).mul (isHomogeneous_X F (2 : Fin 3))
    norm_num at h
    exact h
  have hB : (C V.a₁ * X 0 * X 1 * X 2 : MvPolynomial (Fin 3) F).IsHomogeneous 3 := by
    have h := ((isHomogeneous_C_mul_X V.a₁ (0 : Fin 3)).mul
      (isHomogeneous_X F (1 : Fin 3))).mul (isHomogeneous_X F (2 : Fin 3))
    norm_num at h
    exact h
  have hC : (C V.a₃ * X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) F).IsHomogeneous 3 := by
    have h := (isHomogeneous_C_mul_X V.a₃ (1 : Fin 3)).mul (isHomogeneous_X_pow (2 : Fin 3) 2)
    norm_num at h
    exact h
  have hD : (X 0 ^ 3 : MvPolynomial (Fin 3) F).IsHomogeneous 3 :=
    isHomogeneous_X_pow (0 : Fin 3) 3
  have hE : (C V.a₂ * X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) F).IsHomogeneous 3 := by
    have h := (isHomogeneous_C_mul_X_pow V.a₂ (0 : Fin 3) 2).mul (isHomogeneous_X F (2 : Fin 3))
    norm_num at h
    exact h
  have hF : (C V.a₄ * X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) F).IsHomogeneous 3 := by
    have h := (isHomogeneous_C_mul_X V.a₄ (0 : Fin 3)).mul (isHomogeneous_X_pow (2 : Fin 3) 2)
    norm_num at h
    exact h
  have hG : (C V.a₆ * X 2 ^ 3 : MvPolynomial (Fin 3) F).IsHomogeneous 3 :=
    isHomogeneous_C_mul_X_pow V.a₆ (2 : Fin 3) 3
  rw [WeierstrassCurve.Projective.polynomial]
  exact ((hA.add hB).add hC).sub (((hD.add hE).add hF).add hG)
end ProjWeierstrassCubicPrime
namespace WeierstrassProjModel
open MvPolynomial HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R : Type*} [CommRing R]
theorem span_polynomial_isHomogeneousCR (V : WeierstrassCurve.Projective R) : (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)⟩
def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) : (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl
abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ :=
  MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) : ℕ → Submodule R (ProjModelRingCR V) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme :=
  Proj (projModelGradingCR V)
def projModelStrCR (V : WeierstrassCurve.Projective R) : Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
end Carrier
variable (R : Type u) [CommRing R]
section ZeroSection
variable (W : WeierstrassCurve R)
open MvPolynomial in
theorem kw_mk_X1_mem_one_CR : Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 1 : MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
open MvPolynomial in
def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact WeierstrassCurve.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1 : kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by
  show (MvPolynomial.eval ![(0 : R), 1, 0]) (X 1) = 1
  simp
def kwYChartEval : HomogeneousLocalization.Away (projModelGradingCR W.toProjective) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
      (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap : (kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R :=
  RingHom.ext fun r => by
    show (MvPolynomial.eval ![(0 : R), 1, 0]) (C r) = r
    exact MvPolynomial.eval_C _
theorem kwYChartEval_section : (kwYChartEval R W).comp ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingHom.id_apply, kwYChartEval,
    HomogeneousLocalization.algebraMap_apply]
  have hval :
      (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _
          (algebraMap R (projModelGradingCR W.toProjective 0) r)).val
        = algebraMap (ProjModelRingCR W.toProjective)
            (Localization.Away
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
            (algebraMap R (ProjModelRingCR W.toProjective) r) := by
    rfl
  rw [hval, IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact RingHom.congr_fun (kwYEvalRingHom_comp_algebraMap R W) r
def kwZeroSect : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      kwYChartEval_section, CommRingCat.ofHom_id, Spec.map_id]⟩
end ZeroSection
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
end WeierstrassProjModel
namespace ArithmeticThetaRelativeKatoR0169
open NeronModelInfra
variable (R : Type u) [CommRing R]
abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} :=
  WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) :=
  WeierstrassProjModel.projModelStrCR W.toProjective
def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W :=
  (WeierstrassProjModel.kwZeroSect R W).val
abbrev Law (W : WeierstrassCurve R) :=
  WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)),
    (G.one t).val = t ≫ origin R W) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (structureMap R W)), G.mul t x y = G.mul t y x)
end ArithmeticThetaRelativeKatoR0169
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩
def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1
end WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
namespace GoodReductionJacobian
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
end GoodReductionJacobian
namespace ArithmeticThetaLocalWeierstrassR0203
structure SchemeLaw {S X : Scheme.{u}} (p : X ⟶ S) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    SchemeHomOver t p → SchemeHomOver t p → SchemeHomOver t p
  one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p → SchemeHomOver t p
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y z : SchemeHomOver t p),
    mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p),
    mul t (inv t x) x = one t
  mul_comm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t p), mul t x y = mul t y x
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t p),
    GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ y)
structure Family (S : Scheme.{u}) where
  curve : Scheme.{u}
  p : curve ⟶ S
  law : SchemeLaw p
  proper : IsProper p
  dimension : SmoothOfRelativeDimension 1 p
  connected : GeometricallyConnected p
def Family.zero {S : Scheme.{u}} (E : Family S) : S ⟶ E.curve :=
  (E.law.one (𝟙 S)).val
end ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaLocalWeierstrassR0203
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
end ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaRelativeDiscriminantR0171
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
end ArithmeticThetaRelativeDiscriminantR0171
section Chart
open WeierstrassProjModel MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal
variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
abbrev coord (i : Fin 3) : ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 :=
  mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)
abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos
def xOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
end WeierstrassCurve.DrinfeldGlobal
end Chart
namespace ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
structure FullLevel (L : ℕ) {T : Scheme.{u}} (t : T ⟶ Base R) where
  x : SchemeHomOver t (structureMap R W)
  y : SchemeHomOver t (structureMap R W)
  killed_x : G.nsmul t L x = G.one t
  killed_y : G.nsmul t L y = G.one t
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val)
      (Set.range (origin R W))
end ArithmeticThetaFullLevelCoverR0175
namespace ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra
def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}} (t : T ⟶ S) : ℕ → SchemeHomOver t E.p → SchemeHomOver t E.p | 0, _ => E.law.one t | n + 1, x => E.law.mul t (multiple E t n x) x
structure FullLevel {S : Scheme.{u}} (E : Family S) (L : ℕ) where
  x : SchemeHomOver (𝟙 S) E.p
  y : SchemeHomOver (𝟙 S) E.p
  killed_x : multiple E (𝟙 S) L x = E.law.one (𝟙 S)
  killed_y : multiple E (𝟙 S) L y = E.law.one (𝟙 S)
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (E.law.mul (𝟙 S)
      (multiple E (𝟙 S) i.val x) (multiple E (𝟙 S) j.val y)).val)
      (Set.range E.zero)
end ArithmeticThetaSchemeLevelR0204
namespace ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) : R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
def HasCoordinates (R : Type u) [CommRing R] (W : WeierstrassCurve R) (P : Base R ⟶ Curve R W) (x y : R) : Prop :=
  P ≫ structureMap R W = 𝟙 (Base R) ∧
  ∃ χ : ChartRing R W →+* R,
    P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
    χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = x ∧
    χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = y
def completedCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.X^3 + Polynomial.C (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2) * Polynomial.X^2 +
    Polynomial.C (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃) * Polynomial.X +
    Polynomial.C (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
def SplitCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (e : Fin 3 → R) : Prop :=
  (∀ i j, i ≠ j → IsUnit (e i - e j)) ∧
    completedCubic R W = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (e i))
end ArithmeticThetaLegendreComparisonR0177
namespace ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)
  (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))
def twoLabel (i : Fin 3) : Base R ⟶ Curve R W :=
  ![(G.nsmul (𝟙 _) (L/2) M.x).val,
    (G.nsmul (𝟙 _) (L/2) M.y).val,
    (G.mul (𝟙 _) (G.nsmul (𝟙 _) (L/2) M.x)
      (G.nsmul (𝟙 _) (L/2) M.y)).val] i
def quarterPoint : Base R ⟶ Curve R W := (G.nsmul (𝟙 _) (L/4) M.y).val
def completedY [Algebra ℚ R] (x y : R) : R :=
  y + algebraMap ℚ R (1/2) * (W.a₁ * x + W.a₃)
def Labels [Algebra ℚ R] (e : Fin 3 → R) : Prop :=
  ∀ i, HasCoordinates R W (twoLabel R W G L M i) (e i)
    (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i + W.a₃))
end ArithmeticThetaGlobalFourTorsionR0190
namespace ArithmeticThetaFourTorsion
def splitCurve {k : Type u} [CommRing k] (e₁ e₂ e₃ : k) : WeierstrassCurve.Affine k where
  a₁ := 0
  a₂ := -(e₁ + e₂ + e₃)
  a₃ := 0
  a₄ := e₁ * e₂ + e₁ * e₃ + e₂ * e₃
  a₆ := -(e₁ * e₂ * e₃)
def rootExpression {k : Type u} [Field k] (e₁ e₂ e₃ x y : k) : k :=
  ((x - e₁)^2 - (e₁ - e₂) * (e₁ - e₃)) / (2 * y)
abbrev Mat4 := Matrix (Fin 2) (Fin 2) (ZMod 4)
def generatorS : Mat4 := !![0, -1; 1, 0]
def generatorT2 : Mat4 := !![1, 2; 0, 1]
def reduceTwo (M : Mat4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => ((M i j).val : ZMod 2)
def PreservesEven (M : Mat4) : Prop :=
  M.det = 1 ∧ ∀ v : Fin 2 → ZMod 2,
    (Matrix.mulVec (reduceTwo M) v) 0 * (Matrix.mulVec (reduceTwo M) v) 1 = v 0 * v 1
def characterExponent (M : Mat4) : ZMod 4 :=
  if (M 0 0).val % 2 = 1 then M 0 0 - 1 else M 0 1
end ArithmeticThetaFourTorsion
namespace ArithmeticThetaRelativeFourCharacterR0211
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
variable [Algebra ℚ R] (M : FullLevel R W G 4 (𝟙 (Base R)))
def Coordinates (e : Fin 3 → R) (x y : Fin 2 → R) : Prop :=
  Labels R W G 4 M e ∧ SplitCubic R W e ∧
  HasCoordinates R W M.x.val (x 0) (y 0) ∧
  HasCoordinates R W M.y.val (x 1) (y 1)
end ArithmeticThetaRelativeFourCharacterR0211
namespace ArithmeticThetaRelativeFourCharacterR0211.RelativeGeometricPhase
def tangentNumerator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) (i j : Fin 2) : A :=
  y j * (x i - e i.castSucc) - y i * (x j - e i.castSucc)
def numerator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) : A :=
  tangentNumerator e x y 0 1 ^ 2 * (x 1 - e 1)^2 * (x 0 - e 1)
def denominator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) : A :=
  (x 0 - e 0)^2 * (x 1 - e 0) * tangentNumerator e x y 1 0 ^ 2
end ArithmeticThetaRelativeFourCharacterR0211.RelativeGeometricPhase
namespace ArithmeticThetaArbitraryFourCharacterR0214
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190 ArithmeticThetaRelativeFourCharacterR0211
variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) (G : Law R W)
  (M : FullLevel R W G 4 (𝟙 (Base R)))
def MillerPhase (z : R) : Prop :=
  (∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y) ∧
  ∀ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y →
    let Y := fun i => completedY R W (x i) (y i)
    IsUnit (RelativeGeometricPhase.denominator e x Y) ∧
      RelativeGeometricPhase.denominator e x Y * z =
        RelativeGeometricPhase.numerator e x Y
end ArithmeticThetaArbitraryFourCharacterR0214
namespace ArithmeticThetaSchemeFourCharacterR0215
open NeronModelInfra ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
structure AffineTest {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4) where
  ring : Type u
  [commRing : CommRing ring]
  [rational : Algebra ℚ ring]
  equation : WeierstrassCurve ring
  elliptic : equation.IsElliptic
  law : ArithmeticThetaRelativeKatoR0169.Law ring equation
  originLaw : ArithmeticThetaRelativeKatoR0169.IsOriginLaw ring equation law
  base : Base ring ⟶ S
  comparison : ArithmeticThetaRelativeKatoR0169.Curve ring equation ⟶ E.curve
  cartesian : IsPullback comparison
    (ArithmeticThetaRelativeKatoR0169.structureMap ring equation) E.p base
  zero_eq : ArithmeticThetaRelativeKatoR0169.origin ring equation ≫ comparison = base ≫ E.zero
  mul_eq : ∀ (T : Scheme.{u}) (t : T ⟶ Base ring)
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap ring equation))
    (x' y' : SchemeHomOver (t ≫ base) E.p),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (E.law.mul _ x' y').val = (law.mul t x y).val ≫ comparison
  level : ArithmeticThetaFullLevelCoverR0175.FullLevel ring equation law 4 (𝟙 (Base ring))
  x_eq : level.x.val ≫ comparison = base ≫ M.x.val
  y_eq : level.y.val ≫ comparison = base ≫ M.y.val
attribute [instance] AffineTest.commRing AffineTest.rational
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)
def affineScalar (P : AffineTest E M) (z : Γ(S, ⊤)) : P.ring :=
  (Scheme.ΓSpecIso (CommRingCat.of P.ring)).hom (P.base.appTop z)
def MillerPhase (z : Γ(S, ⊤)) : Prop :=
  ∀ P : AffineTest E M,
    ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase
      P.ring P.equation P.law P.level (affineScalar E M P z)
end ArithmeticThetaSchemeFourCharacterR0215
namespace ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)
def Changes (N : FullLevel E 4) (A : ArithmeticThetaFourTorsion.Mat4) : Prop :=
  N.x = E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 0).val M.x)
    (multiple E (𝟙 S) (A 1 0).val M.y) ∧
  N.y = E.law.mul (𝟙 S) (multiple E (𝟙 S) (A 0 1).val M.x)
    (multiple E (𝟙 S) (A 1 1).val M.y)
end ArithmeticThetaSchemeFourCharacterR0215
namespace ArithmeticThetaPalomarDifferential365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens} (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s
section Differentials
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) :=
  ((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (kaehlerPresheaf f)
def kaehlerToSections (U : X.Opens) : ((kaehlerPresheaf f).obj (op U) : Type u) → (Γ(kaehler f, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (kaehlerPresheaf f)).app (op U)).hom s
def relativeD (U : X.Opens) (a : Γ(X, U)) : Γ(kaehler f, U) :=
  letI : Algebra R Γ(X, U) := sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X, U) a)
end Differentials
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarGlobalFrame401
open ArithmeticThetaPalomarDifferential365
section Differential
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
def AllDerivationsCompatible (m : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX) : Prop :=
  ∀ (U : Y.Opens) (a : Γ(Y,U)),
    m.app (φ ⁻¹ᵁ U) (pullSection φ (relativeD gY U a)) =
      relativeD gX (φ ⁻¹ᵁ U) (φ.app U a)
theorem canonicalDifferentialMap (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) : ∃! m : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX, AllDerivationsCompatible gY gX φ m := by
  sorry
def differentialMap (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX :=
  (canonicalDifferentialMap gY gX φ hφ).exists.choose
end Differential
open ArithmeticThetaRelativeKatoR0169
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) : R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
abbrev CurveFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules) ≅ kaehler (structureMap R W)
def differentialSection (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) :=
  Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve R W, ⊤))
def NormalizedFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : Prop :=
  let j := chartInclusion R W
  let p := j ≫ structureMap R W
  let x := WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective
  let y := WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective
  let toGlobal := (Scheme.ΓSpecIso (CommRingCat.of (ChartRing R W))).inv
  relativeD p ⊤ (toGlobal x) =
    toGlobal (2*y + chartScalar R W W.a₁*x + chartScalar R W W.a₃) •
      (differentialMap (structureMap R W) p j (by simp [p])).app ⊤
        (pullSection j (differentialSection R W δ))
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj (kaehler (structureMap R W))
def hodgeGenerator (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : Γ(Hodge R W,⊤) := pullSection (origin R W) (differentialSection R W δ)
def IsFrame {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) : Prop :=
  ∀ (U : X.Opens) (h : U ≤ ⊤), Function.Bijective (fun a : Γ(X,U) => a • M.presheaf.map (homOfLE h).op s)
theorem normalizedFrameExists (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] : ∃ δ : CurveFrame R W, NormalizedFrame R W δ := by
  sorry
theorem hodgeGeneratorFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : IsFrame (Hodge R W) (hodgeGenerator R W δ) := by
  sorry
theorem normalizedFrameExistsUnique (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] : ∃! δ : CurveFrame R W, NormalizedFrame R W δ ∧ IsFrame (Hodge R W) (hodgeGenerator R W δ) := by
  sorry
end ArithmeticThetaPalomarGlobalFrame401
namespace ArithmeticThetaPalomarConormal436
open ArithmeticThetaPalomarDifferential365
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (e : S ⟶ X)
def Normalized (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Prop :=
  ∀ (U : X.Opens) (x : Γ(idealModule e.ker,U)),
    m.app (e ⁻¹ᵁ U) (pullSection e x) =
      pullSection e (relativeD c U ((idealInclusion e.ker).app U x))
theorem canonicalConormalMap : ∃! m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c), Normalized c e m := by
  sorry
def conormalMap : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c) :=
  (canonicalConormalMap c e).exists.choose
end ArithmeticThetaPalomarConormal436
namespace ArithmeticThetaRelativeDiscriminantR0171
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) := ArithmeticThetaPalomarGlobalFrame401.Hodge R W
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaPullback
def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) :=
  fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s
end ArithmeticThetaPullback
namespace ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171
def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv v
end ArithmeticThetaOpenHodgeR0180
namespace ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)
  (G : Law R W) (L : ℕ) (M : FullLevel R W G L (𝟙 (Base R)))
def RootData [Algebra ℚ R] (e : Fin 3 → R) (x y g : R) : Prop :=
  Labels R W G L M e ∧ SplitCubic R W e ∧
  HasCoordinates R W (quarterPoint R W G L M) x y ∧
  IsUnit (completedY R W x y) ∧ IsUnit g ∧
  2 * completedY R W x y * g = (x-e 0)^2 - (e 0-e 1)*(e 0-e 2) ∧
  g^2 = e 1-e 0
end ArithmeticThetaGlobalFourTorsionR0190
namespace ArithmeticThetaPalomarPullback437
def pullback_unit_iso (X Y : Scheme.{u}) (p : X ⟶ Y) : (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map p.base).Final := by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def squarePullbackIso {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y) (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback s).obj M) ≅ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M) :=
  (Scheme.Modules.pullbackComp a s).app M ≪≫ pullbackEqIso h M ≪≫
    ((Scheme.Modules.pullbackComp t b).app M).symm
end ArithmeticThetaPalomarPullback437
namespace ArithmeticThetaPalomarAffineAlpha437
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (L : ℕ)
  (M : FullLevel R W G L (𝟙 (Base R)))
def RealizesAlpha [Algebra ℚ R] (a : Γ(Hodge R W, ⊤)) : Prop :=
  ∃ (e : Fin 3 → R) (x y g : R) (δ : ArithmeticThetaPalomarGlobalFrame401.CurveFrame R W),
    RootData R W G L M e x y g ∧ ArithmeticThetaPalomarGlobalFrame401.NormalizedFrame R W δ ∧
    a = ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator R W δ
end ArithmeticThetaPalomarAffineAlpha437
namespace ArithmeticThetaPalomarSchemeAlpha437
open NeronModelInfra ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaPalomarDifferential365 ArithmeticThetaPalomarPullback437
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)
def AffineIdealCompatible (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) : Prop :=
  i.hom ≫ (idealInclusion (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) =
    (Scheme.Modules.pullback P.comparison).map (idealInclusion E.zero.ker) ≫
      (ArithmeticThetaPalomarPullback437.pullback_unit_iso _ _ P.comparison).hom
def affineHodgeMap (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) : (Scheme.Modules.pullback P.base).obj (Cotangent E) ⟶ ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation :=
  (squarePullbackIso P.base E.zero
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation) P.comparison
    P.zero_eq.symm (idealModule E.zero.ker)).hom ≫
  (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)).map i.hom ≫
  ArithmeticThetaPalomarConormal436.conormalMap
    (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation)
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)
def affineAlpha (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) (a : Γ(Cotangent E, ⊤)) : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation, ⊤) :=
  (affineHodgeMap E M P i).app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection P.base (Cotangent E) a)
def RealizesAlpha (a : Γ(Cotangent E, ⊤)) : Prop :=
  ∀ P : AffineTest E M,
    (∃ i, AffineIdealCompatible E M P i) ∧
    ∀ i, AffineIdealCompatible E M P i →
      ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha
        P.ring P.equation P.law 4 P.level (affineAlpha E M P i a)
theorem alphaExists (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) (E : Family S) (M : FullLevel E 4) : ∃! a : Γ(Cotangent E, ⊤), RealizesAlpha E M a := by
  sorry
theorem schemeAlphaCharacter :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (a : (Cotangent E).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → RealizesAlpha E M a → ∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A ∧ ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z ∧ (∀ a' : (Cotangent E).presheaf.obj (Opposite.op ⊤), RealizesAlpha E M' a' → a' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val • a) := by
  sorry
end ArithmeticThetaPalomarSchemeAlpha437
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
end AlgebraicGeometry
namespace ArithmeticThetaRelativeDiscriminantR0171
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun a : X.presheaf.obj (Opposite.op V) => a • res F h s)
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra
def Multiplicative {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) : Prop :=
  ∀ (U : Scheme.{u}) (t : U ⟶ T)
    (x y : SchemeHomOver t F.p) (x' y' : SchemeHomOver (t ≫ b) E.p),
    x'.val = x.val ≫ f → y'.val = y.val ≫ f →
    (E.law.mul _ x' y').val = (F.law.mul t x y).val ≫ f
def MarkedCartesian {S T : Scheme.{u}} {L : ℕ} (E : Family S) (F : Family T) (M : FullLevel E L) (N : FullLevel F L) (b : T ⟶ S) (f : F.curve ⟶ E.curve) : Prop :=
  IsPullback f F.p E.p b ∧ F.zero ≫ f = b ≫ E.zero ∧
  Multiplicative E F b f ∧ N.x.val ≫ f = b ≫ M.x.val ∧
  N.y.val ≫ f = b ≫ M.y.val
end ArithmeticThetaSchemeLevelR0204
namespace ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 NeronModelInfra
variable {S : Scheme.{u}} (E : Family S)
structure EvenPoint where
  point : SchemeHomOver (𝟙 S) E.p
  killed : multiple E (𝟙 S) 2 point = E.law.one (𝟙 S)
  avoids : Disjoint (Set.range point.val) (Set.range E.zero)
def Cartesian {T : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) : Prop :=
  IsPullback f F.p E.p b ∧ F.zero ≫ f = b ≫ E.zero ∧ Multiplicative E F b f
end ArithmeticThetaEvenMarkingTorsorR0216
namespace ArithmeticThetaUniversalEvaluationR0213
open ArithmeticThetaLocalWeierstrassR0203
variable {S : Scheme.{u}} (E : Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4)
def evenPoint : S ⟶ E.curve :=
  (E.law.mul (𝟙 S)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.x)
    (ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) 2 M.y)).val
end ArithmeticThetaUniversalEvaluationR0213
namespace ArithmeticThetaPhaseSwitchR0218
def reversal : ArithmeticThetaFourTorsion.Mat4 := !![-1, 0; 0, 1]
end ArithmeticThetaPhaseSwitchR0218
namespace ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
structure MarkedTest where
  base : Scheme.{u}
  family : Family base
  marking : FullLevel family 4
  map : base ⟶ S
  comparison : family.curve ⟶ E.curve
  cartesian : Cartesian E family map comparison
  characteristic : ArithmeticThetaUniversalEvaluationR0213.evenPoint family marking ≫
    comparison = map ≫ P.point.val
def remark (A : MarkedTest E P) (N : FullLevel A.family 4) (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison = A.map ≫ P.point.val) : MarkedTest E P :=
  { A with marking := N, characteristic := hN }
abbrev Frames (L : S.Modules) :=
  (A : MarkedTest E P) → Γ((Scheme.Modules.pullback A.map).obj L, ⊤)
structure TestMap (A B : MarkedTest E P) where
  map : A.base ⟶ B.base
  commutes : map ≫ B.map = A.map
  familyMap : A.family.curve ⟶ B.family.curve
  marked : MarkedCartesian B.family A.family B.marking A.marking map familyMap
  triangle : familyMap ≫ B.comparison = A.comparison
def testPull (L : S.Modules) {A B : MarkedTest E P} (H : TestMap E P A B) (m : Γ((Scheme.Modules.pullback B.map).obj L, ⊤)) : Γ((Scheme.Modules.pullback A.map).obj L, ⊤) :=
  (((Scheme.Modules.pullbackComp H.map B.map).app L) ≪≫
    (Scheme.Modules.pullbackCongr H.commutes).app L).hom.app ⊤
      (pullbackGlobalSection H.map _ m)
def IsMultiplier (L : S.Modules) (m : Frames E P L) : Prop :=
  Scheme.Modules.IsInvertible L ∧
  (∀ A : MarkedTest E P, IsFrame ((Scheme.Modules.pullback A.map).obj L) ⊤ (m A)) ∧
  (∀ (A B : MarkedTest E P) (H : TestMap E P A B), testPull E P L H (m B) = m A) ∧
  (∀ (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val) (z : Γ(A.base, ⊤)), MillerPhase A.family A.marking z →
    ∀ g : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven g →
    Changes A.family A.marking N g →
    m (remark E P A N hN) = z ^ (3 * (ArithmeticThetaFourTorsion.characterExponent g).val) • m A) ∧
  (∀ (A : MarkedTest E P) (N : FullLevel A.family 4)
    (hN : ArithmeticThetaUniversalEvaluationR0213.evenPoint A.family N ≫ A.comparison =
      A.map ≫ P.point.val),
    Changes A.family A.marking N ArithmeticThetaPhaseSwitchR0218.reversal →
    m (remark E P A N hN) = m A)
def PreservesFrames {L K : S.Modules} (m : Frames E P L) (n : Frames E P K) (v : L ≅ K) : Prop :=
  ∀ A : MarkedTest E P, ((Scheme.Modules.pullback A.map).map v.hom).app ⊤ (m A) = n A
variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)
structure RelativeTestMap (A : MarkedTest E P) (B : MarkedTest F Q) where
  map : B.base ⟶ A.base
  commutes : map ≫ A.map = B.map ≫ b
  familyMap : B.family.curve ⟶ A.family.curve
  marked : MarkedCartesian A.family B.family A.marking B.marking map familyMap
  triangle : familyMap ≫ A.comparison = B.comparison ≫ f
def testSquare {A : MarkedTest E P} {B : MarkedTest F Q} (H : RelativeTestMap E P F Q b f A B) (L : S.Modules) : (Scheme.Modules.pullback B.map).obj ((Scheme.Modules.pullback b).obj L) ≅ (Scheme.Modules.pullback H.map).obj ((Scheme.Modules.pullback A.map).obj L) :=
  (Scheme.Modules.pullbackComp B.map b).app L ≪≫
    (Scheme.Modules.pullbackCongr H.commutes.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp H.map A.map).app L).symm
def Compatible (L : S.Modules) (K : T.Modules) (m : Frames E P L) (n : Frames F Q K) (v : (Scheme.Modules.pullback b).obj L ≅ K) : Prop :=
  ∀ (A : MarkedTest E P) (B : MarkedTest F Q)
    (H : RelativeTestMap E P F Q b f A B),
    ((Scheme.Modules.pullback B.map).map v.hom).app ⊤
      ((testSquare E P F Q b f H L).inv.app ⊤
        (pullbackGlobalSection H.map _ (m A))) = n B
end ArithmeticThetaPhaseFreeKeyR0219
namespace ArithmeticThetaPalomarMultiplier450
theorem phaseFreeMultiplier :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∃ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m ∧ (∀ (K : S.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames E P K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P K n → ∃! v : CategoryTheory.Iso L K, ArithmeticThetaPhaseFreeKeyR0219.PreservesFrames E P m n v) := by
  sorry
end ArithmeticThetaPalomarMultiplier450
namespace ArithmeticThetaPalomarMultiplier450
theorem phaseFreeMultiplierBaseChange :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∃! v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K, ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v := by
  sorry
end ArithmeticThetaPalomarMultiplier450
open MonoidalCategory
namespace ArithmeticThetaSheafTensor
variable (X : Scheme.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
def tensorPresheaf (H K : X.Modules) : X.PresheafOfModules := H.val ⊗ K.val
def sheafTensor (H K : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)
def tensorUnitMap (H K : X.Modules) : tensorPresheaf X H K ⟶ (sheafTensor X H K).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _
def tensorSection (H K : X.Modules) (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) : Γ(sheafTensor X H K, U) :=
  (tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X, U)] t)
end ArithmeticThetaSheafTensor
namespace ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaSheafTensor
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) =
      tensorSection X M N (f ⁻¹ᵁ U)
        (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) : ∃! q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N, Compatible f H K M N e d q := by
  sorry
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPalomarIdentity357
open ArithmeticThetaLocalWeierstrassR0203
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def Compatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (f : F.curve ⟶ E.curve) (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) : Prop :=
  i.hom ≫ idealInclusion F.zero.ker =
    (Scheme.Modules.pullback f).map (idealInclusion E.zero.ker) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
def cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F :=
  ((Scheme.Modules.pullbackComp b E.zero).app (idealModule E.zero.ker) ≪≫
    pullbackEqIso hz.symm (idealModule E.zero.ker) ≪≫
    ((Scheme.Modules.pullbackComp F.zero f).app (idealModule E.zero.ker)).symm) ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) : Prop :=
  ∃ i, Compatible E F f i ∧ e = cotangentComparison E F b f hz i
end ArithmeticThetaPalomarIdentity357
namespace ArithmeticThetaPalomarAlphaDescent459
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaSheafTensor ArithmeticThetaPalomarIdentity357 ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaPalomarSchemeAlpha437
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def productLine (L : S.Modules) : S.Modules := sheafTensor S (cotangent E) L
def tensorComparison (L : S.Modules) (A : MarkedTest E P) (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) : (Scheme.Modules.pullback A.map).obj (productLine E L) ≅ sheafTensor A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) :=
  (canonicalBinaryTensor A.map (cotangent E) L (cotangent A.family)
    ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose
def Descends (L : S.Modules) (m : Frames E P L) (β : Γ(productLine E L, ⊤)) : Prop :=
  ∀ A : MarkedTest E P,
    (∃ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c) ∧
    (∃ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a) ∧
    ∀ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c →
      ∀ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a →
      (tensorComparison E P L A c).hom.app ⊤
        (ArithmeticThetaPullback.pullbackGlobalSection A.map (productLine E L) β) =
        tensorSection A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) ⊤ a (m A)
theorem phaseFreeAlphaDescent :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → (∃! β : (productLine E L).presheaf.obj (Opposite.op ⊤), Descends E P L m β) ∧ (∀ β : (productLine E L).presheaf.obj (Opposite.op ⊤), Descends E P L m β → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (productLine E L) ⊤ β) := by
  sorry
end ArithmeticThetaPalomarAlphaDescent459
