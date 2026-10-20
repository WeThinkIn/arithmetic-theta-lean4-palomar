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
namespace ArithmeticThetaGeometricNormR0150
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
def IsFieldMap (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) : Prop :=
  X.fromSpecStalk (genericPoint X) ≫ f =
    Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)
def fieldNorm (φ : Y.functionField →+* X.functionField) (g : X.functionField) : Y.functionField :=
  letI := φ.toAlgebra
  Algebra.norm Y.functionField g
end ArithmeticThetaGeometricNormR0150
namespace ArithmeticThetaGeneralEllipticKatoR0168
open NeronModelInfra
variable (F : Type u) [Field F]
abbrev Curve (W : WeierstrassCurve F) : Scheme.{u} :=
  WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve F) : Curve F W ⟶ Spec (CommRingCat.of F) :=
  WeierstrassProjModel.projModelStrCR W.toProjective
def origin (W : WeierstrassCurve F) : Spec (CommRingCat.of F) ⟶ Curve F W :=
  (WeierstrassProjModel.kwZeroSect F W).val
abbrev Law (W : WeierstrassCurve F) :=
  WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)
def IsOriginLaw (W : WeierstrassCurve F) (G : Law F W) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)),
    (G.one t).val = t ≫ origin F W) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F))
    (x y : SchemeHomOver t (structureMap F W)), G.mul t x y = G.mul t y x)
def originPoint (W : WeierstrassCurve F) : Curve F W :=
  origin F W (IsLocalRing.closedPoint F)
def katoOrder (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) (x : Curve F W) : ℤ := by
  classical
  exact (if x = originPoint F W then (c : ℤ)^2 else 0) -
    (if G.schemeNsmul c x = originPoint F W then 1 else 0)
def HasKatoDivisor (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g : (Curve F W).functionField) : Prop :=
  g ≠ 0 ∧ ∀ x : Curve F W, Scheme.ord g x = katoOrder F W G c x
def IsKatoFunction (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g : (Curve F W).functionField) : Prop :=
  HasKatoDivisor F W G c g ∧
    ∀ d : ℕ, 0 < d → Nat.Coprime c d →
      ∀ φ : (Curve F W).functionField →+* (Curve F W).functionField,
        ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ →
          ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g
end ArithmeticThetaGeneralEllipticKatoR0168
namespace ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R]
abbrev GenericCurve (W : WeierstrassCurve R) : Scheme.{u} :=
  ArithmeticThetaGeneralEllipticKatoR0168.Curve (FractionRing R)
    (W.map (algebraMap R (FractionRing R)))
structure GenericComparison (W : WeierstrassCurve R) (G : Law R W) [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)] where
  law : ArithmeticThetaGeneralEllipticKatoR0168.Law (FractionRing R)
    (W.map (algebraMap R (FractionRing R)))
  originLaw : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (FractionRing R)
    (W.map (algebraMap R (FractionRing R))) law
  map : GenericCurve R W ⟶ Curve R W
  cartesian : IsPullback map
    (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (FractionRing R)
      (W.map (algebraMap R (FractionRing R))))
    (structureMap R W) (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  origin_eq : ArithmeticThetaGeneralEllipticKatoR0168.origin (FractionRing R)
    (W.map (algebraMap R (FractionRing R))) ≫ map =
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ origin R W
  multiplication_eq : ∀ n : ℕ, law.schemeNsmul n ≫ map = map ≫ G.schemeNsmul n
  field : (Curve R W).functionField ≃+* (GenericCurve R W).functionField
  field_eq : ArithmeticThetaGeometricNormR0150.IsFieldMap map field.toRingHom
def katoOrder (W : WeierstrassCurve R) (G : Law R W) (c : ℕ) (x : Curve R W) : ℤ := by
  classical
  exact (if x ∈ Set.range (origin R W) then (c : ℤ)^2 else 0) -
    (if G.schemeNsmul c x ∈ Set.range (origin R W) then 1 else 0)
variable (W : WeierstrassCurve R) (G : Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
def IsRelativeKato (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  g ≠ 0 ∧
  (∀ x : Curve R W, Order.coheight x = 1 → Scheme.ord g x = katoOrder R W G c x) ∧
  (∀ d : ℕ, 0 < d → Nat.Coprime c d →
    ∀ φ : (Curve R W).functionField →+* (Curve R W).functionField,
      ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ →
      ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g)
end ArithmeticThetaRelativeKatoR0169
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
namespace ArithmeticThetaPalomarWeierstrass373
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
theorem projectiveGeometry (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] : IsProper (structureMap R W) ∧ SmoothOfRelativeDimension 1 (structureMap R W) ∧ GeometricallyConnected (structureMap R W) := by
  sorry
def family (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : Family (ArithmeticThetaLocalWeierstrassR0203.Base R) where
  curve := Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul
           mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel
           mul_natural := G.mul_natural, mul_comm := hG.2 }
  proper := (projectiveGeometry R W).1
  dimension := (projectiveGeometry R W).2.1
  connected := (projectiveGeometry R W).2.2
end ArithmeticThetaPalomarWeierstrass373
namespace ArithmeticThetaArbitraryDiscriminantR0243
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
structure Comparison (R S : Type u) [CommRing R] [CommRing S] (W : WeierstrassCurve R) (V : WeierstrassCurve S) (ι : R →+* S) where
  map : Curve S V ⟶ Curve R W
  cartesian : IsPullback map (structureMap S V) (structureMap R W)
    (Spec.map (CommRingCat.ofHom ι))
  pointed : origin S V ≫ map = Spec.map (CommRingCat.ofHom ι) ≫ origin R W
structure NormalModel (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  equation : WeierstrassCurve ring
  [elliptic : equation.IsElliptic]
  [integral : IsIntegral (Curve ring equation)]
  [locallyNoetherian : IsLocallyNoetherian (Curve ring equation)]
  [genericIntegral : IsIntegral (GenericCurve ring equation)]
  [genericLocallyNoetherian : IsLocallyNoetherian (GenericCurve ring equation)]
  law : Law ring equation
  originLaw : IsOriginLaw ring equation law
  scalar : ring →ₐ[ℚ] R
  comparison : Comparison ring R equation W scalar.toRingHom
attribute [instance] NormalModel.commRing NormalModel.domain NormalModel.noetherian
  NormalModel.normal NormalModel.rational NormalModel.elliptic NormalModel.integral
  NormalModel.locallyNoetherian NormalModel.genericIntegral NormalModel.genericLocallyNoetherian
end ArithmeticThetaArbitraryDiscriminantR0243
namespace ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaLocalWeierstrassR0203
structure Comparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) where
  map : F.curve ⟶ E.curve
  cartesian : IsPullback map F.p E.p b
  pointed : F.zero ≫ map = b ≫ E.zero
end ArithmeticThetaSchemeDiscriminantR0244
namespace ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra
def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}} (t : T ⟶ S) : ℕ → SchemeHomOver t E.p → SchemeHomOver t E.p | 0, _ => E.law.one t | n + 1, x => E.law.mul t (multiple E t n x) x
end ArithmeticThetaSchemeLevelR0204
namespace ArithmeticThetaPolygonCartierR0133
def IsEffectiveCartierIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∃ f : X.presheaf.obj (Opposite.op U.1),
      IsRegular f ∧ I.ideal U = Ideal.span ({f} : Set _)
end ArithmeticThetaPolygonCartierR0133
namespace ArithmeticThetaGeometricNormR0150
variable {X Y : Scheme.{u}}
def affineNorm (f : X ⟶ Y) (U : Y.Opens) (a : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U))) : Y.presheaf.obj (Opposite.op U) :=
  letI := (f.app U).hom.toAlgebra
  Algebra.norm (Y.presheaf.obj (Opposite.op U)) a
def AffineFree (f : X ⟶ Y) (U : Y.Opens) : Prop :=
  letI := (f.app U).hom.toAlgebra
  Module.Free (Y.presheaf.obj (Opposite.op U))
    (X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))
end ArithmeticThetaGeometricNormR0150
namespace ArithmeticThetaPalomarNormalized394
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (G : Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
variable [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
def Normalized (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G c g ∧ ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)
end ArithmeticThetaPalomarNormalized394
namespace ArithmeticThetaPalomarAffineKato394
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaPalomarNormalized394
open ArithmeticThetaArbitraryDiscriminantR0243
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
def identityIdeal : (Curve R W).IdealSheafData := (origin R W).ker
def torsionIdeal (c : ℕ) : (Curve R W).IdealSheafData :=
  (identityIdeal R W).comap (G.schemeNsmul c)
def complement (c : ℕ) : (Curve R W).Opens :=
  (torsionIdeal R W G c).support.compl
abbrev UnitSection (c : ℕ) :=
  ((Curve R W).presheaf.obj (Opposite.op (complement R W G c)))ˣ
def restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : X.presheaf.obj (Opposite.op U)) : X.presheaf.obj (Opposite.op V) :=
  X.presheaf.map (homOfLE h).op a
variable [Algebra ℚ R]
def FromModel (M : NormalModel R W) (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∃ hU : Nonempty (complement M.ring M.equation M.law c),
  ∃ g : (Curve M.ring M.equation).functionField,
    Normalized M.ring M.equation M.law c g ∧
    ∃ a : (Curve M.ring M.equation).presheaf.obj
        (Opposite.op (complement M.ring M.equation M.law c)),
      IsUnit a ∧
      @Scheme.germToFunctionField (Curve M.ring M.equation) _
        (complement M.ring M.equation M.law c) hU a = g ∧
      ∃ e : complement R W G c ≤
          M.comparison.map ⁻¹ᵁ complement M.ring M.equation M.law c,
        (v : _) = M.comparison.map.appLE _ _ e a
def IsKatoUnit (c : ℕ) (v : UnitSection R W G c) : Prop :=
  ∀ M : NormalModel R W, FromModel R W G M c v
end ArithmeticThetaPalomarAffineKato394
namespace ArithmeticThetaPalomarSchemeKato394
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
variable {S : Scheme.{u}} (E : Family S)
def multiplication (n : ℕ) : E.curve ⟶ E.curve :=
  (ArithmeticThetaSchemeLevelR0204.multiple E E.p n
    ⟨𝟙 E.curve, Category.id_comp E.p⟩).val
def identityIdeal : E.curve.IdealSheafData := E.zero.ker
def torsionIdeal (c : ℕ) : E.curve.IdealSheafData :=
  (identityIdeal E).comap (multiplication E c)
def complement (c : ℕ) : E.curve.Opens := (torsionIdeal E c).support.compl
abbrev UnitSection (c : ℕ) :=
  (E.curve.presheaf.obj (Opposite.op (complement E c)))ˣ
def IsKatoUnit (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k) (c : ℕ) (v : UnitSection E c) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : ArithmeticThetaRelativeKatoR0169.Law R W)
    (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G)
    (b : Base R ⟶ S), b ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    ∀ C : Comparison E (ArithmeticThetaPalomarWeierstrass373.family R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      ∃ w : ArithmeticThetaPalomarAffineKato394.UnitSection R W G c,
        ArithmeticThetaPalomarAffineKato394.IsKatoUnit R W G c w ∧
        ∃ e : ArithmeticThetaPalomarAffineKato394.complement R W G c ≤
            C.map ⁻¹ᵁ complement E c,
          (w : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj
            (Opposite.op (ArithmeticThetaPalomarAffineKato394.complement R W G c))) =
            C.map.appLE _ _ e (v : _)
def HasCartierDivisor (c : ℕ) (v : UnitSection E c) : Prop :=
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (identityIdeal E) ∧
  ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (torsionIdeal E c) ∧
  ∀ (U : E.curve.affineOpens)
    (a b : E.curve.presheaf.obj (Opposite.op U.1)),
    IsRegular a → IsRegular b →
    (identityIdeal E).ideal U = Ideal.span ({a} : Set _) →
    (torsionIdeal E c).ideal U = Ideal.span ({b} : Set _) →
    ∃ ε : (E.curve.presheaf.obj (Opposite.op U.1))ˣ,
      ArithmeticThetaPalomarAffineKato394.restrict (complement E c)
          (U.1 ⊓ complement E c) inf_le_right (v : _) *
        ArithmeticThetaPalomarAffineKato394.restrict U.1
          (U.1 ⊓ complement E c) inf_le_left b =
      ArithmeticThetaPalomarAffineKato394.restrict U.1
        (U.1 ⊓ complement E c) inf_le_left ((ε : _) * a ^ (c ^ 2))
end ArithmeticThetaPalomarSchemeKato394
namespace ArithmeticThetaPalomarSchemeNorm394
open CategoryTheory AlgebraicGeometry
abbrev Sections (X : Scheme.{u}) (U : X.Opens) :=
  X.presheaf.obj (Opposite.op U)
abbrev restrict {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U) (a : Sections X U) : Sections X V :=
  ArithmeticThetaPalomarAffineKato394.restrict U V h a
def IsNormSection {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)) (b : Sections Y U) : Prop :=
  ∀ (V : Y.affineOpens) (e : V.1 ≤ U),
    ArithmeticThetaGeometricNormR0150.AffineFree f V.1 →
    ArithmeticThetaGeometricNormR0150.affineNorm f V.1
      (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V.1) (f.preimage_mono e) a) =
      restrict U V.1 e b
abbrev NormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ U : Y.Opens, Sections X (f ⁻¹ᵁ U) →* Sections Y U
def IsNormFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (N : NormFamily f) : Prop :=
  (∀ (U : Y.Opens) (a : Sections X (f ⁻¹ᵁ U)), IsNormSection f U a (N U a)) ∧
  ∀ (U V : Y.Opens) (e : V ≤ U) (a : Sections X (f ⁻¹ᵁ U)),
    N V (restrict (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_mono e) a) =
      restrict U V e (N U a)
def LocallyNormFixed {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) : Prop :=
  ∃ e : f ⁻¹ᵁ U ≤ U, IsNormSection f U (restrict U (f ⁻¹ᵁ U) e v) v
def NormInvariant {X : Scheme.{u}} (f : X ⟶ X) (U : X.Opens) (v : Sections X U) : Prop :=
  ∃ N : NormFamily f, IsNormFamily f N ∧
    ∃ e : f ⁻¹ᵁ U ≤ U, N U (restrict U (f ⁻¹ᵁ U) e v) = v
end ArithmeticThetaPalomarSchemeNorm394
namespace ArithmeticThetaPalomarKatoSupport394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
theorem normalModelExists (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] : Nonempty (ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W) := by
  sorry
theorem schemeUnitExists : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃ v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c, ArithmeticThetaPalomarSchemeKato394.IsKatoUnit E k σ c v := by
  sorry
end ArithmeticThetaPalomarKatoSupport394
namespace ArithmeticThetaPalomarKato394
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaPalomarSchemeKato394 ArithmeticThetaPalomarSchemeNorm394
theorem schemeUnitNaturality : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k) (E : Family S), ∀ (T : Scheme.{u}) (τ : T ⟶ Base k) (H : Family T) (b : T ⟶ S), b ≫ σ = τ → ∀ C : Comparison E H b, ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ (v : UnitSection E c) (w : UnitSection H c), IsKatoUnit E k σ c v → IsKatoUnit H k τ c w → ∃ e : complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (complement E c), (w : H.curve.presheaf.obj (Opposite.op (complement H c))) = C.map.appLE _ _ e (v : _) := by
  sorry
theorem schemeIntrinsicCharacterization : ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : Quiver.Hom S (Base k)) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : UnitSection E c, IsKatoUnit E k σ c v ↔ HasCartierDivisor E c v ∧ NormInvariant (multiplication E 2) (complement E c) (v : _) ∧ NormInvariant (multiplication E 3) (complement E c) (v : _) := by
  sorry
end ArithmeticThetaPalomarKato394
namespace ArithmeticThetaNormFiniteR0063
def triangle (n : ℕ) : ℤ := (n : ℤ) * ((n : ℤ) - 1) / 2
def p (c : ℕ) : ℤ := -triangle c
def K (c : ℕ) : ℤ := (c : ℤ) ^ 2 - 1
end ArithmeticThetaNormFiniteR0063
namespace ArithmeticThetaLaurentNormR0064
def Partial (F : Type) [Field F] (d m : ℕ) (a : F) (N : ℕ) : LaurentSeries F :=
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a * HahnSeries.single ((d : ℤ) * l + m) (1 : F))) *
  (∏ l ∈ Finset.range N,
    (1 - HahnSeries.C a⁻¹ * HahnSeries.single ((d : ℤ) * (l + 1) - m) (1 : F)))
def IsGamma (F : Type) [Field F] (d m : ℕ) (a : F) (g : LaurentSeries F) : Prop :=
  ∀ n : ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ e : ℤ, e ≤ n →
    (Partial F d m a N).coeff e = g.coeff e
def t (F : Type) [Field F] : LaurentSeries F := HahnSeries.single 1 1
abbrev Coeff (K : Type) [Field K] := FractionRing (LaurentPolynomial K)
abbrev Series (K : Type) [Field K] := LaurentSeries (Coeff K)
def w (K : Type) [Field K] : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.T 1)
def scalar (K : Type) [Field K] (a : K) : Coeff K :=
  algebraMap (LaurentPolynomial K) (Coeff K) (LaurentPolynomial.C a)
def a (K : Type) [Field K] (ζ : K) (j c : ℕ) : Coeff K :=
  scalar K ζ ^ (c * j) * w K ^ c
def point (K : Type) [Field K] (ζ : K) (i j : ℕ) : Series K :=
  HahnSeries.C (a K ζ j 1) * t (Coeff K) ^ i
def z (K : Type) [Field K] (d : ℕ) : Series K :=
  HahnSeries.C (w K ^ d)
def Q (K : Type) [Field K] (d : ℕ) : Series K := t (Coeff K) ^ d
def fValue (K : Type) [Field K] (c d : ℕ) (v g h : Series K) : Series K :=
  Q K d ^ (ArithmeticThetaNormFiniteR0063.K c / 12) *
    (-v) ^ ArithmeticThetaNormFiniteR0063.p c * g ^ (c ^ 2) / h
end ArithmeticThetaLaurentNormR0064
namespace ArithmeticThetaUnsplitExpansionR0158
def HasExpansion (k : Type) [Field k] [CharZero k] (r c j : ℕ) (v : ArithmeticThetaLaurentNormR0064.Series k) : Prop :=
  ∀ g h : ArithmeticThetaLaurentNormR0064.Series k,
    ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) r j (ArithmeticThetaLaurentNormR0064.w k) g →
    ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) r (c*j) (ArithmeticThetaLaurentNormR0064.w k ^ c) h →
    v = ArithmeticThetaLaurentNormR0064.fValue k c r
      (HahnSeries.C (ArithmeticThetaLaurentNormR0064.w k) * ArithmeticThetaLaurentNormR0064.t (ArithmeticThetaLaurentNormR0064.Coeff k) ^ j) g h
end ArithmeticThetaUnsplitExpansionR0158
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k]
def monomial (a : k) (n : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ n
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2
def yTerm (v : PowerSeries k) : PowerSeries k := v * (1+v) * ((1-v)⁻¹)^3
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  xTerm (monomial a i) +
  (∑ j ∈ Finset.range N,
    (xTerm (monomial a (d*(j+1)+i)) +
     xTerm (monomial a⁻¹ (d*(j+1)-i)))) -
  2 * ∑ j ∈ Finset.range N,
    PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1 - monomial 1 (d*(j+1)))⁻¹
def partialY (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  PowerSeries.C (2 : k)⁻¹ *
    (yTerm (monomial a i) + ∑ j ∈ Finset.range N,
      (yTerm (monomial a (d*(j+1)+i)) -
       yTerm (monomial a⁻¹ (d*(j+1)-i))))
def tateX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
def tateY (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialY d i a (n+1))
end ArithmeticThetaTateSeries
namespace ArithmeticThetaCubicModelR0144
variable (k : Type u) [Field k] [CharZero k]
def rootSeries (r : ℕ) (j : Fin 3) : PowerSeries k :=
  if j.val = 0 then ArithmeticThetaTateSeries.tateX r 0 (-1)
  else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val = 1 then 1 else -1)
end ArithmeticThetaCubicModelR0144
namespace ArithmeticThetaPeriodOneR0246
variable (k : Type) [Field k] [CharZero k]
def ramifiedCoefficient (j : Fin 3) : PowerSeries k :=
  let e := ArithmeticThetaCubicModelR0144.rootSeries k 4
  if j.val = 0 then -(e 0 + e 1 + e 2)
  else if j.val = 1 then e 0 * e 1 + e 0 * e 2 + e 1 * e 2
  else -(e 0 * e 1 * e 2)
def coefficient (j : Fin 3) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff (4*n) (ramifiedCoefficient k j)
def periodOneCurve : WeierstrassCurve (LaurentSeries k) where
  a₁ := 0
  a₂ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 0)
  a₃ := 0
  a₄ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 1)
  a₆ := algebraMap (PowerSeries k) (LaurentSeries k) (coefficient k 2)
end ArithmeticThetaPeriodOneR0246
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
namespace ArithmeticThetaLegendreComparisonR0177
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) : R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
end ArithmeticThetaLegendreComparisonR0177
namespace ArithmeticThetaAnnularNormBridgeR0156
variable (k : Type) [Field k] [CharZero k]
abbrev Coeff := ArithmeticThetaLaurentNormR0064.Coeff k
def coefficientMap : k →+* Coeff k :=
  (algebraMap (LaurentPolynomial k) (Coeff k)).comp LaurentPolynomial.C
end ArithmeticThetaAnnularNormBridgeR0156
namespace ArithmeticThetaRationalTateR0247
def seriesMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
end ArithmeticThetaRationalTateR0247
namespace ArithmeticThetaPeriodOneNormR0248
open CategoryTheory AlgebraicGeometry
variable (k : Type) [Field k] [CharZero k]
abbrev Coeff := ArithmeticThetaLaurentNormR0064.Coeff k
abbrev Series := ArithmeticThetaLaurentNormR0064.Series k
abbrev Curve (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaGeneralEllipticKatoR0168.Curve (LaurentSeries k) W
abbrev ChartRing (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaLegendreComparisonR0177.ChartRing (LaurentSeries k) W
abbrev chartInclusion (W : WeierstrassCurve (LaurentSeries k)) :=
  ArithmeticThetaLegendreComparisonR0177.chartInclusion (LaurentSeries k) W
abbrev periodCurve := ArithmeticThetaPeriodOneR0246.periodOneCurve k
def baseMap : LaurentSeries k →+* Series k :=
  ArithmeticThetaRationalTateR0247.seriesMap
    (ArithmeticThetaAnnularNormBridgeR0156.coefficientMap k)
def xSeries (r : ℕ) : Series k :=
  HahnSeries.ofPowerSeries ℤ (Coeff k)
    (ArithmeticThetaTateSeries.tateX r 0 (ArithmeticThetaLaurentNormR0064.w k))
def ySeries (r : ℕ) : Series k :=
  HahnSeries.ofPowerSeries ℤ (Coeff k)
    (ArithmeticThetaTateSeries.tateY r 0 (ArithmeticThetaLaurentNormR0064.w k))
def IsChartEvaluation (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ) (a : ChartRing k W →+* Series k) : Prop :=
  (∀ b : LaurentSeries k,
    a (ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries k) W b) =
      baseMap k b) ∧
  a (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = xSeries k r ∧
  a (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = ySeries k r
def IsEvaluation (W : WeierstrassCurve (LaurentSeries k)) (r : ℕ) [IsIntegral (Curve k W)] (ev : (Curve k W).functionField →+* Series k) : Prop :=
  ∃ a : ChartRing k W →+* Series k, IsChartEvaluation k W r a ∧
    Spec.map (CommRingCat.ofHom a) ≫ chartInclusion k W =
      Spec.map (CommRingCat.ofHom ev) ≫ (Curve k W).fromSpecStalk (genericPoint (Curve k W))
end ArithmeticThetaPeriodOneNormR0248
namespace ArithmeticThetaPalomarSchemeTate422
open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203
def TateExpansion (k : Type) [Field k] [CharZero k] {B : Scheme.{0}} (σ : B ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) (E : ArithmeticThetaLocalWeierstrassR0203.Family B) (c : ℕ) (v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c) : Prop :=
  ∀ (l : Type) [Field l] [CharZero l] [Algebra k l],
  ∃ hE : (ArithmeticThetaPeriodOneNormR0248.periodCurve l).IsElliptic,
  ∃ hI : IsIntegral (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  ∃ hN : IsLocallyNoetherian (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)),
  letI := hE
  letI := hI
  letI := hN
  ∃ ev : (ArithmeticThetaPeriodOneNormR0248.Curve l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l)).functionField →+*
      ArithmeticThetaPeriodOneNormR0248.Series l,
    ArithmeticThetaPeriodOneNormR0248.IsEvaluation l
      (ArithmeticThetaPeriodOneNormR0248.periodCurve l) 1 ev ∧
    Function.Injective ev ∧
    ∀ (G : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l))
      (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries l)
        (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G)
      (b : ArithmeticThetaLocalWeierstrassR0203.Base (LaurentSeries l) ⟶ B),
      b ≫ σ = Spec.map (CommRingCat.ofHom
        ((algebraMap l (LaurentSeries l)).comp (algebraMap k l))) →
      ∀ C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E
        (ArithmeticThetaPalomarWeierstrass373.family (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G hG) b,
      ∃ e : ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c ≤
          C.map ⁻¹ᵁ ArithmeticThetaPalomarSchemeKato394.complement E c,
      ∃ hU : Nonempty (ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
          (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c),
        ArithmeticThetaUnsplitExpansionR0158.HasExpansion l 1 c 0
          (ev (@Scheme.germToFunctionField (ArithmeticThetaPeriodOneNormR0248.Curve l
            (ArithmeticThetaPeriodOneNormR0248.periodCurve l)) _
            (ArithmeticThetaPalomarAffineKato394.complement (LaurentSeries l)
              (ArithmeticThetaPeriodOneNormR0248.periodCurve l) G c) hU
            (C.map.appLE _ _ e (v : _))))
theorem gammaPair (k : Type) [Field k] [CharZero k] (c : ℕ) : (∃! g : ArithmeticThetaLaurentNormR0064.Series k, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) 1 0 (ArithmeticThetaLaurentNormR0064.w k) g) ∧ (∃! h : ArithmeticThetaLaurentNormR0064.Series k, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff k) 1 0 (ArithmeticThetaLaurentNormR0064.w k ^ c) h) := by
  sorry
theorem schemeKatoFullTateExpansion :
∀ (k : Type) [Field k] [CharZero k] (B : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom B (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family B), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃! v : ArithmeticThetaPalomarSchemeKato394.UnitSection E c, ArithmeticThetaPalomarSchemeKato394.IsKatoUnit E k σ c v ∧ ArithmeticThetaPalomarSchemeKato394.HasCartierDivisor E c v ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ArithmeticThetaPalomarSchemeNorm394.NormInvariant (ArithmeticThetaPalomarSchemeKato394.multiplication E d) (ArithmeticThetaPalomarSchemeKato394.complement E c) (v : _)) ∧ TateExpansion k σ E c v := by
  sorry
end ArithmeticThetaPalomarSchemeTate422
