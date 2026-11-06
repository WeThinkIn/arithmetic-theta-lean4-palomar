module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section elab "mX" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
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
set_option hygiene false
set_option quotPrecheck false
local notation "gh1567_0" => (@HomogeneousIdeal.toIdeal.{0, u_1, u_1} Nat (@Submodule.{u_1, u_1} R (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))) (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Semiring.toModule.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))))) (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat Nat.instAddMonoid)) (@Submodule.setLike.{u_1, u_1} R (@MvPolynomial.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))) (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R (@Finsupp.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Semiring.toModule.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))))) (@WeierstrassProjModel.projModelHomogeneousIdealCR._proof_1.{u_1} R inst) (@MvPolynomial.homogeneousSubmodule.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra.{0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) R (@CommRing.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W)))
local notation "gh1567_1" => (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
local notation "gh1567_2" => (@MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst))
local notation "gh1567_3" => (@Submodule.Quotient.module'.{u_1, u_1, u_1} gh1567_2 gh1567_2 (@AddMonoidAlgebra.ring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toRing.{u_1} R inst) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)) (@AddMonoidAlgebra.addCommGroup.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toRing.{u_1} R inst)) (@Semiring.toModule.{u_1} gh1567_2 (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))) R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Algebra.toSMul.{u_1, u_1} R gh1567_2 (@CommRing.toCommSemiring.{u_1} R inst) (@AddMonoidAlgebra.semiring.{u_1, 0} R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)) (@AddMonoidAlgebra.algebra.{u_1, u_1, 0} R R (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) (@CommRing.toCommSemiring.{u_1} R inst) (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Algebra.id.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))) (@MvPolynomial.instModuleSelf.{0, u_1} gh1567_1 R inst) (@WeierstrassProjModel.kw_lrComul_tensorProj._proof_1.{u_1} R inst) gh1567_0)
local notation "gh1567_4" => (@Finsupp.{0, 0} gh1567_1 Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
local notation "gh1567_5" => (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))
local notation "gh1567_6" => (@Submodule.Quotient.addCommGroup.{u_1, u_1} gh1567_2 gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid))) (@Ring.toAddCommGroup.{u_1} gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid)))) (@Semiring.toModule.{u_1} gh1567_2 (@Ring.toSemiring.{u_1} gh1567_2 (@CommRing.toRing.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid))))) gh1567_0)
local notation "gh1567_7" => (@AddMonoidAlgebra.ring.{u_1, 0} R gh1567_4 (@CommRing.toRing.{u_1} R inst) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))
local notation "gh1567_8" => (@WeierstrassProjModel.ProjModelRingCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W))
local notation "gh1567_9" => (@AddMonoidAlgebra.semiring.{u_1, 0} R gh1567_4 gh1567_5 (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid))
local notation "gh1567_10" => (@Submodule.Quotient.addCommGroup.{u_1, u_1} gh1567_2 gh1567_2 gh1567_7 (@AddMonoidAlgebra.addCommGroup.{u_1, 0} R gh1567_4 (@CommRing.toRing.{u_1} R inst)) (@Semiring.toModule.{u_1} gh1567_2 gh1567_9) gh1567_0)
local notation "gh1567_11" => (@AddMonoidAlgebra.instModule.{u_1, u_1, 0} R R gh1567_4 gh1567_5 gh1567_5 (@Semiring.toModule.{u_1} R gh1567_5))
local notation "gh1567_12" => (@Algebra.toSMul.{u_1, u_1} R gh1567_2 (@CommRing.toCommSemiring.{u_1} R inst) gh1567_9 (@AddMonoidAlgebra.algebra.{u_1, u_1, 0} R R gh1567_4 (@CommRing.toCommSemiring.{u_1} R inst) gh1567_5 (@Algebra.id.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst)) (@Finsupp.instAddMonoid.{0, 0} gh1567_1 Nat Nat.instAddMonoid)))
local notation "gh1567_13" => (@OfNat.ofNat.{u_1} R (nat_lit 0) (@Zero.toOfNat0.{u_1} R (@MulZeroClass.toZero.{u_1} R (@instMulZeroClassOfSemiring.{u_1} R gh1567_5))))
local notation "gh1567_14" => (@AddMonoidAlgebra.instAddCommMonoid.{u_1, 0} R gh1567_4 gh1567_5)
local notation "gh1567_15" => (@Ring.toSemiring.{u_1} gh1567_2 gh1567_7)
local notation "gh1567_16" => (@Ring.toSemiring.{u_1} R (@CommRing.toRing.{u_1} R inst))
set_option quotPrecheck true
set_option hygiene true
theorem _root_.WeierstrassProjModel.kw_lrSixU_toE._proof_1 : @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (@One.toOfNat1.{0} Nat Nat.instOne)) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAddNegDiag_negSubstGen._proof_1 : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrComul_tensorProj._proof_1.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R], @IsScalarTower.{u_1, u_1, u_1} R gh1567_2 gh1567_2 gh1567_12 (@instSMulOfMul.{u_1} gh1567_2 (@Distrib.toMul.{u_1} gh1567_2 (@instDistribOfSemiring.{u_1} gh1567_2 gh1567_9))) gh1567_12 := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R], @AddSubmonoidClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) gh1567_2 (@AddMonoid.toAddZeroClass.{u_1} gh1567_2 (@AddCommMonoid.toAddMonoid.{u_1} gh1567_2 gh1567_14)) (@Submodule.setLike.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) := by sorry
theorem _root_.WeierstrassProjModel.kwYEvalRingHom._proof_2.{u_1} : ∀ (R : Type u_1) [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R) (a : @MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) (ha : @Membership.mem.{u_1, u_1} gh1567_2 (@Ideal.{u_1} gh1567_2 gh1567_15) (@SetLike.instMembership.{u_1, u_1} (@Ideal.{u_1} gh1567_2 gh1567_15) gh1567_2 (@Submodule.setLike.{u_1, u_1} gh1567_2 gh1567_2 gh1567_15 (@Semiring.toAddCommMonoid.{u_1} gh1567_2 gh1567_15) (@Semiring.toModule.{u_1} gh1567_2 gh1567_15))) gh1567_0 a), @Eq.{u_1 + 1} R (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (@RingHom.{u_1, u_1} gh1567_2 R (@Semiring.toNonAssocSemiring.{u_1} gh1567_2 gh1567_15) (@Semiring.toNonAssocSemiring.{u_1} R gh1567_5)) gh1567_2 (fun (x : @MvPolynomial.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) => R) (@RingHom.instFunLike.{u_1, u_1} gh1567_2 R (@Semiring.toNonAssocSemiring.{u_1} gh1567_2 gh1567_15) (@Semiring.toNonAssocSemiring.{u_1} R gh1567_5)) (@MvPolynomial.eval.{u_1, 0} R gh1567_1 (@CommRing.toCommSemiring.{u_1} R inst) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) gh1567_13 (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R (@AddGroupWithOne.toAddMonoidWithOne.{u_1} R (@Ring.toAddGroupWithOne.{u_1} R (@CommRing.toRing.{u_1} R inst)))))) (@Matrix.vecCons.{u_1} R (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) gh1567_13 (@Matrix.vecEmpty.{u_1} R))))) a) gh1567_13 := by sorry
theorem _root_.WeierstrassProjModel.kw_lrChart_aux._proof_1.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @AddSubgroupClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_10) gh1567_3) gh1567_8 (@AddGroup.toSubNegMonoid.{u_1} gh1567_8 (@AddCommGroup.toAddGroup.{u_1} gh1567_8 gh1567_10)) (@Submodule.setLike.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_10) gh1567_3) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrAdd_comulHom._proof_3.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @Ideal.IsTwoSided.{u_1} gh1567_2 (@CommSemiring.toSemiring.{u_1} gh1567_2 (@CommRing.toCommSemiring.{u_1} gh1567_2 (@AddMonoidAlgebra.commRing.{u_1, 0} R gh1567_4 inst (@Finsupp.instAddCommMonoid.{0, 0} gh1567_1 Nat Nat.instAddCommMonoid)))) (@HomogeneousIdeal.toIdeal.{0, u_1, u_1} Nat (@Submodule.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) gh1567_2 gh1567_9 (@Submodule.setLike.{u_1, u_1} R gh1567_2 gh1567_5 gh1567_14 gh1567_11) (@WeierstrassProjModel.kw_lrAdd_comulHom._proof_2.{u_1} R inst) (@MvPolynomial.homogeneousSubmodule.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) instDecidableEqNat Nat.instAddMonoid (@MvPolynomial.gradedAlgebra.{0, u_1} gh1567_1 R (@CommRing.toCommSemiring.{u_1} R inst)) (@WeierstrassProjModel.projModelHomogeneousIdealCR.{u_1} R inst (@WeierstrassCurve.toProjective.{u_1} R W))) := by sorry
theorem _root_.WeierstrassProjModel.kw_lrChart_aux._proof_2.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R), @AddSubgroupClass.{u_1, u_1} (@Submodule.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_6) gh1567_3) gh1567_8 (@AddGroup.toSubNegMonoid.{u_1} gh1567_8 (@AddCommGroup.toAddGroup.{u_1} gh1567_8 gh1567_6)) (@Submodule.setLike.{u_1, u_1} R gh1567_8 gh1567_16 (@AddCommGroup.toAddCommMonoid.{u_1} gh1567_8 gh1567_6) gh1567_3) := by sorry
run_cmd do
  for n in [`WeierstrassProjModel.kw_lrSixU_toE._proof_1,`WeierstrassProjModel.kw_lrAddNegDiag_negSubstGen._proof_1,`WeierstrassProjModel.kw_lrComul_tensorProj._proof_1,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_2,`WeierstrassProjModel.kwYEvalRingHom._proof_2,`WeierstrassProjModel.kw_lrChart_aux._proof_1,`WeierstrassProjModel.kw_lrAdd_comulHom._proof_3,`WeierstrassProjModel.kw_lrChart_aux._proof_2] do
    let env ← Lean.getEnv
    let some ci := env.find? n | throwError "Missing support obligation {n}"
    let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s =>
      { s with lemmas := s.lemmas.insert key (ci.name, ci.levelParams) }
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
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
section OriginalOrigin1626
attribute [local instance 2000] HenselianLocalRing.toIsLocalRing
def originPoint (W : WeierstrassCurve F) : Curve F W :=
  origin F W (IsLocalRing.closedPoint F)
end OriginalOrigin1626
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
namespace ArithmeticThetaTensorPower
open ArithmeticThetaSheafTensor
def tensorPower (X : Scheme.{u}) (H : X.Modules) : ℕ → X.Modules | 0 => SheafOfModules.unit X.ringCatSheaf | n + 1 => sheafTensor X (tensorPower X H n) H
def tensorPowerSection (X : Scheme.{u}) (H : X.Modules) : (n : ℕ) → (U : X.Opens) → Γ(H, U) → Γ(tensorPower X H n, U) | 0, U, _ => (1 : Γ(X, U)) | n + 1, U, s => tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s
def tensorProductSection (X : Scheme.{u}) (H : X.Modules) : (n : ℕ) → (U : X.Opens) → (Fin n → Γ(H, U)) → Γ(tensorPower X H n, U) | 0, U, _ => (1 : Γ(X, U)) | n + 1, U, s => tensorSection X (tensorPower X H n) H U (tensorProductSection X H n U (fun i => s i.castSucc)) (s (Fin.last n))
end ArithmeticThetaTensorPower
theorem ArithmeticThetaFiveNormalization374.FiveNormalized._proof_1.{u_1} : ∀ (R : Type u_1) [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R) [AlgebraicGeometry.IsIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.Curve.{u_1} R inst W)], @IrreducibleSpace.{u_1} (TopCat.carrier.{u_1} (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} (@ArithmeticThetaRelativeKatoR0169.Curve.{u_1} R inst W)))))) (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} (@ArithmeticThetaRelativeKatoR0169.Curve.{u_1} R inst W)))) := fun (R : Type u_1) [inst : CommRing.{u_1} R] (W : WeierstrassCurve.{u_1} R) [inst_1 : AlgebraicGeometry.IsIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.Curve.{u_1} R inst W)] => @AlgebraicGeometry.irreducibleSpace_of_isIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.Curve.{u_1} R inst W) inst_1
theorem ArithmeticThetaFiveNormalization374.FiveNormalized._proof_2.{u_1} : ∀ (R : Type u_1) [inst : CommRing.{u_1} R] [inst_1 : @IsDomain.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))] (W : WeierstrassCurve.{u_1} R) [AlgebraicGeometry.IsIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.GenericCurve.{u_1} R inst inst_1 W)], @IrreducibleSpace.{u_1} (TopCat.carrier.{u_1} (@AlgebraicGeometry.PresheafedSpace.carrier.{u_1, u_1 + 1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} (@ArithmeticThetaRelativeKatoR0169.GenericCurve.{u_1} R inst inst_1 W)))))) (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{u_1 + 1, u_1, u_1} CommRingCat.{u_1} CommRingCat.instCategory.{u_1} (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace.{u_1} (AlgebraicGeometry.Scheme.toLocallyRingedSpace.{u_1} (@ArithmeticThetaRelativeKatoR0169.GenericCurve.{u_1} R inst inst_1 W)))) := fun (R : Type u_1) [inst : CommRing.{u_1} R] [inst_1 : @IsDomain.{u_1} R (@CommSemiring.toSemiring.{u_1} R (@CommRing.toCommSemiring.{u_1} R inst))] (W : WeierstrassCurve.{u_1} R) [inst_2 : AlgebraicGeometry.IsIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.GenericCurve.{u_1} R inst inst_1 W)] => @AlgebraicGeometry.irreducibleSpace_of_isIntegral.{u_1} (@ArithmeticThetaRelativeKatoR0169.GenericCurve.{u_1} R inst inst_1 W) inst_2
theorem ArithmeticThetaFiveNormalization374.FiveInitial._proof_1 : Nat.AtLeastTwo (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
namespace ArithmeticThetaPalomarNormalKato378
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) (G : Law R W)
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
run_cmd do for n in [`ArithmeticThetaFiveNormalization374.FiveNormalized._proof_1, `ArithmeticThetaFiveNormalization374.FiveNormalized._proof_2, `ArithmeticThetaFiveNormalization374.FiveInitial._proof_1] do let ci ← Lean.getConstInfo n; let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }; Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert key (ci.name, ci.levelParams) }
def FiveNormalized (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G 5 g ∧
  ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law 5 (C.field g)
end ArithmeticThetaPalomarNormalKato378
namespace ArithmeticThetaPalomarDifferential365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
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
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
namespace ArithmeticThetaPalomarNormalInitial381
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaTensorPower
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj
    (ArithmeticThetaPalomarDifferential365.kaehler (structureMap R W))
abbrev HodgePower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :=
  tensorPower (ArithmeticThetaPalomarNormalInitial381.Base R) (Hodge R W) n
def localDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R) (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) : Γ(Hodge R W, (origin R W) ⁻¹ᵁ U) :=
  ArithmeticThetaPalomarDifferential365.pullSection (origin R W)
    (ArithmeticThetaPalomarDifferential365.relativeD (structureMap R W) U a)
def localPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) :=
  tensorPowerSection (ArithmeticThetaPalomarNormalInitial381.Base R) (Hodge R W) n
    ((origin R W) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)
def FiveFrame (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (V : (Base R).Opens) (h : V ≤ ⊤),
    Function.Bijective (fun a : (Base R).presheaf.obj (Opposite.op V) =>
      a • (HodgePower R W 24).presheaf.map (homOfLE h).op d)
run_cmd do for n in [`ArithmeticThetaFiveNormalization374.FiveNormalized._proof_1, `ArithmeticThetaFiveNormalization374.FiveNormalized._proof_2, `ArithmeticThetaFiveNormalization374.FiveInitial._proof_1] do let ci ← Lean.getConstInfo n; let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }; Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert key (ci.name, ci.levelParams) }
def FiveInitial (g : (Curve R W).functionField) (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∀ (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a : (Curve R W).presheaf.obj (Opposite.op U.1)),
    (IsRegular a ∧ (origin R W).ker.ideal U = Ideal.span ({a} : Set _) ∧
      ((origin R W).ker.comap (G.schemeNsmul 5)).ideal U =
        (origin R W).ker.ideal U) →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      (5 : (Curve R W).functionField) * g =
        (Curve R W).germToFunctionField U.1 ((ε : _) * a^24) ∧
      (HodgePower R W 24).presheaf.map (homOfLE le_top).op d =
        (origin R W).app U.1 (ε : _) • localPower R W 24 U.1 a
run_cmd do for n in [`ArithmeticThetaFiveNormalization374.FiveNormalized._proof_1, `ArithmeticThetaFiveNormalization374.FiveNormalized._proof_2, `ArithmeticThetaFiveNormalization374.FiveInitial._proof_1] do let ci ← Lean.getConstInfo n; let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }; Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert key (ci.name, ci.levelParams) }
def FiveSpecification (d : Γ(HodgePower R W 24, ⊤)) : Prop :=
  ∃ g : (Curve R W).functionField,
    ArithmeticThetaPalomarNormalKato378.FiveNormalized R W G g ∧ FiveFrame R W d ∧ FiveInitial R W G g d
include hG
theorem initialTensorExistsUnique : ∃! d : Γ(HodgePower R W 24, ⊤), FiveSpecification R W G d := by
  sorry
end ArithmeticThetaPalomarNormalInitial381
open NeronModelInfra
namespace GoodReductionJacobian
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
namespace ArithmeticThetaPalomarDifferential365
open ArithmeticThetaLocalWeierstrassR0203
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
def hodge {R : Type u} [CommRing R] (E : Family (Base R)) : (Base R).Modules :=
  (Scheme.Modules.pullback E.zero).obj (kaehler E.p)
def Normalized {R : Type u} [CommRing R] (E : Family (Base R)) (e : cotangent E ≅ hodge E) : Prop :=
  ∀ (U : E.curve.Opens) (x : Γ(idealModule E.zero.ker, U)),
    e.hom.app (E.zero ⁻¹ᵁ U) (pullSection E.zero x) =
      pullSection E.zero (relativeD E.p U ((idealInclusion E.zero.ker).app U x))
theorem normalizedConormalHodge : ∀ (R : Type u) [CommRing R] (E : Family (Base R)), ∃! e : cotangent E ≅ hodge E, Normalized E e := by
  sorry
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarWeierstrass373
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaPalomarDifferential365
theorem projectiveGeometry (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] : IsProper (structureMap R W) ∧ SmoothOfRelativeDimension 1 (structureMap R W) ∧ GeometricallyConnected (structureMap R W) := by
  sorry
def family (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : Family (ArithmeticThetaPalomarDifferential365.Base R) where
  curve := Curve R W
  p := structureMap R W
  law := { mul := G.mul, one := G.one, inv := G.inv
           mul_assoc := G.mul_assoc, one_mul := G.one_mul
           mul_one := G.mul_one, inv_mul_cancel := G.inv_mul_cancel
           mul_natural := G.mul_natural, mul_comm := hG.2 }
  proper := (projectiveGeometry R W).1
  dimension := (projectiveGeometry R W).2.1
  connected := (projectiveGeometry R W).2.2
theorem family_zero (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : (family R W G hG).zero = origin R W := by
  change (G.one (𝟙 (ArithmeticThetaPalomarDifferential365.Base R))).val = origin R W
  simpa only [Category.id_comp] using hG.1 (𝟙 (ArithmeticThetaPalomarDifferential365.Base R))
def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj (kaehler (structureMap R W))
def originComparison (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : hodge (family R W G hG) ≅ Hodge R W :=
  pullbackEqIso (family_zero R W G hG) (kaehler (structureMap R W))
def Normalized (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) (e : cotangent (family R W G hG) ≅ Hodge R W) : Prop :=
  ArithmeticThetaPalomarDifferential365.Normalized (family R W G hG)
    (e ≪≫ (originComparison R W G hG).symm)
theorem canonicalWeierstrassHodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : ∃! e : cotangent (family R W G hG) ≅ Hodge R W, Normalized R W G hG e := by
  sorry
end ArithmeticThetaPalomarWeierstrass373
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
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
end AlgebraicGeometry
namespace ArithmeticThetaPalomarCanonicalTensor382
open ArithmeticThetaTensorPower
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ K) (n : ℕ) (q : (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X K n) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorPowerSection Y H n U s)) =
      tensorPowerSection X K n (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s))
end ArithmeticThetaPalomarCanonicalTensor382
open ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaPalomarSchemePower383
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaTensorPower
abbrev Cotangent := @ArithmeticThetaPalomarIdentity357.cotangent
def Compatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (q : (Scheme.Modules.pullback b).obj (tensorPower S (Cotangent E) 24) ≅ tensorPower T (Cotangent F) 24) : Prop :=
  ∃ e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F,
    ArithmeticThetaPalomarIdentity357.CotangentCompatible E F b f hz e ∧
      ArithmeticThetaPalomarCanonicalTensor382.Compatible b (Cotangent E) (Cotangent F) e 24 q
theorem canonicalSchemePower (S T : Scheme.{u}) (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) : ∃! q : (Scheme.Modules.pullback b).obj (tensorPower S (Cotangent E) 24) ≅ tensorPower T (Cotangent F) 24, Compatible E F b f hz q := by
  sorry
end ArithmeticThetaPalomarSchemePower383
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
namespace ArithmeticThetaPalomarFullScheme385
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaTensorPower ArithmeticThetaPalomarNormalInitial381
abbrev Cotangent := @ArithmeticThetaPalomarIdentity357.cotangent
abbrev Power {S : Scheme.{u}} (E : Family S) := tensorPower S (Cotangent E) 24
abbrev Sections {S : Scheme.{u}} (E : Family S) := Γ(Power E, ⊤)
def res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(M,U)) := M.presheaf.map (homOfLE h).op s
abbrev WFamily := @ArithmeticThetaPalomarWeierstrass373.family
def WPowerCompatible (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) (q : Power (WFamily R W G hG) ≅ HodgePower R W 24) : Prop :=
  ∃ e : Cotangent (WFamily R W G hG) ≅ Hodge R W,
    ArithmeticThetaPalomarWeierstrass373.Normalized R W G hG e ∧
    ∀ (U : (ArithmeticThetaPalomarNormalInitial381.Base R).Opens)
      (s : Γ(Cotangent (WFamily R W G hG),U)),
      q.hom.app U (tensorPowerSection _ _ 24 U s) =
        tensorPowerSection _ _ 24 U (e.hom.app U s)
theorem canonicalWPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : ∃! q : Power (WFamily R W G hG) ≅ HodgePower R W 24, WPowerCompatible R W G hG q := by
  sorry
abbrev AffineComparison := @ArithmeticThetaArbitraryDiscriminantR0243.Comparison
def AffineLineCompatible {R S : Type u} [CommRing R] [CommRing S] {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S} (C : AffineComparison R S W V ι) (e : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (Hodge R W) ≅ Hodge S V) : Prop :=
  ∀ (U : (Curve R W).Opens) (a : Γ(Curve R W,U))
    (Z : (ArithmeticThetaPalomarNormalInitial381.Base S).Opens)
    (h₁ : Z ≤ (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U))
    (h₂ : Z ≤ (origin S V) ⁻¹ᵁ (C.map ⁻¹ᵁ U)),
    res (Hodge S V) h₁ (e.hom.app _ (ArithmeticThetaPalomarDifferential365.pullSection
      (Spec.map (CommRingCat.ofHom ι)) (localDifferential R W U a))) =
    res (Hodge S V) h₂ (localDifferential S V (C.map ⁻¹ᵁ U) (C.map.app U a))
def AffinePowerCompatible {R S : Type u} [CommRing R] [CommRing S] {W : WeierstrassCurve R} {V : WeierstrassCurve S} {ι : R →+* S} (C : AffineComparison R S W V ι) (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24) : Prop :=
  ∃ e, AffineLineCompatible C e ∧ ArithmeticThetaPalomarCanonicalTensor382.Compatible
    (Spec.map (CommRingCat.ofHom ι)) (Hodge R W) (Hodge S V) e 24 q
theorem canonicalAffinePower {R S : Type u} [CommRing R] [CommRing S] {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S} (C : AffineComparison R S W V ι) : ∃! q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24, AffinePowerCompatible C q := by
  sorry
def affinePower {R S : Type u} [CommRing R] [CommRing S] {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S} (C : AffineComparison R S W V ι) : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ι))).obj (HodgePower R W 24) ≅ HodgePower S V 24 :=
  (canonicalAffinePower C).exists.choose
def affinePull {R S : Type u} [CommRing R] [CommRing S] {W : WeierstrassCurve R} [W.IsElliptic] {V : WeierstrassCurve S} {ι : R →+* S} (C : AffineComparison R S W V ι) (d : Γ(HodgePower R W 24,⊤)) : Γ(HodgePower S V 24,⊤) :=
  res _ (by simp) ((affinePower C).hom.app _
    (ArithmeticThetaPalomarDifferential365.pullSection (Spec.map (CommRingCat.ofHom ι)) d))
def AffineSpecification {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (d : Γ(HodgePower R W 24,⊤)) : Prop :=
  ∀ M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W,
    ∀ d₀ : Γ(HodgePower M.ring M.equation 24,⊤),
      FiveSpecification M.ring M.equation M.law d₀ → d = affinePull M.comparison d₀
theorem normal_test_exists (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] : ∃ M : ArithmeticThetaArbitraryDiscriminantR0243.NormalModel R W, ∃! d₀ : Γ(HodgePower M.ring M.equation 24,⊤), FiveSpecification M.ring M.equation M.law d₀ := by
  sorry
def wPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) : Power (WFamily R W G hG) ≅ HodgePower R W 24 :=
  (canonicalWPower R W G hG).exists.choose
def wValue (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G) (d : Sections (WFamily R W G hG)) :=
  (wPower R W G hG).hom.app ⊤ d
abbrev Comparison := @ArithmeticThetaSchemeDiscriminantR0244.Comparison
def schemePower {S T : Scheme.{u}} {E : Family S} {F : Family T} {b : T ⟶ S} (C : Comparison E F b) : (Scheme.Modules.pullback b).obj (Power E) ≅ Power F :=
  (ArithmeticThetaPalomarSchemePower383.canonicalSchemePower S T E F b C.map C.cartesian C.pointed).exists.choose
def pull {S T : Scheme.{u}} {E : Family S} {F : Family T} {b : T ⟶ S} (C : Comparison E F b) (d : Sections E) : Sections F :=
  res (Power F) (by simp)
    ((schemePower C).hom.app _ (ArithmeticThetaPalomarDifferential365.pullSection b d))
def SchemeSpecification (k : Type u) [Field k] [CharZero k] {S : Scheme.{u}} (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) (d : Sections E) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (b : ArithmeticThetaPalomarNormalInitial381.Base R ⟶ S),
    b ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    ∀ C : Comparison E (WFamily R W G hG) b,
      letI : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
      AffineSpecification W (wValue R W G hG (pull C d))
theorem scheme_exists (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) : ∃ d : Sections E, SchemeSpecification k σ E d := by
  sorry
theorem scheme_naturality (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (E : Family S) (T : Scheme.{u}) (τ : T ⟶ ArithmeticThetaPalomarNormalInitial381.Base k) (F : Family T) (b : T ⟶ S) (hb : b ≫ σ = τ) (C : Comparison E F b) (d : Sections E) (e : Sections F) (hd : SchemeSpecification k σ E d) (he : SchemeSpecification k τ F e) : pull C d = e := by
  sorry
end ArithmeticThetaPalomarFullScheme385
section Chart
open WeierstrassProjModel MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal
variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev coord (i : Fin 3) : ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 :=
  mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)
abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos
def xOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
end WeierstrassCurve.DrinfeldGlobal
end Chart
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
end ArithmeticThetaPalomarGlobalFrame401
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k]
def monomial (a : k) (n : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ n
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  xTerm (monomial a i) +
  (∑ j ∈ Finset.range N,
    (xTerm (monomial a (d*(j+1)+i)) +
     xTerm (monomial a⁻¹ (d*(j+1)-i)))) -
  2 * ∑ j ∈ Finset.range N,
    PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1 - monomial 1 (d*(j+1)))⁻¹
def tateX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
end ArithmeticThetaTateSeries
namespace ArithmeticThetaCubicModelR0144
variable (k : Type u) [Field k] [CharZero k]
def rootSeries (r : ℕ) (j : Fin 3) : PowerSeries k :=
  if j.val = 0 then ArithmeticThetaTateSeries.tateX r 0 (-1)
  else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val = 1 then 1 else -1)
end ArithmeticThetaCubicModelR0144
namespace ArithmeticThetaPeriodOneR0246
variable (k : Type) [Field k] [CharZero k]
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
namespace ArithmeticThetaDiscriminant
noncomputable def partialEuler {R : Type*} [CommRing R] (a : R) (N : ℕ) : PowerSeries R := ∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (j + 1))
noncomputable def euler {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (partialEuler a d))
noncomputable def P : PowerSeries ℚ := euler 1
end ArithmeticThetaDiscriminant
namespace ArithmeticThetaPalomarPeriod404
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaPalomarNormalInitial381
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaPalomarFullScheme385 hiding Sections
abbrev Base (R : Type) [CommRing R] := Spec (CommRingCat.of R)
def scalar (S : Type) [CommRing S] (v : S) : Γ(ArithmeticThetaPalomarNormalInitial381.Base S,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv v
def seriesMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
variable (R : Type) [CommRing R] [Algebra ℚ R]
def rationalMap : LaurentSeries ℚ →+* LaurentSeries R := seriesMap (algebraMap ℚ R)
def equation : WeierstrassCurve (LaurentSeries R) :=
  (ArithmeticThetaPeriodOneR0246.periodOneCurve ℚ).map (rationalMap R)
abbrev Frame := ArithmeticThetaPalomarGlobalFrame401.CurveFrame (LaurentSeries R) (equation R)
abbrev Normalized (δ : Frame R) :=
  ArithmeticThetaPalomarGlobalFrame401.NormalizedFrame (LaurentSeries R) (equation R) δ
abbrev generator (δ : Frame R) :=
  ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator (LaurentSeries R) (equation R) δ
abbrev Sections := (HodgePower (LaurentSeries R) (equation R) 24).presheaf.obj (Opposite.op ⊤)
def productSeries : LaurentSeries R :=
  HahnSeries.ofPowerSeries ℤ R (PowerSeries.map (algebraMap ℚ R)
    (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48))
def IsD2 (d : Sections R) : Prop :=
  ArithmeticThetaPalomarFullScheme385.AffineSpecification (equation R) d
def FullExpansion (δ : Frame R) (d : Sections R) : Prop :=
  d = scalar (LaurentSeries R) (productSeries R) •
    ArithmeticThetaTensorPower.tensorPowerSection (Base (LaurentSeries R))
      (Hodge (LaurentSeries R) (equation R)) 24 ⊤ (generator R δ)
structure TateTest {S : Scheme} (σ : S ⟶ Base ℚ) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) where
  elliptic : (equation R).IsElliptic
  law : Law (LaurentSeries R) (equation R)
  originLaw : IsOriginLaw (LaurentSeries R) (equation R) law
  base : Base (LaurentSeries R) ⟶ S
  base_eq : base ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (LaurentSeries R)))
  comparison : ArithmeticThetaSchemeDiscriminantR0244.Comparison E
    (@ArithmeticThetaPalomarWeierstrass373.family (LaurentSeries R)
      inferInstance (equation R) elliptic law originLaw) base
  differential : Frame R
  normalized : Normalized R differential
def value {S : Scheme} {σ : S ⟶ Base ℚ} {E : ArithmeticThetaLocalWeierstrassR0203.Family S} (V : TateTest R σ E) (d : ArithmeticThetaPalomarFullScheme385.Sections E) : Sections R :=
  letI := V.elliptic
  ArithmeticThetaPalomarFullScheme385.wValue (LaurentSeries R)
    (equation R) V.law V.originLaw (ArithmeticThetaPalomarFullScheme385.pull V.comparison d)
def HasTateExpansions {S : Scheme} (σ : S ⟶ Base ℚ) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (d : ArithmeticThetaPalomarFullScheme385.Sections E) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℚ A] (V : TateTest A σ E),
    FullExpansion A V.differential (value A V d)
theorem equationElliptic : (equation R).IsElliptic := by
  sorry
theorem rationalFullExpansion : ∃ δ : Frame R, Normalized R δ ∧ ∃! d : Sections R, IsD2 R d ∧ ArithmeticThetaPalomarGlobalFrame401.IsFrame (HodgePower (LaurentSeries R) (equation R) 24) d ∧ ∀ δ' : Frame R, Normalized R δ' → FullExpansion R δ' d := by
  sorry
def FullSchemeSpecification (X : Scheme) (σ : X ⟶ Base ℚ) (E : Family X) (d : ArithmeticThetaPalomarFullScheme385.Sections E) : Prop :=
  SchemeSpecification ℚ σ E d ∧ ArithmeticThetaPalomarGlobalFrame401.IsFrame (Power E) d ∧
    HasTateExpansions σ E d ∧
    ∀ (Y : Scheme) (τ : Y ⟶ Base ℚ) (F : Family Y) (b : Y ⟶ X), b ≫ σ = τ →
      ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b)
        (e : ArithmeticThetaPalomarFullScheme385.Sections F), SchemeSpecification ℚ τ F e → pull C d = e
theorem schemePeriodOneDiscriminant (X : Scheme) (σ : X ⟶ Base ℚ) (E : Family X) : ∃! d : ArithmeticThetaPalomarFullScheme385.Sections E, FullSchemeSpecification X σ E d := by
  sorry
end ArithmeticThetaPalomarPeriod404
