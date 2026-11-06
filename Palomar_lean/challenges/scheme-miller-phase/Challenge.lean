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
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
abbrev Mat4 := Matrix (Fin 2) (Fin 2) (ZMod 4)
def splitCurve {k : Type u} [CommRing k] (e₁ e₂ e₃ : k) : WeierstrassCurve.Affine k where
  a₁ := 0
  a₂ := -(e₁ + e₂ + e₃)
  a₃ := 0
  a₄ := e₁ * e₂ + e₁ * e₃ + e₂ * e₃
  a₆ := -(e₁ * e₂ * e₃)
end ArithmeticThetaFourTorsion
namespace ArithmeticThetaMillerR0114
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaFourTorsion.splitCurve (e 0) (e 1) (e 2)
abbrev Coord (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  (Curve k e).CoordinateRing
abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  (Curve k e).FunctionField
def tangentSlope (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (x y : k) : k := (Curve k e).slope x x y y
def tangentClass (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (x y : k) : Coord k e :=
  WeierstrassCurve.Affine.CoordinateRing.YClass (Curve k e)
    (WeierstrassCurve.Affine.linePolynomial x y (tangentSlope k e x y))
def xFunction (k : Type u) [Field k] (e : Fin 3 → k) : FF k e :=
  algebraMap (Coord k e) (FF k e)
    (WeierstrassCurve.Affine.CoordinateRing.XClass (Curve k e) 0)
def yFunction (k : Type u) [Field k] (e : Fin 3 → k) : FF k e :=
  algebraMap (Coord k e) (FF k e)
    (WeierstrassCurve.Affine.CoordinateRing.YClass (Curve k e) 0)
def branchEquation (k : Type u) [Field k] (e : Fin 3 → k) (h : PowerSeries k) : Prop :=
  PowerSeries.constantCoeff h = 1 ∧
    h ^ 2 = ∏ i : Fin 3, (h - PowerSeries.C (e i) * PowerSeries.X ^ 2)
def parameter (k : Type u) [Field k] : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X
def infinityX (k : Type u) [Field k] (h : PowerSeries k) : LaurentSeries k :=
  parameter k ^ (-2 : ℤ) * algebraMap (PowerSeries k) (LaurentSeries k) h
def infinityY (k : Type u) [Field k] (h : PowerSeries k) : LaurentSeries k :=
  -(parameter k ^ (-3 : ℤ) * algebraMap (PowerSeries k) (LaurentSeries k) h)
def IsInfinityEmbedding (k : Type u) [Field k] (e : Fin 3 → k) (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k) : Prop :=
  E (xFunction k e) = infinityX k h ∧ E (yFunction k e) = infinityY k h
end ArithmeticThetaMillerR0114
namespace ArithmeticThetaReciprocityR0116
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e
abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.FF k e
abbrev Translations (k : Type u) [Field k] (e : Fin 3 → k) :=
  (Curve k e).Point → (FF k e ≃ₐ[k] FF k e)
attribute [local instance 2000] Semifield.toCommSemiring instIsDomain
theorem _root_.ArithmeticThetaReciprocityR0116.translatedCoordinates._proof_1.{u_1} : ∀ (k : Type u_1) [inst : Field.{u_1} k] (e : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → k),   Nontrivial.{u_1}     (@WeierstrassCurve.Affine.CoordinateRing.{u_1} k (@Field.toCommRing.{u_1} k inst)       (@ArithmeticThetaMillerR0114.Curve.{u_1} k (@Field.toCommRing.{u_1} k inst) e)) := by sorry
run_cmd do
  let some ci := (← Lean.getEnv).find? `ArithmeticThetaReciprocityR0116.translatedCoordinates._proof_1 | throwError "Missing selected auxiliary target"
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert key (ci.name, ci.levelParams) }
def translatedCoordinates (k : Type u) [Field k] (e : Fin 3 → k) : (Curve k e).Point → FF k e × FF k e | .zero => (ArithmeticThetaMillerR0114.xFunction k e, ArithmeticThetaMillerR0114.yFunction k e) | .some a b _ => let x := ArithmeticThetaMillerR0114.xFunction k e
      let y := ArithmeticThetaMillerR0114.yFunction k e
      let c := algebraMap k (FF k e)
      let slope := (y - c b) / (x - c a)
      let newX := slope ^ 2 + c (e 0 + e 1 + e 2) - x - c a
      (newX, -y + slope * (x - newX))
def IsTranslationSystem (k : Type u) [Field k] (e : Fin 3 → k) (T : Translations k e) : Prop :=
  ∀ P, T P (ArithmeticThetaMillerR0114.xFunction k e) =
    (translatedCoordinates k e P).1 ∧
    T P (ArithmeticThetaMillerR0114.yFunction k e) =
    (translatedCoordinates k e P).2
def expansion (k : Type u) [Field k] (e : Fin 3 → k) (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k) (P : (Curve k e).Point) (f : FF k e) : LaurentSeries k := E (T P f)
def localValue (k : Type u) [Field k] (e : Fin 3 → k) (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k) (f : FF k e) (P : (Curve k e).Point) : k :=
  (expansion k e T E P f).coeff 0
def GoodShift (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (P Q Z : (Curve k e).Point) : Prop :=
  Z ≠ 0 ∧ Z ≠ P ∧ Q + Z ≠ 0 ∧ Q + Z ≠ P
end ArithmeticThetaReciprocityR0116
namespace ArithmeticThetaMarkingR0115
abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e
abbrev Marking (k : Type u) [Field k] (e : Fin 3 → k) :=
  Fin 2 → (Curve k e).Point
def pointX (k : Type u) [Field k] (e : Fin 3 → k) : (Curve k e).Point → k | .zero => 0 | .some x _ _ => x
def pointY (k : Type u) [Field k] (e : Fin 3 → k) : (Curve k e).Point → k | .zero => 0 | .some _ y _ => y
def coordinates (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (b : Marking k e) (z : Fin 2 → ZMod 4) : (Curve k e).Point :=
  (z 0).val • b 0 + (z 1).val • b 1
def IsBasis (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (b : Marking k e) : Prop :=
  (∀ i, 4 • b i = 0) ∧ Function.Injective (coordinates k e b) ∧
    ∀ T : (Curve k e).Point, 4 • T = 0 → ∃ z, coordinates k e b z = T
def labels (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (b : Marking k e) : Fin 3 → k :=
  ![pointX k e (2 • b 0), pointX k e (2 • b 1),
    pointX k e (2 • b 0 + 2 • b 1)]
end ArithmeticThetaMarkingR0115
namespace ArithmeticThetaGeometricPairingR0118
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev Curve (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.Curve k e
abbrev FF (k : Type u) [CommRing k] (e : Fin 3 → k) :=
  ArithmeticThetaMillerR0114.FF k e
structure LocalData (k : Type u) [Field k] (e : Fin 3 → k) where
  translations : ArithmeticThetaReciprocityR0116.Translations k e
  branch : PowerSeries k
  embedding : FF k e →ₐ[k] LaurentSeries k
  translations_spec : ArithmeticThetaReciprocityR0116.IsTranslationSystem k e translations
  branch_spec : ArithmeticThetaMillerR0114.branchEquation k e branch
  embedding_spec : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e branch embedding
def value (k : Type u) [Field k] (e : Fin 3 → k) (D : LocalData k e) (f : FF k e) (P : (Curve k e).Point) : k :=
  ArithmeticThetaReciprocityR0116.localValue k e D.translations D.embedding f P
attribute [local instance 2000] Semifield.toCommSemiring instIsDomain
theorem _root_.ArithmeticThetaGeometricPairingR0118.fourFunction._proof_1.{u_1} : ∀ (k : Type u_1) [inst : Field.{u_1} k] (e : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → k),   Nontrivial.{u_1}     (@WeierstrassCurve.Affine.CoordinateRing.{u_1} k (@Field.toCommRing.{u_1} k inst)       (@ArithmeticThetaMillerR0114.Curve.{u_1} k (@Field.toCommRing.{u_1} k inst) e)) := by sorry
run_cmd do
  let some ci := (← Lean.getEnv).find? `ArithmeticThetaGeometricPairingR0118.fourFunction._proof_1 | throwError "Missing selected auxiliary target"
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun st => { st with lemmas := st.lemmas.insert key (ci.name, ci.levelParams) }
def fourFunction (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) : (Curve k e).Point → FF k e | .zero => 1 | P@(.some x y _) => if y = 0 then (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x)^2 else (algebraMap (ArithmeticThetaMillerR0114.Coord k e) (FF k e) (ArithmeticThetaMillerR0114.tangentClass k e x y))^2 / (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) (ArithmeticThetaMarkingR0115.pointX k e (2 • P)))
def movedValue (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (D : LocalData k e) (P Q Z : (Curve k e).Point) : k :=
  value k e D (fourFunction k e P) (Q + Z) /
    value k e D (fourFunction k e P) Z *
  (value k e D (fourFunction k e Q) (-Z) /
    value k e D (fourFunction k e Q) (P - Z))
def pairing (k : Type u) [Field k] [DecidableEq k] (e : Fin 3 → k) (D : LocalData k e) (P Q : (Curve k e).Point) : k := by
  classical
  exact if h : ∃ Z : (Curve k e).Point, ArithmeticThetaReciprocityR0116.GoodShift k e P Q Z
    then movedValue k e D P Q (Classical.choose h)
    else 0
end ArithmeticThetaGeometricPairingR0118
namespace ArithmeticThetaRelativeFourCharacterR0211
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
def Changes {T : Scheme.{u}} (t : T ⟶ Base R) (M M' : FullLevel R W G 4 t) (A : ArithmeticThetaFourTorsion.Mat4) : Prop :=
  M'.x = G.mul t (G.nsmul t (A 0 0).val M.x) (G.nsmul t (A 1 0).val M.y) ∧
  M'.y = G.mul t (G.nsmul t (A 0 1).val M.x) (G.nsmul t (A 1 1).val M.y)
variable [Algebra ℚ R] (M : FullLevel R W G 4 (𝟙 (Base R)))
def Coordinates (e : Fin 3 → R) (x y : Fin 2 → R) : Prop :=
  Labels R W G 4 M e ∧ SplitCubic R W e ∧
  HasCoordinates R W M.x.val (x 0) (y 0) ∧
  HasCoordinates R W M.y.val (x 1) (y 1)
def FiberCoordinates (e : Fin 3 → R) (x y : Fin 2 → R) (F : Type u) [Field F] (ι : R →+* F) (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e)) : Prop :=
  ∀ i : Fin 2, b i ≠ 0 ∧
    ArithmeticThetaMarkingR0115.pointX F (ι ∘ e) (b i) = ι (x i) ∧
    ArithmeticThetaMarkingR0115.pointY F (ι ∘ e) (b i) =
      ι (completedY R W (x i) (y i))
def GeometricPhase (z : R) : Prop :=
  (∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y) ∧
  ∀ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y →
    ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F)
      (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e)),
      FiberCoordinates R W e x y F ι b →
      ∀ D : ArithmeticThetaGeometricPairingR0118.LocalData F (ι ∘ e),
        ι z = ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1)
end ArithmeticThetaRelativeFourCharacterR0211
namespace ArithmeticThetaRelativeFourCharacterR0211.RelativeGeometricPhase
def tangentNumerator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) (i j : Fin 2) : A :=
  y j * (x i - e i.castSucc) - y i * (x j - e i.castSucc)
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
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
namespace ArithmeticThetaPalomarSchemePhase433
theorem localDataExists (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k) (he : Function.Injective e) : Nonempty (ArithmeticThetaGeometricPairingR0118.LocalData k e) := by
  sorry
theorem arbitrarySplitFiberBasis :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∃ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y) ∧ (∀ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y → ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F),  Function.Injective (ι ∘ e) ∧ (∃! b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b) ∧ (∀ b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b → ArithmeticThetaMarkingR0115.IsBasis F (ι ∘ e) b ∧ ArithmeticThetaMarkingR0115.labels F (ι ∘ e) b = ι ∘ e)) := by
  sorry
theorem schemeMillerPhase :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z) ∧ (∀ z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → IsUnit z ∧ z^2 = -1 ∧ (Nontrivial (S.presheaf.obj (Opposite.op ⊤)) → IsPrimitiveRoot z 4) ∧ (∀ P : ArithmeticThetaSchemeFourCharacterR0215.AffineTest E M, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase P.ring P.equation P.law P.level (ArithmeticThetaSchemeFourCharacterR0215.affineScalar E M P z))) := by
  sorry
end ArithmeticThetaPalomarSchemePhase433
