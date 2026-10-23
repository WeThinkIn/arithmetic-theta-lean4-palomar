module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace NeronModelInfra
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) := {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
namespace HomogeneousIdealQuotientGrading
open DirectSum
section Engine
variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)
def pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) : 𝒜 i →+ ℬ i := AddMonoidHom.codRestrict ((Ideal.Quotient.mk I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i) (fun a => hmem i a a.2)
@[simp] lemma pieceHom_coe (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) (a : 𝒜 i) : (pieceHom 𝒜 I ℬ hmem i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := by sorry
omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in
theorem gradedMonoidOfImages [AddMonoid ι] [SetLike.GradedMonoid 𝒜] (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) : SetLike.GradedMonoid ℬ := by sorry
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (y : ⨁ i, 𝒜 i) : DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y) = Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 y) := by sorry
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) : A →+ ⨁ i, ℬ i := (DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : preDecompose 𝒜 I ℬ hmem a = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (decompose 𝒜 a) := rfl
lemma preDecompose_apply_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) (i : ι) : preDecompose 𝒜 I ℬ hmem a i = pieceHom 𝒜 I ℬ hmem i (decompose 𝒜 a i) := by
  rw [preDecompose_apply, DirectSum.map_apply]
lemma preDecompose_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) {i : ι} {a : A} (ha : a ∈ 𝒜 i) : preDecompose 𝒜 I ℬ hmem a = DirectSum.of (fun j => ℬ j) i ⟨Ideal.Quotient.mk I a, hmem i a ha⟩ := by sorry
lemma coeAddMonoidHom_preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = Ideal.Quotient.mk I a := by sorry
lemma preDecompose_eq_zero_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) : preDecompose 𝒜 I ℬ hmem a = 0 := by sorry
def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i := QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem) (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
@[simp] lemma quotDecompose_mk (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) (a : A) : quotDecompose 𝒜 I ℬ hmem hI (Ideal.Quotient.mk I a) = preDecompose 𝒜 I ℬ hmem a := by sorry
@[reducible] def decompositionOfImages (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition ℬ :=
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
@[reducible] def gradedRingOfImages (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) (hI : I.IsHomogeneous 𝒜) : GradedRing ℬ where
  toGradedMonoid := gradedMonoidOfImages 𝒜 I ℬ hmem hsurj
  toDecomposition := decompositionOfImages 𝒜 I ℬ hmem hsurj hI
end Engine
section SubmoduleVersion
variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)
variable (I : Ideal A)
def quotGradingSubmodule (i : ι) : Submodule R (A ⧸ I) := (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap
lemma mem_quotGradingSubmodule_iff {i : ι} {x : A ⧸ I} : x ∈ quotGradingSubmodule 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = x := by sorry
lemma mk_mem_quotGradingSubmodule {i : ι} {a : A} (ha : a ∈ 𝒜 i) : Ideal.Quotient.mk I a ∈ quotGradingSubmodule 𝒜 I i := (mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a, ha, rfl⟩
instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotGradingSubmodule 𝒜 I) := by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 I) := gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I) (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha) (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J : HomogeneousIdeal 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal) := quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
end SubmoduleVersion
end HomogeneousIdealQuotientGrading
namespace ProjWeierstrassCubicPrime
open MvPolynomial
variable {F : Type*} [CommRing F]
theorem isHomogeneous_polynomial (V : WeierstrassCurve.Projective F) : V.polynomial.IsHomogeneous 3 := by sorry
end ProjWeierstrassCubicPrime
namespace WeierstrassProjModel
open MvPolynomial HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra
section Carrier
variable {R : Type*} [CommRing R]
theorem span_polynomial_isHomogeneousCR (V : WeierstrassCurve.Projective R) : (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) := by sorry
def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) := ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) : (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl
abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ := MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) : ℕ → Submodule R (ProjModelRingCR V) := quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme := Proj (projModelGradingCR V)
def projModelStrCR (V : WeierstrassCurve.Projective R) : Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) := Proj.toSpecZero (projModelGradingCR V) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
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
theorem kw_mk_X1_mem_one_CR : Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X 1 : MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1 := mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))
open MvPolynomial in
def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact WeierstrassCurve.Projective.equation_zero
open MvPolynomial in
theorem kwYEvalRingHom_mk_X1 : kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by sorry
def kwYChartEval : HomogeneousLocalization.Away (projModelGradingCR W.toProjective) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R := (IsLocalization.Away.lift (g := kwYEvalRingHom R W) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))) (Localization.Away (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))
open MvPolynomial in
theorem kwYEvalRingHom_comp_algebraMap : (kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R := by sorry
theorem kwYChartEval_section : (kwYChartEval R W).comp ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by sorry
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
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 := rfl
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f → SchemeHomOver t f
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t (inv t x) x = one t
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t f), schemeHomOverComp ψ hψ (mul t x y) = mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
end WeierstrassProjModel
namespace ArithmeticThetaRelativeKatoR0169
open NeronModelInfra
variable (R : Type u) [CommRing R]
abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} := WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) := WeierstrassProjModel.projModelStrCR W.toProjective
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W := (WeierstrassProjModel.kwZeroSect R W).val
abbrev Law (W : WeierstrassCurve R) := WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop := (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)), (G.one t).val = t ≫ origin R W) ∧ (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (structureMap R W)), G.mul t x y = G.mul t y x)
end ArithmeticThetaRelativeKatoR0169
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f := Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
end WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
namespace GoodReductionJacobian
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f → SchemeHomOver t f
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), mul t (inv t x) x = one t
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t f), schemeHomOverComp ψ hψ (mul t x y) = mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
namespace RelativeGroupLaw
def IsCommutative {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : Prop := ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x
end RelativeGroupLaw
end GoodReductionJacobian
namespace GoodReductionJacobian.RelativeGroupLaw
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f := Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
abbrev idPoint : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩
def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A := (G.nsmul f n idPoint).1
end GoodReductionJacobian.RelativeGroupLaw
namespace ArithmeticThetaRelativeDiscriminantR0171
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
structure FullLevel (L : ℕ) {T : Scheme.{u}} (t : T ⟶ Base R) where
  x : SchemeHomOver t (structureMap R W)
  y : SchemeHomOver t (structureMap R W)
  killed_x : G.nsmul t L x = G.one t
  killed_y : G.nsmul t L y = G.one t
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 → Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val) (Set.range (origin R W))
structure LevelScheme (L : ℕ) where
  space : Scheme.{u}
  projection : space ⟶ Base R
  level : FullLevel R W G L projection
def Represents {L : ℕ} (D : LevelScheme R W G L) : Prop := ∀ (T : Scheme.{u}) (t : T ⟶ Base R) (A : FullLevel R W G L t), ∃! q : SchemeHomOver t D.projection, q.val ≫ D.level.x.val = A.x.val ∧ q.val ≫ D.level.y.val = A.y.val
def levelDegree (L : ℕ) : ℕ := Nat.card ((ZMod L × ZMod L) ≃+ (ZMod L × ZMod L))
end ArithmeticThetaFullLevelCoverR0175
namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
abbrev LegendreRing (k : Type u) [Field k] := Localization.Away (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
def parameter (k : Type u) [Field k] : LegendreRing k := algebraMap (Polynomial k) (LegendreRing k) Polynomial.X
def legendre (k : Type u) [Field k] : WeierstrassCurve (LegendreRing k) where
  a₁ := 0
  a₂ := -(parameter k + 1)
  a₃ := 0
  a₄ := parameter k
  a₆ := 0
def legendreBaseMap (k : Type u) [Field k] : Base (LegendreRing k) ⟶ Base k := Spec.map (CommRingCat.ofHom (algebraMap k (LegendreRing k)))
structure SignAction (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L) where
  map : Z.space ⟶ Z.space
  over_eq : map ≫ Z.projection = Z.projection
  square : map ≫ map = 𝟙 _
  x_eq : map ≫ Z.level.x.val = (G.inv Z.projection Z.level.x).val
  y_eq : map ≫ Z.level.y.val = (G.inv Z.projection Z.level.y).val
  free : IsEmpty (equalizer map (𝟙 Z.space) : Scheme.{u})
structure SignQuotient (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Base k) (σ : X ⟶ X) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  q : X ⟶ Base ring
  over_eq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k ring)) = p
  invariant : σ ≫ q = q
  finite : IsFinite q
  etale : Etale q
  surjective : Surjective q
  degree : ∀ x, q.finrank x = 2
  smooth : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k ring)))
  relation : (X ⨿ X) ≅ pullback q q
  left_fst : coprod.inl ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  left_snd : coprod.inl ≫ relation.hom ≫ pullback.snd q q = 𝟙 X
  right_fst : coprod.inr ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  right_snd : coprod.inr ≫ relation.hom ≫ pullback.snd q q = σ
  universal : ∀ (T : Scheme.{u}) (a : X ⟶ T), σ ≫ a = a → ∃! b : Base ring ⟶ T, q ≫ b = a
attribute [instance] SignQuotient.commRing SignQuotient.algebra
abbrev coverCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) := pullback (structureMap R W) Z.projection
abbrev coverToCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) := pullback.fst (structureMap R W) Z.projection
abbrev coverToLevel (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) := pullback.snd (structureMap R W) Z.projection
def coverSection (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) (s : SchemeHomOver Z.projection (structureMap R W)) : Z.space ⟶ coverCurve R W Z :=
  pullback.lift s.val (𝟙 _) (by simpa using s.property)
structure EllipticFamily (S : Type u) [CommRing S] where
  curve : Scheme.{u}
  projection : curve ⟶ Base S
  law : GoodReductionJacobian.RelativeGroupLaw S projection
  commutative : law.IsCommutative
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  connected : GeometricallyConnected projection
structure FamilyLevel (S : Type u) [CommRing S] (E : EllipticFamily S) (L : ℕ) where
  x : SchemeHomOver (𝟙 (Base S)) E.projection
  y : SchemeHomOver (𝟙 (Base S)) E.projection
  killed_x : x.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  killed_y : y.val ≫ E.law.schemeNsmul L = (E.law.one (𝟙 _)).val
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 → Disjoint (Set.range (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i.val x) (E.law.nsmul (𝟙 _) j.val y)).val) (Set.range (E.law.one (𝟙 _)).val)
def FamilyRigid (S : Type u) [CommRing S] (E : EllipticFamily S) {L : ℕ} (M : FamilyLevel S E L) : Prop := ∀ e : E.curve ≅ E.curve, e.hom ≫ E.projection = E.projection → (E.law.one (𝟙 _)).val ≫ e.hom = (E.law.one (𝟙 _)).val → M.x.val ≫ e.hom = M.x.val → M.y.val ≫ e.hom = M.y.val → e.hom = 𝟙 E.curve
structure FamilyDescent (k R : Type u) [Field k] [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L) (σ : SignAction R W G Z) (Q : SignQuotient k (Z.projection ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map) where
  family : EllipticFamily Q.ring
  comparison : coverCurve R W Z ⟶ family.curve
  cartesian : IsPullback comparison (coverToLevel R W Z) family.projection Q.q
  origin_eq : coverSection R W Z (G.one Z.projection) ≫ comparison = Q.q ≫ (family.law.one (𝟙 _)).val
  action : coverCurve R W Z ⟶ coverCurve R W Z
  action_level : action ≫ coverToLevel R W Z = coverToLevel R W Z ≫ σ.map
  action_curve : action ≫ coverToCurve R W Z = (G.inv (coverToLevel R W Z ≫ Z.projection) ⟨coverToCurve R W Z, pullback.condition⟩).val
  invariant : action ≫ comparison = comparison
structure LegendreAtlas (k : Type u) [Field k] (L : ℕ) where
  law : Law (LegendreRing k) (legendre k)
  originLaw : IsOriginLaw (LegendreRing k) (legendre k) law
  level : LevelScheme (LegendreRing k) (legendre k) law L
  represents : Represents (LegendreRing k) (legendre k) law level
  sign : SignAction (LegendreRing k) (legendre k) law level
  quotient : SignQuotient k (level.projection ≫ legendreBaseMap k) sign.map
  descent : FamilyDescent k (LegendreRing k) (legendre k) law level sign quotient
  marking : FamilyLevel quotient.ring descent.family L
  rigid : FamilyRigid quotient.ring descent.family marking
  x_eq : coverSection (LegendreRing k) (legendre k) level level.level.x ≫ descent.comparison = quotient.q ≫ marking.x.val
  y_eq : coverSection (LegendreRing k) (legendre k) level level.level.y ≫ descent.comparison = quotient.q ≫ marking.y.val
end ArithmeticThetaLegendreAtlasR0176
section Chart
open WeierstrassProjModel MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal
variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev coord (i : Fin 3) : ProjModelRingCR W := Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 := mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)
abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W := Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos
def xOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)
def yOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)
end WeierstrassCurve.DrinfeldGlobal
end Chart
namespace ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) := WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W := WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) : R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
def HasCoordinates (R : Type u) [CommRing R] (W : WeierstrassCurve R) (P : Base R ⟶ Curve R W) (x y : R) : Prop := P ≫ structureMap R W = 𝟙 (Base R) ∧ ∃ χ : ChartRing R W →+* R, P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧ χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = x ∧ χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = y
def completedCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) : Polynomial R := Polynomial.X^3 + Polynomial.C (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2) * Polynomial.X^2 + Polynomial.C (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃) * Polynomial.X + Polynomial.C (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
def SplitCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (e : Fin 3 → R) : Prop := (∀ i j, i ≠ j → IsUnit (e i - e j)) ∧ completedCubic R W = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (e i))
end ArithmeticThetaLegendreComparisonR0177
namespace ArithmeticThetaCompatibleLevelR0178
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177
variable (k : Type u) [Field k] [CharZero k] (L : ℕ) (A : LegendreAtlas k L)
abbrev TwoMarking := FullLevel (LegendreRing k) (legendre k) A.law 2 (𝟙 (Base (LegendreRing k)))
def CanonicalTwo (B : TwoMarking k L A) : Prop := HasCoordinates (LegendreRing k) (legendre k) B.x.val 0 0 ∧ HasCoordinates (LegendreRing k) (legendre k) B.y.val 1 0
def CompatibleAt (B : TwoMarking k L A) {T : Scheme.{u}} (a : T ⟶ A.level.space) : Prop := a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.x).val = (a ≫ A.level.projection) ≫ B.x.val ∧ a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.y).val = (a ≫ A.level.projection) ≫ B.y.val
structure CompatibleCover (B : TwoMarking k L A) where
  space : Scheme.{u}
  inclusion : space ⟶ A.level.space
  openImmersion : IsOpenImmersion inclusion
  closedImmersion : IsClosedImmersion inclusion
  compatible : CompatibleAt k L A B inclusion
  represents : ∀ (T : Scheme.{u}) (a : T ⟶ A.level.space), CompatibleAt k L A B a ↔ ∃! b : T ⟶ space, b ≫ inclusion = a
  finite : IsFinite (inclusion ≫ A.level.projection)
  etale : Etale (inclusion ≫ A.level.projection)
  surjective : Surjective (inclusion ≫ A.level.projection)
  degree : ∀ z, (inclusion ≫ A.level.projection).finrank z = levelDegree L / 6
structure CompatibleQuotient (B : TwoMarking k L A) (C : CompatibleCover k L A B) where
  sign : C.space ⟶ C.space
  sign_eq : sign ≫ C.inclusion = C.inclusion ≫ A.sign.map
  sign_square : sign ≫ sign = 𝟙 _
  sign_free : IsEmpty (equalizer sign (𝟙 C.space) : Scheme.{u})
  quotient : SignQuotient k (C.inclusion ≫ A.level.projection ≫ legendreBaseMap k) sign
  inclusion : Base quotient.ring ⟶ Base A.quotient.ring
  cartesian : IsPullback C.inclusion quotient.q A.quotient.q inclusion
  openImmersion : IsOpenImmersion inclusion
  closedImmersion : IsClosedImmersion inclusion
  over_eq : inclusion ≫ Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) = Spec.map (CommRingCat.ofHom (algebraMap k quotient.ring))
end ArithmeticThetaCompatibleLevelR0178
namespace ArithmeticThetaProjectiveEffectivityR0135
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace (S : Type u) [CommRing S] (N : ℕ) : Scheme.{u} := AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin N) S)
def projectiveStructure (S : Type u) [CommRing S] (N : ℕ) : projectiveSpace S N ⟶ Spec (CommRingCat.of S) := Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin N) S) ≫ Spec.map (CommRingCat.ofHom (algebraMap S ((MvPolynomial.homogeneousSubmodule (Fin N) S) 0)))
end ArithmeticThetaProjectiveEffectivityR0135
namespace ArithmeticThetaLevelCompactificationR0179
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178
structure LevelData (k : Type u) [Field k] (L : ℕ) where
  atlas : LegendreAtlas k L
  two : TwoMarking k L atlas
  canonical : CanonicalTwo k L atlas two
  cover : CompatibleCover k L atlas two
  quotient : CompatibleQuotient k L atlas two cover
variable (k : Type u) [Field k] (L : ℕ)
abbrev OpenBase (D : LevelData k L) := Base D.quotient.quotient.ring
def openStructure (D : LevelData k L) : OpenBase k L D ⟶ Base k := Spec.map (CommRingCat.ofHom (algebraMap k D.quotient.quotient.ring))
def IsParameter (D : LevelData k L) (p : OpenBase k L D ⟶ Base (LegendreRing k)) : Prop := D.quotient.quotient.q ≫ p = D.cover.inclusion ≫ D.atlas.level.projection ∧ p ≫ legendreBaseMap k = openStructure k L D
structure Compactification (D : LevelData k L) where
  space : Scheme.{u}
  projection : space ⟶ Base k
  inclusion : OpenBase k L D ⟶ space
  over_eq : inclusion ≫ projection = openStructure k L D
  openImmersion : IsOpenImmersion inclusion
  dense : DenseRange inclusion.base
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  dimension : ℕ
  embedding : space ⟶ ArithmeticThetaProjectiveEffectivityR0135.projectiveSpace k (dimension+1)
  closedImmersion : IsClosedImmersion embedding
  embedding_over : embedding ≫ ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = projection
def boundary (D : LevelData k L) (X : Compactification k L D) : Set X.space := (Set.range X.inclusion.base)ᶜ
end ArithmeticThetaLevelCompactificationR0179
namespace ArithmeticThetaLevelCount
def PrimitivePair (L : ℕ) := {v : ZMod L × ZMod L // IsCoprime v.1 v.2}
def SignedPrimitivePair (L : ℕ) := Quot (fun a b : PrimitivePair L => b.val = -a.val)
end ArithmeticThetaLevelCount
open TopologicalSpace MonoidalCategory
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev idPoint : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩
def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A := (G.nsmul f n idPoint).1
end WeierstrassProjModel.RelativeGroupLaw
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
end AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom
variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) := (f.constToPresheaf.app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf
def kaehler : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf
def kaehlerToSections (U : X.Opens) : (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) := fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app f.kaehlerPresheaf).app (op U)).hom s
end AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (φ : X ⟶ Y) {L : Y.Modules} {U : Y.Opens}
def pullbackLocalSection (s : Γ(L, U)) : Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U) := ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s
end AlgebraicGeometry.Scheme.Modules
namespace ArithmeticThetaSheafTensor
variable (X : Scheme.{u})
local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
def tensorPresheaf (H K : X.Modules) : X.PresheafOfModules := H.val ⊗ K.val
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def sheafTensor (H K : X.Modules) : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf X H K)
end ArithmeticThetaSheafTensor
namespace ArithmeticThetaTensorPower
open ArithmeticThetaSheafTensor
def tensorPower (X : Scheme.{u}) (H : X.Modules) : ℕ → X.Modules | 0 => SheafOfModules.unit X.ringCatSheaf | n + 1 => sheafTensor X (tensorPower X H n) H
end ArithmeticThetaTensorPower
namespace ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaTensorPower
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) := (Scheme.Modules.pullback (origin R W)).obj (structureMap R W).kaehler
abbrev HodgePower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) := tensorPower (Base R) (Hodge R W) n
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) : Prop := ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective (fun a : X.presheaf.obj (Opposite.op V) => a • res F h s)
def baseMap (R : Type u) [CommRing R] (S : Type u) [CommRing S] (ι : R →+* S) : Base S ⟶ Base R := Spec.map (CommRingCat.ofHom ι)
end ArithmeticThetaRelativeDiscriminantR0171
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_2.{u_1} : (type_of% @ArithmeticThetaSheafTensor.sheafTensor._proof_2.{u_1}) := by sorry
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_3.{u_1} : (type_of% @ArithmeticThetaSheafTensor.sheafTensor._proof_3.{u_1}) := by sorry
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_1.{u_1} : (type_of% @ArithmeticThetaSheafTensor.sheafTensor._proof_1.{u_1}) := by sorry
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_4.{u_1} : (type_of% @ArithmeticThetaSheafTensor.sheafTensor._proof_4.{u_1}) := by sorry
run_cmd do
  for n in [`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_2,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_3,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_1,`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.T0.unitD._proof_4] do
    let env ← Lean.getEnv
    let some ci := env.find? n | throwError "Missing original support obligation"
    let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s => { s with lemmas := s.lemmas.insert key (ci.name, ci.levelParams) }
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
section Main
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)
include hφ
lemma fac (U : Y.Opens) : CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) = gY.constToPresheaf.app (op U) ≫ φ.app U := by
  have h1 : gY.constToPresheaf.app (op U) ≫ φ.app U =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (φ ≫ gY).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.app U = _
    rw [Category.assoc, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  have h2 : CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change CommRingCat.ofHom (algebraMap A B) ≫
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top) = _
    rw [Scheme.Hom.comp_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  rw [h1, h2, hφ]
lemma fac_apply (U : Y.Opens) (a : A) : φ.app U (gY.constToPresheaf.app (op U) a) = gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) (algebraMap A B a) := by
  have := CategoryTheory.ConcreteCategory.congr_hom (fac gY gX φ hφ U) a
  exact this.symm
def kdMap (U : Y.Opens) : gY.kaehlerPresheaf.obj (op U) ⟶ (ModuleCat.restrictScalars (φ.app U).hom).obj (gX.kaehlerPresheaf.obj (op (φ ⁻¹ᵁ U))) := CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
abbrev unit1 (V : X.Opens) : gX.kaehlerPresheaf.obj (op V) ⟶ gX.kaehler.val.obj (op V) := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf).app (op V)
lemma unit1_apply (V : X.Opens) (x : gX.kaehlerPresheaf.obj (op V)) : unit1 gX V x = gX.kaehlerToSections V x := rfl
omit hφ in
def dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V : Z.Opens) (b : Γ(Z, V)) : (g.kaehlerPresheaf.obj (op V) : Type u) := CommRingCat.KaehlerDifferential.d (f := g.constToPresheaf.app (op V)) b
omit hφ in
lemma kp_map_dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) {V V' : Z.Opens} (i : op V ⟶ op V') (b : Γ(Z, V)) : g.kaehlerPresheaf.map i (dK g V b) = dK g V' (Z.presheaf.map i b) := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d g.constToPresheaf i b
omit hφ in
lemma kp_hom_ext {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V : Z.Opens) {M : ModuleCat Γ(Z, V)} {α β : g.kaehlerPresheaf.obj (op V) ⟶ M} (h : ∀ b : Γ(Z, V), α (dK g V b) = β (dK g V b)) : α = β := CommRingCat.KaehlerDifferential.ext h
omit hφ in
lemma map_unit1 {V V' : X.Opens} (j : op V ⟶ op V') (x : gX.kaehlerPresheaf.obj (op V)) : gX.kaehler.val.map j (unit1 gX V x) = unit1 gX V' (gX.kaehlerPresheaf.map j x) := (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf) j x).symm
omit hφ in
lemma φ_naturality_apply {U U' : Y.Opens} (i : op U ⟶ op U') (b : Γ(Y, U)) : X.presheaf.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op (φ.app U b) = φ.app U' (Y.presheaf.map i b) := (CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm
def k1app (U : Y.Opens) : gY.kaehlerPresheaf.obj (op U) ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val.obj (op U) := kdMap gY gX φ hφ U ≫ (ModuleCat.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))
lemma k1app_dK (U : Y.Opens) (b : Γ(Y, U)) : k1app gY gX φ hφ U (dK gY U b) = unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)) := by
  show unit1 gX (φ ⁻¹ᵁ U) (CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
    (CommRingCat.KaehlerDifferential.d b)) = _
  rw [CommRingCat.KaehlerDifferential.map_d]
  rfl
def k1pre : gY.kaehlerPresheaf ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val where
  app U := k1app gY gX φ hφ U.unop
  naturality {U U'} i := by
    obtain ⟨U⟩ := U; obtain ⟨U'⟩ := U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b)) =
      gX.kaehler.val.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK, k1app_dK, k1app_dK, map_unit1, kp_map_dK, φ_naturality_apply]
abbrev adjY := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
def k1 : gY.kaehler ⟶ (Scheme.Modules.pushforward φ).obj gX.kaehler := ((adjY (Y := Y)).homEquiv gY.kaehlerPresheaf ((Scheme.Modules.pushforward φ).obj gX.kaehler)).symm (k1pre gY gX φ hφ)
end Main
end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull
section DifferentialMap
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {X Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
def differentialMap : (Scheme.Modules.pullback φ).obj gY.kaehler ⟶ gX.kaehler := ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm (k1 gY gX φ hφ)
theorem differentialMap_isIso (hc : CategoryTheory.IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) [SmoothOfRelativeDimension 1 gY] : IsIso (differentialMap gY gX φ hφ) := by sorry
end DifferentialMap
variable {X Y : Scheme.{u}}
def pullbackEqIso {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def squarePullbackIso {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y) (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback s).obj M) ≅ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M) := (Scheme.Modules.pullbackComp a s).app M ≪≫ pullbackEqIso h M ≪≫ ((Scheme.Modules.pullbackComp t b).app M).symm
section PointedComparison
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hc : CategoryTheory.IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 gY]
    (s : Spec (CommRingCat.of A) ⟶ Y) (t : Spec (CommRingCat.of B) ⟶ X)
    (hpt : t ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s)
def pointedDifferentialIso : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj ((Scheme.Modules.pullback s).obj gY.kaehler) ≅ (Scheme.Modules.pullback t).obj gX.kaehler := by
  letI := differentialMap_isIso gY gX φ hc.w hc
  exact squarePullbackIso _ s t φ hpt.symm gY.kaehler ≪≫
    (Scheme.Modules.pullback t).mapIso (asIso (differentialMap gY gX φ hc.w))
end PointedComparison
end ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
namespace ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
abbrev zero {S : Type u} [CommRing S] (E : EllipticFamily S) : Base S ⟶ E.curve := (E.law.one (𝟙 _)).val
abbrev hodge {S : Type u} [CommRing S] (E : EllipticFamily S) := (Scheme.Modules.pullback (zero E)).obj E.projection.kaehler
abbrev power {S : Type u} [CommRing S] (E : EllipticFamily S) (n : ℕ) := tensorPower (Base S) (hodge E) n
structure Test (S : Type u) [CommRing S] (E : EllipticFamily S) (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) where
  scalar : S →+* R
  map : Curve R W ⟶ E.curve
  cartesian : IsPullback map (structureMap R W) E.projection (baseMap S R scalar)
  origin_eq : origin R W ≫ map = baseMap S R scalar ≫ zero E
  nsmul_eq : ∀ n, G.schemeNsmul n ≫ map = map ≫ E.law.schemeNsmul n
def comparison {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) : (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (hodge E) ≅ Hodge R W := by
  letI : Algebra S R := C.scalar.toAlgebra
  letI : SmoothOfRelativeDimension 1 E.projection := E.smooth
  exact pointedDifferentialIso E.projection (structureMap R W) C.map
    C.cartesian (zero E) (origin R W) C.origin_eq
end ArithmeticThetaOpenHodgeR0180
namespace ArithmeticThetaCompatibleLevelR0178
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175
variable (k : Type u) [Field k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
def Classifies (B : TwoMarking k L A) (C : CompatibleCover k L A B) (Q : CompatibleQuotient k L A B C) (R : Type u) [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W) (M : FullLevel R W G L (𝟙 (Base R))) (b : Base R ⟶ Base Q.quotient.ring) (f : Curve R W ⟶ A.descent.family.curve) : Prop := b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧ IsPullback f (structureMap R W) A.descent.family.projection (b ≫ Q.inclusion) ∧ origin R W ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val ∧ M.x.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.x.val ∧ M.y.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.y.val
end ArithmeticThetaCompatibleLevelR0178
namespace ArithmeticThetaTateSeries
variable {k : Type u} [Field k]
def monomial (a : k) (n : ℕ) : PowerSeries k := PowerSeries.C a * PowerSeries.X ^ n
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2
def yTerm (v : PowerSeries k) : PowerSeries k := v * (1+v) * ((1-v)⁻¹)^3
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k := xTerm (monomial a i) + (∑ j ∈ Finset.range N, (xTerm (monomial a (d*(j+1)+i)) + xTerm (monomial a⁻¹ (d*(j+1)-i)))) - 2 * ∑ j ∈ Finset.range N, PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) * (1 - monomial 1 (d*(j+1)))⁻¹
def partialY (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k := PowerSeries.C (2 : k)⁻¹ * (yTerm (monomial a i) + ∑ j ∈ Finset.range N, (yTerm (monomial a (d*(j+1)+i)) - yTerm (monomial a⁻¹ (d*(j+1)-i))))
def tateX (d i : ℕ) (a : k) : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
def tateY (d i : ℕ) (a : k) : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff n (partialY d i a (n+1))
end ArithmeticThetaTateSeries
namespace ArithmeticThetaCubicModelR0144
variable (k : Type u) [Field k] [CharZero k]
def rootSeries (r : ℕ) (j : Fin 3) : PowerSeries k := if j.val = 0 then ArithmeticThetaTateSeries.tateX r 0 (-1) else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val = 1 then 1 else -1)
end ArithmeticThetaCubicModelR0144
namespace ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCubicModelR0144
variable (k : Type u) [Field k] [CharZero k]
def root (r : ℕ) (j : Fin 3) : LaurentSeries k := algebraMap (PowerSeries k) (LaurentSeries k) (rootSeries k r j)
def curve (r : ℕ) : WeierstrassCurve (LaurentSeries k) where
  a₁ := 0
  a₂ := -(root k r 0 + root k r 1 + root k r 2)
  a₃ := 0
  a₄ := root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2
  a₆ := -(root k r 0 * root k r 1 * root k r 2)
abbrev projectiveCurve (r : ℕ) : Scheme.{u} := WeierstrassProjModel.projModelCR (curve k r).toProjective
def projectiveStructure (r : ℕ) : projectiveCurve k r ⟶ Spec (CommRingCat.of (LaurentSeries k)) := WeierstrassProjModel.projModelStrCR (curve k r).toProjective
abbrev ChartRing (r : ℕ) := WeierstrassCurve.DrinfeldGlobal.ZChartRing (curve k r).toProjective
def chartInclusion (r : ℕ) : Spec (CommRingCat.of (ChartRing k r)) ⟶ projectiveCurve k r := WeierstrassCurve.DrinfeldGlobal.zChartι (curve k r).toProjective
def relativeD {F : Type u} [CommRing F] {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens) (a : C.presheaf.obj (Opposite.op U)) : Γ(f.kaehler, U) :=
  letI : Algebra F (C.presheaf.obj (Opposite.op U)) := f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (Opposite.op U)) a)
end ArithmeticThetaCompactifiedDifferentialR0145
namespace ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
def chartScalar : LaurentSeries k →+* ChartRing k r :=
  (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR (curve k r).toProjective)
    (Submonoid.powers (coord (curve k r).toProjective 2))).comp
      (algebraMap (LaurentSeries k) (projModelGradingCR (curve k r).toProjective 0))
end ArithmeticThetaCompactifiedDifferentialR0145.ProjectiveCubicChart
namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
section ChartEquiv
variable {B : Type u} [CommRing B] {C : Scheme.{u}} (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]
def chartRingEquiv : Γ(C, i ''ᵁ ⊤) ≃+* B := ((i.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
end ChartEquiv
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (E : C ≅ projectiveCurve k r)
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
attribute [local instance 1001] MvPolynomial.instModuleSelf
local instance zchartAlgebra : Algebra (LaurentSeries k) (ChartRing k r) := (ProjectiveCubicChart.chartScalar k r).toAlgebra
abbrev zLeg := chartInclusion k r ≫ E.inv
instance zLeg_open : IsOpenImmersion (zLeg k r E) := by dsimp [zLeg, chartInclusion]; infer_instance
abbrev zOpen : C.Opens := zLeg k r E ''ᵁ ⊤
abbrev zSection : ChartRing k r ≃+* Γ(C, zOpen k r E) := (chartRingEquiv (zLeg k r E)).symm
end ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
namespace ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLevelCompactificationR0179
variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
abbrev TateCurve := ArithmeticThetaCompactifiedDifferentialR0145.curve k L
abbrev Disk := Base (PowerSeries k)
abbrev Puncture := Base (LaurentSeries k)
def genericInclusion : Puncture k ⟶ Disk k := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
def diskStructure : Disk k ⟶ Base k := Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))
def closedPoint : Disk k := ⟨IsLocalRing.maximalIdeal (PowerSeries k), inferInstance⟩
structure TateLevel where
  elliptic : (TateCurve k L).IsElliptic
  law : Law (LaurentSeries k) (TateCurve k L)
  originLaw : IsOriginLaw (LaurentSeries k) (TateCurve k L) law
  marking : FullLevel (LaurentSeries k) (TateCurve k L) law L (𝟙 (Puncture k))
def Extends (D : LevelData k L) (X : Compactification k L D) (b : Puncture k ⟶ OpenBase k L D) (d : Disk k ⟶ X.space) : Prop := d ≫ X.projection = diskStructure k ∧ genericInclusion k ≫ d = b ≫ X.inclusion ∧ d (closedPoint k) ∈ boundary k L D X
end ArithmeticThetaTateCuspsR0181
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
namespace ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
abbrev CurveFrame := (SheafOfModules.unit (Curve (LaurentSeries k) (TateCurve k L)).ringCatSheaf : (Curve (LaurentSeries k) (TateCurve k L)).Modules) ≅ (structureMap (LaurentSeries k) (TateCurve k L)).kaehler
def Normalized (δ : CurveFrame k L) : Prop :=
  let E := Iso.refl (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k L)
  let U := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen k L E
  let x := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)
  let y := ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection k L E
    (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)
  ArithmeticThetaCompactifiedDifferentialR0145.relativeD
    (structureMap (LaurentSeries k) (TateCurve k L)) U x =
      (2*y) • Scheme.Modules.Hom.app δ.hom U (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), U))
def hodgeGenerator (δ : CurveFrame k L) : Γ(Hodge (LaurentSeries k) (TateCurve k L), ⊤) :=
  res _ (by simp) (Scheme.Modules.pullbackLocalSection
    (origin (LaurentSeries k) (TateCurve k L)) (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))))
structure Test (D : LevelData k L) where
  level : TateLevel k L
  base : Puncture k ⟶ OpenBase k L D
  map : Curve (LaurentSeries k) (TateCurve k L) ⟶ D.atlas.descent.family.curve
  classifies : ArithmeticThetaCompatibleLevelR0178.Classifies k L D.atlas D.two D.cover D.quotient (LaurentSeries k) (TateCurve k L) level.law level.marking base map
  nsmul_eq : ∀ n, level.law.schemeNsmul n ≫ map = map ≫ D.atlas.descent.family.law.schemeNsmul n
  differential : CurveFrame k L
  normalized : Normalized k L differential
structure DiskTest (D : LevelData k L) (X : Compactification k L D) extends Test k L D where
  disk : Disk k ⟶ X.space
  extends_eq : Extends k L D X base disk
abbrev openHodge (D : LevelData k L) := (Scheme.Modules.pullback D.quotient.inclusion).obj (hodge D.atlas.descent.family)
abbrev openPower (D : LevelData k L) (n : ℕ) := tensorPower (OpenBase k L D) (openHodge k L D) n
def testIso {D : LevelData k L} (T : Test k L D) : (Scheme.Modules.pullback (T.base ≫ D.quotient.inclusion)).obj (hodge D.atlas.descent.family) ≅ Hodge (LaurentSeries k) (TateCurve k L) := by
  let ι : D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
  have hmap : baseMap D.atlas.quotient.ring (LaurentSeries k) ι =
      T.base ≫ D.quotient.inclusion := Spec.map_preimage _
  let C : ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring
      D.atlas.descent.family (LaurentSeries k) (TateCurve k L) T.level.law :=
    { scalar := ι
      map := T.map
      cartesian := by rw [hmap]; exact T.classifies.2.1
      origin_eq := by rw [hmap]; exact T.classifies.2.2.1
      nsmul_eq := T.nsmul_eq }
  exact pullbackEqIso hmap.symm (hodge D.atlas.descent.family) ≪≫ comparison C
def openTestIso {D : LevelData k L} (T : Test k L D) : (Scheme.Modules.pullback T.base).obj (openHodge k L D) ≅ Hodge (LaurentSeries k) (TateCurve k L) := (Scheme.Modules.pullbackComp T.base D.quotient.inclusion).app _ ≪≫ testIso k L T
structure Extension (D : LevelData k L) (X : Compactification k L D) where
  line : X.space.Modules
  invertible : Scheme.Modules.IsInvertible line
  onOpen : (Scheme.Modules.pullback X.inclusion).obj line ≅ openHodge k L D
def diskGenericIso {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (T : DiskTest k L D X) : (Scheme.Modules.pullback (genericInclusion k)).obj ((Scheme.Modules.pullback T.disk).obj H.line) ≅ Hodge (LaurentSeries k) (TateCurve k L) := (Scheme.Modules.pullbackComp (genericInclusion k) T.disk).app H.line ≪≫ pullbackEqIso T.extends_eq.2.1 H.line ≪≫
    ((Scheme.Modules.pullbackComp T.base X.inclusion).app H.line).symm ≪≫ (Scheme.Modules.pullback T.base).mapIso H.onOpen ≪≫ openTestIso k L T.toTest
def ExtendsGenerator {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (T : DiskTest k L D X) (η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤)) : Prop :=
  IsFrame ((Scheme.Modules.pullback T.disk).obj H.line) ⊤ η ∧
  res _ (by simp) ((diskGenericIso k L H T).hom.app _
    (Scheme.Modules.pullbackLocalSection (genericInclusion k) η)) =
      hodgeGenerator k L T.differential
def Canonical {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) : Prop := ∀ T : DiskTest k L D X, ∃! η : Γ((Scheme.Modules.pullback T.disk).obj H.line, ⊤), ExtendsGenerator k L H T η
end ArithmeticThetaBoundaryHodgeR0182
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by sorry
end ArithmeticThetaPalomarComponent485
namespace ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem compactComponent._proof_1 (x : X.space) : IsOpen (irreducibleComponent x) := by sorry
def compactComponent (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, compactComponent._proof_1 k L D X x⟩
end ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
namespace ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (x : X.space)
abbrev componentOpen : X.space.Opens :=
  ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x
abbrev Component : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
abbrev projection : Component k L D X x ⟶ Spec (CommRingCat.of k) :=
  inclusion k L D X x ≫ X.projection
theorem componentIntegral : IsIntegral (Component k L D X x) := by sorry
attribute [instance] componentIntegral
theorem componentLocallyNoetherian : IsLocallyNoetherian (Component k L D X x) := by sorry
attribute [instance] componentLocallyNoetherian
def cuspSet : Set (Component k L D X x) :=
  {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps := {y : Component k L D X x // y ∈ cuspSet k L D X x}
abbrev hodge (H : Extension k L D X) : (Component k L D X x).Modules :=
  (Scheme.Modules.pullback (inclusion k L D X x)).obj H.line
abbrev power (H : Extension k L D X) (n : ℕ) : (Component k L D X x).Modules :=
  tensorPower (Component k L D X x) (hodge k L D X x H) n
end ArithmeticThetaComponentDegreeR0184
namespace ArithmeticThetaLineRoot
structure LocalFrame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) where
  equiv (V : X.Opens) (hVU : V ≤ U) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(H, V)
  naturality (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (a : Γ(X, V)) :
    H.presheaf.map (homOfLE hWV).op (equiv V hVU a) =
      equiv W (hWV.trans hVU) (X.presheaf.map (homOfLE hWV).op a)
variable (X : Scheme.{u}) [IsIntegral X]
structure NormalFrameCover (H : X.Modules) (ι : Type v) where
  opens : ι → X.Opens
  covers : (⊤ : X.Opens) ≤ iSup opens
  nonempty : ∀ i, Nonempty (opens i)
  affine : ∀ i, IsAffineOpen (opens i)
  normal : ∀ i, IsIntegrallyClosed Γ(X, opens i)
  frame : ∀ i, LocalFrame X H (opens i)
instance {X : Scheme.{u}} {H : X.Modules} {ι : Type v} (C : NormalFrameCover X H ι) (i : ι) : Nonempty (C.opens i) := C.nonempty i
end ArithmeticThetaLineRoot
namespace ArithmeticThetaNormalizedSections
open ArithmeticThetaLineRoot
def sectionCoordinate (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) (e : LocalFrame X H U) (s : Γ(H, ⊤)) : Γ(X,U) :=
  (e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)
def sectionCoefficient (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (U : X.Opens) [Nonempty U] (e : LocalFrame X H U) (s : Γ(H, ⊤)) : X.functionField :=
  X.germToFunctionField U (sectionCoordinate X H U e s)
end ArithmeticThetaNormalizedSections
namespace ArithmeticThetaSectionOrder
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
def localOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules) {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i : ι) (x : X) : ℤ :=
  Scheme.ord (sectionCoefficient X H (C.opens i) (C.frame i) s) x
def MatchesSectionOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (H : X.Modules) {ι : Type v} (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (D : X →₀ ℤ) : Prop :=
  ∀ (i : ι) (x : X), x ∈ C.opens i → D x = localOrder X H C s i x
end ArithmeticThetaSectionOrder
namespace ArithmeticThetaCurveDegree
def baseToResidue (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : k →+* X.residueField x :=
  (Scheme.Γevaluation X x).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
def placeDegree (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) := (baseToResidue k f x).toAlgebra
  Module.finrank k (X.residueField x)
def weightedDegree (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (D : X →₀ ℤ) : ℤ :=
  D.sum (fun x n => (placeDegree k f x : ℤ) * n)
end ArithmeticThetaCurveDegree
namespace ArithmeticThetaPalomarHodge495
theorem componentHodgePowerDegree :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) ι) (t : (ArithmeticThetaComponentDegreeR0184.power k L D X x H n).presheaf.obj (Opposite.op ⊤)) (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ), t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) C t E → 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) = (n : ℤ) * (2*L : ℕ) * (Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) : ℤ) ∧ 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) ≤ (n : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by
  sorry
end ArithmeticThetaPalomarHodge495
