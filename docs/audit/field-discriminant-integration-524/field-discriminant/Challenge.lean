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
abbrev coord (i : Fin 3) : ProjModelRingCR W := Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 := mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
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
open TopologicalSpace MonoidalCategory
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
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
namespace ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
section ChartEquiv
variable {B : Type u} [CommRing B] {C : Scheme.{u}} (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]
def chartRingEquiv : Γ(C, i ''ᵁ ⊤) ≃+* B := ((i.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
end ChartEquiv
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (E : C ≅ projectiveCurve k r)
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
namespace ArithmeticThetaSheafTensor
variable (X : Scheme.{u})
def tensorUnitMap (H K : X.Modules) : tensorPresheaf X H K ⟶ (sheafTensor X H K).val := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _
def tensorSection (H K : X.Modules) (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) : Γ(sheafTensor X H K, U) := (tensorUnitMap X H K).app (op U) (s ⊗ₜ[Γ(X, U)] t)
end ArithmeticThetaSheafTensor
namespace ArithmeticThetaTensorPower
open ArithmeticThetaSheafTensor
def tensorPowerSection (X : Scheme.{u}) (H : X.Modules) : (n : ℕ) → (U : X.Opens) → Γ(H, U) → Γ(tensorPower X H n, U) | 0, U, _ => (1 : Γ(X, U)) | n + 1, U, s => tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s
end ArithmeticThetaTensorPower
namespace ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaSheafTensor
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)), q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) = tensorSection X M N (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) : ∃! q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N, Compatible f H K M N e d q := by sorry
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPullback
def pullback_unit_iso (X Y : Scheme.{u}) (p : X ⟶ Y) : (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map p.base).Final := by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
end ArithmeticThetaPullback
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaSheafTensor ArithmeticThetaTensorPower
def binary {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj K) := Classical.choose (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor f H K _ _ (Iso.refl _) (Iso.refl _)).exists
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaPullback
open ArithmeticThetaSheafTensor
local instance instMonoidalCategoryPresheafOfModules_pullbackTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
def sheafTensorCongr (X : Scheme.{u}) {H H' K K' : X.Modules} (e : H ≅ H') (d : K ≅ K') : sheafTensor X H K ≅ sheafTensor X H' K' := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso d))
end ArithmeticThetaPullback
namespace ArithmeticThetaPalomarHalf505
open ArithmeticThetaTensorPower
def powerComparison (X Y : Scheme.{u}) (f : X ⟶ Y) (H : Y.Modules) : (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPower Y H n) ≅ tensorPower X ((Scheme.Modules.pullback f).obj H) n | 0 => ArithmeticThetaPullback.pullback_unit_iso X Y f | n+1 => binary f (tensorPower Y H n) H ≪≫ ArithmeticThetaPullback.sheafTensorCongr X (powerComparison X Y f H n) (Iso.refl _)
end ArithmeticThetaPalomarHalf505
namespace ArithmeticThetaGeometricNormR0150
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
def IsFieldMap (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) : Prop := X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)
def fieldNorm (φ : Y.functionField →+* X.functionField) (g : X.functionField) : Y.functionField :=
  letI := φ.toAlgebra
  Algebra.norm Y.functionField g
end ArithmeticThetaGeometricNormR0150
namespace ArithmeticThetaGeneralEllipticKatoR0168
open NeronModelInfra
variable (F : Type u) [Field F]
abbrev Curve (W : WeierstrassCurve F) : Scheme.{u} := WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve F) : Curve F W ⟶ Spec (CommRingCat.of F) := WeierstrassProjModel.projModelStrCR W.toProjective
def origin (W : WeierstrassCurve F) : Spec (CommRingCat.of F) ⟶ Curve F W := (WeierstrassProjModel.kwZeroSect F W).val
abbrev Law (W : WeierstrassCurve F) := WeierstrassProjModel.RelativeGroupLaw F (structureMap F W)
def IsOriginLaw (W : WeierstrassCurve F) (G : Law F W) : Prop := (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)), (G.one t).val = t ≫ origin F W) ∧ (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of F)) (x y : SchemeHomOver t (structureMap F W)), G.mul t x y = G.mul t y x)
def originPoint (W : WeierstrassCurve F) : Curve F W := origin F W (IsLocalRing.closedPoint F)
def katoOrder (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) (x : Curve F W) : ℤ := by
  classical
  exact (if x = originPoint F W then (c : ℤ)^2 else 0) - (if G.schemeNsmul c x = originPoint F W then 1 else 0)
def HasKatoDivisor (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g : (Curve F W).functionField) : Prop := g ≠ 0 ∧ ∀ x : Curve F W, Scheme.ord g x = katoOrder F W G c x
def IsKatoFunction (W : WeierstrassCurve F) (G : Law F W) (c : ℕ) [IsIntegral (Curve F W)] [IsLocallyNoetherian (Curve F W)] (g : (Curve F W).functionField) : Prop := HasKatoDivisor F W G c g ∧ ∀ d : ℕ, 0 < d → Nat.Coprime c d → ∀ φ : (Curve F W).functionField →+* (Curve F W).functionField, ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ →
          ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g
end ArithmeticThetaGeneralEllipticKatoR0168
namespace ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R]
abbrev GenericCurve (W : WeierstrassCurve R) : Scheme.{u} := ArithmeticThetaGeneralEllipticKatoR0168.Curve (FractionRing R) (W.map (algebraMap R (FractionRing R)))
structure GenericComparison (W : WeierstrassCurve R) (G : Law R W) [IsIntegral (Curve R W)] [IsIntegral (GenericCurve R W)] where
  law : ArithmeticThetaGeneralEllipticKatoR0168.Law (FractionRing R) (W.map (algebraMap R (FractionRing R)))
  originLaw : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw (FractionRing R) (W.map (algebraMap R (FractionRing R))) law
  map : GenericCurve R W ⟶ Curve R W
  cartesian : IsPullback map (ArithmeticThetaGeneralEllipticKatoR0168.structureMap (FractionRing R) (W.map (algebraMap R (FractionRing R)))) (structureMap R W) (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  origin_eq : ArithmeticThetaGeneralEllipticKatoR0168.origin (FractionRing R) (W.map (algebraMap R (FractionRing R))) ≫ map = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ origin R W
  multiplication_eq : ∀ n : ℕ, law.schemeNsmul n ≫ map = map ≫ G.schemeNsmul n
  field : (Curve R W).functionField ≃+* (GenericCurve R W).functionField
  field_eq : ArithmeticThetaGeometricNormR0150.IsFieldMap map field.toRingHom
def katoOrder (W : WeierstrassCurve R) (G : Law R W) (c : ℕ) (x : Curve R W) : ℤ := by
  classical
  exact (if x ∈ Set.range (origin R W) then (c : ℤ)^2 else 0) - (if G.schemeNsmul c x ∈ Set.range (origin R W) then 1 else 0)
variable (W : WeierstrassCurve R) (G : Law R W)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
def IsRelativeKato (c : ℕ) (g : (Curve R W).functionField) : Prop := g ≠ 0 ∧ (∀ x : Curve R W, Order.coheight x = 1 → Scheme.ord g x = katoOrder R W G c x) ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ∀ φ : (Curve R W).functionField →+* (Curve R W).functionField, ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ → ArithmeticThetaGeometricNormR0150.fieldNorm φ g = g)
end ArithmeticThetaRelativeKatoR0169
namespace ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R]
variable (W : WeierstrassCurve R) (G : Law R W)
def identityIdeal : (Curve R W).IdealSheafData := (origin R W).ker
def torsionIdeal (n : ℕ) : (Curve R W).IdealSheafData := (identityIdeal R W).comap (G.schemeNsmul n)
variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
variable [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
def Normalized (c : ℕ) (g : (Curve R W).functionField) : Prop := IsRelativeKato R W G c g ∧ ∀ C : GenericComparison R W G, ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R) (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)
end ArithmeticThetaRelativeKatoNaturalityR0170
namespace ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaTensorPower
def localDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R) (U : (Curve R W).Opens) (a : (Curve R W).presheaf.obj (Opposite.op U)) : Γ(Hodge R W, (origin R W) ⁻¹ᵁ U) := Scheme.Modules.pullbackLocalSection (origin R W) (ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U a)
def localPower (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℕ) (U : (Curve R W).Opens) (a : (Curve R W).presheaf.obj (Opposite.op U)) : Γ(HodgePower R W n, (origin R W) ⁻¹ᵁ U) := tensorPowerSection (Base R) (Hodge R W) n ((origin R W) ⁻¹ᵁ U) (localDifferential R W U a)
variable (R : Type u) [CommRing R] [IsDomain R]
variable (W : WeierstrassCurve R) (G : Law R W)
def IdentityChart (c : ℕ) (U : (Curve R W).affineOpens) (a : (Curve R W).presheaf.obj (Opposite.op U.1)) : Prop := IsRegular a ∧ (identityIdeal R W).ideal U = Ideal.span ({a} : Set _) ∧ (torsionIdeal R W G c).ideal U = (identityIdeal R W).ideal U
variable [IsIntegral (Curve R W)]
def RepresentsInitial (c : ℕ) (g : (Curve R W).functionField) (d : Γ(HodgePower R W (c^2-1), ⊤)) : Prop := ∀ (U : (Curve R W).affineOpens) [Nonempty U.1] (a : (Curve R W).presheaf.obj (Opposite.op U.1)), IdentityChart R W G c U a → ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ, (c : (Curve R W).functionField) * g = (Curve R W).germToFunctionField U.1 ((ε : _) * a^(c^2-1)) ∧
      res (HodgePower R W (c^2-1)) le_top d = (origin R W).app U.1 (ε : _) • localPower R W (c^2-1) U.1 a
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaPullback ArithmeticThetaTensorPower
def powerCongr (X : Scheme.{u}) {H K : X.Modules} (e : H ≅ K) : (n : ℕ) → tensorPower X H n ≅ tensorPower X K n | 0 => Iso.refl _ | n + 1 => sheafTensorCongr X (powerCongr X e n) e
end ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
namespace ArithmeticThetaPullback
def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) := fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s
end ArithmeticThetaPullback
namespace ArithmeticThetaPalomarD2_509.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
def tensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (H : Y.Modules) (K : X.Modules) (e : (Scheme.Modules.pullback p).obj H ≅ K) (n : ℕ) : (Scheme.Modules.pullback p).obj (tensorPower Y H n) ≅ tensorPower X K n := ArithmeticThetaPalomarHalf505.powerComparison X Y p H n ≪≫ powerCongr X e n
end ArithmeticThetaPalomarD2_509.HodgeBaseChange
namespace ArithmeticThetaPalomarD2_509.OpenHodge
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower ArithmeticThetaOpenHodgeR0180
def powerComparison {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) : (Scheme.Modules.pullback (baseMap S R C.scalar)).obj (power E n) ≅ HodgePower R W n := ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison (baseMap S R C.scalar) (hodge E) (Hodge R W) (comparison C) n
def pullSection {S R : Type u} [CommRing S] [CommRing R] {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W} (C : Test S E R W G) (n : ℕ) (s : Γ(power E n, ⊤)) : Γ(HodgePower R W n, ⊤) :=
  res (HodgePower R W n) (by simp)
    ((powerComparison C n).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S R C.scalar) s))
def IsD2 {S : Type u} [CommRing S] (E : EllipticFamily S) (d : Γ(power E 24, ⊤)) : Prop := IsFrame (power E 24) ⊤ d ∧ ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)] [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G → ∀ (C : Test S E R W G) (g : (Curve R W).functionField), Normalized R W G 5 g → RepresentsInitial R W G 5 g (pullSection C 24 d)
end ArithmeticThetaPalomarD2_509.OpenHodge
namespace ArithmeticThetaPalomarD2_509.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def pullToOpen {D : LevelData k L} (n : ℕ) (s : Γ(power D.atlas.descent.family n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarHalf505.powerComparison _ _
    D.quotient.inclusion (hodge D.atlas.descent.family) n).hom.app _
      (Scheme.Modules.pullbackLocalSection D.quotient.inclusion s))
def restrictPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(openPower k L D n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison X.inclusion H.line (openHodge k L D)
    H.onOpen n).hom.app _ (Scheme.Modules.pullbackLocalSection X.inclusion s))
end ArithmeticThetaPalomarD2_509.BoundaryHodge
namespace ArithmeticThetaFullLevelCoverR0175
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
def coordinatePoint {L : ℕ} (A : FullLevel R W G L (𝟙 (Base R))) (i j : Fin L) : Base R ⟶ Curve R W := (G.mul (𝟙 (Base R)) (G.nsmul (𝟙 (Base R)) i.val A.x) (G.nsmul (𝟙 (Base R)) j.val A.y)).val
end ArithmeticThetaFullLevelCoverR0175
namespace ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [IsIntegral (Curve R W)]
def HasValue (P : Spec (CommRingCat.of R) ⟶ Curve R W) (g : (Curve R W).functionField) (v : R) : Prop := ∃ (U : (Curve R W).Opens) (hU : Nonempty U) (e : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U) (a : (Curve R W).presheaf.obj (Opposite.op U)), IsUnit a ∧ @Scheme.germToFunctionField (Curve R W) _ U hU a = g ∧ (Scheme.ΓSpecIso (CommRingCat.of R)).hom (P.appLE U ⊤ e a) = v
end ArithmeticThetaRelativeKatoNaturalityR0170
namespace ArithmeticThetaOpenHodgeR0180
open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
def IsKatoValue {S : Type u} [CommRing S] (E : EllipticFamily S) (c : ℕ) (P : Base S ⟶ E.curve) (v : S) : Prop := IsUnit v ∧ ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)] [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W), IsOriginLaw R W G → ∀ (C : Test S E R W G) (P' : Base R ⟶ Curve R W), P' ≫ structureMap R W = 𝟙 _ → P' ≫ C.map = baseMap S R C.scalar ≫ P → ∀ g : (Curve R W).functionField, Normalized R W G c g → HasValue R W P' g (C.scalar v)
structure Pointed (S : Type u) [CommRing S] (E F : EllipticFamily S) where
  map : E.curve ⟶ F.curve
  over_eq : map ≫ F.projection = E.projection
  zero_eq : zero E ≫ map = zero F
def imagePoint {S : Type u} [CommRing S] {E F : EllipticFamily S} (f : Pointed S E F) {T : Scheme.{u}} (t : T ⟶ Base S) (P : SchemeHomOver t E.projection) : SchemeHomOver t F.projection :=
  ⟨P.val ≫ f.map, by rw [Category.assoc, f.over_eq, P.property]⟩
def IsHom {S : Type u} [CommRing S] {E F : EllipticFamily S} (f : Pointed S E F) : Prop := ∀ (T : Scheme.{u}) (t : T ⟶ Base S) (P Q : SchemeHomOver t E.projection), imagePoint f t (E.law.mul t P Q) = F.law.mul t (imagePoint f t P) (imagePoint f t Q)
def familyHodgeMap {S : Type u} [CommRing S] {E F : EllipticFamily S} (f : Pointed S E F) : hodge F ⟶ hodge E :=
  (pullbackEqIso f.zero_eq.symm F.projection.kaehler).hom ≫
    ((Scheme.Modules.pullbackComp (zero E) f.map).app F.projection.kaehler).inv ≫
    (Scheme.Modules.pullback (zero E)).map
      (differentialMap F.projection E.projection f.map (by simpa using f.over_eq))
structure Quotient (S : Type u) [CommRing S] (E : EllipticFamily S) (m : ℕ) (P : Base S ⟶ E.curve) where
  target : EllipticFamily S
  arrow : Pointed S E target
  hom : IsHom arrow
  finite : IsFinite arrow.map
  etale : Etale arrow.map
  surjective : Surjective arrow.map
  degree : ∀ z, arrow.map.finrank z = m
  kernel : (zero target).ker.comap arrow.map = ⨅ i : Fin m, (P ≫ E.law.schemeNsmul i.val).ker
  universal : ∀ (F : EllipticFamily S) (f : Pointed S E F), IsHom f → (∀ i : Fin m, P ≫ E.law.schemeNsmul i.val ≫ f.map = zero F) → ∃! g : Pointed S target F, IsHom g ∧ arrow.map ≫ g.map = f.map
variable (k : Type u) [Field k] (L : ℕ) (A : LegendreAtlas k L)
abbrev levelFamily := A.descent.family
def kernelPoint (m : ℕ) : Base A.quotient.ring ⟶ (levelFamily k L A).curve := ((levelFamily k L A).law.nsmul (𝟙 _) (L / m) A.marking.x).val
def liftPoint (m N a b : ℕ) : Base A.quotient.ring ⟶ (levelFamily k L A).curve := ((levelFamily k L A).law.mul (𝟙 _) ((levelFamily k L A).law.nsmul (𝟙 _) (L / (m*N) * b) A.marking.x) ((levelFamily k L A).law.nsmul (𝟙 _) (L / N * a) A.marking.y)).val
def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv v
def IsNormalizedPower (m N : ℕ) (Q : Quotient A.quotient.ring (levelFamily k L A) m (kernelPoint k L A m)) (d : Γ(power Q.target 24, ⊤)) (v : A.quotient.ring) (F : Γ(power (levelFamily k L A) (((1+12*N)^2-1)/2), ⊤)) : Prop := ∀ (U : (Base A.quotient.ring).Opens) (η : Γ(hodge Q.target, U)) (a : (Base A.quotient.ring).presheaf.obj (Opposite.op U)), IsFrame (hodge Q.target) U η →
    res (power Q.target 24) le_top d = a • tensorPowerSection (Base A.quotient.ring) (hodge Q.target) 24 U η → res (power (levelFamily k L A) (((1+12*N)^2-1)/2)) le_top F = ((Base A.quotient.ring).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (scalar A.quotient.ring ((algebraMap k A.quotient.ring (m : k)⁻¹)^(((1+12*N)^2-1)/2) * v)) * a^(((1+12*N)^2-1)/48)) •
      tensorPowerSection (Base A.quotient.ring) (hodge (levelFamily k L A)) (((1+12*N)^2-1)/2) U ((familyHodgeMap Q.arrow).app U η)
end ArithmeticThetaOpenHodgeR0180
namespace ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175
variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
def CanonicalMarking (ζ : k) (E : TateLevel k L) : Prop := ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 → ArithmeticThetaLegendreComparisonR0177.HasCoordinates (LaurentSeries k) (TateCurve k L) (coordinatePoint (LaurentSeries k) (TateCurve k L) E.law E.marking i j) (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateX L j.val (ζ ^ i.val)))
      (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaTateSeries.tateY L j.val (ζ ^ i.val)))
end ArithmeticThetaTateCuspsR0181
namespace ArithmeticThetaUnaryProduct
noncomputable def unaryA (m : ℕ) (ν : ℤ) : ℕ := (12*(m : ℤ)^2+24*(m : ℤ)*ν).toNat
noncomputable def clearedUnaryTheta (m : ℕ) (ν : ℤ) : PowerSeries ℤ := PowerSeries.mk (fun n => ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1), if 12*((m : ℤ)*k+ν)^2=(n : ℤ) then (1 : ℤ) else 0)
end ArithmeticThetaUnaryProduct
namespace ArithmeticThetaUnaryKatoPowerR0160
def integerSeries (k : Type) [Field k] : PowerSeries ℤ →+* LaurentSeries k := (HahnSeries.ofPowerSeries ℤ k).comp (PowerSeries.map (Int.castRingHom k))
def unary (k : Type) [Field k] (d m : ℕ) (ν : ℤ) : LaurentSeries k := integerSeries k (PowerSeries.subst (PowerSeries.X^d) (ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν))
end ArithmeticThetaUnaryKatoPowerR0160
namespace ArithmeticThetaBoundaryHodgeR0182
def unaryResidue (m N : ℕ) (ν : ℤ) : ℕ := Int.toNat ((((N / 2 : ℕ) : ℤ) + ((N / m : ℕ) : ℤ) * ν) % (N : ℤ))
end ArithmeticThetaBoundaryHodgeR0182
namespace ArithmeticThetaCompactUnaryR0183
abbrev level (N : ℕ) : ℕ := 24*N^2
abbrev exponent (N : ℕ) : ℕ := (1+12*N)^2-1
abbrev weight (N : ℕ) : ℕ := exponent N / 2
abbrev dExponent (N : ℕ) : ℕ := exponent N / 48
end ArithmeticThetaCompactUnaryR0183
namespace ArithmeticThetaPalomarUnary514.BoundaryHodge
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeDiscriminantR0171
variable (k : Type) [Field k] [CharZero k] (L : ℕ)
def diskPower {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (T : DiskTest k L D X) (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) : Γ(tensorPower (Disk k) ((Scheme.Modules.pullback T.disk).obj H.line) n, ⊤) :=
  res _ (by simp) ((ArithmeticThetaPalomarHalf505.powerComparison _ _
    T.disk H.line n).hom.app _ (Scheme.Modules.pullbackLocalSection T.disk s))
end ArithmeticThetaPalomarUnary514.BoundaryHodge
namespace ArithmeticThetaPalomarDifferential365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules := kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf := kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens} (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s
section Differentials
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) := ((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
def kaehler : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (kaehlerPresheaf f)
def kaehlerToSections (U : X.Opens) : ((kaehlerPresheaf f).obj (op U) : Type u) → (Γ(kaehler f, U) : Type u) := fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (kaehlerPresheaf f)).app (op U)).hom s
def relativeD (U : X.Opens) (a : Γ(X, U)) : Γ(kaehler f, U) :=
  letI : Algebra R Γ(X, U) := sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X, U) a)
end Differentials
end ArithmeticThetaPalomarDifferential365
namespace ArithmeticThetaPalomarConormal436
open ArithmeticThetaPalomarDifferential365
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (e : S ⟶ X)
def Normalized (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Prop := ∀ (U : X.Opens) (x : Γ(idealModule e.ker,U)), m.app (e ⁻¹ᵁ U) (pullSection e x) = pullSection e (relativeD c U ((idealInclusion e.ker).app U x))
theorem canonicalConormalMap : ∃! m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c), Normalized c e m := by sorry
def conormalMap : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c) := (canonicalConormalMap c e).exists.choose
end ArithmeticThetaPalomarConormal436
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) : SheafOfModules.unit Y.ringCatSheaf ⟶ (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
end AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory.Limits
variable {X : Scheme.{u}}
def module (I : X.IdealSheafData) : X.Modules := (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)
def moduleι (I : X.IdealSheafData) : I.module ⟶ SheafOfModules.unit X.ringCatSheaf := kernel.ι I.subschemeι.unitToPushforwardUnit
end AlgebraicGeometry.Scheme.IdealSheafData
namespace ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory.Limits NeronModelInfra
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
structure SchemeLaw {S X : Scheme.{u}} (p : X ⟶ S) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p → SchemeHomOver t p → SchemeHomOver t p
  one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p → SchemeHomOver t p
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y z : SchemeHomOver t p), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t (inv t x) x = one t
  mul_comm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t p), mul t x y = mul t y x
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t p), GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t x y) = mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) (GoodReductionJacobian.schemeHomOverComp ψ hψ y)
structure Family (S : Scheme.{u}) where
  curve : Scheme.{u}
  p : curve ⟶ S
  law : SchemeLaw p
  proper : IsProper p
  dimension : SmoothOfRelativeDimension 1 p
  connected : GeometricallyConnected p
def Family.zero {S : Scheme.{u}} (E : Family S) : S ⟶ E.curve := (E.law.one (𝟙 S)).val
end ArithmeticThetaLocalWeierstrassR0203
namespace ArithmeticThetaSchemeLevelR0204
open CategoryTheory.Limits NeronModelInfra ArithmeticThetaLocalWeierstrassR0203
def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}} (t : T ⟶ S) : ℕ → SchemeHomOver t E.p → SchemeHomOver t E.p | 0, _ => E.law.one t | n + 1, x => E.law.mul t (multiple E t n x) x
structure FullLevel {S : Scheme.{u}} (E : Family S) (L : ℕ) where
  x : SchemeHomOver (𝟙 S) E.p
  y : SchemeHomOver (𝟙 S) E.p
  killed_x : multiple E (𝟙 S) L x = E.law.one (𝟙 S)
  killed_y : multiple E (𝟙 S) L y = E.law.one (𝟙 S)
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 → Disjoint (Set.range (E.law.mul (𝟙 S) (multiple E (𝟙 S) i.val x) (multiple E (𝟙 S) j.val y)).val) (Set.range E.zero)
variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
def UniversalMultiplicative {S : Scheme.{u}} (E : Family S) (b : S ⟶ Base A.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) : Prop := ∀ (T : Scheme.{u}) (t : T ⟶ S) (x y : SchemeHomOver t E.p) (x' y' : SchemeHomOver (t ≫ b) A.descent.family.projection), x'.val = x.val ≫ f → y'.val = y.val ≫ f → (A.descent.family.law.mul _ x' y').val = (E.law.mul t x y).val ≫ f
def Classifies (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (M : FullLevel E L) (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) : Prop :=
  b ≫ Spec.map (CommRingCat.ofHom (algebraMap k Q.quotient.ring)) = σ ∧ IsPullback f E.p A.descent.family.projection (b ≫ Q.inclusion) ∧ E.zero ≫ f = (b ≫ Q.inclusion) ≫ (A.descent.family.law.one (𝟙 _)).val ∧ M.x.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.x.val ∧ M.y.val ≫ f = (b ≫ Q.inclusion) ≫ A.marking.y.val ∧ UniversalMultiplicative k L A E (b ≫ Q.inclusion) f
end ArithmeticThetaSchemeLevelR0204
namespace ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier
open ArithmeticThetaLocalWeierstrassR0203
def universalFamily {k : Type u} [Field k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) : Family (Base A.quotient.ring) where
  curve := A.descent.family.curve
  p := A.descent.family.projection
  law :=
    { mul := A.descent.family.law.mul, one := A.descent.family.law.one
      inv := A.descent.family.law.inv
      mul_assoc := A.descent.family.law.mul_assoc
      one_mul := A.descent.family.law.one_mul
      mul_one := A.descent.family.law.mul_one
      inv_mul_cancel := A.descent.family.law.inv_mul_cancel
      mul_comm := A.descent.family.commutative
      mul_natural := A.descent.family.law.mul_natural }
  proper := A.descent.family.proper
  dimension := A.descent.family.smooth
  connected := A.descent.family.connected
end ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier
namespace ArithmeticThetaPalomarField519.Hodge
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules := (Scheme.Modules.pullback E.zero).obj E.zero.ker.module
def IdealCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (f : F.curve ⟶ E.curve) (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) : Prop := i.hom ≫ F.zero.ker.moduleι = (Scheme.Modules.pullback f).map E.zero.ker.moduleι ≫ (ArithmeticThetaPullback.pullback_unit_iso F.curve E.curve f).hom
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F := squarePullbackIso b E.zero F.zero f hz.symm E.zero.ker.module ≪≫ (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F) : Prop := ∃ i, IdealCompatible E F f i ∧ e = cotangentComparison E F b f hz i
abbrev affineDifferential {R : Type u} [CommRing R] (E : Family (Base R)) : Cotangent E ⟶ (Scheme.Modules.pullback E.zero).obj E.p.kaehler := ArithmeticThetaPalomarConormal436.conormalMap E.p E.zero
variable (k : Type u) [Field k] [CharZero k] (L : ℕ)
  (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)
  (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A)
  (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B)
  (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C)
abbrev universalFamily := ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily L A
abbrev ModularHodge : (Base Q.quotient.ring).Modules := (Scheme.Modules.pullback Q.inclusion).obj ((Scheme.Modules.pullback (universalFamily k L A).zero).obj (universalFamily k L A).p.kaehler)
def ClassifierHodge {S : Scheme.{u}} (E : Family S) (b : S ⟶ Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) (e : (Scheme.Modules.pullback b).obj (ModularHodge k L A B C Q) ≅ Cotangent E) : Prop := ∃ (hz : E.zero ≫ f = (b ≫ Q.inclusion) ≫ (universalFamily k L A).zero) (i : (Scheme.Modules.pullback f).obj (universalFamily k L A).zero.ker.module ≅ E.zero.ker.module),
    IdealCompatible (universalFamily k L A) E f i ∧ (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback Q.inclusion).map (affineDifferential (universalFamily k L A))) ≫ e.hom = ((Scheme.Modules.pullbackComp b Q.inclusion).app (Cotangent (universalFamily k L A))).hom ≫ (cotangentComparison (universalFamily k L A) E (b ≫ Q.inclusion) f hz i).hom
end ArithmeticThetaPalomarField519.Hodge
namespace ArithmeticThetaPalomarField519.Level
open CategoryTheory.Limits ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaPalomarField519.Hodge
abbrev constants {k l : Type} [Field k] [Field l] (ι : k →+* l) : Base l ⟶ Base k := Spec.map (CommRingCat.ofHom ι)
abbrev Classifies {k : Type} [Field k] [CharZero k] {L : ℕ} (D : LevelData k L) {S : Scheme.{0}} (σ : S ⟶ Base k) (F : Family S) (M : FullLevel F L) (b : S ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve) := ArithmeticThetaSchemeLevelR0204.Classifies k L D.atlas D.two D.cover D.quotient σ F M b f
def RespectsClassifiers {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (f : OpenBase l L E ⟶ OpenBase k L D) : Prop := f ≫ openStructure k L D = openStructure l L E ≫ constants ι ∧ ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L) (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve),
    Classifies E σ F M b g → ∃ a : F.curve ⟶ D.atlas.descent.family.curve, Classifies D (σ ≫ constants ι) F M (b ≫ f) a
abbrev weight {k : Type} [Field k] [CharZero k] {L : ℕ} (D : LevelData k L) := ModularHodge k L D.atlas D.two D.cover D.quotient
def HodgeCompatible {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (f : OpenBase l L E ⟶ OpenBase k L D) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) : Prop := ∀ (S : Scheme.{0}) (σ : S ⟶ Base l) (F : Family S) (M : FullLevel F L) (b : S ⟶ OpenBase l L E) (g : F.curve ⟶ E.atlas.descent.family.curve)
    (a : F.curve ⟶ D.atlas.descent.family.curve), Classifies E σ F M b g → Classifies D (σ ≫ constants ι) F M (b ≫ f) a → ∀ (el : (Scheme.Modules.pullback b).obj (weight E) ≅ Cotangent F) (ek : (Scheme.Modules.pullback (b ≫ f)).obj (weight D) ≅ Cotangent F), ClassifierHodge l L E.atlas E.two E.cover E.quotient F b g el → ClassifierHodge k L D.atlas D.two D.cover D.quotient F (b ≫ f) a ek →
    (Scheme.Modules.pullback b).map e.hom ≫ el.hom = ((Scheme.Modules.pullbackComp b f).app (weight D)).hom ≫ ek.hom
def Extends {k l : Type} [Field k] [Field l] {L : ℕ} (ι : k →+* l) (D : LevelData k L) (E : LevelData l L) (X : Compactification k L D) (Y : Compactification l L E) (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) : Prop := F ≫ X.projection = Y.projection ≫ constants ι ∧ Y.inclusion ≫ F = f ≫ X.inclusion
end ArithmeticThetaPalomarField519.Level
namespace ArithmeticThetaPalomarField519.Boundary
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaPalomarField519.Level
variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
def CompactCompatible (ι : k →+* l) {L : ℕ} {D : LevelData k L} {E : LevelData l L} {X : Compactification k L D} {Y : Compactification l L E} (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) (hF : ArithmeticThetaPalomarField519.Level.Extends ι D E X Y f F) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) (H : Extension k L D X) (J : Extension l L E Y) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) : Prop :=
  (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom = ((Scheme.Modules.pullbackComp Y.inclusion F).app H.line).hom ≫ (pullbackEqIso hF.2 H.line).hom ≫ ((Scheme.Modules.pullbackComp f X.inclusion).app H.line).inv ≫ (Scheme.Modules.pullback f).map H.onOpen.hom ≫ e.hom
def GeometricallyCanonical {L : ℕ} {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) : Prop := ∀ (l : Type) [Field l] [CharZero l] [IsAlgClosed l] (ι : k →+* l) (E : LevelData l L) (Y : Compactification l L E) (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) (hf : RespectsClassifiers ι D E f) (hF : ArithmeticThetaPalomarField519.Level.Extends ι D E X Y f F)
    (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E), HodgeCompatible ι D E f e → ∀ J : Extension l L E Y, Canonical l L J → ∃! a : (Scheme.Modules.pullback F).obj H.line ≅ J.line, CompactCompatible ι f F hF e H J a
end ArithmeticThetaPalomarField519.Boundary
namespace ArithmeticThetaDiscriminant
noncomputable def partialEuler {R : Type*} [CommRing R] (a : R) (N : ℕ) : PowerSeries R := ∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (j + 1))
noncomputable def euler {R : Type*} [CommRing R] (a : R) : PowerSeries R := PowerSeries.mk (fun d => PowerSeries.coeff d (partialEuler a d))
noncomputable def P : PowerSeries ℚ := euler 1
end ArithmeticThetaDiscriminant
namespace ArithmeticThetaHodgeInitialR0163
variable (k : Type) [Field k] [CharZero k]
def discriminantSeries (r : ℕ) : PowerSeries k := PowerSeries.subst (PowerSeries.X^r) (PowerSeries.map (algebraMap ℚ k) (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48))
end ArithmeticThetaHodgeInitialR0163
namespace ArithmeticThetaPalomarFieldD2_522
open ArithmeticThetaTensorPower ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelCompactificationR0179
def RealizesDiscriminant (k : Type) [Field k] [CharZero k] (L : ℕ) {D : LevelData k L} {X : Compactification k L D} (H : Extension k L D X) (d : Γ(ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24, ⊤)) (s : Γ(tensorPower X.space H.line 24, ⊤)) : Prop := ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k L H 24 s = ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k L 24 d ∧
  ∀ (V : DiskTest k L D X) (η : Γ((Scheme.Modules.pullback V.disk).obj H.line, ⊤)), ExtendsGenerator k L H V η → ArithmeticThetaPalomarUnary514.BoundaryHodge.diskPower k L H V 24 s = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) • tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k)
        ((Scheme.Modules.pullback V.disk).obj H.line) 24 ⊤ η ∧ (∀ j : ℕ, j < 2*L → PowerSeries.coeff j (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 0) ∧ PowerSeries.coeff (2*L) (ArithmeticThetaHodgeInitialR0163.discriminantSeries k L) = 1
end ArithmeticThetaPalomarFieldD2_522
namespace ArithmeticThetaPalomarFieldD2_522
theorem fieldCompactDiscriminant : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaPalomarField519.Boundary.GeometricallyCanonical H → ∀ d : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPalomarD2_509.OpenHodge.IsD2 D.atlas.descent.family d → ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPalomarFieldD2_522.RealizesDiscriminant k L H d s := by sorry
end ArithmeticThetaPalomarFieldD2_522
