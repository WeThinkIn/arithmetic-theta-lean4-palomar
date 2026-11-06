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
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) := {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
namespace HomogeneousIdealQuotientGrading
open DirectSum
section Engine
variable {ι A σ τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)
def pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) : 𝒜 i →+ ℬ i := AddMonoidHom.codRestrict
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 i))) (ℬ i) (fun a => hmem i a a.2)
@[simp] lemma pieceHom_coe (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (i : ι) (a : 𝒜 i) : (pieceHom 𝒜 I ℬ hmem i a : A ⧸ I) = Ideal.Quotient.mk I (a : A) := by sorry
omit [AddSubmonoidClass σ A] [AddSubmonoidClass τ (A ⧸ I)] in
theorem gradedMonoidOfImages [AddMonoid ι] [SetLike.GradedMonoid 𝒜] (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hsurj : ∀ (i : ι), ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = b) : SetLike.GradedMonoid ℬ := by sorry
variable [DecidableEq ι]
lemma coeAddMonoidHom_map_pieceHom (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (y : ⨁ i, 𝒜 i) : DirectSum.coeAddMonoidHom ℬ (DirectSum.map (pieceHom 𝒜 I ℬ hmem) y) = Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 y) := by sorry
variable [AddMonoid ι] [GradedRing 𝒜]
def preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) : A →+ ⨁ i, ℬ i :=
  (DirectSum.map (pieceHom 𝒜 I ℬ hmem)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom
lemma preDecompose_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : preDecompose 𝒜 I ℬ hmem a = DirectSum.map (pieceHom 𝒜 I ℬ hmem) (decompose 𝒜 a) := rfl
lemma preDecompose_apply_apply (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) (i : ι) : preDecompose 𝒜 I ℬ hmem a i = pieceHom 𝒜 I ℬ hmem i (decompose 𝒜 a i) := by
  rw [preDecompose_apply, DirectSum.map_apply]
lemma preDecompose_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) {i : ι} {a : A} (ha : a ∈ 𝒜 i) : preDecompose 𝒜 I ℬ hmem a = DirectSum.of (fun j => ℬ j) i ⟨Ideal.Quotient.mk I a, hmem i a ha⟩ := by sorry
lemma coeAddMonoidHom_preDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (a : A) : DirectSum.coeAddMonoidHom ℬ (preDecompose 𝒜 I ℬ hmem a) = Ideal.Quotient.mk I a := by sorry
lemma preDecompose_eq_zero_of_mem (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) : preDecompose 𝒜 I ℬ hmem a = 0 := by sorry
def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i) (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem) (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)
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
lemma mk_mem_quotGradingSubmodule {i : ι} {a : A} (ha : a ∈ 𝒜 i) : Ideal.Quotient.mk I a ∈ quotGradingSubmodule 𝒜 I i :=
  (mem_quotGradingSubmodule_iff 𝒜 I).mpr ⟨a, ha, rfl⟩
instance quotGradingSubmoduleGradedMonoid [AddMonoid ι] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (quotGradingSubmodule 𝒜 I) := by sorry
variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜]
@[reducible] def quotGradingSubmoduleGradedAlgebra (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 I) :=
  gradedRingOfImages 𝒜 I (quotGradingSubmodule 𝒜 I) (fun _ _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha)
    (fun _ _ hb => (mem_quotGradingSubmodule_iff 𝒜 I).mp hb) hI
instance quotGradingSubmoduleGradedAlgebraOfHomogeneous (J : HomogeneousIdeal 𝒜) : GradedAlgebra (quotGradingSubmodule 𝒜 J.toIdeal) :=
  quotGradingSubmoduleGradedAlgebra 𝒜 J.toIdeal J.isHomogeneous
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
def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩
@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) : (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl
abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ := MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) : ℕ → Submodule R (ProjModelRingCR V) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal
abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme := Proj (projModelGradingCR V)
def projModelStrCR (V : WeierstrassCurve.Projective R) : Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projModelGradingCR V) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
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
theorem kwYEvalRingHom_mk_X1 : kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by sorry
def kwYChartEval : HomogeneousLocalization.Away (projModelGradingCR W.toProjective) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W) (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp (algebraMap (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))) (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))
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
abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} := WeierstrassProjModel.projModelCR W.toProjective
def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) := WeierstrassProjModel.projModelStrCR W.toProjective
def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W := (WeierstrassProjModel.kwZeroSect R W).val
abbrev Law (W : WeierstrassCurve R) := WeierstrassProjModel.RelativeGroupLaw R (structureMap R W)
def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop := (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)),
    (G.one t).val = t ≫ origin R W) ∧ (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (structureMap R W)), G.mul t x y = G.mul t y x)
end ArithmeticThetaRelativeKatoR0169
namespace WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
end WeierstrassProjModel.RelativeGroupLaw
open NeronModelInfra
namespace GoodReductionJacobian
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
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
namespace RelativeGroupLaw
def IsCommutative {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x
end RelativeGroupLaw
end GoodReductionJacobian
namespace GoodReductionJacobian.RelativeGroupLaw
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩
def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1
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
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (G.mul t (G.nsmul t i.val x) (G.nsmul t j.val y)).val)
      (Set.range (origin R W))
structure LevelScheme (L : ℕ) where
  space : Scheme.{u}
  projection : space ⟶ Base R
  level : FullLevel R W G L projection
def Represents {L : ℕ} (D : LevelScheme R W G L) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Base R) (A : FullLevel R W G L t),
    ∃! q : SchemeHomOver t D.projection,
      q.val ≫ D.level.x.val = A.x.val ∧ q.val ≫ D.level.y.val = A.y.val
def levelDegree (L : ℕ) : ℕ := Nat.card ((ZMod L × ZMod L) ≃+ (ZMod L × ZMod L))
end ArithmeticThetaFullLevelCoverR0175
namespace ArithmeticThetaLegendreAtlasR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
abbrev LegendreRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
def parameter (k : Type u) [Field k] : LegendreRing k :=
  algebraMap (Polynomial k) (LegendreRing k) Polynomial.X
def legendre (k : Type u) [Field k] : WeierstrassCurve (LegendreRing k) where
  a₁ := 0
  a₂ := -(parameter k + 1)
  a₃ := 0
  a₄ := parameter k
  a₆ := 0
def legendreBaseMap (k : Type u) [Field k] : Base (LegendreRing k) ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LegendreRing k)))
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
  smooth : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k ring)))
  relation : (X ⨿ X) ≅ pullback q q
  left_fst : coprod.inl ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  left_snd : coprod.inl ≫ relation.hom ≫ pullback.snd q q = 𝟙 X
  right_fst : coprod.inr ≫ relation.hom ≫ pullback.fst q q = 𝟙 X
  right_snd : coprod.inr ≫ relation.hom ≫ pullback.snd q q = σ
  universal : ∀ (T : Scheme.{u}) (a : X ⟶ T), σ ≫ a = a →
    ∃! b : Base ring ⟶ T, q ≫ b = a
attribute [instance] SignQuotient.commRing SignQuotient.algebra
abbrev coverCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback (structureMap R W) Z.projection
abbrev coverToCurve (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback.fst (structureMap R W) Z.projection
abbrev coverToLevel (R : Type u) [CommRing R] (W : WeierstrassCurve R) {G : Law R W} {L : ℕ} (Z : LevelScheme R W G L) :=
  pullback.snd (structureMap R W) Z.projection
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
  avoids : ∀ i j : Fin L, i.val ≠ 0 ∨ j.val ≠ 0 →
    Disjoint (Set.range (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) i.val x)
      (E.law.nsmul (𝟙 _) j.val y)).val) (Set.range (E.law.one (𝟙 _)).val)
def FamilyRigid (S : Type u) [CommRing S] (E : EllipticFamily S) {L : ℕ} (M : FamilyLevel S E L) : Prop :=
  ∀ e : E.curve ≅ E.curve,
    e.hom ≫ E.projection = E.projection →
    (E.law.one (𝟙 _)).val ≫ e.hom = (E.law.one (𝟙 _)).val →
    M.x.val ≫ e.hom = M.x.val → M.y.val ≫ e.hom = M.y.val →
    e.hom = 𝟙 E.curve
structure FamilyDescent (k R : Type u) [Field k] [CommRing R] [Algebra k R] (W : WeierstrassCurve R) (G : Law R W) {L : ℕ} (Z : LevelScheme R W G L) (σ : SignAction R W G Z) (Q : SignQuotient k (Z.projection ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map) where
  family : EllipticFamily Q.ring
  comparison : coverCurve R W Z ⟶ family.curve
  cartesian : IsPullback comparison (coverToLevel R W Z) family.projection Q.q
  origin_eq : coverSection R W Z (G.one Z.projection) ≫ comparison =
    Q.q ≫ (family.law.one (𝟙 _)).val
  action : coverCurve R W Z ⟶ coverCurve R W Z
  action_level : action ≫ coverToLevel R W Z = coverToLevel R W Z ≫ σ.map
  action_curve : action ≫ coverToCurve R W Z =
    (G.inv (coverToLevel R W Z ≫ Z.projection)
      ⟨coverToCurve R W Z, pullback.condition⟩).val
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
  x_eq : coverSection (LegendreRing k) (legendre k) level level.level.x ≫
    descent.comparison = quotient.q ≫ marking.x.val
  y_eq : coverSection (LegendreRing k) (legendre k) level level.level.y ≫
    descent.comparison = quotient.q ≫ marking.y.val
end ArithmeticThetaLegendreAtlasR0176
section Chart
open WeierstrassProjModel MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace WeierstrassCurve.DrinfeldGlobal
variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
abbrev coord (i : Fin 3) : ProjModelRingCR W := Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)
theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 := mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)
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
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) := WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def HasCoordinates (R : Type u) [CommRing R] (W : WeierstrassCurve R) (P : Base R ⟶ Curve R W) (x y : R) : Prop :=
  P ≫ structureMap R W = 𝟙 (Base R) ∧ ∃ χ : ChartRing R W →+* R, P = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion R W ∧
    χ (WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective) = x ∧ χ (WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective) = y
def completedCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.X^3 + Polynomial.C (W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2) * Polynomial.X^2 +
    Polynomial.C (W.a₄ + algebraMap ℚ R (1/2) * W.a₁ * W.a₃) * Polynomial.X + Polynomial.C (W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2)
def SplitCubic (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (e : Fin 3 → R) : Prop :=
  (∀ i j, i ≠ j → IsUnit (e i - e j)) ∧ completedCubic R W = ∏ i : Fin 3, (Polynomial.X - Polynomial.C (e i))
end ArithmeticThetaLegendreComparisonR0177
namespace ArithmeticThetaCompatibleLevelR0178
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaLegendreComparisonR0177
variable (k : Type u) [Field k] [CharZero k] (L : ℕ) (A : LegendreAtlas k L)
abbrev TwoMarking := FullLevel (LegendreRing k) (legendre k) A.law 2
  (𝟙 (Base (LegendreRing k)))
def CanonicalTwo (B : TwoMarking k L A) : Prop :=
  HasCoordinates (LegendreRing k) (legendre k) B.x.val 0 0 ∧
  HasCoordinates (LegendreRing k) (legendre k) B.y.val 1 0
def CompatibleAt (B : TwoMarking k L A) {T : Scheme.{u}} (a : T ⟶ A.level.space) : Prop :=
  a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.x).val =
    (a ≫ A.level.projection) ≫ B.x.val ∧
  a ≫ (A.law.nsmul A.level.projection (L / 2) A.level.level.y).val =
    (a ≫ A.level.projection) ≫ B.y.val
structure CompatibleCover (B : TwoMarking k L A) where
  space : Scheme.{u}
  inclusion : space ⟶ A.level.space
  openImmersion : IsOpenImmersion inclusion
  closedImmersion : IsClosedImmersion inclusion
  compatible : CompatibleAt k L A B inclusion
  represents : ∀ (T : Scheme.{u}) (a : T ⟶ A.level.space),
    CompatibleAt k L A B a ↔ ∃! b : T ⟶ space, b ≫ inclusion = a
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
  over_eq : inclusion ≫ Spec.map (CommRingCat.ofHom (algebraMap k A.quotient.ring)) =
    Spec.map (CommRingCat.ofHom (algebraMap k quotient.ring))
end ArithmeticThetaCompatibleLevelR0178
namespace ArithmeticThetaProjectiveEffectivityR0135
attribute [local instance] MvPolynomial.gradedAlgebra
def projectiveSpace (S : Type u) [CommRing S] (N : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin N) S)
def projectiveStructure (S : Type u) [CommRing S] (N : ℕ) : projectiveSpace S N ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin N) S) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap S ((MvPolynomial.homogeneousSubmodule (Fin N) S) 0)))
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
def openStructure (D : LevelData k L) : OpenBase k L D ⟶ Base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k D.quotient.quotient.ring))
def IsParameter (D : LevelData k L) (p : OpenBase k L D ⟶ Base (LegendreRing k)) : Prop :=
  D.quotient.quotient.q ≫ p = D.cover.inclusion ≫ D.atlas.level.projection ∧
  p ≫ legendreBaseMap k = openStructure k L D
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
  embedding_over : embedding ≫
    ArithmeticThetaProjectiveEffectivityR0135.projectiveStructure k (dimension+1) = projection
def boundary (D : LevelData k L) (X : Compactification k L D) : Set X.space :=
  (Set.range X.inclusion.base)ᶜ
end ArithmeticThetaLevelCompactificationR0179
namespace ArithmeticThetaLevelCount
def PrimitivePair (L : ℕ) := {v : ZMod L × ZMod L // IsCoprime v.1 v.2}
def SignedPrimitivePair (L : ℕ) := Quot (fun a b : PrimitivePair L => b.val = -a.val)
end ArithmeticThetaLevelCount
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by
  sorry
def componentOpen (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, componentIsOpen k L D X x⟩
abbrev Component (x : X.space) : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion (x : X.space) : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
def cuspSet (x : X.space) : Set (Component k L D X x) := {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps (x : X.space) := {y : Component k L D X x // y ∈ cuspSet k L D X x}
theorem geometricComponentCuspBound :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaPalomarComponent485.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by sorry
end ArithmeticThetaPalomarComponent485
