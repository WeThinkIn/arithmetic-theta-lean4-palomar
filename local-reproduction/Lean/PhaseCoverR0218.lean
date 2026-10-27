import PhaseSwitchDefinitionsR0218

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203

namespace PhaseCoverProof

lemma polynomial_eq (k : Type u) [Field k] :
    phasePolynomial k = Polynomial.X^2 - Polynomial.C (-1 : k) := by
  simp [phasePolynomial]

lemma root_sq (k : Type u) [Field k] :
    (AdjoinRoot.root (phasePolynomial k))^2 = -1 := by
  have h := AdjoinRoot.mk_self (f := phasePolynomial k)
  change AdjoinRoot.mk (phasePolynomial k) (Polynomial.X^2 + 1) = 0 at h
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, eq_neg_iff_add_eq_zero] using h

lemma geometry (k : Type u) [Field k] [CharZero k] :
    IsFinite (phaseMap k) ∧ Etale (phaseMap k) ∧ Surjective (phaseMap k) ∧
      ∀ z, (phaseMap k).finrank z = 2 := by
  classical
  have hm : (phasePolynomial k).Monic := by
    rw [polynomial_eq]; exact Polynomial.monic_X_pow_sub_C _ (by decide)
  obtain ⟨he, hf⟩ := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit
    2 (-1 : k) (isUnit_iff_ne_zero.mpr (by norm_num)) (by simp)
  rw [← polynomial_eq] at he hf
  letI := he
  letI := hf
  letI : Module.Free k (PhaseAlgebra k) := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have hfin : IsFinite (phaseMap k) := by
    rw [phaseMap, Scheme.Spec_map, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have het : Etale (phaseMap k) := by
    rw [phaseMap, Scheme.Spec_map, HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  letI := hfin
  letI := het
  have hr : ∀ z, (phaseMap k).finrank z = 2 := by
    intro z
    change (Spec.map (CommRingCat.ofHom (algebraMap k (PhaseAlgebra k)))).finrank z = 2
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free,
      (AdjoinRoot.powerBasis' hm).finrank]
    change (phasePolynomial k).natDegree = 2
    rw [polynomial_eq]
    exact Polynomial.natDegree_X_pow_sub_C
  refine ⟨hfin, het, ?_, hr⟩
  apply (Scheme.Hom.one_le_finrank_iff_surjective _).mp
  intro z
  rw [hr]
  norm_num

lemma value_sq (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k) :
    (phaseValue k S σ)^2 = -1 := by
  have h := congrArg (((pullback.snd σ (phaseMap k)).appTop).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (PhaseAlgebra k))).inv.hom) (root_sq k)
  change (((pullback.snd σ (phaseMap k)).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PhaseAlgebra k))).inv.hom
      (AdjoinRoot.root (phasePolynomial k))))^2 = -1
  simpa only [map_pow, map_neg, map_one, RingHom.comp_apply] using! h

/-- The ring homomorphism corresponding to a morphism into an affine scheme. -/
def coordinates {R : Type u} [CommRing R] {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

lemma coordinates_comp {R : Type u} [CommRing R] {T U : Scheme.{u}}
    (f : T ⟶ U) (g : U ⟶ Spec (CommRingCat.of R)) :
    coordinates (f ≫ g) = f.appTop.hom.comp (coordinates g) := rfl

lemma coordinates_spec {R A : Type u} [CommRing R] [CommRing A]
    {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of A)) (i : R →+* A) :
    coordinates (f ≫ Spec.map (CommRingCat.ofHom i)) = (coordinates f).comp i := by
  apply RingHom.ext
  intro x
  exact ConcreteCategory.congr_hom
    (by simpa only [Scheme.Hom.comp_appTop, Category.assoc] using
      (Scheme.ΓSpecIso_inv_naturality_assoc (CommRingCat.ofHom i) f.appTop).symm) x

lemma coordinates_injective {R : Type u} [CommRing R] {T : Scheme.{u}}
    {f g : T ⟶ Spec (CommRingCat.of R)} (h : coordinates f = coordinates g) : f = g := by
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

lemma hom_ext (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    {T : Scheme.{u}} {q r : T ⟶ phaseSpace k S σ}
    (hb : q ≫ phaseProjection k S σ = r ≫ phaseProjection k S σ)
    (hv : q.appTop (phaseValue k S σ) = r.appTop (phaseValue k S σ)) : q = r := by
  apply pullback.hom_ext hb
  apply coordinates_injective
  apply AdjoinRoot.ringHom_ext
  · rw [← coordinates_spec, ← coordinates_spec]
    apply congrArg coordinates
    change q ≫ pullback.snd σ (phaseMap k) ≫ phaseMap k =
      r ≫ pullback.snd σ (phaseMap k) ≫ phaseMap k
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun a => a ≫ σ) hb
  · exact hv

lemma represents (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    (T : Scheme.{u}) (b : T ⟶ S) (w : Γ(T, ⊤)) (hw : w^2 = -1) :
    ∃! q : T ⟶ phaseSpace k S σ,
      q ≫ phaseProjection k S σ = b ∧ q.appTop (phaseValue k S σ) = w := by
  let i : k →+* Γ(T, ⊤) := coordinates (b ≫ σ)
  have hp : (phasePolynomial k).eval₂ i w = 0 := by
    simp only [phasePolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one, hw, neg_add_cancel]
  let l : PhaseAlgebra k →+* Γ(T, ⊤) := AdjoinRoot.lift i w hp
  let f : T ⟶ Spec (CommRingCat.of (PhaseAlgebra k)) :=
    (ΓSpec.adjunction.homEquiv T _) (CommRingCat.ofHom l).op
  have hc : coordinates f = l := by
    exact congrArg CommRingCat.Hom.hom
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom l))
  have hf : f ≫ phaseMap k = b ≫ σ := by
    apply coordinates_injective
    rw [show phaseMap k = Spec.map (CommRingCat.ofHom (AdjoinRoot.of (phasePolynomial k))) from rfl,
      coordinates_spec, hc]
    exact AdjoinRoot.lift_comp_of hp
  let q : T ⟶ phaseSpace k S σ := pullback.lift b f hf.symm
  have hq : q ≫ phaseProjection k S σ = b := pullback.lift_fst _ _ _
  have hv : q.appTop (phaseValue k S σ) = w := by
    change coordinates (q ≫ pullback.snd σ (phaseMap k)) (AdjoinRoot.root _) = w
    rw [show q ≫ pullback.snd σ (phaseMap k) = f from pullback.lift_snd _ _ _, hc]
    exact AdjoinRoot.lift_root hp
  exact ⟨q, ⟨hq, hv⟩, fun r hr => hom_ext k S σ (hr.1.trans hq.symm) (hr.2.trans hv.symm)⟩

lemma negating_square (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    (q : phaseSpace k S σ ⟶ phaseSpace k S σ)
    (hb : q ≫ phaseProjection k S σ = phaseProjection k S σ)
    (hv : q.appTop (phaseValue k S σ) = -(phaseValue k S σ)) : q ≫ q = 𝟙 _ := by
  apply hom_ext k S σ
  · simpa only [Category.assoc, hb, Category.id_comp]
  · change q.appTop.hom (q.appTop.hom (phaseValue k S σ)) = phaseValue k S σ
    rw [show q.appTop.hom (phaseValue k S σ) = -(phaseValue k S σ) from hv,
      map_neg, show q.appTop.hom (phaseValue k S σ) = -(phaseValue k S σ) from hv,
      neg_neg]

lemma involution (k : Type u) [Field k] (S : Scheme.{u}) (σ : S ⟶ Base k) :
    ∃! τ : phaseSpace k S σ ≅ phaseSpace k S σ,
      τ.hom ≫ phaseProjection k S σ = phaseProjection k S σ ∧
        τ.hom.appTop (phaseValue k S σ) = -(phaseValue k S σ) := by
  obtain ⟨q, hq, _⟩ := represents k S σ (phaseSpace k S σ) (phaseProjection k S σ)
    (-(phaseValue k S σ)) (by rw [neg_sq, value_sq])
  have hqq := negating_square k S σ q hq.1 hq.2
  let τ : phaseSpace k S σ ≅ phaseSpace k S σ := ⟨q, q, hqq, hqq⟩
  refine ⟨τ, hq, ?_⟩
  intro e he
  apply Iso.ext
  exact hom_ext k S σ (he.1.trans hq.1.symm) (he.2.trans hq.2.symm)

end PhaseCoverProof

/-- The explicit phase cover, on arbitrary scheme bases and arbitrary scheme tests. -/
theorem phase_cover : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)), AlgebraicGeometry.IsFinite (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) ∧ AlgebraicGeometry.Etale (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) ∧ AlgebraicGeometry.Surjective (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) ∧ (∀ s : S, (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ).finrank s = 2) ∧ (ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ)^2 = -1 ∧ (∀ (T : AlgebraicGeometry.Scheme.{u}) (b : Quiver.Hom (T) (S)) (w : T.presheaf.obj (Opposite.op ⊤)), w^2 = -1 → ∃! q : Quiver.Hom (T) (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ), CategoryTheory.CategoryStruct.comp (q) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) = b ∧ q.appTop (ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ) = w) ∧ (∃! τ : CategoryTheory.Iso (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ), CategoryTheory.CategoryStruct.comp (τ.hom) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) = ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ ∧ τ.hom.appTop (ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ) = -(ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ)) ∧ (∀ τ : CategoryTheory.Iso (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ) (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ), (CategoryTheory.CategoryStruct.comp (τ.hom) (ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ) = ArithmeticThetaPhaseSwitchR0218.phaseProjection k S σ ∧ τ.hom.appTop (ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ) = -(ArithmeticThetaPhaseSwitchR0218.phaseValue k S σ)) → CategoryTheory.CategoryStruct.comp (τ.hom) (τ.hom) = CategoryTheory.CategoryStruct.id (ArithmeticThetaPhaseSwitchR0218.phaseSpace k S σ)) := by
  intro k _ _ S σ
  obtain ⟨hf, he, hs, hr⟩ := PhaseCoverProof.geometry k
  letI := hf
  letI := he
  letI := hs
  refine ⟨?_, ?_, ?_, ?_, PhaseCoverProof.value_sq k S σ,
    PhaseCoverProof.represents k S σ, PhaseCoverProof.involution k S σ, ?_⟩
  · exact inferInstanceAs (IsFinite (pullback.fst σ (phaseMap k)))
  · exact inferInstanceAs (Etale (pullback.fst σ (phaseMap k)))
  · exact inferInstanceAs (Surjective (pullback.fst σ (phaseMap k)))
  · intro s
    change (pullback.fst σ (phaseMap k)).finrank s = 2
    rw [Scheme.Hom.finrank_pullback_fst, hr]
  · intro τ hτ
    exact PhaseCoverProof.negating_square k S σ τ.hom hτ.1 hτ.2

#print axioms phase_cover

end ArithmeticThetaPhaseSwitchR0218
