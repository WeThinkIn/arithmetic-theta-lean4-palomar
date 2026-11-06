module

public import MarkedFieldActionR0153
public import Mathlib.FieldTheory.Fixed
public import CoprimeTorsionDivisorNormR0150

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSplitNormR0153
namespace SplitDeckExhaustion
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaGeometricNormR0150 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open MarkedFieldAction MarkedPointAddition

variable {F : Type u} [Field F] {X : Scheme.{u}} {q : X ⟶ Spec (.of F)}

def ActsBy (G : RelativeGroupLaw F q) (f : X ⟶ X)
    (P : SchemeHomOver (𝟙 _) q) : Prop :=
  ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x : SchemeHomOver t q),
    (G.mul t x (schemeHomOverComp t (Category.comp_id t) P)).val = x.val ≫ f

lemma acts_id (G : RelativeGroupLaw F q) : ActsBy G (𝟙 X) (G.one (𝟙 _)) := by
  intro V t x
  rw [G.one_natural, G.mul_one, Category.comp_id]

lemma acts_comp (G : RelativeGroupLaw F q) {f g : X ⟶ X}
    {P Q : SchemeHomOver (𝟙 _) q} (hf : ActsBy G f P) (hg : ActsBy G g Q) :
    ActsBy G (f ≫ g) (G.mul (𝟙 _) P Q) := by
  intro V t x
  rw [G.mul_natural, ← G.mul_assoc, hg, hf, Category.assoc]

lemma acts_iterate (G : RelativeGroupLaw F q) {f : X ⟶ X}
    {P : SchemeHomOver (𝟙 _) q} (hf : ActsBy G f P) (n : ℕ) :
    ∃ Q, ActsBy G (iterateHom f n) Q := by
  induction n with
  | zero => exact ⟨G.one (𝟙 _), acts_id G⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨G.mul (𝟙 _) Q P, acts_comp G hQ hf⟩

lemma acts_origin (G : RelativeGroupLaw F q) {f : X ⟶ X}
    {P : SchemeHomOver (𝟙 _) q} (hf : ActsBy G f P) :
    P.val = (G.one (𝟙 _)).val ≫ f := by
  have h := hf (𝟙 _) (G.one (𝟙 _))
  have hp : schemeHomOverComp (𝟙 _) (Category.comp_id _) P = P :=
    Subtype.ext (Category.id_comp _)
  simpa only [hp, G.one_mul] using h

lemma nsmul_product (G : RelativeGroupLaw F q)
    (hc : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x y : SchemeHomOver t q),
      G.mul t x y = G.mul t y x)
    {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x y : SchemeHomOver t q) (n : ℕ) :
    G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y) := by
  letI := G.pointGroup t
  exact (CoprimeTorsion.nsmul_pow G t n (G.mul t x y)).trans
    (((show Commute x y from hc t x y).mul_pow n).trans
      (congrArg₂ (G.mul t) (CoprimeTorsion.nsmul_pow G t n x).symm
        (CoprimeTorsion.nsmul_pow G t n y).symm))

lemma acts_deck (G : RelativeGroupLaw F q)
    (hc : ∀ {V : Scheme.{u}} (t : V ⟶ Spec (.of F)) (x y : SchemeHomOver t q),
      G.mul t x y = G.mul t y x)
    {f : X ⟶ X} {P : SchemeHomOver (𝟙 _) q} (hf : ActsBy G f P)
    (n : ℕ) (hP : G.nsmul (𝟙 _) n P = G.one (𝟙 _)) :
    f ≫ G.schemeNsmul n = G.schemeNsmul n := by
  let x : SchemeHomOver q q := ⟨𝟙 X, Category.id_comp q⟩
  have ht := hf q x
  have hk : G.nsmul q n (schemeHomOverComp q (Category.comp_id q) P) = G.one q := by
    rw [← G.nsmul_natural, hP, G.one_natural]
  calc
    f ≫ G.schemeNsmul n = (G.mul q x (schemeHomOverComp q (Category.comp_id q) P)).val ≫ G.schemeNsmul n := by
      rw [ht]; simp only [x, Category.id_comp]
    _ = (G.nsmul q n (G.mul q x (schemeHomOverComp q (Category.comp_id q) P))).val := comp_schemeNsmul G _ _ _
    _ = (G.nsmul q n x).val := by rw [nsmul_product G hc, hk, G.mul_one]
    _ = G.schemeNsmul n := by rw [← comp_schemeNsmul]; exact Category.id_comp _

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (h3 : 3 ≤ r) (he : Even r) (M : Model k T) (hM : IsModel k T M)
variable (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
variable (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
variable (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
variable (ha : Actions k M rot scal inv)

include he s hs hG in
lemma translation_acts (i : Fin r) (a : kˣ) :
    ActsBy G (translation k M rot scal inv ha i a) (point k h3 M hM i a) := by
  have hrot : ActsBy G (rotationMap k M rot scal inv ha)
      (point k h3 M hM (next r hr (zeroIndex r hr)) 1) := by
    intro V t x
    simpa only [point, pointOver, schemeHomOverComp, Category.id_comp] using
      actual_rotation_translation k r hr h3 T he M hM s hs G hG rot scal inv ha
        (sectionAt k h3 M hM (next r hr (zeroIndex r hr)) 1)
        (sectionAt_spec k h3 M hM (next r hr (zeroIndex r hr)) 1) t x
  have hscal : ActsBy G (scalarMap k M rot scal inv ha a)
      (point k h3 M hM (zeroIndex r hr) a) := by
    intro V t x
    simpa only [point, pointOver, schemeHomOverComp, Category.id_comp] using
      actual_scalar_translation k r hr h3 T he M hM s hs G hG rot scal inv ha a
        (sectionAt k h3 M hM (zeroIndex r hr) a)
        (sectionAt_spec k h3 M hM (zeroIndex r hr) a) t x
  obtain ⟨P, hP⟩ := acts_iterate G hrot i.val
  have ht : ActsBy G (translation k M rot scal inv ha i a)
      (G.mul (𝟙 _) P (point k h3 M hM (zeroIndex r hr) a)) := acts_comp G hP hscal
  have hQ : G.mul (𝟙 _) P (point k h3 M hM (zeroIndex r hr) a) = point k h3 M hM i a := by
    apply Subtype.ext
    rw [acts_origin G ht, ← MarkedExactTorsion.point_one k M hM h3 s hs G hG]
    exact point_translation k M rot scal inv ha h3 hM i a
  intro V t x
  simpa only [hQ] using ht t x

lemma kernelIndex_val (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r) (a : Fin d) :
    (kernelIndex (hr := hr) d a).val = (r/d)*a.val := by
  apply Nat.mod_eq_of_lt
  calc
    r / d * a.val < r / d * d := Nat.mul_lt_mul_of_pos_left a.isLt (Nat.div_pos (Nat.le_of_dvd hr hdiv) hd)
    _ = r := Nat.div_mul_cancel hdiv

lemma kernelIndex_injective (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r) :
    Function.Injective (kernelIndex (hr := hr) d) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [kernelIndex_val d hd hdiv, kernelIndex_val d hd hdiv] at hv
  exact Nat.eq_of_mul_eq_mul_left (Nat.div_pos (Nat.le_of_dvd hr hdiv) hd) hv

include he s hs hG in
lemma kernel_killed (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) d) (ab : Fin d × Fin d) :
    G.nsmul (𝟙 _) d (point k h3 M hM (kernelIndex (hr := hr) d ab.1) (ζ^ab.2.val)) = G.one (𝟙 _) := by
  apply (marked_exact_torsion k r hr h3 T he M hM s hs G hG _ _ _
    (sectionAt_spec k h3 M hM _ _) d).2
  constructor
  · rw [kernelIndex_val d hd hdiv, ← Nat.mul_assoc, Nat.mul_div_cancel' hdiv]
    exact dvd_mul_right r ab.1.val
  · have hz : ζ ^ d = 1 := Units.ext (by simpa using hζ.pow_eq_one)
    rw [← pow_mul, Nat.mul_comm ab.2.val d, pow_mul, hz, one_pow]

include h3 he hM s hs hG in
lemma translation_deck (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r)
    (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) d) (ab : Fin d × Fin d) :
    translation k M rot scal inv ha (kernelIndex (hr := hr) d ab.1) (ζ^ab.2.val) ≫
      multiplication k M G d = multiplication k M G d :=
  acts_deck G hG.2
    (translation_acts k h3 he M hM s hs G hG rot scal inv ha _ _) d
    (kernel_killed k h3 he M hM s hs G hG d hd hdiv ζ hζ ab)

/-- The degree bound exhausts a full-sized family of embeddings for the specified scalar map. -/
lemma exhaustive_of_degree (K L : Type u) [Field K] [Field L] (μ : K →+* L)
    (hfin : letI := μ.toAlgebra; FiniteDimensional K L)
    (I : Type*) [Fintype I] (τ : I → (L →+* L))
    (hinj : Function.Injective τ) (hτ : ∀ i, (τ i).comp μ = μ)
    (hcard : Fintype.card I = (letI := μ.toAlgebra; Module.finrank K L))
    (ψ : L →+* L) : ψ.comp μ = μ ↔ ∃! i, ψ = τ i := by
  classical
  letI := μ.toAlgebra
  letI : FiniteDimensional K L := hfin
  let f : I → (L →ₐ[K] L) := fun i =>
    { τ i with commutes' := fun x => DFunLike.congr_fun (hτ i) x }
  have hf : Function.Injective f := by
    intro i j h
    exact hinj (congrArg AlgHom.toRingHom h)
  have hcount : Fintype.card I = Fintype.card (L →ₐ[K] L) :=
    le_antisymm (Fintype.card_le_of_injective f hf) ((AlgHom.card_le (F := K) (K := L)).trans_eq hcard.symm)
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcount⟩).2
  constructor
  · intro hψ
    let g : L →ₐ[K] L := { ψ with commutes' := fun x => DFunLike.congr_fun hψ x }
    obtain ⟨i, hi⟩ := hsurj g
    have hi' : ψ = τ i := (congrArg AlgHom.toRingHom hi).symm
    exact ⟨i, hi', fun j hj => hinj (hj.symm.trans hi')⟩
  · rintro ⟨i, rfl, _⟩
    exact hτ i

end SplitDeckExhaustion

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaHodgeFourTorsionR0147
open SplitDeckExhaustion MarkedFieldAction ActualMultiplicationFieldNorm

/-- All embeddings over actual multiplication are exactly the labelled split translations. -/
theorem split_deck_exhaustion :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → (CategoryTheory.Iso M.X M.X)) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv) (σ : Fin r → kˣ → ((AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) ≃+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)))) (hσ : ArithmeticThetaSplitNormR0153.IsFieldAction k M rot scal inv ha σ) (d : ℕ) (hd : 0 < d) (hdiv : d ∣ r) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) d) (μ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M))) (hμ : ArithmeticThetaGeometricNormR0150.IsFieldMap (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G d) μ), ∀ ψ : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) →+* (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ψ.comp μ = μ ↔ ∃! ab : Fin d × Fin d, ψ = (σ (ArithmeticThetaSplitNormR0153.kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)).toRingHom := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ rot scal inv ha σ hσ d hd hdiv ζ hζ μ hμ
  obtain ⟨σ₀, ⟨h₀, hinj, _, _⟩, _⟩ := marked_field_action k r hr h3 T he M hM s hs G hG rot scal inv ha
  have heq : σ₀ = σ := by
    funext i a
    apply RingEquiv.toRingHom_injective
    exact fieldMap_unique _ _ _ (hσ i a) (h₀ i a)
  subst σ₀
  obtain ⟨ν, hν, hfin, hdeg, _, _⟩ :=
    actual_multiplication_field_norm k r hr h3 T he M hM s hs G hG d hd
  have hνμ : ν = μ := fieldMap_unique _ _ _ hμ hν
  subst ν
  let τ : Fin d × Fin d → ((genericScheme k M).functionField →+* (genericScheme k M).functionField) :=
    fun ab => (σ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)).toRingHom
  have hτinj : Function.Injective τ := by
    intro ab cd hh
    have he : σ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val) =
        σ (kernelIndex (hr := hr) d cd.1) (ζ ^ cd.2.val) := RingEquiv.toRingHom_injective hh
    have hh' := hinj (a₁ := (kernelIndex (hr := hr) d ab.1, ζ ^ ab.2.val))
      (a₂ := (kernelIndex (hr := hr) d cd.1, ζ ^ cd.2.val)) he
    have hfst := congrArg Prod.fst hh'
    have hsnd := congrArg Prod.snd hh'
    apply Prod.ext (kernelIndex_injective (hr := hr) d hd hdiv hfst)
    apply Fin.ext
    apply hζ.pow_inj ab.2.isLt cd.2.isLt
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hsnd
  have hτ : ∀ ab, (τ ab).comp μ = μ := by
    intro ab
    have hh := field_comp (hσ (kernelIndex (hr := hr) d ab.1) (ζ ^ ab.2.val)) hμ
    rw [translation_deck k h3 he M hM s hs G hG rot scal inv ha d hd hdiv ζ hζ ab] at hh
    exact fieldMap_unique _ _ _ hμ hh
  intro ψ
  apply exhaustive_of_degree (genericScheme k M).functionField (genericScheme k M).functionField
    μ hfin (Fin d × Fin d) τ hτinj hτ _ ψ
  simpa only [fieldDegree, Fintype.card_prod, Fintype.card_fin, pow_two] using hdeg.symm

#print axioms split_deck_exhaustion
end ArithmeticThetaSplitNormR0153
