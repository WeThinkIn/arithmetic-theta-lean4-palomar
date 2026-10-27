import SchemeMidpointThetaLiftR0259
import RelativeCyclicThetaSplittingR0256

/-! Coherent cyclic lifts of the actual theta line over arbitrary scheme bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeCyclicThetaSplitting
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open SchemeDoubledTorsionLift
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeDoubledTorsionThetaLiftR0255
open ArithmeticThetaRelativeThetaRelationsR0256.RelativeCyclicThetaSplittingR0256

variable {S : Scheme.{u}} (E : Family S)

lemma multiple_killed (m : ℕ) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S)) (n : ℕ) :
    multiple E (multiple E P n) (2*m) = E.law.one (𝟙 S) := by
  letI := pointCommGroup E (𝟙 S)
  simp only [multiple, multiple_eq_pow] at hP ⊢
  change P ^ (2*m) = 1 at hP
  change (P ^ n) ^ (2*m) = 1
  rw [← pow_mul, Nat.mul_comm n, pow_mul, hP, one_pow]

lemma translation_multiple_zero (P : point E) :
    translation E (multiple E P 0) = 𝟙 E.curve := by
  apply SchemeDoubledTorsionLift.translation_eq_id_of_two_killed
  letI := pointCommGroup E (𝟙 S)
  simp only [multiple, multiple_eq_pow, pow_zero, one_pow]
  rfl

lemma translation_comp (P Q : point E) :
    translation E P ≫ translation E Q = translation E (E.law.mul (𝟙 S) P Q) := by
  letI := pointCommGroup E (𝟙 S)
  letI := pointCommGroup E E.p
  let a : curvePoint E := ⟨𝟙 E.curve, Category.id_comp _⟩
  have ht (R : point E) : translation E R = (a * constantPoint E R ^ 2).val :=
    (id_mul_constantPoint_two E R).symm
  rw [ht P, point_translation]
  change ((a * constantPoint E P ^ 2) * constantPoint E (multiple E Q 2)).val = _
  change ((a * constantPoint E P ^ 2) * constantPoint E (multiple E Q 2)).val =
    translation E (P * Q)
  rw [ht (P * Q)]
  have hpow : constantPoint E (multiple E Q 2) = constantPoint E Q ^ 2 := by
    rw [multiple, multiple_eq_pow]
    exact map_pow (pointPullback E (𝟙 S) E.p E.p (Category.comp_id _)) Q 2
  have hmul : constantPoint E (P * Q) = constantPoint E P * constantPoint E Q :=
    map_mul (pointPullback E (𝟙 S) E.p E.p (Category.comp_id _)) P Q
  rw [hpow, hmul, mul_pow, mul_assoc]

lemma translation_multiple_add (P : point E) (a b : ℕ) :
    translation E (multiple E P a) ≫ translation E (multiple E P b) =
      translation E (multiple E P (a+b)) := by
  rw [translation_comp]
  congr 1
  letI := pointCommGroup E (𝟙 S)
  simp only [multiple, multiple_eq_pow]
  exact (pow_add P a b).symm

lemma translation_multiple_period (m : ℕ) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S)) (a : ℕ) :
    translation E (multiple E P (a+m)) = translation E (multiple E P a) := by
  have hd : multiple E (multiple E P (a+m)) 2 = multiple E (multiple E P a) 2 := by
    letI := pointCommGroup E (𝟙 S)
    simp only [multiple, multiple_eq_pow] at hP ⊢
    change P ^ (2*m) = 1 at hP
    rw [← pow_mul, Nat.add_mul, pow_add, Nat.mul_comm m 2, hP, mul_one, pow_mul]
  unfold translation
  congr 2
  exact Subtype.ext (congrArg (fun R : point E => E.p ≫ R.val) hd)

lemma multiple_one (P : point E) : multiple E P 1 = P := by
  letI := pointCommGroup E (𝟙 S)
  simp only [multiple, multiple_eq_pow, pow_one]

def translationIso (P : point E) : E.curve ≅ E.curve where
  hom := translation E P
  inv := translation E (E.law.inv (𝟙 S) P)
  hom_inv_id := by
    rw [translation_comp]
    letI := pointCommGroup E (𝟙 S)
    change translation E (P * P⁻¹) = _
    rw [mul_inv_cancel]
    exact translation_multiple_zero E P
  inv_hom_id := by
    rw [translation_comp, E.law.inv_mul_cancel]
    exact translation_multiple_zero E P

lemma midpoint_step (P : point E) (n : ℕ) :
    negative E (multiple E P (n+2)) ≫ translation E P =
      negative E (multiple E P n) := by
  unfold negative
  rw [point_translation]
  have hid : (⟨𝟙 _ ≫ (multiple E P 2).val, by
      rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩ : point E) =
      multiple E P 2 := Subtype.ext (Category.id_comp _)
  rw [hid]
  congr 1
  letI := pointCommGroup E (𝟙 S)
  simp only [multiple, multiple_eq_pow]
  change (P ^ (n+2))⁻¹ * P ^ 2 = (P ^ n)⁻¹
  group

lemma reflection_step (P : point E) (n : ℕ) :
    translation E P ≫ reflection E (multiple E P n) =
      reflection E (multiple E P (n+2)) ≫ translation E P := by
  have hi : translation E P ≫ inverse E ≫
      translation E P = inverse E := by
    letI : IsIso (inverse E) := (SchemeThetaInversion.inversionIso E).isIso_hom
    apply (cancel_mono (inverse E)).mp
    simpa only [Category.assoc, reflection, SchemeThetaInversion.inverse_square] using
      SchemeMidpointThetaLift.reflection_square E P
  have hadd (a b : ℕ) := translation_multiple_add E P a b
  have hleft : translation E P ≫
      translation E (multiple E P n) =
      translation E (multiple E P (n+1)) := by
    simpa only [multiple_one, Nat.add_comm 1 n] using hadd 1 n
  have hright : translation E (multiple E P (n+1)) ≫
      translation E P =
      translation E (multiple E P (n+2)) := by
    simpa only [multiple_one, Nat.add_assoc] using hadd (n+1) 1
  unfold reflection
  rw [← Category.assoc, hleft, ← hright]
  simp only [Category.assoc]
  rw [hi]

lemma negative_multiple_zero (P : point E) : negative E (multiple E P 0) = E.zero := by
  change (E.law.inv (𝟙 S) (E.law.one (𝟙 S))).val = E.zero
  letI := pointCommGroup E (𝟙 S)
  change (1 : point E)⁻¹.val = E.zero
  rw [inv_one]
  rfl

lemma identityLift_midpoint_zero (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    MidpointNormalized E m (multiple E P 0) ι
      (changeMap E m (translation_multiple_zero E P) (identityLift E m)) := by
  unfold MidpointNormalized reflectionLift reflection changeMap identityLift
  exact identity_reflection_normalized _ _ _ (translation_multiple_zero E P) _ ι
    (by rw [negative_multiple_zero E P]; exact hι.1)

/-- The exact even-degree theta line is a square of the half-degree theta line. -/
def thetaLineDoubleIso (k : ℕ) (hk : 0 < k) :
    thetaLine E (k+k) ≅ MonoidalCategory.tensorObj (thetaLine E k) (thetaLine E k) := by
  let L := primitiveLine E
  have hL := primitiveLine_invertible E
  have hpow : Nonempty (L.tensorPow (k+k) ≅
      MonoidalCategory.tensorObj (L.tensorPow k) (L.tensorPow k)) := by
    apply (lineClass_eq_iff _ _ (hL.tensorPow (k+k))
      ((hL.tensorPow k).tensor_monoidalV2 (hL.tensorPow k))).mp
    rw [lineClass_tensor _ _ (hL.tensorPow k) (hL.tensorPow k),
      lineClass_tensorPow L hL, lineClass_tensorPow L hL, pow_add]
  exact linePowerIso E (k+k) (by omega) ≪≫ hpow.some ≪≫
    MonoidalCategory.tensorIso (linePowerIso E k hk).symm (linePowerIso E k hk).symm

variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)

/-- Conjugation by an actual translation lift shifts the normalized reflection by two. -/
lemma normalized_reflection_step (m : ℕ) (P : point E) (n : ℕ)
    (α : Lift E m (translation E (multiple E P 1)))
    (β : Lift E m (reflection E (multiple E P n)))
    (γ : Lift E m (reflection E (multiple E P (n+2))))
    (hβ : ∃ h : negative E (multiple E P n) ≫ reflection E (multiple E P n) =
        negative E (multiple E P n),
      (Scheme.Modules.pullback (negative E (multiple E P n))).mapIso β =
        fixedComparison E m _ _ h)
    (hγ : ∃ h : negative E (multiple E P (n+2)) ≫ reflection E (multiple E P (n+2)) =
        negative E (multiple E P (n+2)),
      (Scheme.Modules.pullback (negative E (multiple E P (n+2)))).mapIso γ =
        fixedComparison E m _ _ h) :
    TotalLift.lift (thetaLine E m) _ γ =
      (TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) α).hom ≫
        TotalLift.lift (thetaLine E m) _ β ≫
          (TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) α).inv := by
  let e := translationIso E (multiple E P 1)
  let T := TotalLift.aut (thetaLine E m) e α
  have hg : reflection E (multiple E P (n+2)) =
      e.hom ≫ reflection E (multiple E P n) ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    simpa only [e, translationIso, multiple_one, reflection, Category.assoc] using (reflection_step E P n).symm
  obtain ⟨δ, hδ⟩ := TotalLift.conjugate_lift (thetaLine E m) e α _ β _ hg
  have hδfixed : TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2))) ≫
      TotalLift.lift (thetaLine E m) _ δ =
      TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2))) := by
    rw [hδ]
    apply TotalLift.conjugate_fixed
    change TotalLift.sectionHom (thetaLine E m)
      (negative E (multiple E P (n+2)) ≫ e.hom) ≫ TotalLift.lift (thetaLine E m) _ β =
        TotalLift.sectionHom (thetaLine E m) (negative E (multiple E P (n+2)) ≫ e.hom)
    have he : negative E (multiple E P (n+2)) ≫ e.hom = negative E (multiple E P n) := by
      simpa only [e, translationIso, multiple_one] using midpoint_step E P n
    rw [he]
    obtain ⟨h, hβ⟩ := hβ
    exact TotalLift.fixed_of_normalized _ _ _ _ h hβ
  obtain ⟨hδbase, hδnorm⟩ := TotalLift.normalized_of_fixed _ _ _ _ hδfixed
  obtain ⟨hγbase, hγnorm⟩ := hγ
  have hδγ : δ = γ :=
    (SchemeMidpointThetaLift.normalized_reflection E m (multiple E P (n+2)) ⟨δ⟩).unique
      hδnorm hγnorm
  rw [hδγ] at hδ
  exact hδ

include k σ in
lemma pointwise_exists_unique (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    ∃! α : Lift E m (translation E (multiple E P n)),
      MidpointNormalized E m (multiple E P n) ι α ∧
        Symmetric E m (multiple E P n) ι α :=
  scheme_midpoint_theta_lift k S σ E m hm he (multiple E P n)
    (multiple_killed E m P hP n) ι hι

def normalizedFamily (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    ∀ n : ℕ, Lift E m (translation E (multiple E P n)) :=
  fun n => Classical.choose (pointwise_exists_unique (k := k) (σ := σ) E m hm he P hP ι hι n)

lemma normalizedFamily_spec (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    MidpointNormalized E m (multiple E P n) ι (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι n) ∧
      Symmetric E m (multiple E P n) ι (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι n) :=
  (Classical.choose_spec (pointwise_exists_unique (k := k) (σ := σ) E m hm he P hP ι hι n)).1

lemma symmetric_of_midpoint (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P))
    (hα : MidpointNormalized E m P ι α) : Symmetric E m P ι α := by
  obtain ⟨h, hα⟩ := hα
  exact ⟨SchemeMidpointThetaLift.reflection_square E P,
    SchemeMidpointThetaLift.normalized_square E m P _ hα⟩

lemma normalizedFamily_zero (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) :
    normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι 0 =
      changeMap E m (translation_multiple_zero E P) (identityLift E m) := by
  apply (pointwise_exists_unique (k := k) (σ := σ) E m hm he P hP ι hι 0).unique
  · exact normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι 0
  · have h := identityLift_midpoint_zero E m P ι hι
    exact ⟨h, symmetric_of_midpoint E m (multiple E P 0) ι _ h⟩

/-- Every normalized family member is the corresponding power of its generator,
expressed in the category of the actual module sheaves. -/
lemma normalizedFamily_powers (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (n : ℕ) :
    TotalLift.lift (thetaLine E m) _ (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι n) =
      ((TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1))
        (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι 1)) ^ n).hom := by
  let a := normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι
  let A := fun n => TotalLift.lift (thetaLine E m) _ (a n)
  let I := TotalLift.aut (thetaLine E m) (SchemeThetaInversion.inversionIso E) ι
  let T := TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1)) (a 1)
  have href (k : ℕ) : TotalLift.lift (thetaLine E m) _
      (reflectionLift E m (multiple E P k) ι (a k)) = A k ≫ I.hom :=
    TotalLift.lift_comp _ _ _ _ _
  apply TotalLift.powers_of_reflections T I A ?_ rfl ?_ ?_ ?_ n
  · dsimp only [A, a]
    rw [normalizedFamily_zero, changeMap, TotalLift.lift_change, identityLift, TotalLift.lift_id]
  · obtain ⟨hi, hιsquare⟩ := hι.2
    exact TotalLift.lift_square _ _ _ hi hιsquare
  · obtain ⟨hr, hα⟩ := (normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι 1).2
    rw [← href]
    exact TotalLift.lift_square _ _ _ hr hα
  · intro j
    have h := normalized_reflection_step E m P j (a 1) _ _
      (normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι j).1
      (normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι (j+2)).1
    rw [href, href] at h
    exact h

/-- The all-a+b composition law is an equality of actual sheaf isomorphisms. -/
lemma normalizedFamily_add (m : ℕ) (hm : 0 < m) (he : Even m) (P : point E)
    (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (a b : ℕ) :
    compose E m _ _ (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι a)
      (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι b) =
      changeMap E m (translation_multiple_add E P a b)
        (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι (a+b)) := by
  apply TotalLift.lift_injective (thetaLine E m) _
  unfold compose changeMap
  rw [TotalLift.lift_comp, TotalLift.lift_change,
    normalizedFamily_powers, normalizedFamily_powers, normalizedFamily_powers]
  rw [Nat.add_comm a b, pow_add]
  rfl

/-- Reduction of the period law to the actual inversion action at the two-torsion
midpoint. This lemma does not assert that the remaining inversion equation holds. -/
lemma normalizedFamily_period_of_fixedInversion (m : ℕ) (hm : 0 < m) (he : Even m)
    (P : point E) (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι)
    (hfix : ∃ h : negative E (multiple E P m) ≫ inverse E = negative E (multiple E P m),
      (Scheme.Modules.pullback (negative E (multiple E P m))).mapIso ι =
        fixedComparison E m _ _ h) (a : ℕ) :
    normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι (a+m) =
      changeMap E m (translation_multiple_period E m P hP a)
        (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι a) := by
  have ht : translation E (multiple E P m) = 𝟙 E.curve := by
    simpa only [Nat.zero_add] using
      (translation_multiple_period E m P hP 0).trans (translation_multiple_zero E P)
  have hmid : MidpointNormalized E m (multiple E P m) ι
      (changeMap E m ht (identityLift E m)) := by
    unfold MidpointNormalized reflectionLift reflection changeMap identityLift
    exact identity_reflection_normalized _ _ _ ht _ ι hfix
  have ham : normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι m =
      changeMap E m ht (identityLift E m) := by
    exact (pointwise_exists_unique (k := k) (σ := σ) E m hm he P hP ι hι m).unique
      (normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι m)
      ⟨hmid, symmetric_of_midpoint E m (multiple E P m) ι _ hmid⟩
  let T := TotalLift.aut (thetaLine E m) (translationIso E (multiple E P 1))
    (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι 1)
  have hpow : T ^ m = 1 := by
    apply Aut.ext
    change (T ^ m).hom = 𝟙 _
    rw [← normalizedFamily_powers (k := k) (σ := σ) E m hm he P hP ι hι m, ham]
    unfold changeMap identityLift
    rw [TotalLift.lift_change, TotalLift.lift_id]
  apply TotalLift.lift_injective (thetaLine E m) _
  unfold changeMap
  rw [TotalLift.lift_change, normalizedFamily_powers, normalizedFamily_powers]
  change (T ^ (a+m)).hom = (T ^ a).hom
  rw [pow_add, hpow, mul_one]

open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily in
/-- Even-degree normalized inversion is the identity on every fixed section. -/
lemma even_inversion_fixed (m : ℕ) (hm : 0 < m) (he : Even m)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι)
    (e : S ⟶ E.curve) (hefix : e ≫ inverse E = e) :
    (Scheme.Modules.pullback e).mapIso ι = fixedComparison E m e (inverse E) hefix := by
  obtain ⟨k, rfl⟩ := he
  have hk : 0 < k := by omega
  obtain ⟨α, hα, _⟩ := SchemeThetaInversion.normalized_exists_unique E k
  obtain ⟨hf, hαsquare⟩ := hα.2
  have hs : (Scheme.Modules.pullback (inverse E)).mapIso α ≪≫ α =
      FixedPointPullback.squareComparison (inverse E) hf (thetaLine E k) := by
    simpa only [FixedPointPullback.squareComparison, FixedPointPullback.compare,
      NatIso.trans_app, squareComparison, Iso.trans_assoc] using hαsquare
  let η := thetaLineDoubleIso E k hk
  let β := Scheme.Modules.pullbackTensorObjIso (inverse E) (thetaLine E k) (thetaLine E k) ≪≫
    MonoidalCategory.tensorIso α α
  let γ : Lift E (k+k) (inverse E) := (Scheme.Modules.pullback (inverse E)).mapIso η ≪≫
    β ≪≫ η.symm
  have hn (o : S ⟶ E.curve) (ho : o ≫ inverse E = o) :
      (Scheme.Modules.pullback o).mapIso γ = fixedComparison E (k+k) o (inverse E) ho := by
    exact EvenInversion.transport_fixed o (inverse E) ho η β
      (EvenInversion.tensor_lift_fixed o (inverse E) ho hf (thetaLine E k)
        (SchemeThetaInversion.line_invertible E k) α hs)
  have hγι : γ = ι := (SchemeThetaInversion.unique_fixed_lift E (k+k)).unique
    (hn (E.zero) (SchemeThetaInversion.inverse_zero E)) hι.1.choose_spec
  rw [← hγι]
  exact hn e hefix

/-- The full period law, with no additional hypothesis on inversion. -/
lemma normalizedFamily_period (m : ℕ) (hm : 0 < m) (he : Even m)
    (P : point E) (hP : multiple E P (2*m) = E.law.one (𝟙 S))
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι) (a : ℕ) :
    normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι (a+m) =
      changeMap E m (translation_multiple_period E m P hP a)
        (normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι a) := by
  apply normalizedFamily_period_of_fixedInversion (k := k) (σ := σ) E m hm he P hP ι hι
  have ht : translation E (multiple E P m) = 𝟙 E.curve := by
    simpa only [Nat.zero_add] using
      (translation_multiple_period E m P hP 0).trans (translation_multiple_zero E P)
  have hf : negative E (multiple E P m) ≫ inverse E = negative E (multiple E P m) := by
    simpa only [reflection, ht, Category.id_comp] using
      SchemeDoubledTorsionLift.reflection_fixed E (multiple E P m)
  exact ⟨hf, even_inversion_fixed E m hm he ι hι _ hf⟩

lemma cyclicSystem_unique (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (A B : ∀ n : ℕ, Lift E m (translation E (multiple E P n)))
    (hA : CyclicSystem E m P ι A) (hB : CyclicSystem E m P ι B) : A = B := by
  funext n
  exact (SchemeMidpointThetaLift.midpoint_exists_unique E m (multiple E P n)
    ι ⟨A n⟩).unique (hA.1 n) (hB.1 n)


end SchemeCyclicThetaSplitting

open SchemeCyclicThetaSplitting in
/-- Unique coherent midpoint-normalized cyclic lifts on every characteristic-zero base. -/
theorem scheme_cyclic_theta_splitting :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (m : ℕ), 0 < m → Even m → ∀ (P : ArithmeticThetaSchemeThetaMarkingR0259.point E), ArithmeticThetaSchemeThetaMarkingR0259.multiple E P (2*m) = E.law.one (CategoryTheory.CategoryStruct.id S) → ∀ (ι : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.inverse E)), ArithmeticThetaSchemeThetaMarkingR0259.NormalizedInversion E m ι → ∃! A : (∀ n : ℕ, ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E (ArithmeticThetaSchemeThetaMarkingR0259.multiple E P n))), ArithmeticThetaSchemeThetaMarkingR0259.CyclicSystem E m P ι A := by
  intro k _ _ S σ E m hm he P hP ι hι
  let A := normalizedFamily (k := k) (σ := σ) E m hm he P hP ι hι
  have hA : CyclicSystem E m P ι A := by
    refine ⟨normalizedFamily_spec (k := k) (σ := σ) E m hm he P hP ι hι,
      ⟨translation_multiple_zero E P, normalizedFamily_zero (k := k) (σ := σ) E m hm he P hP ι hι⟩, ?_, ?_⟩
    · intro a b
      exact ⟨translation_multiple_add E P a b, normalizedFamily_add (k := k) (σ := σ) E m hm he P hP ι hι a b⟩
    · intro a
      exact ⟨translation_multiple_period E m P hP a, normalizedFamily_period (k := k) (σ := σ) E m hm he P hP ι hι a⟩
  exact ⟨A, hA, fun B hB => cyclicSystem_unique E m P ι B A hB hA⟩

#print axioms scheme_cyclic_theta_splitting
end ArithmeticThetaSchemeThetaMarkingR0259
