module

public import GlobalizationDefinitions
public import Mathlib

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ArithmeticThetaGlobalization
abbrev Prim (R : Type*) [CommRing R] := {v : R × R // IsCoprime v.1 v.2}

def primEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) : Prim R ≃ Prim S where
  toFun v := ⟨(e v.val.1, e v.val.2), v.property.map e.toRingHom⟩
  invFun v := ⟨(e.symm v.val.1, e.symm v.val.2), v.property.map e.symm.toRingHom⟩
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

def primProd (R S : Type*) [CommRing R] [CommRing S] : Prim (R × S) ≃ Prim R × Prim S where
  toFun v := (⟨(v.val.1.1, v.val.2.1), v.property.map (RingHom.fst R S)⟩,
              ⟨(v.val.1.2, v.val.2.2), v.property.map (RingHom.snd R S)⟩)
  invFun v := ⟨((v.1.val.1,v.2.val.1),(v.1.val.2,v.2.val.2)), by
    obtain ⟨a,b,h⟩ := v.1.property
    obtain ⟨c,d,k⟩ := v.2.property
    exact ⟨(a,c),(b,d), Prod.ext h k⟩⟩
  left_inv v := rfl
  right_inv v := rfl

lemma primCard_mul (m n : ℕ) (h : m.Coprime n) :
    Nat.card (Prim (ZMod (m*n))) = Nat.card (Prim (ZMod m)) * Nat.card (Prim (ZMod n)) := by
  rw [Nat.card_congr ((primEquiv (ZMod.chineseRemainder h)).trans (primProd _ _)), Nat.card_prod]

-- The determinant completion of a unimodular row has one free scalar.
def completionsEquiv {R : Type*} [CommRing R] (a b u v : R) (h : u*a+v*b=1) :
    {w : R × R // a*w.2-b*w.1=1} ≃ R where
  toFun w := u*w.val.1+v*w.val.2
  invFun t := ⟨(-v+t*a,u+t*b), by dsimp; linear_combination h⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      linear_combination w.val.1*h + v*w.property
    · dsimp
      linear_combination w.val.2*h - u*w.property
  right_inv t := by dsimp; linear_combination t*h

lemma coprime_prime_pow (p k : ℕ) (hp : p.Prime) (a b : ZMod (p^(k+1))) :
    IsCoprime a b ↔ IsUnit a ∨ IsUnit b := by
  letI : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have ha : p ∣ a.val := by
      have hh := hn.1
      rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime] at hh
      simpa [Nat.coprime_pow_right_iff, Nat.coprime_comm, hp.coprime_iff_not_dvd] using hh
    have hb : p ∣ b.val := by
      have hh := hn.2
      rw [← ZMod.natCast_zmod_val b, ZMod.isUnit_iff_coprime] at hh
      simpa [Nat.coprime_pow_right_iff, Nat.coprime_comm, hp.coprime_iff_not_dvd] using hh
    letI : Fact p.Prime := ⟨hp⟩
    have hc := h.map (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p))
    have hca : (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p)) a = 0 := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a, map_natCast]
      simpa only [ZMod.natCast_eq_zero_iff] using ha
    have hcb : (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p)) b = 0 := by
      conv_lhs => rw [← ZMod.natCast_zmod_val b, map_natCast]
      simpa only [ZMod.natCast_eq_zero_iff] using hb
    simpa [hca,hcb] using hc
  · rintro (ha|hb)
    · obtain ⟨u,hu⟩ := isUnit_iff_exists_inv'.mp ha
      exact ⟨u,0,by simpa using hu⟩
    · obtain ⟨u,hu⟩ := isUnit_iff_exists_inv'.mp hb
      exact ⟨0,u,by simpa using hu⟩

def unitsSubtype (R : Type*) [CommRing R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := by apply Units.ext; simp
  right_inv x := by ext; simp

lemma primCard_local (R : Type*) [CommRing R] [Fintype R]
    (h : ∀ a b : R, IsCoprime a b ↔ IsUnit a ∨ IsUnit b) :
    Nat.card (Prim R) = Nat.card R ^ 2 - (Nat.card R - Nat.card Rˣ)^2 := by
  classical
  let P : R × R → Prop := fun x => IsCoprime x.1 x.2
  have e : {x : R × R // ¬ P x} ≃ {x : R // ¬ IsUnit x} × {x : R // ¬ IsUnit x} :=
    (Equiv.subtypeEquivRight (fun x => by simp [P,h])).trans Equiv.subtypeProdEquivProd
  have hc := Fintype.card_subtype_compl P
  have hu : Fintype.card {x : R // IsUnit x} = Fintype.card Rˣ :=
    (Fintype.card_congr (unitsSubtype R)).symm
  have hn : Fintype.card {x : R × R // ¬ P x} = (Fintype.card R - Fintype.card Rˣ)^2 := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype_compl, hu, pow_two]
  have hle : Fintype.card (Prim R) ≤ Fintype.card R ^ 2 := by
    simpa [Fintype.card_prod,pow_two] using Fintype.card_subtype_le P
  simp only [Fintype.card_prod] at hc
  simp only [Nat.card_eq_fintype_card]
  change Fintype.card (Prim R) = _
  change Fintype.card (Prim R) ≤ _ at hle
  change Fintype.card {x // ¬ P x} = _ - Fintype.card (Prim R) at hc
  simp only [pow_two] at *
  omega

lemma primCard_prime_pow (p k : ℕ) (hp : p.Prime) :
    (Nat.card (Prim (ZMod (p^(k+1)))) : ℚ) =
      (p^(k+1) : ℚ)^2 * (1-(p:ℚ)⁻¹^2) := by
  letI : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [primCard_local _ (coprime_prime_pow p k hp)]
  simp only [Nat.card_eq_fintype_card, ZMod.card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hle : p^k*(p-1) ≤ p^(k+1) := by
    rw [pow_succ]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hs : (p^(k+1)-p^k*(p-1))^2 ≤ (p^(k+1))^2 :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  rw [Nat.cast_sub hs]
  push_cast [Nat.cast_sub hle, Nat.cast_sub hp1]
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [pow_succ]
  field_simp
  <;> ring

lemma primCard_formula (L : ℕ) (hL : L ≠ 0) :
    (Nat.card (Prim (ZMod L)) : ℚ) =
      (L:ℚ)^2 * ∏ p ∈ L.primeFactors, (1-(p:ℚ)⁻¹^2) := by
  induction L using Nat.recOnPrimeCoprime with
  | zero => contradiction
  | prime_pow p k hp =>
    cases k with
    | zero =>
      have hprim : Subsingleton (Prim (ZMod 1)) := inferInstance
      have hne : Nonempty (Prim (ZMod 1)) := ⟨⟨(1,0),⟨1,0,by simp⟩⟩⟩
      haveI := hprim
      haveI := hne
      simp only [pow_zero, Nat.cast_one, one_pow, Nat.primeFactors_one, Finset.prod_empty, mul_one]
      exact_mod_cast (Nat.card_eq_one_iff_unique.mpr ⟨hprim,hne⟩ : Nat.card (Prim (ZMod 1)) = 1)
    | succ k =>
      simpa [Nat.primeFactors_pow_succ, hp.primeFactors] using primCard_prime_pow p k hp
  | coprime a b ha hb hab ihA ihB =>
    rw [primCard_mul a b hab, Nat.cast_mul, ihA (by omega), ihB (by omega),
      hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors, Nat.cast_mul]
    ring

def slRows (R : Type*) [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R ≃
    Σ a : Prim R, {w : R × R // a.val.1*w.2-a.val.2*w.1=1} where
  toFun A := ⟨⟨(A.1 0 0,A.1 0 1), A.1 1 1, -A.1 1 0, by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    dsimp
    linear_combination h⟩, ⟨(A.1 1 0,A.1 1 1), by simpa only [Matrix.det_fin_two] using A.2⟩⟩
  invFun w := ⟨!![w.1.val.1,w.1.val.2;w.2.val.1,w.2.val.2], by
    simpa [Matrix.det_fin_two] using w.2.property⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv w := by cases w; rfl

def slPrimScalar (R : Type*) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 2) R ≃ Prim R × R :=
  (slRows R).trans ((Equiv.sigmaCongrRight fun a =>
    completionsEquiv a.val.1 a.val.2 (Classical.choose a.property)
      (Classical.choose (Classical.choose_spec a.property))
      (Classical.choose_spec (Classical.choose_spec a.property))).trans
    (Equiv.sigmaEquivProd (Prim R) R))

lemma slCard (L : ℕ) : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) =
    Nat.card (Prim (ZMod L)) * Nat.card (ZMod L) := by
  rw [Nat.card_congr (slPrimScalar (ZMod L)),Nat.card_prod]

lemma involQuot_eq {A : Type*} (f : A → A) (hf : Function.Involutive f) (x y : A) :
    Quot.mk (fun a b => b = f a) x = Quot.mk (fun a b => b = f a) y ↔
      y = x ∨ y = f x := by
  constructor
  · intro h
    have he := Quot.eqvGen_exact h
    clear h
    induction he with
    | rel a b h => exact Or.inr h
    | refl a => exact Or.inl rfl
    | symm a b h ih =>
      rcases ih with h|h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h,hf])
    | trans a b c h k ih ik =>
      rcases ih with rfl|rfl <;> rcases ik with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (hf _)
  · rintro (rfl|h)
    · rfl
    · exact Quot.sound h

lemma involQuot_card {A : Type*} [Finite A] (f : A → A)
    (hf : Function.Involutive f) (hfree : ∀ x, f x ≠ x) :
    Nat.card A = 2 * Nat.card (Quot (fun a b => b = f a)) := by
  classical
  let Q := Quot (fun a b => b = f a)
  let q : A → Q := Quot.mk _
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite Q
  have hc (z : Q) : Fintype.card {x : A // q x = z} = 2 := by
    induction z using Quot.ind with
    | mk a =>
      have e : {x : A // q x = q a} ≃ {x : A // x = a ∨ x = f a} :=
        Equiv.subtypeEquivRight (fun x => by
          rw [eq_comm, involQuot_eq f hf])
      rw [Fintype.card_congr e]
      exact Fintype.card_subtype_eq_or_eq_of_ne (hfree a).symm
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv q)
  simp only [Fintype.card_sigma, hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  simpa only [Nat.card_eq_fintype_card, mul_comm] using h.symm

def primNeg (L : ℕ) (a : Prim (ZMod L)) : Prim (ZMod L) :=
  ⟨-a.val,a.property.neg_neg⟩

lemma primNeg_invol (L : ℕ) : Function.Involutive (primNeg L) := by
  intro a
  apply Subtype.ext
  exact neg_neg a.val

lemma primNeg_free (L : ℕ) (hL : 3 ≤ L) (a : Prim (ZMod L)) : primNeg L a ≠ a := by
  intro h
  have h1 : -a.val.1 = a.val.1 := congrArg (fun x : Prim (ZMod L) => x.val.1) h
  have h2 : -a.val.2 = a.val.2 := congrArg (fun x : Prim (ZMod L) => x.val.2) h
  obtain ⟨u,v,huv⟩ := a.property
  have hz : (2 : ZMod L) = 0 := by
    linear_combination -2*huv - u*h1 - v*h2
  have hd : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp hz
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma signedCard (L : ℕ) (hL : 3 ≤ L) :
    Nat.card (Prim (ZMod L)) = 2 * Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair L) := by
  letI : NeZero L := ⟨by omega⟩
  have e : Quot (fun a b : Prim (ZMod L) => b = primNeg L a) ≃
      ArithmeticThetaLevelCount.SignedPrimitivePair L :=
    Quot.congr (Equiv.refl _) (fun a b => by
      change (b = primNeg L a) ↔ b.val = -a.val
      exact Subtype.ext_iff)
  rw [← Nat.card_congr e]
  exact involQuot_card (primNeg L) (primNeg_invol L) (primNeg_free L hL)

/-- Full determinant-one markings and primitive sign orbits at every level at least three. -/
theorem finite_full_level_count : ∀ L : ℕ, 3 ≤ L →
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℚ) =
      ArithmeticThetaLevelCount.levelIndex L ∧
    (2 * L : ℚ) * (Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair L) : ℚ) =
      ArithmeticThetaLevelCount.levelIndex L := by
  intro L hL
  letI : NeZero L := ⟨by omega⟩
  have hp := primCard_formula L (by omega)
  have hs := signedCard L hL
  have hz : Nat.card (ZMod L) = L := by simp [Nat.card_eq_fintype_card]
  constructor
  · rw [slCard, Nat.cast_mul, hz, hp]
    unfold ArithmeticThetaLevelCount.levelIndex
    ring
  · have hsq : (Nat.card (Prim (ZMod L)) : ℚ) =
        2 * (Nat.card (ArithmeticThetaLevelCount.SignedPrimitivePair L) : ℚ) := by exact_mod_cast hs
    rw [mul_comm 2 (L:ℚ), mul_assoc, ← hsq, hp]
    unfold ArithmeticThetaLevelCount.levelIndex
    ring

end ArithmeticThetaGlobalization

