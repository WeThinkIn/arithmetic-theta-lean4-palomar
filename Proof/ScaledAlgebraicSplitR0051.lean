module

public import ScaledNormalRecoveryDefinitionsR0051

@[expose] public section

/-! The algebraic split map, including both branches and every base coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaScaledNormalRecoveryR0051
open ArithmeticThetaScaledTateBridgeR0046
open MvPolynomial
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

@[simp] private lemma scaled_C (a : Base k) :
    quotientMap k r (C a) = algebraMap (Base k) (Node k r) a := rfl

private lemma scaled_xy : x k r * y k r = t k r := by
  have h : quotientMap k r (relation k r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  change quotientMap k r (relation k r) = 0 at h
  simpa only [relation, map_sub, map_mul, scaled_C, x, y, t, sub_eq_zero] using h

private def embeddingPoly : PolynomialChart k →+* ArithmeticThetaNodeCharts.Node k :=
  MvPolynomial.eval₂Hom (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k))
    (fun i => if i = (0 : Fin 2) then ArithmeticThetaNodeCharts.x k ^ r else ArithmeticThetaNodeCharts.y k ^ r)

private lemma embedding_relation : embeddingPoly k r (relation k r) = 0 := by
  simp only [embeddingPoly, relation, map_sub, map_mul, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C, Fin.isValue, if_true,
    show (1 : Fin 2) ≠ 0 by decide, if_false]
  rw [← mul_pow, ArithmeticThetaNodeCharts.node_xy]
  simp [ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter, parameter]

private def embedding : Node k r →ₐ[Base k] ArithmeticThetaNodeCharts.Node k :=
  { Ideal.Quotient.lift (relationIdeal k r) (embeddingPoly k r) (by
      change relationIdeal k r ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro q hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      exact embedding_relation k r) with
    commutes' := by
      intro a
      change embeddingPoly k r (C a) = _
      simp [embeddingPoly] }

@[simp] private lemma embedding_x : embedding k r (x k r) = ArithmeticThetaNodeCharts.x k ^ r := by
  simp [embedding, embeddingPoly, x, quotientMap]
@[simp] private lemma embedding_y : embedding k r (y k r) = ArithmeticThetaNodeCharts.y k ^ r := by
  simp [embedding, embeddingPoly, y, quotientMap]

private def unitBasis : Module.Basis ℤ (Base k) (ArithmeticThetaNodeCharts.Node k) :=
  (ArithmeticThetaNodeCharts.node_free_basis k).choose
private lemma unitBasis_eq (i : ℤ) : unitBasis k i = ArithmeticThetaNodeCharts.normalMonomial k i :=
  (ArithmeticThetaNodeCharts.node_free_basis k).choose_spec i

private def projectedMonomial (i : ℤ) : Node k r :=
  if 0 ≤ i then
    if r ∣ i.toNat then x k r ^ (i.toNat / r) else 0
  else if r ∣ (-i).toNat then y k r ^ ((-i).toNat / r) else 0

private def projection : ArithmeticThetaNodeCharts.Node k →ₗ[Base k] Node k r :=
  (unitBasis k).constr (Base k) (projectedMonomial k r)

private lemma projection_normal (i : ℤ) :
    projection k r (ArithmeticThetaNodeCharts.normalMonomial k i) = projectedMonomial k r i := by
  rw [← unitBasis_eq]
  exact (unitBasis k).constr_basis (Base k) (projectedMonomial k r) i

private lemma projection_xpow (n : ℕ) :
    projection k r (ArithmeticThetaNodeCharts.x k ^ n) = if r ∣ n then x k r ^ (n / r) else 0 := by
  rw [← ArithmeticThetaNodeCharts.normalMonomial_nat, projection_normal]
  simp [projectedMonomial]

private lemma projection_ypow (n : ℕ) :
    projection k r (ArithmeticThetaNodeCharts.y k ^ n) = if r ∣ n then y k r ^ (n / r) else 0 := by
  cases n with
  | zero => simpa using projection_xpow k r 0
  | succ n =>
    rw [← ArithmeticThetaNodeCharts.normalMonomial_neg, projection_normal]
    simp only [projectedMonomial, if_neg (show ¬ (0 : ℤ) ≤ -((n+1 : ℕ) : ℤ) by omega), neg_neg, Int.toNat_natCast]

private lemma projection_coeff (a : Base k) (b : ArithmeticThetaNodeCharts.Node k) :
    projection k r (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a * b) =
      algebraMap (Base k) (Node k r) a * projection k r b := by
  simpa only [Algebra.smul_def] using (projection k r).map_smul a b


/-- The two elementary branch computations, stated once to allow swapping branches. -/
private lemma branch_projection {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    (P : A →ₗ[R] B) (u v : A) (x y : B) (c : R) (r : ℕ) (hr : 0 < r)
    (huv : u * v = algebraMap R A c)
    (hxy : x * y = algebraMap R B (c ^ r))
    (hu : ∀ n : ℕ, P (u ^ n) = if r ∣ n then x ^ (n / r) else 0)
    (hv : ∀ n : ℕ, P (v ^ n) = if r ∣ n then y ^ (n / r) else 0) :
    (∀ n : ℕ, P (u ^ r * u ^ n) = x * P (u ^ n)) ∧
    (∀ n : ℕ, P (u ^ r * v ^ n) = x * P (v ^ n)) := by
  have hc (a : R) (b : A) :
      P (algebraMap R A a * b) = algebraMap R B a * P b := by
    simpa only [Algebra.smul_def] using P.map_smul a b
  constructor
  · intro n
    rw [← pow_add, hu, hu]
    have hd : r ∣ r + n ↔ r ∣ n := Nat.dvd_add_right (dvd_refl r)
    simp only [hd]
    split_ifs with h
    · rw [Nat.add_div_left _ hr, pow_succ]
      ring
    · simp
  · intro n
    by_cases hnr : r ≤ n
    · have he : u ^ r * v ^ n = algebraMap R A (c ^ r) * v ^ (n-r) := by
        conv_lhs => rw [show n = r + (n-r) from (Nat.add_sub_of_le hnr).symm]
        rw [pow_add, ← mul_assoc, ← mul_pow, huv, map_pow]
      rw [he, hc, hv, hv]
      have hd : r ∣ n - r ↔ r ∣ n := by
        have hn : n = r + (n-r) := (Nat.add_sub_of_le hnr).symm
        conv_rhs => rw [hn]
        exact (Nat.dvd_add_right (dvd_refl r)).symm
      simp only [hd]
      split_ifs with h
      · have hn : n / r = (n-r) / r + 1 := by
          conv_lhs => rw [show n = r + (n-r) from (Nat.add_sub_of_le hnr).symm]
          rw [Nat.add_div_left _ hr]
        rw [hn, pow_succ, ← hxy]
        ring
      · simp
    · have hn : n < r := Nat.lt_of_not_ge hnr
      by_cases hn0 : n = 0
      · subst n
        have h1 : P 1 = 1 := by simpa using hu 0
        simp only [pow_zero, mul_one, hu, if_pos (dvd_refl r),
          Nat.div_self hr, pow_one, h1]
      · have he : u ^ r * v ^ n = algebraMap R A (c ^ n) * u ^ (r-n) := by
          conv_lhs => rw [show r = (r-n) + n from (Nat.sub_add_cancel hn.le).symm]
          rw [pow_add, mul_assoc, ← mul_pow, huv, map_pow]
          ring
        have hd : ¬ r ∣ n := fun h => hn.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h)
        have hd' : ¬ r ∣ r-n := by
          intro h
          have := Nat.le_of_dvd (Nat.sub_pos_of_lt hn) h
          omega
        rw [he, hc, hu, hv, if_neg hd', if_neg hd]
        simp


private lemma projection_generators (hr : 0 < r) (b : ArithmeticThetaNodeCharts.Node k) :
    projection k r (ArithmeticThetaNodeCharts.x k ^ r * b) = x k r * projection k r b ∧
    projection k r (ArithmeticThetaNodeCharts.y k ^ r * b) = y k r * projection k r b := by
  have hx := branch_projection (projection k r)
    (ArithmeticThetaNodeCharts.x k) (ArithmeticThetaNodeCharts.y k) (x k r) (y k r)
    (PowerSeries.X : Base k) r hr (ArithmeticThetaNodeCharts.node_xy k) (scaled_xy k r)
    (projection_xpow k r) (projection_ypow k r)
  have hy := branch_projection (projection k r)
    (ArithmeticThetaNodeCharts.y k) (ArithmeticThetaNodeCharts.x k) (y k r) (x k r)
    (PowerSeries.X : Base k) r hr
    (by simpa only [mul_comm, ArithmeticThetaNodeCharts.t, ArithmeticThetaNodeCharts.parameter] using ArithmeticThetaNodeCharts.node_xy k)
    (by simpa only [mul_comm, t, parameter] using scaled_xy k r)
    (projection_ypow k r) (projection_xpow k r)
  have hb : b ∈ Submodule.span (Base k) (Set.range (ArithmeticThetaNodeCharts.normalMonomial k)) := by
    rw [ArithmeticThetaNodeCharts.normal_span]
    trivial
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    cases i with
    | ofNat n =>
      simpa [ArithmeticThetaNodeCharts.normalMonomial] using And.intro (hx.1 n) (hy.2 n)
    | negSucc n =>
      have hn : ArithmeticThetaNodeCharts.normalMonomial k (Int.negSucc n) =
          ArithmeticThetaNodeCharts.y k ^ (n+1) := by
        simp [ArithmeticThetaNodeCharts.normalMonomial]
      rw [hn]
      exact ⟨hx.2 (n+1), hy.1 (n+1)⟩
  | zero => simp
  | add a b ha hb ia ib =>
    simpa only [mul_add, map_add, ia.1, ia.2, ib.1, ib.2] using
      And.intro (rfl : x k r * projection k r a + x k r * projection k r b = _)
        (rfl : y k r * projection k r a + y k r * projection k r b = _)
  | smul a b hb ih =>
    simpa only [mul_smul_comm, map_smul, ih.1, ih.2] using ih

private lemma projection_module (hr : 0 < r) (a : Node k r)
    (b : ArithmeticThetaNodeCharts.Node k) :
    projection k r (embedding k r a * b) = a * projection k r b := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change projection k r (embedding k r (quotientMap k r q) * b) =
    quotientMap k r q * projection k r b
  induction q using MvPolynomial.induction_on generalizing b with
  | C a =>
    rw [scaled_C, AlgHom.commutes]
    exact projection_coeff k r a b
  | add q q' ih ih' =>
    simp only [map_add, add_mul, ih, ih']
  | mul_X q i ih =>
    simp only [map_mul]
    rw [mul_assoc, ih]
    fin_cases i
    · change quotientMap k r q * projection k r (embedding k r (x k r) * b) = _
      rw [embedding_x, (projection_generators k r hr b).1]
      exact (mul_assoc _ _ _).symm
    · change quotientMap k r q * projection k r (embedding k r (y k r) * b) = _
      rw [embedding_y, (projection_generators k r hr b).2]
      exact (mul_assoc _ _ _).symm

private lemma projection_one : projection k r 1 = 1 := by
  simpa using projection_xpow k r 0

private lemma projection_retract (hr : 0 < r) (a : Node k r) :
    projection k r (embedding k r a) = a := by
  simpa only [mul_one, projection_one] using projection_module k r hr a 1


private lemma embedding_parameter : embedding k r (t k r) = ArithmeticThetaNodeCharts.t k ^ r := by
  simp only [t, AlgHom.commutes, parameter, map_pow, ArithmeticThetaNodeCharts.t,
    ArithmeticThetaNodeCharts.parameter]

private lemma embedding_filtered : ForwardFiltered k r (embedding k r).toRingHom := by
  intro n a ha
  rw [nodeIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [ArithmeticThetaNodeCharts.nodeIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨embedding k r b, ?_⟩
  change embedding k r (t k r ^ n * b) = _
  rw [map_mul, map_pow, embedding_parameter, pow_mul]

private lemma projection_filtered (hr : 0 < r) :
    BackwardFiltered k r (projection k r).toAddMonoidHom := by
  intro n b hb
  rw [ArithmeticThetaNodeCharts.nodeIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  rw [nodeIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨projection k r c, ?_⟩
  change projection k r (ArithmeticThetaNodeCharts.t k ^ (r*n) * c) = _
  rw [pow_mul, ← embedding_parameter, ← map_pow, projection_module k r hr]

/-- The concrete algebraic splitting, with both adic bounds and all coefficient formulas. -/
theorem algebraic_split_exists :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      ∃ (f : (ArithmeticThetaScaledTateBridgeR0046.Node k r →+* ArithmeticThetaNodeCharts.Node k))
        (p : (ArithmeticThetaNodeCharts.Node k →+ ArithmeticThetaScaledTateBridgeR0046.Node k r)),
        ArithmeticThetaScaledNormalRecoveryR0051.AlgebraicSplit k r f p := by
  intro k _ _ r hr
  refine ⟨(embedding k r).toRingHom, (projection k r).toAddMonoidHom, ?_⟩
  refine ⟨(embedding k r).commutes, embedding_x k r, embedding_y k r,
    projection_retract k r hr, projection_module k r hr, embedding_filtered k r,
    projection_filtered k r hr, ?_, ?_⟩
  · intro a n
    change projection k r (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a *
      ArithmeticThetaNodeCharts.x k ^ n) = _
    rw [projection_coeff, projection_xpow]
    split_ifs <;> simp
  · intro a n
    change projection k r (algebraMap (Base k) (ArithmeticThetaNodeCharts.Node k) a *
      ArithmeticThetaNodeCharts.y k ^ n) = _
    rw [projection_coeff, projection_ypow]
    split_ifs <;> simp

end ArithmeticThetaScaledNormalRecoveryR0051
