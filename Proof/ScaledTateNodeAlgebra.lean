module

public import ScaledTateNodeBridgeDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.privateInPublic true

/-! Normal forms and algebraic properties of the scaled node. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaScaledTateBridgeR0046
open MvPolynomial
variable (k : Type u) [Field k] (r : ℕ)

private def normalMonomial (i : ℤ) : Node k r :=
  if 0 ≤ i then x k r ^ i.toNat else y k r ^ (-i).toNat

private lemma parameter_ne_zero : parameter k r ≠ 0 := by
  exact pow_ne_zero _ PowerSeries.X_ne_zero

@[simp] private lemma quotient_C (a : Base k) :
    quotientMap k r (C a) = algebraMap (Base k) (Node k r) a := by
  rfl

private lemma node_xy : x k r * y k r = t k r := by
  have h : quotientMap k r (relation k r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation, map_sub, map_mul, quotient_C, x, y, t, sub_eq_zero] using h

private lemma torus_relation : torusMap k r (relation k r) = 0 := by
  simp [torusMap, relation]

private def nodeToTorus : Node k r →ₐ[Base k] Torus k :=
  { Ideal.Quotient.lift (relationIdeal k r) (torusMap k r) (by
      intro p hp
      exact (show relationIdeal k r ≤ RingHom.ker (torusMap k r) from Ideal.span_le.mpr (by
        intro q hq
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact torus_relation k r)) hp) with
    commutes' := by
      intro a
      change torusMap k r (C a) = LaurentPolynomial.C a
      simp [torusMap] }

@[simp] private lemma nodeToTorus_x : nodeToTorus k r (x k r) = LaurentPolynomial.T 1 := by
  simp [nodeToTorus, x, quotientMap, torusMap]
@[simp] private lemma nodeToTorus_y : nodeToTorus k r (y k r) =
    LaurentPolynomial.C (parameter k r) * LaurentPolynomial.T (-1) := by
  simp [nodeToTorus, y, quotientMap, torusMap]

@[simp] private lemma normalMonomial_nat (n : ℕ) :
    normalMonomial k r (n : ℤ) = x k r ^ n := by
  simp [normalMonomial]
private lemma normalMonomial_neg (n : ℕ) :
    normalMonomial k r (-(n : ℤ)) = y k r ^ n := by
  by_cases h : n = 0
  · simp [h, normalMonomial]
  · simp [normalMonomial, h]

private lemma image_normal (i : ℤ) : nodeToTorus k r (normalMonomial k r i) =
    LaurentPolynomial.C (parameter k r ^ (-i).toNat) * LaurentPolynomial.T i := by
  cases i with
  | ofNat n => simp [normalMonomial]
  | negSucc n =>
    simp only [normalMonomial, Int.negSucc_not_nonneg, if_false,
      map_pow, nodeToTorus_y, mul_pow, LaurentPolynomial.T_pow]
    simp [← map_pow, Int.negSucc_eq]

private lemma normal_span :
    Submodule.span (Base k) (Set.range (normalMonomial k r)) = ⊤ := by
  let S := Submodule.span (Base k) (Set.range (normalMonomial k r))
  have hx (n : ℕ) : x k r ^ n ∈ S := by
    exact Submodule.subset_span ⟨(n : ℤ), normalMonomial_nat k r n⟩
  have hy (n : ℕ) : y k r ^ n ∈ S := by
    exact Submodule.subset_span ⟨-(n : ℤ), normalMonomial_neg k r n⟩
  have hm (z : Node k r) (hz : z ∈ S) : z * x k r ∈ S ∧ z * y k r ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨i, rfl⟩
      cases i with
      | ofNat n =>
        change x k r ^ n * x k r ∈ S ∧ x k r ^ n * y k r ∈ S
        constructor
        · simpa [pow_succ] using hx (n+1)
        · cases n with
          | zero => simpa using hy 1
          | succ n =>
            have he : x k r ^ (n+1) * y k r = parameter k r • x k r ^ n := by
              rw [Algebra.smul_def, ← t, pow_succ, mul_assoc, node_xy]
              ring
            rw [he]
            exact S.smul_mem _ (hx n)
      | negSucc n =>
        have he : normalMonomial k r (Int.negSucc n) = y k r ^ (n+1) := by
          simp [normalMonomial]
        rw [he]
        constructor
        · have he : y k r ^ (n+1) * x k r = parameter k r • y k r ^ n := by
            rw [Algebra.smul_def, ← t, pow_succ]
            rw [mul_assoc, mul_comm (y k r), node_xy]
            ring
          rw [he]
          exact S.smul_mem _ (hy n)
        · simpa [pow_succ] using hy (n+2)
    | zero => simp
    | add a b ha hb ia ib =>
      simpa [add_mul] using And.intro (S.add_mem ia.1 ib.1) (S.add_mem ia.2 ib.2)
    | smul a z hz ih =>
      simpa [smul_mul_assoc] using And.intro (S.smul_mem a ih.1) (S.smul_mem a ih.2)
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change quotientMap k r p ∈ S
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hc : quotientMap k r (C a) = a • (1 : Node k r) := by
      simp [Algebra.smul_def]
    rw [hc]
    exact S.smul_mem _ (by simpa using hx 0)
  | add p q hp hq => simpa using S.add_mem hp hq
  | mul_X p i hp =>
    fin_cases i
    · simpa [map_mul, x] using (hm _ hp).1
    · simpa [map_mul, y] using (hm _ hp).2

private lemma image_normal_independent : LinearIndependent (Base k)
    (fun i : ℤ => nodeToTorus k r (normalMonomial k r i)) := by
  classical
  rw [linearIndependent_iff']
  intro s a ha j hj
  have hc := congrArg (fun p : Torus k => p.coeff j) ha
  simp only [image_normal, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, Finsupp.zero_apply] at hc
  simp only [mul_ite, mul_zero] at hc
  simp only [Finset.sum_ite_eq', if_pos hj] at hc
  exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (parameter_ne_zero k r))

private lemma nodeToTorus_injective : Function.Injective (nodeToTorus k r) := by
  have hd := Submodule.range_ker_disjoint (f := (nodeToTorus k r).toLinearMap)
    (image_normal_independent k r)
  rw [normal_span] at hd
  exact LinearMap.ker_eq_bot.mp (by simpa using hd)

private lemma node_free_basis :
    ∃ b : Module.Basis ℤ (Base k) (Node k r), ∀ i : ℤ, b i = normalMonomial k r i := by
  have hi : LinearIndependent (Base k) (normalMonomial k r) :=
    ((nodeToTorus k r).toLinearMap.linearIndependent_iff_of_injOn
      (nodeToTorus_injective k r).injOn).mp (image_normal_independent k r)
  exact ⟨Module.Basis.mk hi (by rw [normal_span]), Module.Basis.mk_apply _ _⟩

theorem node_algebra :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ), 0 < r →
      IsDomain (Node k r) ∧ IsNoetherianRing (Node k r) ∧
      Algebra.FiniteType (Base k) (Node k r) ∧ Module.Flat (Base k) (Node k r) ∧
      parameter k r ≠ 0 ∧ t k r ≠ 0 := by
  intro k _ _ r hr
  obtain ⟨b, hb⟩ := node_free_basis k r
  let : Module.Free (Base k) (Node k r) := Module.Free.of_basis b
  refine ⟨Function.Injective.isDomain (nodeToTorus k r) (nodeToTorus_injective k r),
    inferInstance, inferInstance, inferInstance, parameter_ne_zero k r, ?_⟩
  intro h
  have he := congrArg (fun z : Node k r => (nodeToTorus k r z).coeff 0) h
  simp [t, LaurentPolynomial.C_apply, parameter_ne_zero k r] at he

end ArithmeticThetaScaledTateBridgeR0046
