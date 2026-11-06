import TateNodeChartDefinitions

/-! Normal forms for the algebraic node over the actual power-series base. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaNodeCharts
open MvPolynomial
variable (k : Type u) [Field k]

@[simp] lemma quotient_C (r : Base k) : quotientMap k (C r) = algebraMap (Base k) (Node k) r := by
  rfl

lemma node_xy : x k * y k = t k := by
  have h : quotientMap k (relation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation, map_sub, map_mul, quotient_C, x, y, t, sub_eq_zero] using h

lemma torus_relation : torusMap k (relation k) = 0 := by
  simp [torusMap, relation, parameter]

noncomputable def nodeToTorus : Node k →ₐ[Base k] Torus k :=
  { Ideal.Quotient.lift (relationIdeal k) (torusMap k) (by
      intro p hp
      exact (show relationIdeal k ≤ RingHom.ker (torusMap k) from Ideal.span_le.mpr (by
        intro q hq
        rcases Set.mem_singleton_iff.mp hq with rfl
        exact torus_relation k)) hp) with
    commutes' := by
      intro r
      change torusMap k (C r) = LaurentPolynomial.C r
      simp [torusMap] }

@[simp] lemma nodeToTorus_x : nodeToTorus k (x k) = LaurentPolynomial.T 1 := by
  simp [nodeToTorus, x, quotientMap, torusMap]
@[simp] lemma nodeToTorus_y : nodeToTorus k (y k) =
    LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1) := by
  simp [nodeToTorus, y, quotientMap, torusMap]

@[simp] lemma normalMonomial_nat (n : ℕ) : normalMonomial k (n : ℤ) = x k ^ n := by
  simp [normalMonomial]
lemma normalMonomial_neg (n : ℕ) : normalMonomial k (-(n : ℤ)) = y k ^ n := by
  by_cases h : n = 0
  · simp [h, normalMonomial]
  · simp [normalMonomial, h]

lemma image_normal (i : ℤ) : nodeToTorus k (normalMonomial k i) =
    LaurentPolynomial.C (parameter k ^ (-i).toNat) * LaurentPolynomial.T i := by
  cases i with
  | ofNat n => simp [normalMonomial]
  | negSucc n =>
    simp only [normalMonomial, Int.negSucc_not_nonneg, if_false,
      map_pow, nodeToTorus_y, mul_pow, LaurentPolynomial.T_pow]
    simp [← map_pow, Int.negSucc_eq]


lemma normal_span : Submodule.span (Base k) (Set.range (normalMonomial k)) = ⊤ := by
  let S := Submodule.span (Base k) (Set.range (normalMonomial k))
  have hx (n : ℕ) : x k ^ n ∈ S := by
    exact Submodule.subset_span ⟨(n : ℤ), normalMonomial_nat k n⟩
  have hy (n : ℕ) : y k ^ n ∈ S := by
    exact Submodule.subset_span ⟨-(n : ℤ), normalMonomial_neg k n⟩
  have hm (z : Node k) (hz : z ∈ S) : z * x k ∈ S ∧ z * y k ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨i, rfl⟩
      cases i with
      | ofNat n =>
        change x k ^ n * x k ∈ S ∧ x k ^ n * y k ∈ S
        constructor
        · simpa [pow_succ] using hx (n+1)
        · cases n with
          | zero => simpa using hy 1
          | succ n =>
            have he : x k ^ (n+1) * y k = parameter k • x k ^ n := by
              rw [Algebra.smul_def, ← t, pow_succ, mul_assoc, node_xy]
              ring
            rw [he]
            exact S.smul_mem _ (hx n)
      | negSucc n =>
        have he : normalMonomial k (Int.negSucc n) = y k ^ (n+1) := by
          simp [normalMonomial]
        rw [he]
        constructor
        · have he : y k ^ (n+1) * x k = parameter k • y k ^ n := by
            rw [Algebra.smul_def, ← t, pow_succ]
            rw [mul_assoc, mul_comm (y k), node_xy]
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
  change quotientMap k p ∈ S
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hc : quotientMap k (C r) = r • (1 : Node k) := by
      simp [Algebra.smul_def]
    rw [hc]
    exact S.smul_mem _ (by simpa using hx 0)
  | add p q hp hq => simpa using S.add_mem hp hq
  | mul_X p i hp =>
    fin_cases i
    · simpa [map_mul, x] using (hm _ hp).1
    · simpa [map_mul, y] using (hm _ hp).2

lemma image_normal_independent : LinearIndependent (Base k)
    (fun i : ℤ => nodeToTorus k (normalMonomial k i)) := by
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
  exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ PowerSeries.X_ne_zero)

lemma nodeToTorus_injective : Function.Injective (nodeToTorus k) := by
  have hd := Submodule.range_ker_disjoint (f := (nodeToTorus k).toLinearMap)
    (image_normal_independent k)
  rw [normal_span] at hd
  exact LinearMap.ker_eq_bot.mp (by simpa using hd)

theorem node_kernel_and_descent (k : Type u) [Field k] [CharZero k] :
    RingHom.ker (torusMap k) = relationIdeal k ∧
    ∃! phi : Node k →+* Torus k,
      phi.comp (quotientMap k) = torusMap k ∧ Function.Injective phi := by
  have hcomp : (nodeToTorus k).toRingHom.comp (quotientMap k) = torusMap k := by
    apply RingHom.ext
    intro p
    rfl
  constructor
  · ext p
    change torusMap k p = 0 ↔ p ∈ relationIdeal k
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change torusMap k p = 0 ↔ quotientMap k p = 0
    change nodeToTorus k (quotientMap k p) = 0 ↔ quotientMap k p = 0
    exact map_eq_zero_iff _ (nodeToTorus_injective k)
  · refine ⟨(nodeToTorus k).toRingHom, ⟨hcomp, nodeToTorus_injective k⟩, ?_⟩
    intro phi hphi
    apply Ideal.Quotient.ringHom_ext
    exact hphi.1.trans hcomp.symm

theorem node_free_basis (k : Type u) [Field k] [CharZero k] :
    ∃ b : Module.Basis ℤ (Base k) (Node k), ∀ i : ℤ, b i = normalMonomial k i := by
  have hinj : Function.Injective (nodeToTorus k) := by
    obtain ⟨phi, ⟨hsq, hmono⟩, _⟩ := (node_kernel_and_descent k).2
    have he : phi = (nodeToTorus k).toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      exact hsq.trans (by apply RingHom.ext; intro p; rfl)
    rw [he] at hmono
    exact hmono
  have hi : LinearIndependent (Base k) (normalMonomial k) :=
    ((nodeToTorus k).toLinearMap.linearIndependent_iff_of_injOn hinj.injOn).mp
      (image_normal_independent k)
  exact ⟨Module.Basis.mk hi (by rw [normal_span]), Module.Basis.mk_apply _ _⟩

/-- Specialization at the crossing of the two components of the special fiber. -/
def nodeOrigin : Node k →+* k :=
  Ideal.Quotient.lift (relationIdeal k)
    (MvPolynomial.eval₂Hom PowerSeries.constantCoeff (fun _ => 0)) (by
      change relationIdeal k ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      simp [relation, parameter])

@[simp] lemma nodeOrigin_t : nodeOrigin k (t k) = 0 := by
  change (MvPolynomial.eval₂Hom PowerSeries.constantCoeff (fun _ => (0 : k)))
    (C (parameter k)) = 0
  simp [parameter]

lemma node_coordinates_nonunit : ¬ IsUnit (x k) ∧ ¬ IsUnit (y k) := by
  have hx : nodeOrigin k (x k) = 0 := by simp [nodeOrigin, x, quotientMap]
  have hy : nodeOrigin k (y k) = 0 := by simp [nodeOrigin, y, quotientMap]
  constructor
  · intro h
    have he := h.map (nodeOrigin k)
    simp [hx] at he
  · intro h
    have he := h.map (nodeOrigin k)
    simp [hy] at he

theorem node_flat_domain_parameter (k : Type u) [Field k] [CharZero k] :
    IsDomain (Node k) ∧ Module.Flat (Base k) (Node k) ∧ t k ≠ 0 ∧
      ¬ IsUnit (t k) ∧ x k * y k = t k := by
  obtain ⟨b, hb⟩ := node_free_basis k
  let : Module.Free (Base k) (Node k) := Module.Free.of_basis b
  refine ⟨Function.Injective.isDomain (nodeToTorus k) (nodeToTorus_injective k),
    inferInstance, ?_, ?_, node_xy k⟩
  · intro h
    have he := congrArg (fun z : Node k => (nodeToTorus k z).coeff 0) h
    simp [t, parameter, LaurentPolynomial.C_apply] at he
  · intro h
    have he := h.map (nodeOrigin k)
    simp at he

end ArithmeticThetaNodeCharts
