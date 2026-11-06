module

public import TruncatedLaurentPresentationR0131

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Finite-stage constancy for the actual cyclic node atlas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
namespace PolygonCechKernelR0131
open ArithmeticThetaInfinitesimalPolygonR0129

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

abbrev qNode := trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n
abbrev qBase := trunc (PowerSeries k) PowerSeries.X n

def monomial (j : ℤ) : A k n := qNode k n (ArithmeticThetaNodeCharts.normalMonomial k j)

omit [CharZero k] in
lemma monomial_nat (d : ℕ) : monomial k n (d : ℤ) = coordX k n ^ d := by
  simp [monomial, ArithmeticThetaNodeCharts.normalMonomial_nat, coordX]

omit [CharZero k] in
lemma monomial_neg (d : ℕ) : monomial k n (-(d : ℤ)) = coordY k n ^ d := by
  simp [monomial, ArithmeticThetaNodeCharts.normalMonomial_neg, coordY]

/-- Reduce the accepted untruncated basis expansion coefficient by coefficient. -/
lemma exists_expansion (a : A k n) :
    ∃ c : ℤ →₀ R k n, a = c.sum (fun j z => base k n z * monomial k n j) := by
  classical
  obtain ⟨b, hb⟩ := ArithmeticThetaNodeCharts.node_free_basis k
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  let f := b.repr z
  refine ⟨f.mapRange (qBase k n) (map_zero _), ?_⟩
  have hz := b.linearCombination_repr z
  apply Eq.symm
  calc
    _ = f.sum (fun j v => base k n (qBase k n v) * monomial k n j) := by
      rw [Finsupp.sum_mapRange_index]; intro; simp
    _ = qNode k n (f.sum (fun j v => v • b j)) := by
      simp only [Finsupp.sum, map_sum, Algebra.smul_def, map_mul, hb]
      rfl
    _ = qNode k n z := congrArg (qNode k n) hz

variable {k n} (L : B k n true ≃+* LaurentPolynomial (R k n))
  (hL : LaurentPresentation k n L)
  (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)

def rightMap : A k n →+* LaurentPolynomial (R k n) :=
  L.toRingHom.comp (restriction k n true)

def leftMap : A k n →+* LaurentPolynomial (R k n) :=
  L.toRingHom.comp (E.toRingHom.comp (restriction k n false))

include hL

omit [CharZero k] in
lemma right_base (z : R k n) : rightMap L (base k n z) = LaurentPolynomial.C z :=
  RingHom.congr_fun hL.1 z

include hE in
lemma left_base (z : R k n) : leftMap L E (base k n z) = LaurentPolynomial.C z := by
  change L (E (restriction k n false (base k n z))) = _
  rw [show E (restriction k n false (base k n z)) =
    restriction k n true (base k n z) from RingHom.congr_fun (adjacent_base hE) z]
  exact right_base L hL z

omit [CharZero k] in
lemma right_x : rightMap L (coordX k n) = LaurentPolynomial.T 1 := hL.2

lemma right_y : rightMap L (coordY k n) =
    LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T (-1) := by
  apply (LaurentPolynomial.isUnit_T (R := R k n) 1).mul_left_cancel
  calc
    LaurentPolynomial.T 1 * rightMap L (coordY k n) =
        rightMap L (base k n (parameter k n)) := by
      rw [← right_x L hL, ← map_mul, coordX_mul_coordY]
    _ = LaurentPolynomial.C (parameter k n) := right_base L hL _
    _ = _ := by rw [mul_left_comm, ← LaurentPolynomial.T_add]; simp

include hE in
lemma left_y : leftMap L E (coordY k n) = LaurentPolynomial.T (-1) := by
  apply (LaurentPolynomial.isUnit_T (R := R k n) 1).mul_right_cancel
  calc
    leftMap L E (coordY k n) * LaurentPolynomial.T 1 = 1 := by
      change L (E (restriction k n false (coordY k n))) * LaurentPolynomial.T 1 = 1
      rw [← hL.2, ← map_mul, adjacent_y_mul_x hE, map_one]
    _ = _ := by rw [← LaurentPolynomial.T_add]; simp

include hE in
lemma left_x : leftMap L E (coordX k n) =
    LaurentPolynomial.C (parameter k n) * LaurentPolynomial.T 1 := by
  apply (LaurentPolynomial.isUnit_T (R := R k n) (-1)).mul_right_cancel
  calc
    leftMap L E (coordX k n) * LaurentPolynomial.T (-1) =
        leftMap L E (base k n (parameter k n)) := by
      rw [← left_y L hL E hE, ← map_mul, coordX_mul_coordY]
    _ = LaurentPolynomial.C (parameter k n) := left_base L hL E hE _
    _ = _ := by rw [mul_assoc, ← LaurentPolynomial.T_add]; simp

lemma right_monomial (j : ℤ) : rightMap L (monomial k n j) =
    LaurentPolynomial.C (parameter k n ^ (-j).toNat) * LaurentPolynomial.T j := by
  cases j with
  | ofNat d => simp [monomial_nat, right_x L hL]
  | negSucc d =>
    rw [show Int.negSucc d = -((d+1 : ℕ) : ℤ) by omega, monomial_neg]
    simp only [map_pow, right_y L hL, mul_pow, LaurentPolynomial.T_pow]
    simp [← map_pow, neg_add_rev]

include hE in
lemma left_monomial (j : ℤ) : leftMap L E (monomial k n j) =
    LaurentPolynomial.C (parameter k n ^ j.toNat) * LaurentPolynomial.T j := by
  cases j with
  | ofNat d =>
    change leftMap L E (monomial k n (d : ℤ)) = _
    rw [monomial_nat, map_pow, left_x L hL E hE, mul_pow]
    simp [← map_pow]
  | negSucc d =>
    rw [show Int.negSucc d = -((d+1 : ℕ) : ℤ) by omega, monomial_neg]
    simp [left_y L hL E hE, Int.toNat_of_nonpos (show -1 + -(d : ℤ) ≤ 0 by omega)]

omit hL [CharZero k] in
lemma expansion_coeff {F : A k n →+* LaurentPolynomial (R k n)}
    (hb : ∀ z, F (base k n z) = LaurentPolynomial.C z)
    (w : ℤ → R k n)
    (hm : ∀ j, F (monomial k n j) = LaurentPolynomial.C (w j) * LaurentPolynomial.T j)
    (c : ℤ →₀ R k n) (j : ℤ) :
    (F (c.sum (fun i z => base k n z * monomial k n i))).coeff j = c j * w j := by
  classical
  have ht (i : ℤ) : F (base k n (c i) * monomial k n i) =
      AddMonoidAlgebra.single i (c i * w i) := by
    rw [map_mul, hb, hm, ← mul_assoc, ← map_mul, LaurentPolynomial.single_eq_C_mul_T]
  simp only [Finsupp.sum, map_sum, ht, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases hj : j ∈ c.support
  · simp [Finset.sum_ite_eq', hj]
  · simp [Finset.sum_ite_eq', hj, Finsupp.notMem_support_iff.mp hj]

lemma right_coeff (c : ℤ →₀ R k n) (j : ℤ) :
    (rightMap L (c.sum (fun i z => base k n z * monomial k n i))).coeff j =
      c j * parameter k n ^ (-j).toNat :=
  expansion_coeff (right_base L hL) _ (right_monomial L hL) c j

include hE in
lemma left_coeff (c : ℤ →₀ R k n) (j : ℤ) :
    (leftMap L E (c.sum (fun i z => base k n z * monomial k n i))).coeff j =
      c j * parameter k n ^ j.toNat :=
  expansion_coeff (left_base L hL E hE) _ (left_monomial L hL E hE) c j

omit hL

/-- A recurrence with nilpotent multiplier vanishes after finitely many steps. -/
lemma nilpotent_recursion {S I : Type*} [CommRing S] (q : S) (N : ℕ)
    (hq : q ^ N = 0) (f : I → I) (c : I → S)
    (h : ∀ i, c i = q * c (f i)) : ∀ i, c i = 0 := by
  have he : ∀ m i, ∃ z, c i = q ^ m * z := by
    intro m
    induction m with
    | zero => intro i; exact ⟨c i, by simp⟩
    | succ m ih =>
      intro i
      obtain ⟨z, hz⟩ := ih (f i)
      refine ⟨z, ?_⟩
      rw [h i, hz, pow_succ]
      ring
  intro i
  obtain ⟨z, hz⟩ := he N i
  simpa [hq] using hz

lemma nilpotent_recursion_surjective {S I : Type*} [CommRing S] (q : S) (N : ℕ)
    (hq : q ^ N = 0) (f : I → I) (hf : Function.Surjective f) (c : I → S)
    (h : ∀ i, c (f i) = q * c i) : ∀ i, c i = 0 := by
  classical
  let g : I → I := fun i => (hf i).choose
  apply nilpotent_recursion q N hq g c
  intro i
  have hi : f (g i) = i := (hf i).choose_spec
  simpa only [hi] using h (g i)

lemma parameter_power_nilpotent (d : ℕ) (hd : 0 < d) :
    (parameter k n ^ d) ^ (n+1) = 0 := by
  rw [← pow_mul, Nat.mul_comm d, pow_mul, parameter_pow, zero_pow (by omega)]

lemma cyclic_constant {S : Type*} (r : ℕ) (hr : 0 < r) (c : Fin r → S)
    (h : ∀ i, c (next r hr i) = c i) : ∀ i, c i = c ⟨0, hr⟩ := by
  have he : ∀ m (hm : m < r), c ⟨m, hm⟩ = c ⟨0, hr⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have hn : next r hr ⟨m, hm'⟩ = ⟨m+1, hm⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hm
      rw [← hn, h]
      exact ih hm'
  intro i
  exact he i.val i.isLt

/-- Nonzero modes vanish; the zero mode is constant on the cyclic index set. -/
lemma compatible_expansions (r : ℕ) (hr : 0 < r)
    (c : Fin r → ℤ →₀ R k n)
    (hc : ∀ i j, c i j * parameter k n ^ j.toNat =
      c (next r hr i) j * parameter k n ^ (-j).toNat) :
    ∃ z : R k n, ∀ i, c i = Finsupp.single 0 z := by
  classical
  have hnz : ∀ j : ℤ, j ≠ 0 → ∀ i, c i j = 0 := by
    intro j hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · have hpos : 0 < (-j).toNat := by omega
      apply nilpotent_recursion (parameter k n ^ (-j).toNat) (n+1)
        (parameter_power_nilpotent (-j).toNat hpos) (next r hr)
      intro i
      simpa [Int.toNat_of_nonpos (le_of_lt hj), mul_comm] using hc i j
    · have hpos : 0 < j.toNat := by omega
      apply nilpotent_recursion_surjective (parameter k n ^ j.toNat) (n+1)
        (parameter_power_nilpotent j.toNat hpos) (next r hr) (next_surjective r hr)
      intro i
      simpa [Int.toNat_of_nonpos (show -j ≤ 0 by omega), mul_comm] using (hc i j).symm
  have hz : ∀ i, c i 0 = c ⟨0, hr⟩ 0 := by
    apply cyclic_constant r hr (fun i => c i 0)
    intro i
    simpa using (hc i 0).symm
  refine ⟨c ⟨0, hr⟩ 0, ?_⟩
  intro i
  ext j
  by_cases hj : j = 0
  · subst j; simpa using hz i
  · simp [hj, hnz j hj i]

end PolygonCechKernelR0131

open ArithmeticThetaInfinitesimalPolygonR0129 PolygonCechKernelR0131

/-- Every compatible finite-stage chart family is a unique structural scalar. -/
theorem polygon_cech_kernel :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (E : B k n false ≃+* B k n true), IsAdjacent k n E →
      ∀ a : Fin r → A k n,
        difference k r n hr E a = 0 ↔ ∃! c : R k n, constants k r n c = a := by
  intro k _ _ r n hr _ E hE a
  classical
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  have hinj : Function.Injective (base k n) := by
    intro x y h
    have he := congrArg (rightMap L) h
    rw [right_base L hL, right_base L hL] at he
    have he' := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff 0) he
    simpa [LaurentPolynomial.C_apply, AddMonoidAlgebra.coeff_single] using he'
  constructor
  · intro ha
    choose c hc using fun i => exists_expansion k n (a i)
    have he (i : Fin r) : leftMap L E (a i) = rightMap L (a (next r hr i)) := by
      apply congrArg L
      exact sub_eq_zero.mp (congrFun ha i)
    have hcoeff (i : Fin r) (j : ℤ) :
        c i j * parameter k n ^ j.toNat =
          c (next r hr i) j * parameter k n ^ (-j).toNat := by
      have h := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff j) (he i)
      rw [hc i, hc (next r hr i), left_coeff L hL E hE, right_coeff L hL] at h
      exact h
    obtain ⟨z, hz⟩ := compatible_expansions r hr c hcoeff
    have haz : constants k r n z = a := by
      funext i
      rw [hc i, hz i]
      simp [constants, Finsupp.sum_single_index, monomial,
        ArithmeticThetaNodeCharts.normalMonomial]
    refine ⟨z, haz, ?_⟩
    intro w hw
    apply hinj
    exact congrFun (hw.trans haz.symm) ⟨0, hr⟩
  · rintro ⟨z, rfl, _⟩
    funext i
    exact sub_eq_zero.mpr (RingHom.congr_fun (adjacent_base hE) z)

end ArithmeticThetaPolygonCohomologyR0131
