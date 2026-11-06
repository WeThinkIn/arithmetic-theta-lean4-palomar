module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Formal Jacobi triple product

The finite polynomial proof is integrated from the frozen FiniteQBinomial
reference candidate. Every supporting definition and proof is included here.
The full product is defined from stable coefficients in the actual ring
`PowerSeries (LaurentPolynomial ℤ)`; integer Laurent indices are retained.
-/

universe u

namespace ArithmeticThetaDurfee

noncomputable def finiteEuler {R : Type u} [CommRing R] (q : R) (n : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.range n, (1 + Polynomial.C (q ^ j) * Polynomial.X)

def qFactorial {R : Type u} [CommRing R] (q : R) (n : ℕ) : R :=
  ∏ j ∈ Finset.range n, (1 - q ^ (j + 1))

@[simp] theorem qFactorial_zero {R : Type u} [CommRing R] (q : R) : qFactorial q 0 = 1 := rfl

theorem finiteEuler_succ {R : Type u} [CommRing R] (q : R) (n : ℕ) :
    finiteEuler q (n + 1) = finiteEuler q n * (1 + Polynomial.C (q ^ n) * Polynomial.X) := by
  exact Finset.prod_range_succ _ _

theorem qFactorial_succ {R : Type u} [CommRing R] (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * (1 - q ^ (n + 1)) := by
  exact Finset.prod_range_succ _ _

theorem finiteEuler_constant {R : Type u} [CommRing R] (q : R) (n : ℕ) :
    (finiteEuler q n).coeff 0 = 1 := by
  induction n with
  | zero => simp [finiteEuler]
  | succ n ih =>
    rw [finiteEuler_succ, Polynomial.mul_coeff_zero]
    simp [ih]

theorem finiteEuler_coeff_succ {R : Type u} [CommRing R] (q : R) (n k : ℕ) :
    (finiteEuler q (n + 1)).coeff (k + 1) =
      (finiteEuler q n).coeff (k + 1) + q ^ n * (finiteEuler q n).coeff k := by
  rw [finiteEuler_succ, mul_add, mul_one]
  rw [Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
  rw [mul_comm]

theorem finiteEuler_natDegree {R : Type u} [CommRing R] (q : R) (n : ℕ) :
    (finiteEuler q n).natDegree ≤ n := by
  induction n with
  | zero => simp [finiteEuler]
  | succ n ih =>
    rw [finiteEuler_succ]
    calc
      _ ≤ (finiteEuler q n).natDegree +
          (1 + Polynomial.C (q ^ n) * Polynomial.X).natDegree := Polynomial.natDegree_mul_le
      _ ≤ n + 1 := by
        apply add_le_add ih
        apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · simp
        · apply Polynomial.natDegree_mul_le.trans
          rw [Polynomial.natDegree_C, zero_add]
          exact Polynomial.natDegree_X_le

theorem tri_succ (k : ℕ) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  simpa [Nat.choose_two_right, Nat.choose_one_right, add_comm] using Nat.choose_succ_succ k 1

theorem finite_q_binomial_coefficient
    (R : Type u) [CommRing R] (q : R) (n k : ℕ) (hk : k ≤ n) :
    (finiteEuler q n).coeff k * qFactorial q k * qFactorial q (n - k) =
      q ^ (k * (k - 1) / 2) * qFactorial q n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [finiteEuler, qFactorial]
  | succ n ih =>
    cases k with
    | zero => simp [finiteEuler_constant, qFactorial]
    | succ k =>
      have hkn : k ≤ n := by omega
      rw [finiteEuler_coeff_succ]
      by_cases hkeq : k = n
      · subst k
        have hz : (finiteEuler q n).coeff (n + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (finiteEuler_natDegree q n) (by omega))
        have hn := ih n le_rfl
        simp only [Nat.sub_self, qFactorial_zero, mul_one] at hn
        simp only [hz, zero_add, Nat.sub_self, qFactorial_zero, mul_one, qFactorial_succ]
        rw [Nat.add_sub_cancel, tri_succ, pow_add]
        calc
          _ = q ^ n * ((finiteEuler q n).coeff n * qFactorial q n) * (1-q^(n+1)) := by ring
          _ = _ := by rw [hn]; ring
      · have hklt : k + 1 ≤ n := by omega
        have h1 := ih (k + 1) hklt
        have h2 := ih k hkn
        have hnsub : n - k = (n - (k + 1)) + 1 := by omega
        have hsuccsub : n + 1 - (k + 1) = n - k := by omega
        rw [hsuccsub]
        have hpow : n + k * (k - 1) / 2 = (k + 1) * k / 2 + (n - k) := by
          rw [tri_succ]
          omega
        have hpow2 : (n - k) + (k + 1) = n + 1 := by omega
        rw [add_mul, add_mul]
        have hterm1 : (finiteEuler q n).coeff (k + 1) * qFactorial q (k + 1) * qFactorial q (n - k) =
            q ^ ((k + 1) * k / 2) * qFactorial q n * (1 - q ^ (n - k)) := by
          rw [show qFactorial q (n-k) = qFactorial q (n-(k+1)) * (1-q^(n-k)) by
            conv_lhs => rw [hnsub, qFactorial_succ]
            rw [← hnsub]]
          rw [← mul_assoc, h1]
          simp
        have hterm2 : q ^ n * (finiteEuler q n).coeff k * qFactorial q (k + 1) * qFactorial q (n - k) =
            q ^ ((k + 1) * k / 2) * qFactorial q n * (q ^ (n - k) * (1 - q ^ (k + 1))) := by
          rw [qFactorial_succ]
          calc
            _ = q ^ n * ((finiteEuler q n).coeff k * qFactorial q k * qFactorial q (n-k)) * (1-q^(k+1)) := by ring
            _ = _ := by rw [h2, ← mul_assoc, ← pow_add, hpow, pow_add]; ring
        rw [hterm1, hterm2, qFactorial_succ]
        simp only [Nat.add_sub_cancel]
        rw [← mul_add, show (1 - q ^ (n-k)) + q ^ (n-k) * (1-q^(k+1)) = 1-q^(n+1) by
          rw [mul_sub, mul_one, ← pow_add, hpow2]; ring]
        ring

noncomputable def finiteBackward {R : Type u} [CommRing R] (q : R) (m : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.range m, (Polynomial.X + Polynomial.C (q ^ (j + 1)))

theorem finiteEuler_shift {R : Type u} [CommRing R] (q : R) (n m : ℕ) :
    finiteEuler q (m + n) = finiteEuler q m *
      (finiteEuler q n).comp (Polynomial.C (q ^ m) * Polynomial.X) := by
  rw [finiteEuler, Finset.prod_range_add]
  congr 1
  simp only [finiteEuler, Polynomial.prod_comp, Polynomial.add_comp, Polynomial.one_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  apply Finset.prod_congr rfl
  intro j hj
  rw [pow_add, Polynomial.C_mul]
  ring

theorem finiteBackward_scale {R : Type u} [CommRing R] (q : R) (m : ℕ) :
    (finiteBackward q m).comp (Polynomial.C (q ^ m) * Polynomial.X) =
      Polynomial.C (q ^ (m * (m + 1) / 2)) * finiteEuler q m := by
  simp only [finiteBackward, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  have hfactor (j : ℕ) (hj : j ∈ Finset.range m) :
      Polynomial.C (q ^ m) * Polynomial.X + Polynomial.C (q ^ (j + 1)) =
      Polynomial.C (q ^ (j+1)) * (1 + Polynomial.C (q ^ (m-1-j)) * Polynomial.X) := by
    have hexp : j + 1 + (m-1-j) = m := by simp only [Finset.mem_range] at hj; omega
    rw [mul_add, mul_one, ← mul_assoc, ← Polynomial.C_mul, ← pow_add, hexp]
    ring
  simp_rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ j ∈ Finset.range m, (j + 1)) = m * (m+1)/2 := by
    rw [Finset.sum_add_distrib, Finset.sum_range_id]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [← tri_succ]
    congr 1
    ring
  rw [hsum, Finset.prod_range_reflect (fun j => (1 + Polynomial.C (q ^ j) * Polynomial.X)) m]
  rfl

theorem central_polynomial_scaling {R : Type u} [CommRing R] (q : R) (n m : ℕ) :
    ((finiteEuler q n * finiteBackward q m).comp (Polynomial.C (q ^ m) * Polynomial.X)) =
      Polynomial.C (q ^ (m * (m+1)/2)) * finiteEuler q (n+m) := by
  rw [Polynomial.mul_comp, finiteBackward_scale, Nat.add_comm n m, finiteEuler_shift]
  ring

theorem double_triangular (m : ℕ) : m*(m+1)/2 + m*(m-1)/2 = m*m := by
  have hmod : m * (m-1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_pred_self m)
  have hdiv := Nat.mod_add_div (m*(m-1)) 2
  rw [show m*(m+1)/2 = (m+1)*m/2 by rw [Nat.mul_comm], tri_succ]
  cases m with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel] at hmod hdiv ⊢; nlinarith

theorem finite_central_coefficient
    (R : Type u) [CommRing R] [IsDomain R] (q : R) (hq : q ≠ 0) (n m : ℕ) :
    (finiteEuler q n * finiteBackward q m).coeff m * qFactorial q m * qFactorial q n =
      qFactorial q (n+m) := by
  have hscale := congrArg (fun p : Polynomial R => p.coeff m) (central_polynomial_scaling q n m)
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul, ← pow_mul] at hscale
  have hchoose := finite_q_binomial_coefficient R q (n+m) m (by omega)
  rw [show n + m - m = n by omega] at hchoose
  apply mul_right_cancel₀ (pow_ne_zero (m*m) hq)
  calc
    _ = ((finiteEuler q n * finiteBackward q m).coeff m * q ^ (m*m)) * qFactorial q m * qFactorial q n := by ring
    _ = q ^ (m*(m+1)/2) * ((finiteEuler q (n+m)).coeff m * qFactorial q m * qFactorial q n) := by rw [hscale]; ring
    _ = _ := by rw [hchoose, ← mul_assoc, ← pow_add, double_triangular]; ring

noncomputable def finiteLaurent {R : Type u} [CommRing R] (q : R) (n m : ℕ) : LaurentPolynomial R :=
  (∏ j ∈ Finset.range n, (1 + LaurentPolynomial.C (q ^ j) * LaurentPolynomial.T 1)) *
    ∏ j ∈ Finset.range m, (1 + LaurentPolynomial.C (q ^ (j+1)) * LaurentPolynomial.T (-1))

theorem shifted_polynomial_coeff {R : Type u} [CommRing R] (p : Polynomial R) (m : ℕ) :
    (p.toLaurent * LaurentPolynomial.T (-(m : ℤ))).coeff 0 = p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [add_mul, hp, hr]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, LaurentPolynomial.mul_T_assoc,
      ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Polynomial.coeff_monomial]
    have hiff : (n : ℤ) + -(m : ℤ) = 0 ↔ n = m := by omega
    simp only [hiff, eq_comm]

theorem backward_to_laurent {R : Type u} [CommRing R] (q : R) (m : ℕ) :
    (finiteBackward q m).toLaurent * LaurentPolynomial.T (-(m : ℤ)) =
      ∏ j ∈ Finset.range m, (1 + LaurentPolynomial.C (q ^ (j+1)) * LaurentPolynomial.T (-1)) := by
  induction m with
  | zero => simp [finiteBackward]
  | succ m ih =>
    have hB : finiteBackward q (m+1) = finiteBackward q m * (Polynomial.X + Polynomial.C (q^(m+1))) :=
      Finset.prod_range_succ _ _
    rw [hB, map_mul, Finset.prod_range_succ, ← ih]
    have hT : LaurentPolynomial.T (-((m+1 : ℕ) : ℤ)) =
        (LaurentPolynomial.T (-(m : ℤ)) * LaurentPolynomial.T (-1) : LaurentPolynomial R) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    rw [hT, map_add, Polynomial.toLaurent_X, Polynomial.toLaurent_C]
    have hcancel : (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) : LaurentPolynomial R) = 1 := by
      rw [← LaurentPolynomial.T_add]
      norm_num
    calc
      _ = ((finiteBackward q m).toLaurent * LaurentPolynomial.T (-(m : ℤ))) *
        (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) + LaurentPolynomial.C (q^(m+1)) * LaurentPolynomial.T (-1)) := by ring
      _ = _ := by rw [hcancel]

theorem central_coeff_eq_laurent_coeff {R : Type u} [CommRing R] (q : R) (n m : ℕ) :
    (finiteEuler q n * finiteBackward q m).coeff m = (finiteLaurent q n m).coeff 0 := by
  rw [← shifted_polynomial_coeff, map_mul, mul_assoc, backward_to_laurent]
  simp only [finiteEuler, map_prod, map_add, map_one, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  rfl

theorem finite_laurent_constant
    (R : Type u) [CommRing R] [IsDomain R] (q : R) (hq : q ≠ 0) (n m : ℕ) :
    (finiteLaurent q n m).coeff 0 * qFactorial q m * qFactorial q n = qFactorial q (n+m) := by
  rw [← central_coeff_eq_laurent_coeff]
  exact finite_central_coefficient R q hq n m

theorem finite_laurent_constant_tail
    (R : Type u) [CommRing R] [IsDomain R] (q : R) (hq : q ≠ 0) (n m : ℕ)
    (hn : qFactorial q n ≠ 0) :
    (finiteLaurent q n m).coeff 0 * qFactorial q m =
      ∏ j ∈ Finset.range m, (1 - q ^ (n+j+1)) := by
  apply mul_right_cancel₀ hn
  rw [finite_laurent_constant R q hq]
  simp only [qFactorial, Finset.prod_range_add]
  exact mul_comm _ _

theorem qFactorial_series_ne_zero (n : ℕ) :
    qFactorial (PowerSeries.X : PowerSeries ℤ) n ≠ 0 := by
  have hc : PowerSeries.constantCoeff (qFactorial (PowerSeries.X : PowerSeries ℤ) n) = 1 := by
    simp [qFactorial, map_prod]
  intro h
  rw [h, map_zero] at hc
  norm_num at hc

theorem coeff_high_tail_product (d n m : ℕ) (h : d ≤ n) :
    PowerSeries.coeff d (∏ j ∈ Finset.range m,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ (n+j+1))) =
      PowerSeries.coeff d (1 : PowerSeries ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      PowerSeries.coeff_mul_X_pow']
    rw [if_neg (by omega), sub_zero, ih]

theorem finite_formal_constant_normalization (N d : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d
      ((finiteLaurent (PowerSeries.X : PowerSeries ℤ) (N+1) N).coeff 0 *
        qFactorial (PowerSeries.X : PowerSeries ℤ) N) =
      PowerSeries.coeff d (1 : PowerSeries ℤ) := by
  rw [finite_laurent_constant_tail (PowerSeries ℤ) PowerSeries.X PowerSeries.X_ne_zero
    (N+1) N (qFactorial_series_ne_zero (N+1))]
  exact coeff_high_tail_product d (N+1) N (by omega)

noncomputable def zPowerHom : Multiplicative ℤ →* PowerSeries (LaurentPolynomial ℤ) where
  toFun k := PowerSeries.C (LaurentPolynomial.T k.toAdd)
  map_one' := by simp
  map_mul' a b := by
    change PowerSeries.C (LaurentPolynomial.T (a.toAdd + b.toAdd)) = _
    rw [LaurentPolynomial.T_add, map_mul]

noncomputable def swapVariables : LaurentPolynomial (PowerSeries ℤ) →+* PowerSeries (LaurentPolynomial ℤ) :=
  AddMonoidAlgebra.liftNCRingHom (PowerSeries.map LaurentPolynomial.C) zPowerHom
    (fun _ _ => Commute.all _ _)

theorem swap_single (k : ℤ) (a : PowerSeries ℤ) :
    swapVariables (AddMonoidAlgebra.single k a) =
      PowerSeries.map LaurentPolynomial.C a * PowerSeries.C (LaurentPolynomial.T k) := by
  exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _

theorem coeff_swap (F : LaurentPolynomial (PowerSeries ℤ)) (d : ℕ) (k : ℤ) :
    (PowerSeries.coeff d (swapVariables F)).coeff k = PowerSeries.coeff d (F.coeff k) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => simp [hF, hG]
  | C_mul_T j a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, swap_single, PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> simp

theorem swap_C (a : PowerSeries ℤ) :
    swapVariables (LaurentPolynomial.C a) = PowerSeries.map LaurentPolynomial.C a := by
  change swapVariables (AddMonoidAlgebra.single 0 a) = _
  rw [swap_single]
  simp

theorem swap_T (k : ℤ) :
    swapVariables (LaurentPolynomial.T k) = PowerSeries.C (LaurentPolynomial.T k) := by
  rw [LaurentPolynomial.T, swap_single]
  simp

noncomputable def normalizedFiniteLaurent (N : ℕ) : LaurentPolynomial (PowerSeries ℤ) :=
  finiteLaurent PowerSeries.X (N+1) N * LaurentPolynomial.C (qFactorial PowerSeries.X N)

noncomputable def normalizedFiniteProduct (N : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  (1 + PowerSeries.C (LaurentPolynomial.T 1)) *
    ∏ j ∈ Finset.range N,
      (1 - PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j+1)) *
      (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j+1))

theorem swap_normalized_finite (N : ℕ) :
    swapVariables (normalizedFiniteLaurent N) = normalizedFiniteProduct N := by
  simp only [normalizedFiniteLaurent, finiteLaurent, map_mul, map_prod, map_add, map_one,
    swap_C, swap_T, map_pow, PowerSeries.map_X]
  rw [Finset.prod_range_succ']
  simp only [pow_zero, one_mul]
  simp only [qFactorial, map_prod, map_sub, map_one, map_pow, PowerSeries.map_X]
  unfold normalizedFiniteProduct
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [mul_comm (PowerSeries.X ^ _) (PowerSeries.C _)]
  ring

theorem normalized_partial_laurent_constant (N d : ℕ) (hd : d ≤ N) :
    (PowerSeries.coeff d (normalizedFiniteProduct N)).coeff 0 =
      PowerSeries.coeff d (1 : PowerSeries ℤ) := by
  rw [← swap_normalized_finite, coeff_swap]
  have hcoeff : (normalizedFiniteLaurent N).coeff 0 =
      (finiteLaurent (PowerSeries.X : PowerSeries ℤ) (N+1) N).coeff 0 *
      qFactorial (PowerSeries.X : PowerSeries ℤ) N := by
    change ((finiteLaurent (PowerSeries.X : PowerSeries ℤ) (N+1) N) *
      AddMonoidAlgebra.single 0 (qFactorial PowerSeries.X N)).coeff 0 = _
    rw [AddMonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [hcoeff]
  exact finite_formal_constant_normalization N d hd

theorem formal_laurent_constant_normalization
    (F : PowerSeries (LaurentPolynomial ℤ))
    (hF : ∀ d : ℕ, PowerSeries.coeff d F = PowerSeries.coeff d (normalizedFiniteProduct d)) :
    PowerSeries.mk (fun d => (PowerSeries.coeff d F).coeff 0) = (1 : PowerSeries ℤ) := by
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_mk, hF d, normalized_partial_laurent_constant d d le_rfl]

theorem canonical_product_laurent_constant :
    PowerSeries.mk (fun d => (PowerSeries.coeff d (normalizedFiniteProduct d)).coeff 0) =
      (1 : PowerSeries ℤ) := by
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_mk, normalized_partial_laurent_constant d d le_rfl]

theorem finiteEuler_qshift {R : Type u} [CommRing R] (q : R) (n : ℕ) :
    (finiteEuler q n).comp (Polynomial.C q * Polynomial.X) * (1 + Polynomial.X) =
      finiteEuler q n * (1 + Polynomial.C (q^n) * Polynomial.X) := by
  rw [← finiteEuler_succ]
  have h := finiteEuler_shift q n 1
  have h1 : finiteEuler q 1 = 1 + Polynomial.X := by
    simp only [finiteEuler, Finset.prod_range_one, pow_zero, map_one, one_mul]
  rw [h1, pow_one, Nat.add_comm 1 n] at h
  exact (mul_comm _ _).trans h.symm

theorem finiteBackward_qshift {R : Type u} [CommRing R] (q : R) (m : ℕ) :
    (finiteBackward q (m+1)).comp (Polynomial.C q * Polynomial.X) =
      Polynomial.C (q^(m+1)) * (Polynomial.X + 1) * finiteBackward q m := by
  simp only [finiteBackward, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  have hf (j : ℕ) : Polynomial.C q * Polynomial.X + Polynomial.C (q^(j+1)) =
      Polynomial.C q * (Polynomial.X + Polynomial.C (q^j)) := by
    rw [pow_succ, Polynomial.C_mul]
    ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← map_pow,
    Finset.prod_range_succ']
  simp only [pow_zero, map_one]
  ring

theorem central_polynomial_qshift {R : Type u} [CommRing R] (q : R) (n m : ℕ) :
    (Polynomial.X + Polynomial.C (q^m)) *
        (finiteEuler q n * finiteBackward q m).comp (Polynomial.C q * Polynomial.X) =
      Polynomial.C (q^m) * (1 + Polynomial.C (q^n) * Polynomial.X) *
        (finiteEuler q n * finiteBackward q m) := by
  rw [Polynomial.mul_comp]
  cases m with
  | zero =>
    simp only [finiteBackward, Finset.range_zero, Finset.prod_empty, Polynomial.one_comp,
      mul_one, pow_zero, map_one, one_mul]
    convert finiteEuler_qshift q n using 1 <;> ring
  | succ m =>
    rw [finiteBackward_qshift]
    have hB : finiteBackward q (m+1) = finiteBackward q m * (Polynomial.X + Polynomial.C (q^(m+1))) :=
      Finset.prod_range_succ _ _
    rw [hB]
    calc
      _ = Polynomial.C (q^(m+1)) *
        ((finiteEuler q n).comp (Polynomial.C q * Polynomial.X) * (1+Polynomial.X)) *
        (finiteBackward q m * (Polynomial.X + Polynomial.C (q^(m+1)))) := by ring
      _ = _ := by rw [finiteEuler_qshift]; ring

theorem shifted_polynomial_coeff_nat {R : Type u} [CommRing R] (p : Polynomial R) (m k : ℕ) :
    (p.toLaurent * LaurentPolynomial.T (-(m : ℤ))).coeff (k : ℤ) = p.coeff (m+k) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [add_mul, hp, hr]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, LaurentPolynomial.mul_T_assoc,
      ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Polynomial.coeff_monomial]
    have hiff : (n : ℤ) + -(m : ℤ) = (k : ℤ) ↔ n = m+k := by omega
    simp only [hiff]

theorem laurent_coeff_nat_eq {R : Type u} [CommRing R] (q : R) (n m k : ℕ) :
    (finiteLaurent q n m).coeff (k : ℤ) = (finiteEuler q n * finiteBackward q m).coeff (m+k) := by
  rw [← shifted_polynomial_coeff_nat, map_mul, mul_assoc, backward_to_laurent]
  simp only [finiteEuler, map_prod, map_add, map_one, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  rfl

theorem finite_laurent_coeff_recurrence
    (R : Type u) [CommRing R] [IsDomain R] (q : R) (hq : q ≠ 0) (N k : ℕ) :
    q^k * (finiteLaurent q (N+1) N).coeff (k : ℤ) +
        q^(N+k+1) * (finiteLaurent q (N+1) N).coeff ((k+1 : ℕ) : ℤ) =
      (finiteLaurent q (N+1) N).coeff ((k+1 : ℕ) : ℤ) +
        q^(N+1) * (finiteLaurent q (N+1) N).coeff (k : ℤ) := by
  simp only [laurent_coeff_nat_eq]
  have h := congrArg (fun p : Polynomial R => p.coeff (N+k+1))
    (central_polynomial_qshift q (N+1) N)
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff] at h
  have hrhs : Polynomial.C (q^N) * (1+Polynomial.C (q^(N+1))*Polynomial.X) *
      (finiteEuler q (N+1) * finiteBackward q N) =
      Polynomial.C (q^N) * ((finiteEuler q (N+1) * finiteBackward q N) +
        Polynomial.C (q^(N+1)) * ((finiteEuler q (N+1) * finiteBackward q N) * Polynomial.X)) := by ring
  rw [hrhs, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X] at h
  apply mul_left_cancel₀ (pow_ne_zero N hq)
  simp only [pow_add, pow_one, Nat.add_assoc] at h ⊢
  convert h using 1
  ring

theorem normalized_partial_step (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (normalizedFiniteProduct (N+1)) =
      PowerSeries.coeff d (normalizedFiniteProduct N) := by
  have hm (f : PowerSeries (LaurentPolynomial ℤ)) (a : LaurentPolynomial ℤ) :
      PowerSeries.coeff d (f * (1 + PowerSeries.C a * PowerSeries.X^(N+1))) = PowerSeries.coeff d f := by
    simp [mul_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', show ¬N+1≤d by omega]
  have he (f : PowerSeries (LaurentPolynomial ℤ)) :
      PowerSeries.coeff d (f * (1 - PowerSeries.X^(N+1))) = PowerSeries.coeff d f := by
    simp [mul_sub, PowerSeries.coeff_mul_X_pow', show ¬N+1≤d by omega]
  have hp : normalizedFiniteProduct (N+1) = normalizedFiniteProduct N *
      (1-PowerSeries.X^(N+1)) *
      (1+PowerSeries.C (LaurentPolynomial.T 1)*PowerSeries.X^(N+1)) *
      (1+PowerSeries.C (LaurentPolynomial.T (-1))*PowerSeries.X^(N+1)) := by
    simp [normalizedFiniteProduct, Finset.prod_range_succ, mul_assoc]
  rw [hp, hm, hm, he]

theorem normalized_partial_stable (d N : ℕ) (h : d ≤ N) :
    PowerSeries.coeff d (normalizedFiniteProduct N) =
      PowerSeries.coeff d (normalizedFiniteProduct d) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih => rw [normalized_partial_step d N h, ih]

noncomputable def fullProduct : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (normalizedFiniteProduct d))

noncomputable def laurentCoeffSeries (k : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun d => (PowerSeries.coeff d fullProduct).coeff k)

noncomputable def finiteLaurentCoeff (N : ℕ) (k : ℤ) : PowerSeries ℤ :=
  (normalizedFiniteLaurent N).coeff k

theorem finiteLaurentCoeff_eq (N : ℕ) (k : ℤ) :
    finiteLaurentCoeff N k = (finiteLaurent (PowerSeries.X : PowerSeries ℤ) (N+1) N).coeff k *
      qFactorial PowerSeries.X N := by
  change ((finiteLaurent (PowerSeries.X : PowerSeries ℤ) (N+1) N) *
      AddMonoidAlgebra.single 0 (qFactorial PowerSeries.X N)).coeff k = _
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp

theorem finite_normalized_recurrence (N k : ℕ) :
    PowerSeries.X^k * finiteLaurentCoeff N (k : ℤ) +
        PowerSeries.X^(N+k+1) * finiteLaurentCoeff N ((k+1 : ℕ) : ℤ) =
      finiteLaurentCoeff N ((k+1 : ℕ) : ℤ) +
        PowerSeries.X^(N+1) * finiteLaurentCoeff N (k : ℤ) := by
  simp only [finiteLaurentCoeff_eq]
  have h := congrArg (fun a : PowerSeries ℤ => a * qFactorial PowerSeries.X N)
    (finite_laurent_coeff_recurrence (PowerSeries ℤ) PowerSeries.X PowerSeries.X_ne_zero N k)
  linear_combination h

theorem finite_normalized_coeff_recurrence (N k d : ℕ) (hd : d ≤ N) :
    PowerSeries.coeff d (finiteLaurentCoeff N ((k+1 : ℕ) : ℤ)) =
      PowerSeries.coeff d (PowerSeries.X^k * finiteLaurentCoeff N (k : ℤ)) := by
  have h := congrArg (PowerSeries.coeff d) (finite_normalized_recurrence N k)
  simp only [map_add] at h
  have he (e : ℕ) (he : d < e) (f : PowerSeries ℤ) :
      PowerSeries.coeff d (PowerSeries.X^e * f) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [he (N+k+1) (by omega), he (N+1) (by omega), add_zero, add_zero] at h
  exact h.symm

theorem full_coeff_series_match (N d : ℕ) (hd : d ≤ N) (k : ℤ) :
    PowerSeries.coeff d (laurentCoeffSeries k) = PowerSeries.coeff d (finiteLaurentCoeff N k) := by
  simp only [laurentCoeffSeries, fullProduct, PowerSeries.coeff_mk]
  rw [← normalized_partial_stable d N hd, ← swap_normalized_finite, coeff_swap]
  rfl

theorem full_coeff_recurrence (k : ℕ) :
    laurentCoeffSeries ((k+1 : ℕ) : ℤ) = PowerSeries.X^k * laurentCoeffSeries (k : ℤ) := by
  apply PowerSeries.ext
  intro d
  rw [full_coeff_series_match d d le_rfl, finite_normalized_coeff_recurrence d k d le_rfl]
  simp only [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · exact (full_coeff_series_match d (d-k) (by omega) k).symm
  · rfl

theorem full_nonneg_laurent_coeff (k : ℕ) :
    laurentCoeffSeries (k : ℤ) = PowerSeries.X ^ (k*(k-1)/2) := by
  induction k with
  | zero =>
    simpa only [laurentCoeffSeries, fullProduct, PowerSeries.coeff_mk, Nat.cast_zero,
      Nat.zero_sub, Nat.zero_mul, Nat.zero_div, pow_zero] using canonical_product_laurent_constant
  | succ k ih =>
    rw [full_coeff_recurrence, ih, ← pow_add]
    simp only [Nat.add_sub_cancel]
    rw [tri_succ, Nat.add_comm]

theorem normalized_invert (N : ℕ) :
    PowerSeries.C (LaurentPolynomial.T 1) *
        PowerSeries.map LaurentPolynomial.invert.toRingHom (normalizedFiniteProduct N) =
      normalizedFiniteProduct N := by
  have hinvT (k : ℤ) : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.T k : LaurentPolynomial ℤ) =
      LaurentPolynomial.T (-k) := LaurentPolynomial.invert_T k
  simp only [normalizedFiniteProduct, map_mul, map_prod, map_add, map_one, map_sub,
    map_pow, PowerSeries.map_X, PowerSeries.map_C, hinvT,
    neg_neg]
  have hhead : (PowerSeries.C (LaurentPolynomial.T 1) : PowerSeries (LaurentPolynomial ℤ)) *
      (1 + PowerSeries.C (LaurentPolynomial.T (-1))) = 1 + PowerSeries.C (LaurentPolynomial.T 1) := by
    rw [mul_add, mul_one, ← map_mul, ← LaurentPolynomial.T_add]
    norm_num
    ring
  rw [← mul_assoc, hhead]
  apply congrArg (fun F : PowerSeries (LaurentPolynomial ℤ) => (1 + PowerSeries.C (LaurentPolynomial.T 1)) * F)
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem full_laurent_coeff_symmetry (k : ℕ) :
    laurentCoeffSeries (-(k : ℤ)) = laurentCoeffSeries ((k+1 : ℕ) : ℤ) := by
  apply PowerSeries.ext
  intro d
  simp only [laurentCoeffSeries, fullProduct, PowerSeries.coeff_mk]
  have h := congrArg (fun F : PowerSeries (LaurentPolynomial ℤ) =>
    (PowerSeries.coeff d F).coeff (-(k : ℤ))) (normalized_invert d)
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul] at h
  change (LaurentPolynomial.invert (PowerSeries.coeff d (normalizedFiniteProduct d))).coeff (-1 + -(k : ℤ)) = _ at h
  rw [LaurentPolynomial.invert_apply] at h
  convert h.symm using 1
  congr 1
  push_cast
  ring

theorem full_neg_laurent_coeff (k : ℕ) :
    laurentCoeffSeries (-(k : ℤ)) = PowerSeries.X ^ ((k+1)*k/2) := by
  rw [full_laurent_coeff_symmetry, full_nonneg_laurent_coeff]
  simp

theorem triangular_twice (k : ℕ) : 2 * (k*(k-1)/2) = k*(k-1) := by
  have hmod : k*(k-1)%2=0 := Nat.even_iff.mp (Nat.even_mul_pred_self k)
  have hdiv := Nat.mod_add_div (k*(k-1)) 2
  omega

theorem integer_triangular_nonneg_iff (k d : ℕ) :
    (k : ℤ) * ((k : ℤ)-1) = 2*(d : ℤ) ↔ d = k*(k-1)/2 := by
  have htwo := triangular_twice k
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel] at htwo ⊢
    have htwoZ := congrArg (fun n : ℕ => (n : ℤ)) htwo
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at htwoZ
    simp only [Nat.cast_add, Nat.cast_one]
    constructor
    · intro h
      exact_mod_cast (show (d : ℤ) = (((k+1)*k/2 : ℕ) : ℤ) by nlinarith)
    · intro h
      subst d
      nlinarith

theorem integer_triangular_neg_iff (k d : ℕ) :
    (-(k : ℤ)) * (-(k : ℤ)-1) = 2*(d : ℤ) ↔ d = (k+1)*k/2 := by
  have htwo := triangular_twice (k+1)
  simp only [Nat.add_sub_cancel] at htwo
  constructor <;> intro h <;> nlinarith

theorem full_jacobi_double_coefficient (d : ℕ) (k : ℤ) :
    (PowerSeries.coeff d fullProduct).coeff k =
      if k*(k-1) = 2*(d : ℤ) then 1 else 0 := by
  have hbase : (PowerSeries.coeff d fullProduct).coeff k = PowerSeries.coeff d (laurentCoeffSeries k) :=
    by simp only [laurentCoeffSeries, PowerSeries.coeff_mk]
  rw [hbase]
  cases k with
  | ofNat k =>
    change PowerSeries.coeff d (laurentCoeffSeries (k : ℤ)) =
      if (k : ℤ)*((k : ℤ)-1) = 2*(d : ℤ) then 1 else 0
    rw [full_nonneg_laurent_coeff, PowerSeries.coeff_X_pow]
    simp only [integer_triangular_nonneg_iff]
  | negSucc k =>
    change PowerSeries.coeff d (laurentCoeffSeries (-((k+1 : ℕ) : ℤ))) =
      if (-((k+1 : ℕ) : ℤ)) * (-((k+1 : ℕ) : ℤ)-1) = 2*(d : ℤ) then 1 else 0
    rw [full_neg_laurent_coeff, PowerSeries.coeff_X_pow]
    simp only [integer_triangular_neg_iff]

theorem jacobi_support_bound (d : ℕ) (k : ℤ)
    (h : k*(k-1)=2*(d : ℤ)) : -(d : ℤ) ≤ k ∧ k ≤ (d : ℤ)+1 := by
  constructor
  · by_contra hk
    have hk' : k ≤ -(d : ℤ)-1 := by omega
    have hmul := mul_nonneg (show 0 ≤ -k-(d : ℤ)-1 by omega) (show 0 ≤ -k+(d : ℤ) by omega)
    nlinarith [sq_nonneg (d : ℤ)]
  · by_contra hk
    have hk' : (d : ℤ)+2 ≤ k := by omega
    have hmul := mul_nonneg (show 0 ≤ k-(d : ℤ)-2 by omega) (show 0 ≤ k+(d : ℤ)+1 by omega)
    nlinarith [sq_nonneg (d : ℤ)]

theorem formal_jacobi_triple_product :
    fullProduct = PowerSeries.mk (fun d =>
      ∑ k ∈ Finset.Icc (-(d : ℤ)) ((d : ℤ)+1),
        if k*(k-1)=2*(d : ℤ) then (LaurentPolynomial.T k : LaurentPolynomial ℤ) else 0) := by
  apply PowerSeries.ext
  intro d
  apply LaurentPolynomial.ext
  intro k
  rw [PowerSeries.coeff_mk, full_jacobi_double_coefficient]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single k]
  · split_ifs <;> simp [LaurentPolynomial.T_apply]
  · intro j hj hne
    split_ifs <;> simp [LaurentPolynomial.T_apply, hne]
  · intro hk
    have hne : ¬ k*(k-1)=2*(d : ℤ) := by
      intro h
      exact hk (Finset.mem_Icc.mpr (jacobi_support_bound d k h))
    simp [hne]

end ArithmeticThetaDurfee
