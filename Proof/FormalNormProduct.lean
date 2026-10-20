module

public import Mathlib
public import FormalNormDefinitions

@[expose] public section

namespace ArithmeticThetaFormalNorm

theorem inverse_positive (d i r : ℕ) (hd : 0 < d) (hi : i < d) :
    0 < d * (r + 1) - i := by
  have hmul : d ≤ d * (r + 1) := Nat.le_mul_of_pos_right d (by omega)
  omega

theorem partial_step {R : Type*} [CommRing R] (d i : ℕ) (a b : R) (n N : ℕ)
    (hd : 0 < d) (hi : i < d) (hn : n < N) :
    PowerSeries.coeff n (partialGamma d i a b (N + 1)) =
      PowerSeries.coeff n (partialGamma d i a b N) := by
  have hf : n < d * N + i := by nlinarith
  have hb : n < d * (N + 1) - i := by
    have hN : N ≤ d * N := Nat.le_mul_of_pos_left N hd
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmul (f : PowerSeries R) (c : R) (e : ℕ) (he : n < e) :
      PowerSeries.coeff n (f * (1 - PowerSeries.C c * PowerSeries.X ^ e)) =
        PowerSeries.coeff n f := by
    simp [mul_sub, ← mul_assoc, PowerSeries.coeff_mul_X_pow', show ¬e ≤ n by omega]
  have heq : partialGamma d i a b (N + 1) =
      partialGamma d i a b N * (1 - PowerSeries.C a * PowerSeries.X ^ (d*N+i)) *
        (1 - PowerSeries.C b * PowerSeries.X ^ (d*(N+1)-i)) := by
    simp only [partialGamma, Finset.prod_range_succ]
    ring
  rw [heq, hmul _ b _ hb, hmul _ a _ hf]

theorem partial_stable (R : Type) [CommRing R] (d i : ℕ) (a b : R) (n N : ℕ)
    (hd : 0 < d) (hi : i < d) (hn : n < N) :
    PowerSeries.coeff n (partialGamma d i a b N) =
      PowerSeries.coeff n (fullGamma d i a b) := by
  simp only [fullGamma, PowerSeries.coeff_mk]
  have hle : n + 1 ≤ N := hn
  induction N, hle using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [partial_step d i a b n N hd hi (by omega), ih (by omega)]

theorem root_polynomial (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    (∏ j ∈ Finset.range d, (1 - Polynomial.C (ζ ^ j) * Polynomial.X)) =
      (1 - Polynomial.X ^ d : Polynomial K) := by
  have hp : IsPrimitiveRoot (Polynomial.C ζ) d :=
    hζ.map_of_injective Polynomial.C_injective
  have hfactor := X_pow_sub_C_eq_prod hp hd
    (rfl : (Polynomial.X : Polynomial K)^d = Polynomial.X^d)
  have heval := congrArg (Polynomial.eval (1 : Polynomial K)) hfactor
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Polynomial.eval_C, Polynomial.eval_prod, ← map_pow] using heval.symm

theorem root_product {K S : Type} [Field K] [CharZero K] [CommRing S]
    (d : ℕ) (ζ : K) (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (f : K →+* S) (x : S) :
    (∏ j ∈ Finset.range d, (1 - f (ζ ^ j) * x)) = 1 - x ^ d := by
  have h := congrArg (Polynomial.eval₂RingHom f x)
    (root_polynomial K d ζ hd hζ)
  simpa only [map_prod, map_sub, map_mul, map_one, map_pow,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X] using h

theorem forward_blocks {M : Type} [CommMonoid M] (f : ℕ → M) (d N : ℕ) :
    (∏ i ∈ Finset.range d, ∏ r ∈ Finset.range N, f (d*r+i)) =
      ∏ k ∈ Finset.range (d*N), f k := by
  rw [Finset.prod_comm]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add]

theorem backward_blocks {M : Type} [CommMonoid M] (f : ℕ → M) (d N : ℕ) :
    (∏ i ∈ Finset.range d, ∏ r ∈ Finset.range N, f (d*(r+1)-i)) =
      ∏ k ∈ Finset.range (d*N), f (k+1) := by
  rw [Finset.prod_comm]
  have hreflect (r : ℕ) :
      (∏ i ∈ Finset.range d, f (d*(r+1)-i)) =
        ∏ i ∈ Finset.range d, f (d*r+i+1) := by
    calc
      _ = ∏ i ∈ Finset.range d, f (d*r+(d-1-i)+1) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        congr 1
        rw [Nat.mul_add, Nat.mul_one]
        omega
      _ = _ := Finset.prod_range_reflect (fun i => f (d*r+i+1)) d
  simp_rw [hreflect]
  rw [Finset.prod_comm]
  exact forward_blocks (fun k => f (k+1)) d N

theorem coeff_mul_congr {R : Type*} [CommRing R] (n : ℕ)
    (f f' g g' : PowerSeries R)
    (hf : ∀ k ≤ n, PowerSeries.coeff k f = PowerSeries.coeff k f')
    (hg : ∀ k ≤ n, PowerSeries.coeff k g = PowerSeries.coeff k g') :
    PowerSeries.coeff n (f*g) = PowerSeries.coeff n (f'*g') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega), hg ij.2 (by omega)]

theorem coeff_prod_congr {R A : Type*} [CommRing R] (s : Finset A)
    (f g : A → PowerSeries R) (n : ℕ)
    (h : ∀ a ∈ s, ∀ k ≤ n, PowerSeries.coeff k (f a) =
      PowerSeries.coeff k (g a)) :
    PowerSeries.coeff n (∏ a ∈ s, f a) =
      PowerSeries.coeff n (∏ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    apply coeff_mul_congr
    · exact h a (Finset.mem_insert_self _ _)
    · intro k hk
      apply ih
      intro b hb l hl
      exact h b (Finset.mem_insert_of_mem hb) l (hl.trans hk)

theorem root_factor {K R : Type} [Field K] [CharZero K] [CommRing R]
    (d : ℕ) (ζ : K) (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (f : K →+* R) (a : R) (e : ℕ) :
    (∏ j ∈ Finset.range d,
      (1 - PowerSeries.C (f (ζ ^ j) * a) * PowerSeries.X ^ e)) =
      1 - PowerSeries.C (a ^ d) * PowerSeries.X ^ (e * d) := by
  have h := root_product d ζ hd hζ (PowerSeries.C.comp f)
    (PowerSeries.C a * PowerSeries.X ^ e)
  simpa only [RingHom.comp_apply, map_mul, map_pow, mul_assoc, mul_pow, pow_mul] using h

theorem root_forward (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) (e : ℕ) :
    (∏ j ∈ Finset.range d,
      (1 - PowerSeries.C (twistA ζ j) * PowerSeries.X ^ e)) =
      1 - PowerSeries.C (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial K) *
        PowerSeries.X ^ (d*e) := by
  have h := root_factor d ζ hd hζ LaurentPolynomial.C
    (LaurentPolynomial.T 1) e
  simpa only [twistA, LaurentPolynomial.T_pow, mul_one, Nat.mul_comm e d] using h

theorem root_backward (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) (e : ℕ) :
    (∏ j ∈ Finset.range d,
      (1 - PowerSeries.C (twistB ζ j) * PowerSeries.X ^ e)) =
      1 - PowerSeries.C (LaurentPolynomial.T (-(d : ℤ)) : LaurentPolynomial K) *
        PowerSeries.X ^ (d*e) := by
  have h := root_factor d (ζ⁻¹) hd hζ.inv LaurentPolynomial.C
    (LaurentPolynomial.T (-1)) e
  simpa only [twistB, LaurentPolynomial.T_pow, mul_neg, mul_one, Nat.mul_comm e d] using h

theorem finite_one_residue (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) (i N : ℕ) :
    (∏ j ∈ Finset.range d, partialTwisted d ζ i j N) =
      (∏ r ∈ Finset.range N,
        (1 - PowerSeries.C (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial K) *
          PowerSeries.X ^ (d*(d*r+i)))) *
      (∏ r ∈ Finset.range N,
        (1 - PowerSeries.C (LaurentPolynomial.T (-(d : ℤ)) : LaurentPolynomial K) *
          PowerSeries.X ^ (d*(d*(r+1)-i)))) := by
  simp only [partialTwisted, partialGamma, Finset.prod_mul_distrib]
  rw [Finset.prod_comm, Finset.prod_comm (s := Finset.range d)]
  simp_rw [root_forward K d ζ hd hζ, root_backward K d ζ hd hζ]

theorem finite_norm (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K) (N : ℕ)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    (∏ i ∈ Finset.range d, ∏ j ∈ Finset.range d,
      partialTwisted d ζ i j N) = partialBase K d (d * N) := by
  simp_rw [finite_one_residue K d ζ hd hζ]
  rw [Finset.prod_mul_distrib,
    forward_blocks (fun k => 1 - PowerSeries.C
      (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial K) * PowerSeries.X ^ (d*k)) d N,
    backward_blocks (fun k => 1 - PowerSeries.C
      (LaurentPolynomial.T (-(d : ℤ)) : LaurentPolynomial K) * PowerSeries.X ^ (d*k)) d N]
  simp [partialBase, partialGamma]

theorem full_norm (K : Type) [Field K] [CharZero K] (d : ℕ) (ζ : K)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    (∏ i ∈ Finset.range d, ∏ j ∈ Finset.range d,
      twisted d ζ i j) = baseGamma K d := by
  apply PowerSeries.ext
  intro n
  calc
    _ = PowerSeries.coeff n
        (∏ i ∈ Finset.range d, ∏ j ∈ Finset.range d,
          partialTwisted d ζ i j (n+1)) := by
      apply coeff_prod_congr
      intro i hi k hk
      apply coeff_prod_congr
      intro j hj l hl
      exact (partial_stable (LaurentPolynomial K) d i (twistA ζ j)
        (twistB ζ j) l (n+1) hd (Finset.mem_range.mp hi) (by omega)).symm
    _ = PowerSeries.coeff n (partialBase K d (d*(n+1))) := by
      rw [finite_norm K d ζ (n+1) hd hζ]
    _ = _ := by
      apply partial_stable (LaurentPolynomial K) d 0 _ _ n (d*(n+1)) hd hd
      have hmul := Nat.le_mul_of_pos_left (n+1) hd
      omega

end ArithmeticThetaFormalNorm
