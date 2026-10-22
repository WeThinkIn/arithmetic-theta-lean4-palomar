module

public import TateSeriesDefinitions
public import UnaryThetaProduct
public import FormalNormDefinitions
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval

@[expose] public section

/-! The literal theta series, its Jacobi product, and the gamma normalization. -/
noncomputable section
universe u
namespace ArithmeticThetaTateIdentities
open ArithmeticThetaUnaryProduct ArithmeticThetaFormalNorm

lemma integer_square_count (n : ℕ) :
    (∑ z ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) + 1),
      if z^2 = (n : ℤ) then (1 : ℤ) else 0) =
    (if n = 0 then 1 else 0) +
      2 * ((Finset.Icc 1 n).filter (fun j : ℕ => j^2 = n)).card := by
  classical
  let f : ℤ → ℤ := fun z => if z^2 = (n : ℤ) then 1 else 0
  have heven : f.Even := by intro z; simp [f]
  have htrim : ∑ z ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) + 1), f z =
      ∑ z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f z := by
    symm
    apply Finset.sum_subset
    · intro z hz; simp only [Finset.mem_Icc] at hz ⊢; omega
    · intro z hz hn
      have hz' : z = (n : ℤ) + 1 := by
        simp only [Finset.mem_Icc] at hz hn
        omega
      rw [hz']
      apply if_neg
      have hn0 : (0 : ℤ) ≤ n := by positivity
      nlinarith
  change (∑ z ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) + 1), f z) = _
  rw [htrim, Finset.sum_Icc_of_even_eq_range heven]
  have hr : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp)]
  have hc : (∑ j ∈ Finset.Icc 1 n, f j) =
      (((Finset.Icc 1 n).filter (fun j : ℕ => j^2 = n)).card : ℤ) := by
    simp only [f, ← Nat.cast_pow, Nat.cast_inj]
    rw [← Finset.sum_filter]
    simp
  rw [hc]
  have hf0 : f 0 = if n = 0 then 1 else 0 := by simp [f, eq_comm]
  simp only [Nat.cast_zero, hf0, nsmul_eq_mul]
  ring

lemma theta_eq_specialized {k : Type u} [Field k] :
    ArithmeticThetaTateSeries.theta k =
      PowerSeries.map (Int.castRingHom k) (specializedProduct 2 1) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, specialized_product_coefficient 2 1 (by decide)]
  have he (z : ℤ) : (2 : ℤ)*z*(z-1)+2*1*z=2*(n : ℤ) ↔ z^2=(n : ℤ) := by
    constructor <;> intro h <;> nlinarith
  simp only [Nat.cast_ofNat, Nat.cast_one, he]
  rw [integer_square_count]
  simp [ArithmeticThetaTateSeries.theta, PowerSeries.coeff_mk]

lemma mapped_siegel_partial {k : Type u} [Field k] (N : ℕ) :
    partialGamma 2 1 (-1 : k) ((-1 : k)⁻¹) (N+1) =
      PowerSeries.map (Int.castRingHom k) (siegelPartial 2 1 N) *
        (1 + PowerSeries.X^(2*(N+1)-1)) := by
  simp only [partialGamma, inv_neg, inv_one, map_neg, map_one, neg_mul, sub_neg_eq_add,
    one_mul, siegelPartial, map_mul, map_add, map_pow, PowerSeries.map_X, map_prod]
  rw [Finset.prod_range_succ' (fun r => (1 : PowerSeries k) + PowerSeries.X^(2*r+1)),
    Finset.prod_range_succ]
  simp only [mul_zero, zero_add, Finset.prod_mul_distrib]
  ring

lemma siegel_eq_gamma {k : Type u} [Field k] :
    PowerSeries.map (Int.castRingHom k) (siegelProduct 2 1) =
      fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹) := by
  apply PowerSeries.ext
  intro n
  rw [fullGamma, PowerSeries.coeff_mk, mapped_siegel_partial]
  have hn : ¬ 2*(n+1)-1 ≤ n := by omega
  rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow', if_neg hn, add_zero]
  simp only [PowerSeries.coeff_map, siegelProduct, PowerSeries.coeff_mk]

/-- Both all-degree identities, with the literal zero-index normalization. -/
theorem theta_jacobi_bridge : ∀ {k : Type u} [Field k] [CharZero k],
    ArithmeticThetaTateSeries.theta k =
      PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.specializedProduct 2 1) ∧
    ArithmeticThetaTateSeries.theta k =
      (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct 2)) *
        (ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹)) := by
  intro k _ _
  refine ⟨theta_eq_specialized, ?_⟩
  rw [theta_eq_specialized, ← eta_mul_siegel 2 1 (by decide), map_mul, siegel_eq_gamma]

end ArithmeticThetaTateIdentities
#print axioms ArithmeticThetaTateIdentities.theta_jacobi_bridge
