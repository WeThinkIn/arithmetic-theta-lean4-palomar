module

public import LaurentGammaTranslationR0064
public import LaurentGammaNonzeroR0064
public import LaurentUnpoweredNormR0064
public import LaurentGammaExistenceR0064
public import NormResiduePermutationR0062
public import Mathlib.Algebra.AffineMonoid.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064
open ArithmeticThetaNormFiniteR0063 ArithmeticThetaNormQuotientsR0062

private theorem pn_root_product (F : Type) [Field F] (d : ℕ) (ζ x : F)
    (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    (∏ j : Fin d, -(ζ ^ j.val * x)) = -(x ^ d) := by
  have hf := X_pow_sub_C_eq_prod hζ hd (rfl : x ^ d = x ^ d)
  have he := congrArg (Polynomial.eval (0 : F)) hf
  rw [Fin.prod_univ_eq_prod_range (fun j => -(ζ ^ j * x)) d]
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, zero_pow (Nat.ne_of_gt hd), zero_sub] using he.symm

private theorem pn_residue_bijective (c d : ℕ) (hc : 1 < c) (hd : 0 < d)
    (hcop : Nat.Coprime c d) :
    Function.Bijective (fun i : Fin d => (⟨residue c d i.val, Nat.mod_lt _ hd⟩ : Fin d)) := by
  apply Finite.surjective_iff_bijective.mp
  intro j
  have hj : j.val ∈ Finset.image (residue c d) (Finset.range d) := by
    rw [residue_permutation c d hc hd hcop]
    exact Finset.mem_range.mpr j.isLt
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, Fin.ext he⟩

private theorem pn_scalar_root (K : Type) [Field K] (d : ℕ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ d) : IsPrimitiveRoot (scalar K ζ) d := by
  exact hζ.map_of_injective
    ((algebraMap (LaurentPolynomial K) (Coeff K)).comp LaurentPolynomial.C).injective

private theorem pn_row (K : Type) [Field K] (c d r k : ℕ) (ζ : K)
    (hd : 0 < d) (hcop : Nat.Coprime c d) (hζ : IsPrimitiveRoot ζ d) :
    (∏ j : Fin d,
      (-(HahnSeries.C (a K ζ j.val c) * t (Coeff K) ^ r)) ^ (-(k : ℤ)) *
        Q K d ^ (-triangle k)) =
    (-1 : Series K) ^ (-(k : ℤ)) * z K d ^ (-(c : ℤ) * k) *
      Q K d ^ (-((r : ℤ) * k + (d : ℤ) * triangle k)) := by
  have ht : t (Coeff K) ≠ 0 := by simp [t]
  have hq : Q K d ≠ 0 := pow_ne_zero _ ht
  have hs : IsPrimitiveRoot (HahnSeries.C (scalar K ζ ^ c) : Series K) d :=
    ((pn_scalar_root K d ζ hζ).pow_of_coprime c hcop).map_of_injective
      HahnSeries.C_injective
  have hp := pn_root_product (Series K) d (HahnSeries.C (scalar K ζ ^ c))
    (HahnSeries.C (w K ^ c) * t (Coeff K) ^ r) hd hs
  have he (j : Fin d) :
      HahnSeries.C (a K ζ j.val c) * t (Coeff K) ^ r =
      (HahnSeries.C (scalar K ζ ^ c) : Series K) ^ j.val *
        (HahnSeries.C (w K ^ c) * t (Coeff K) ^ r) := by
    simp only [a, map_mul, map_pow, pow_mul, mul_assoc]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_zpow, hp]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbase : (HahnSeries.C (w K ^ c) * t (Coeff K) ^ r : Series K) ^ d =
      z K d ^ c * Q K d ^ r := by
    simp only [mul_pow, ← map_pow, z, Q]
    congr 1 <;> simp only [← pow_mul, Nat.mul_comm]
  rw [hbase, show -(z K d ^ c * Q K d ^ r) =
    (-1 : Series K) * (z K d ^ c * Q K d ^ r) by ring, mul_zpow, mul_zpow]
  simp only [← zpow_natCast, ← zpow_mul]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ hq]
  ring_nf

private theorem pn_prod_zpow_sum {F : Type} [Field F] {ι : Type}
    (s : Finset ι) (x : F) (hx : x ≠ 0) (e : ι → ℤ) :
    (∏ i ∈ s, x ^ e i) = x ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ hx]

/-- The powered gamma product, with its actual quotient and residue corrections. -/
theorem powered_gamma_norm : ∀ (K : Type) [Field K] [CharZero K]
    (c d : ℕ) (ζ : K), 1 < c → 0 < d → Nat.Coprime c d → IsPrimitiveRoot ζ d →
    ∀ (H : Fin d → Fin d → Series K) (b : Series K),
      (∀ i j : Fin d, IsGamma (Coeff K) d (c * i.val) (a K ζ j.val c) (H i j)) →
      IsGamma (Coeff K) d 0 (w K ^ (c * d)) b →
      (∏ i : Fin d, ∏ j : Fin d, H i j) =
        (-1 : Series K) ^ (-S c d) * z K d ^ (-(c : ℤ) * S c d) *
          Q K d ^ (-E c d) * b := by
  intro K _ _ c d ζ hc hd hcop hζ H b hH hb
  let : CharZero (Coeff K) := charZero_of_injective_ringHom
    ((algebraMap (LaurentPolynomial K) (Coeff K)).comp LaurentPolynomial.C).injective
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hn := coefficient_nonzero K ζ hζ0
  have ha (j : Fin d) : a K ζ j.val c ≠ 0 := (hn.1 j.val c (by omega)).1
  have haeq (j : Fin d) : a K ζ j.val c =
      (scalar K ζ ^ c) ^ j.val * w K ^ c := by simp only [a, pow_mul]
  have hζc : IsPrimitiveRoot (scalar K ζ ^ c) d :=
    (pn_scalar_root K d ζ hζ).pow_of_coprime c hcop
  have hex (i j : Fin d) : ∃ g : Series K,
      IsGamma (Coeff K) d i.val (a K ζ j.val c) g :=
    (gamma_exists_unique (Coeff K) d i.val (a K ζ j.val c) hd (ha j)).exists
  choose G hG using hex
  let R : Fin d → Fin d := fun i => ⟨residue c d i.val, Nat.mod_lt _ hd⟩
  have hnorm : (∏ i : Fin d, ∏ j : Fin d, G (R i) j) = b := by
    rw [Fintype.prod_bijective R (pn_residue_bijective c d hc hd hcop)
      (fun i => ∏ j, G (R i) j) (fun i => ∏ j, G i j) (fun _ => rfl)]
    apply transport_unpowered_norm (Coeff K) d (scalar K ζ ^ c) (w K ^ c)
      hd hζc (hn.2.1 c (by omega)).1 G b
    · intro i j
      simpa only [haeq] using hG i j
    · simpa only [pow_mul] using hb
  have htrans (i j : Fin d) : H i j =
      (-(HahnSeries.C (a K ζ j.val c) * t (Coeff K) ^ (residue c d i.val))) ^
          (-(quotient c d i.val : ℤ)) *
        Q K d ^ (-triangle (quotient c d i.val)) * G (R i) j := by
    apply gamma_translation (Coeff K) d (residue c d i.val) (quotient c d i.val)
      (a K ζ j.val c) hd (Nat.mod_lt _ hd) (ha j) (G (R i) j) (H i j) (hG (R i) j)
    simpa only [residue, quotient, Nat.mod_add_div] using hH i j
  have hrow (i : Fin d) : (∏ j : Fin d, H i j) =
      ((-1 : Series K) ^ (-(quotient c d i.val : ℤ)) *
        z K d ^ (-(c : ℤ) * quotient c d i.val) *
        Q K d ^ (-((residue c d i.val : ℤ) * quotient c d i.val +
          (d : ℤ) * triangle (quotient c d i.val)))) * ∏ j : Fin d, G (R i) j := by
    simp_rw [htrans i]
    rw [Finset.prod_mul_distrib, pn_row K c d _ _ ζ hd hcop hζ]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib, hnorm]
  congr 1
  simp only [Finset.prod_mul_distrib]
  rw [pn_prod_zpow_sum _ _ (neg_ne_zero.mpr one_ne_zero),
    pn_prod_zpow_sum _ _ (hn.2.2.1 d).2,
    pn_prod_zpow_sum _ _ (hn.2.2.1 d).1]
  have hS : (∑ i : Fin d, (quotient c d i.val : ℤ)) = S c d :=
    Fin.sum_univ_eq_sum_range (fun i => (quotient c d i : ℤ)) d
  have hE : (∑ i : Fin d, ((residue c d i.val : ℤ) * quotient c d i.val +
      (d : ℤ) * triangle (quotient c d i.val))) = E c d :=
    Fin.sum_univ_eq_sum_range (fun i => ((residue c d i : ℤ) * quotient c d i +
      (d : ℤ) * triangle (quotient c d i))) d
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, hS, hE]

end ArithmeticThetaLaurentNormR0064
