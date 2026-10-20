module

public import FormalSchrodingerDefinitionsR0119

@[expose] public section

/-! Exact operator laws for the literal bilateral theta coefficients. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

private theorem monomial_mul (k : Type u) [Field k] (a b : ℤ) :
    monomial k a * monomial k b = monomial k (a+b) := by
  simp [monomial, HahnSeries.single_mul_single]

private theorem monomial_zero (k : Type u) [Field k] : monomial k 0 = 1 := by
  simp [monomial]

private theorem scalar_mul (k : Type u) [Field k] (a b : k) :
    scalar k a * scalar k b = scalar k (a*b) := by
  simp [scalar, HahnSeries.single_mul_single]

private theorem scalar_pow (k : Type u) [Field k] (a : k) (n : ℕ) :
    scalar k a ^ n = scalar k (a^n) := by
  simp [scalar, HahnSeries.single_pow]

private theorem zpow_residue (k : Type u) [Field k] (m : ℕ) [NeZero m]
    (ζ : k) (hζ : IsPrimitiveRoot ζ m) (a b : ℤ) (h : Int.ModEq (m : ℤ) a b) :
    ζ ^ a = ζ ^ b := by
  have hz := hζ.ne_zero (NeZero.ne m)
  have per (r : ℤ) : ζ ^ r = ζ ^ (r % (m : ℤ)) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv r (m : ℤ)]
    rw [zpow_add₀ hz, zpow_mul, hζ.zpow_eq_one, one_zpow, mul_one]
  rw [per a, per b, h]

private theorem theta_A (k : Type u) [Field k] (m : ℕ) [NeZero m]
    (ζ : k) (hζ : IsPrimitiveRoot ζ m) (ν : Fin m) :
    A k ζ (theta k m ν) = scalar k (ζ ^ ν.val) • theta k m ν := by
  funext r
  change scalar k (ζ ^ r) * (if Int.ModEq (m : ℤ) r (ν.val : ℤ) then _ else _) =
    scalar k (ζ ^ ν.val) * (if Int.ModEq (m : ℤ) r (ν.val : ℤ) then _ else _)
  split_ifs with h
  · rw [zpow_residue k m ζ hζ r ν.val h, zpow_natCast]
  · simp

private theorem theta_B (k : Type u) [Field k] (m : ℕ) [NeZero m] (ν : Fin m) :
    B k (theta k m ν) = theta k m (next m ν) := by
  have hm (r : ℤ) : Int.ModEq (m : ℤ) (r-1) (ν.val : ℤ) ↔
      Int.ModEq (m : ℤ) r ((next m ν).val : ℤ) := by
    have hn : Int.ModEq (m : ℤ) ((ν.val : ℤ)+1) ((next m ν).val : ℤ) := by
      simp [Int.ModEq, next, Int.natCast_emod]
    constructor
    · intro h
      simpa using (h.add_right 1).trans hn
    · intro h
      simpa using (h.trans hn.symm).sub (Int.ModEq.refl (n := (m : ℤ)) 1)
  funext r
  change monomial k (2*r-1) * (if Int.ModEq (m : ℤ) (r-1) (ν.val : ℤ) then _ else _) =
    (if Int.ModEq (m : ℤ) r ((next m ν).val : ℤ) then _ else _)
  simp only [hm r]
  split_ifs
  · rw [monomial_mul]
    congr 1
    ring
  · simp

private theorem iterate_A (k : Type u) [Field k] (ζ : k) (n : ℕ)
    (f : Coefficients k) (r : ℤ) :
    Nat.iterate (A k ζ) n f r = scalar k (ζ ^ r) ^ n * f r := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change scalar k (ζ ^ r) * Nat.iterate (A k ζ) n f r = _
    rw [ih, pow_succ]
    ring

private theorem iterate_B (k : Type u) [Field k] (n : ℕ)
    (f : Coefficients k) (r : ℤ) :
    Nat.iterate (B k) n f r = monomial k (2*(n : ℤ)*r-(n : ℤ)^2) * f (r-n) := by
  induction n generalizing r with
  | zero => simp [Nat.iterate, monomial_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change monomial k (2*r-1) * Nat.iterate (B k) n f (r-1) = _
    rw [ih, ← mul_assoc, monomial_mul]
    have he : 2*r-1+(2*(n : ℤ)*(r-1)-(n : ℤ)^2) =
        2*((n+1 : ℕ) : ℤ)*r-((n+1 : ℕ) : ℤ)^2 := by push_cast; ring
    have hr : r-1-(n : ℤ) = r-((n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, hr]

theorem theta_operator_laws :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m → ∀ ζ : k,
      IsPrimitiveRoot ζ m →
      (∀ ν : Fin m,
          A k ζ (theta k m ν) = scalar k (ζ ^ ν.val) • theta k m ν ∧
            B k (theta k m ν) = theta k m (next m ν)) ∧
        (∀ f : Coefficients k, f ∈ Solutions k m →
          A k ζ f ∈ Solutions k m ∧ B k f ∈ Solutions k m ∧
          inversion k f ∈ Solutions k m ∧ Nat.iterate (A k ζ) m f = f ∧
          Nat.iterate (B k) m f = f ∧
          A k ζ (B k f) = scalar k ζ • B k (A k ζ f) ∧
          inversion k (A k ζ (inversion k f)) = A k (ζ⁻¹) f ∧
          inversion k (B k (inversion k f)) = BInv k f) := by
  intro k _ _ m _ _hm ζ hζ
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  constructor
  · intro ν
    exact ⟨theta_A k m ζ hζ ν, theta_B k m ν⟩
  · intro f hf
    change (∀ r : ℤ, f (r + m) = monomial k (2 * (m : ℤ) * r + (m : ℤ)^2) * f r) at hf
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ∀ r : ℤ, scalar k (ζ ^ (r+m)) * f (r+m) =
        monomial k (2*(m : ℤ)*r+(m : ℤ)^2) * (scalar k (ζ^r)*f r)
      intro r
      rw [hf r, zpow_add₀ hz, hζ.zpow_eq_one, mul_one]
      ring
    · change ∀ r : ℤ, monomial k (2*(r+m)-1) * f (r+m-1) =
        monomial k (2*(m : ℤ)*r+(m : ℤ)^2) * (monomial k (2*r-1)*f (r-1))
      intro r
      rw [show r+(m : ℤ)-1 = (r-1)+m by ring, hf (r-1)]
      rw [← mul_assoc, ← mul_assoc, monomial_mul, monomial_mul]
      congr 2
      ring
    · change ∀ r : ℤ, f (-(r+m)) =
        monomial k (2*(m : ℤ)*r+(m : ℤ)^2) * f (-r)
      intro r
      have h := hf (-r-m)
      rw [show -r-(m : ℤ)+m = -r by ring] at h
      rw [h, ← mul_assoc, monomial_mul]
      rw [show 2*(m : ℤ)*r+(m : ℤ)^2+(2*m*(-r-m)+(m : ℤ)^2) = 0 by ring,
        monomial_zero, one_mul]
      congr 1
      ring
    · funext r
      rw [iterate_A, scalar_pow]
      have he : (ζ ^ r)^m = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm r, zpow_mul, hζ.zpow_eq_one, one_zpow]
      simp [he, scalar]
    · funext r
      rw [iterate_B]
      have h := hf (r-m)
      rw [show r-(m : ℤ)+m = r by ring] at h
      rw [h]
      congr 2
      ring
    · funext r
      change scalar k (ζ^r) * (monomial k (2*r-1)*f (r-1)) =
        scalar k ζ * (monomial k (2*r-1)*(scalar k (ζ^(r-1))*f (r-1)))
      have he : ζ^r = ζ * ζ^(r-1) := by
        calc
          ζ^r = ζ^(1+(r-1)) := by congr 1; ring
          _ = ζ * ζ^(r-1) := by rw [zpow_add₀ hz, zpow_one]
      rw [he, ← scalar_mul]
      ring
    · funext r
      simp only [inversion, A, neg_neg, zpow_neg, inv_zpow]
    · funext r
      simp only [inversion, B, BInv, neg_sub]
      congr 2 <;> ring

end ArithmeticThetaSchrodingerR0119
