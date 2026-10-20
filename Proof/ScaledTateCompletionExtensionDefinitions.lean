module

public import ScaledTateNodeBridgeDefinitions

@[expose] public section

/-! Ordinary carriers and maps for the r0048 completion-extension scope.
All continuity, tower compatibility, completion, separation, and uniqueness
claims remain frozen proof obligations; this module only fixes their objects. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaScaledTateCompletionExtensionR0048

open ArithmeticThetaScaledTateBridgeR0046

variable (k : Type u) [Field k]

def targetIdeal : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}

def baseMap : ArithmeticThetaScaledTateBridgeR0046.Base k →+* PowerSeries k :=
  RingHom.id (PowerSeries k)

def nodeMap (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0) : ArithmeticThetaScaledTateBridgeR0046.Node k r →+* PowerSeries k := by
  let f : ArithmeticThetaScaledTateBridgeR0046.PolynomialChart k →+* PowerSeries k :=
    MvPolynomial.eval₂Hom (baseMap k)
      (fun q : Fin 2 =>
        if q = (0 : Fin 2) then PowerSeries.C a * PowerSeries.X ^ i
        else PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i))
  exact Ideal.Quotient.lift (ArithmeticThetaScaledTateBridgeR0046.relationIdeal k r) f (by
    intro q hq
    change q ∈ Ideal.span {ArithmeticThetaScaledTateBridgeR0046.relation k r} at hq
    rw [Ideal.mem_span_singleton] at hq
    obtain ⟨v, rfl⟩ := hq
    simp only [Set.mem_singleton_iff, ArithmeticThetaScaledTateBridgeR0046.relation]
    dsimp [f]
    rw [MvPolynomial.eval₂_mul]
    have hrel :
        MvPolynomial.eval₂ (baseMap k)
            (fun q : Fin 2 =>
              if q = (0 : Fin 2) then PowerSeries.C a * PowerSeries.X ^ i
              else PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i))
            (MvPolynomial.X 0 * MvPolynomial.X 1 -
              MvPolynomial.C (ArithmeticThetaScaledTateBridgeR0046.parameter k r)) = 0 := by
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul]
      simp only [MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, if_pos rfl]
      change PowerSeries.C a * PowerSeries.X ^ i *
          (PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i)) - PowerSeries.X ^ r = 0
      have hsum : i + (r - i) = r := Nat.add_sub_of_le (Nat.le_of_lt hi)
      have hprod : PowerSeries.C a * PowerSeries.X ^ i *
          (PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i)) = PowerSeries.X ^ r := by
        calc
          PowerSeries.C a * PowerSeries.X ^ i *
              (PowerSeries.C a⁻¹ * PowerSeries.X ^ (r - i)) =
              (PowerSeries.C a * PowerSeries.C a⁻¹) *
                (PowerSeries.X ^ i * PowerSeries.X ^ (r - i)) := by ring
          _ = 1 * PowerSeries.X ^ r := by
            rw [show PowerSeries.C a * PowerSeries.C a⁻¹ = 1 by
              simpa using congrArg PowerSeries.C (mul_inv_cancel₀ ha),
              ← pow_add, hsum]
          _ = PowerSeries.X ^ r := one_mul _
      exact sub_eq_zero.mpr hprod
    rw [hrel, zero_mul])

def nodeMapQuot (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0) (n : ℕ) :
    ArithmeticThetaScaledTateBridgeR0046.Node k r →+*
      PowerSeries k ⧸ (targetIdeal k) ^ n :=
  (Ideal.Quotient.mk ((targetIdeal k) ^ n)).comp (nodeMap k r i hr hi a ha)

def nodeMapMod (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0)
    (hcont : ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
      Ideal.comap (nodeMap k r i hr hi a ha) (targetIdeal k))
    (n : ℕ) :
    ArithmeticThetaScaledTateBridgeR0046.Node k r ⧸
        (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n →+*
      PowerSeries k ⧸ (targetIdeal k) ^ n := by
  let g := nodeMap k r i hr hi a ha
  let q : ArithmeticThetaScaledTateBridgeR0046.Node k r →+*
      PowerSeries k ⧸ (targetIdeal k) ^ n :=
    (Ideal.Quotient.mk ((targetIdeal k) ^ n)).comp g
  have hpow : (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n ≤
      Ideal.comap g ((targetIdeal k) ^ n) :=
    (pow_le_pow_left' hcont n).trans (Ideal.le_comap_pow g n)
  exact Ideal.Quotient.lift ((ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) ^ n) q (by
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact hpow hz)

def compFamily (r i : ℕ) (hr : 0 < r) (hi : i < r)
    (a : k) (ha : a ≠ 0)
    (hcont : ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r ≤
      Ideal.comap (nodeMap k r i hr hi a ha) (targetIdeal k))
    (n : ℕ) : ArithmeticThetaScaledTateBridgeR0046.CompletedNode k r →+*
      PowerSeries k ⧸ (targetIdeal k) ^ n :=
  (nodeMapMod k r i hr hi a ha hcont n).comp
    (AdicCompletion.evalₐ (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k r) n).toRingHom

end ArithmeticThetaScaledTateCompletionExtensionR0048
