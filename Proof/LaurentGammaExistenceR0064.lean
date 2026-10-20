module

public import LaurentNormDefinitionsR0064

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064

/-- The nonnegative tail after the first `m` factors on each side. -/
def existenceTail (F : Type) [Field F] (d m : ℕ) (a : F) (N : ℕ) : PowerSeries F :=
  (∏ l ∈ Finset.range N,
    (1 - PowerSeries.C a * PowerSeries.X ^ (d * (m + l) + m))) *
  (∏ l ∈ Finset.range N,
    (1 - PowerSeries.C a⁻¹ * PowerSeries.X ^ (d * (m + l + 1) - m)))

theorem existenceTail_step (F : Type) [Field F] (d m : ℕ) (a : F)
    (n N : ℕ) (hd : 0 < d) (hn : n < N) :
    PowerSeries.coeff n (existenceTail F d m a (N + 1)) =
      PowerSeries.coeff n (existenceTail F d m a N) := by
  have hf : n < d * (m + N) + m := by
    have := Nat.le_mul_of_pos_left (m + N) hd
    omega
  have hb : n < d * (m + N + 1) - m := by
    have := Nat.le_mul_of_pos_left (m + N + 1) hd
    omega
  have hmul (f : PowerSeries F) (b : F) (e : ℕ) (he : n < e) :
      PowerSeries.coeff n (f * (1 - PowerSeries.C b * PowerSeries.X ^ e)) =
        PowerSeries.coeff n f := by
    calc
      _ = PowerSeries.coeff n (f * 1) := by
        apply ArithmeticThetaFormalNorm.coeff_mul_congr
        · intro k hk
          rfl
        · intro k hk
          simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
            show k ≠ e by omega]
      _ = _ := by rw [mul_one]
  have heq : existenceTail F d m a (N + 1) =
      existenceTail F d m a N *
        (1 - PowerSeries.C a * PowerSeries.X ^ (d * (m + N) + m)) *
        (1 - PowerSeries.C a⁻¹ * PowerSeries.X ^ (d * (m + N + 1) - m)) := by
    simp only [existenceTail, Finset.prod_range_succ]
    ring
  rw [heq, hmul _ _ _ hb, hmul _ _ _ hf]

def existenceTailLimit (F : Type) [Field F] (d m : ℕ) (a : F) : PowerSeries F :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (existenceTail F d m a (n + 1)))

theorem existenceTail_stable (F : Type) [Field F] (d m : ℕ) (a : F)
    (n N : ℕ) (hd : 0 < d) (hn : n < N) :
    PowerSeries.coeff n (existenceTail F d m a N) =
      PowerSeries.coeff n (existenceTailLimit F d m a) := by
  simp only [existenceTailLimit, PowerSeries.coeff_mk]
  have hle : n + 1 ≤ N := hn
  induction N, hle using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [existenceTail_step F d m a n N hd (by omega), ih (by omega)]

/-- Literal product splitting, with the integer subtraction retained on the head. -/
theorem existence_partial_split (F : Type) [Field F] (d m : ℕ) (a : F)
    (N : ℕ) (hd : 0 < d) :
    Partial F d m a (m + N) =
      Partial F d m a m * HahnSeries.ofPowerSeries ℤ F (existenceTail F d m a N) := by
  have hb (l : ℕ) : m ≤ d * (m + l + 1) := by
    have := Nat.le_mul_of_pos_left (m + l + 1) hd
    omega
  simp only [Partial, existenceTail, Finset.prod_range_add, map_mul, map_prod,
    map_sub, map_one, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Int.natCast_sub (hb _)]
  ring

/-- Multiplication by a fixed Laurent series preserves uniform lower-coefficient agreement. -/
theorem existence_head_coeff (F : Type) [Field F] (H : LaurentSeries F)
    (u v : PowerSeries F) (n e : ℤ) (he : e ≤ n)
    (h : ∀ k : ℕ, k ≤ (n - H.order).toNat →
      PowerSeries.coeff k u = PowerSeries.coeff k v) :
    (H * HahnSeries.ofPowerSeries ℤ F u).coeff e =
      (H * HahnSeries.ofPowerSeries ℤ F v).coeff e := by
  have hu : H * HahnSeries.ofPowerSeries ℤ F u =
      HahnSeries.single H.order 1 *
        HahnSeries.ofPowerSeries ℤ F (H.powerSeriesPart * u) := by
    rw [map_mul, ← mul_assoc, LaurentSeries.single_order_mul_powerSeriesPart]
  have hv : H * HahnSeries.ofPowerSeries ℤ F v =
      HahnSeries.single H.order 1 *
        HahnSeries.ofPowerSeries ℤ F (H.powerSeriesPart * v) := by
    rw [map_mul, ← mul_assoc, LaurentSeries.single_order_mul_powerSeriesPart]
  rw [hu, hv, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul, one_mul]
  change ((H.powerSeriesPart * u : PowerSeries F) : LaurentSeries F).coeff _ =
    ((H.powerSeriesPart * v : PowerSeries F) : LaurentSeries F).coeff _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hneg
  · rfl
  · apply ArithmeticThetaFormalNorm.coeff_mul_congr
    · intro k hk
      rfl
    · intro k hk
      apply h k
      have habs : ((e - H.order).natAbs : ℤ) = e - H.order :=
        by simp only [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ e - H.order)]
      omega

/-- Coefficientwise existence and uniqueness for the literal Laurent gamma product. -/
theorem gamma_exists_unique : ∀ (F : Type) [Field F] (d m : ℕ) (a : F),
    0 < d → a ≠ 0 → ∃! g : LaurentSeries F, IsGamma F d m a g := by
  intro F _ d m a hd _ha
  let H := Partial F d m a m
  let g := H * HahnSeries.ofPowerSeries ℤ F (existenceTailLimit F d m a)
  have hg : IsGamma F d m a g := by
    intro n
    refine ⟨m + (n - H.order).toNat + 1, ?_⟩
    intro N hN e he
    have hmN : m ≤ N := by omega
    have hsplit := existence_partial_split F d m a (N - m) hd
    rw [Nat.add_sub_of_le hmN] at hsplit
    rw [hsplit]
    apply existence_head_coeff F H _ _ n e he
    intro k hk
    apply existenceTail_stable F d m a k (N - m) hd
    omega
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply HahnSeries.ext
  funext e
  obtain ⟨N, hN⟩ := hg e
  obtain ⟨M, hM⟩ := hg' e
  exact (hM (max N M) (le_max_right _ _) e le_rfl).symm.trans
    (hN (max N M) (le_max_left _ _) e le_rfl)

end ArithmeticThetaLaurentNormR0064
