module

public import SubstitutedTorsionDifferencesR0108
public import FourTorsionRoot

@[expose] public section

noncomputable section
universe u
namespace ArithmeticThetaAllCuspR0108

/-- A Laurent square root of a power series is itself a power series. -/
private lemma square_root_regular (k : Type u) [Field k]
    (a : LaurentSeries k) (b : PowerSeries k)
    (h : a ^ 2 = ArithmeticThetaTateSeries.toLaurent k b) :
    ∃ f : PowerSeries k, ArithmeticThetaTateSeries.toLaurent k f = a := by
  apply IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := PowerSeries k)
    (n := 2) (by decide)
  rw [h]
  exact isIntegral_algebraMap

/-- Regularity and exact order for every actual half and every marking. -/
theorem all_half_formal_regularity :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq (LaurentSeries k)]
      (w : PowerSeries k), w ≠ 0 → PowerSeries.constantCoeff w = 0 →
      ∀ (σ : Equiv.Perm (Fin 3))
        (hP : (markedCurve k w σ).Nonsingular (rootValue k w (σ 1)) 0)
        (R : (markedCurve k w σ).Point),
        2 • R = WeierstrassCurve.Affine.Point.some (rootValue k w (σ 1)) 0 hP →
        ∃ (x y : LaurentSeries k) (hR : (markedCurve k w σ).Nonsingular x y)
          (f : PowerSeries k),
          R = WeierstrassCurve.Affine.Point.some x y hR ∧ y ≠ 0 ∧ f ≠ 0 ∧
          (ArithmeticThetaTateSeries.toLaurent k) f = alphaCoefficient k w σ x y ∧
          f.order = (if σ 0 = 0 ∨ σ 1 = 0 then 0 else w.order) := by
  intro k _ _ _ w hw hw0 σ hP R hd
  have : CharZero (LaurentSeries k) :=
    charZero_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective
  have : CharZero (PowerSeries k) :=
    charZero_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective
  have hinj : Function.Injective (ArithmeticThetaTateSeries.toLaurent k) :=
    HahnSeries.ofPowerSeries_injective
  have hne : ∀ i j : Fin 3, i ≠ j → rootValue k w (σ i) ≠ rootValue k w (σ j) := by
    intro i j hij heq
    apply (substituted_two_torsion_differences k w hw hw0 (σ i) (σ j)
      (σ.injective.ne hij)).1
    exact sub_eq_zero.mpr (hinj heq)
  obtain ⟨x, y, hR, hRx, hy, hsquare, _⟩ :=
    ArithmeticThetaFourTorsion.actual_half_root (LaurentSeries k)
      (rootValue k w (σ 0)) (rootValue k w (σ 1)) (rootValue k w (σ 2))
      hP R (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide)) hd
  let d := rootSeries k w (σ 1) - rootSeries k w (σ 0)
  have hd0 : d ≠ 0 :=
    (substituted_two_torsion_differences k w hw hw0 (σ 1) (σ 0)
      (σ.injective.ne (by decide))).1
  have hdo : d.order = if σ 0 = 0 ∨ σ 1 = 0 then 0 else 2 * w.order := by
    simpa only [or_comm] using
      (substituted_two_torsion_differences k w hw hw0 (σ 1) (σ 0)
        (σ.injective.ne (by decide))).2
  have ha : (alphaCoefficient k w σ x y)^2 =
      ArithmeticThetaTateSeries.toLaurent k (4 * d) := by
    rw [alphaCoefficient, mul_pow, hsquare]
    simp only [map_mul, map_ofNat, map_sub, d, rootValue]
    ring
  obtain ⟨f, hf⟩ := square_root_regular k (alphaCoefficient k w σ x y) (4 * d) ha
  have hfsq : f ^ 2 = 4 * d := by
    apply hinj
    rw [map_pow, hf, ha]
  have hf0 : f ≠ 0 := by
    intro hz
    have : (4 : PowerSeries k) * d = 0 := by simpa [hz] using hfsq.symm
    exact (mul_ne_zero (by norm_num) hd0) this
  have hfour : (4 : PowerSeries k).order = 0 := by
    apply (PowerSeries.order_eq_nat (n := 0)).2
    constructor
    · norm_num [map_ofNat]
    · simp
  have ho := congrArg PowerSeries.order hfsq
  rw [PowerSeries.order_pow, PowerSeries.order_mul, hfour, zero_add, hdo] at ho
  refine ⟨x, y, hR, f, hRx, hy, hf0, hf, ?_⟩
  rw [← PowerSeries.coe_toNat_order hf0, ← PowerSeries.coe_toNat_order hw] at ho ⊢
  simp only [nsmul_eq_mul] at ho
  split_ifs at ho ⊢ with hcase
  · have he : 2 * f.order.toNat = 0 := by exact_mod_cast ho
    have : f.order.toNat = 0 := by omega
    simp [this]
  · have he : 2 * f.order.toNat = 2 * w.order.toNat := by exact_mod_cast ho
    have : f.order.toNat = w.order.toNat := by omega
    rw [this]

end ArithmeticThetaAllCuspR0108
