module

public import LaurentGammaExistenceR0064

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaLaurentNormR0064

private def evalAt {F : Type} [Field F] (a : F) (ha : a ≠ 0) :
    LaurentPolynomial F →+* F :=
  LaurentPolynomial.eval₂ (RingHom.id F) (Units.mk0 a ha)

private def mappedSeries {F : Type} [Field F] (a : F) (ha : a ≠ 0)
    (p : PowerSeries (LaurentPolynomial F)) : LaurentSeries F :=
  HahnSeries.ofPowerSeries ℤ F (PowerSeries.map (evalAt a ha) p)

private def mappedHom {F : Type} [Field F] (a : F) (ha : a ≠ 0) :
    PowerSeries (LaurentPolynomial F) →+* LaurentSeries F :=
  (HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map (evalAt a ha))

private theorem evalAt_T {F : Type} [Field F] (a : F) (ha : a ≠ 0) (n : ℤ) :
    evalAt a ha (LaurentPolynomial.T n) = a ^ n := by
  simp [evalAt]

private theorem evalAt_C {F : Type} [Field F] (a : F) (ha : a ≠ 0) (b : F) :
    evalAt a ha (LaurentPolynomial.C b) = b := by
  simp [evalAt]

private theorem partial_as_powerSeries (F : Type) [Field F] (d i : ℕ)
    (a : F) (N : ℕ) (hi : i < d) :
    Partial F d i a N = HahnSeries.ofPowerSeries ℤ F
      (ArithmeticThetaFormalNorm.partialGamma d i a a⁻¹ N) := by
  have hb (l : ℕ) : i ≤ d * (l + 1) := by
    have h := Nat.le_mul_of_pos_right d (by omega : 0 < l + 1)
    omega
  simp only [Partial, ArithmeticThetaFormalNorm.partialGamma, map_mul, map_prod,
    map_sub, map_one, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow]
  simp only [Int.natCast_sub (hb _), Nat.cast_add, Nat.cast_mul]
  simp only [Nat.cast_one]

private theorem isGamma_of_fullGamma (F : Type) [Field F] (d i : ℕ)
    (a : F) (hd : 0 < d) (hi : i < d) :
    IsGamma F d i a (HahnSeries.ofPowerSeries ℤ F
      (ArithmeticThetaFormalNorm.fullGamma d i a a⁻¹)) := by
  intro n
  refine ⟨n.toNat + 1, ?_⟩
  intro N hN e he
  rw [partial_as_powerSeries F d i a N hi]
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hneg
  · rfl
  · exact ArithmeticThetaFormalNorm.partial_stable F d i a a⁻¹
      e.natAbs N hd hi (by omega)

private theorem map_partialGamma {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (d i N : ℕ) (a b : R) :
    PowerSeries.map f (ArithmeticThetaFormalNorm.partialGamma d i a b N) =
      ArithmeticThetaFormalNorm.partialGamma d i (f a) (f b) N := by
  simp [ArithmeticThetaFormalNorm.partialGamma]

private theorem map_fullGamma {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (d i : ℕ) (a b : R) :
    PowerSeries.map f (ArithmeticThetaFormalNorm.fullGamma d i a b) =
      ArithmeticThetaFormalNorm.fullGamma d i (f a) (f b) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, ArithmeticThetaFormalNorm.fullGamma,
    PowerSeries.coeff_mk]
  rw [← PowerSeries.coeff_map, map_partialGamma]

private theorem evalAt_twistA {F : Type} [Field F] (a : F) (ha : a ≠ 0)
    (ζ : F) (j : ℕ) :
    evalAt a ha (ArithmeticThetaFormalNorm.twistA ζ j) = ζ ^ j * a := by
  simp [ArithmeticThetaFormalNorm.twistA, evalAt_C, evalAt_T]

private theorem evalAt_twistB {F : Type} [Field F] (a : F) (ha : a ≠ 0)
    (ζ : F) (j : ℕ) :
    evalAt a ha (ArithmeticThetaFormalNorm.twistB ζ j) = (ζ ^ j * a)⁻¹ := by
  simp only [ArithmeticThetaFormalNorm.twistB, map_mul, evalAt_C, evalAt_T,
    zpow_neg, zpow_one, inv_pow, mul_inv_rev]
  ac_rfl

private theorem mapped_twisted (F : Type) [Field F] (a : F) (ha : a ≠ 0)
    (d i j : ℕ) (ζ : F) :
    mappedHom a ha (ArithmeticThetaFormalNorm.twisted d ζ i j) =
      HahnSeries.ofPowerSeries ℤ F
        (ArithmeticThetaFormalNorm.fullGamma d i (ζ ^ j * a) (ζ ^ j * a)⁻¹) := by
  change mappedSeries a ha (ArithmeticThetaFormalNorm.twisted d ζ i j) = _
  simp only [mappedSeries, ArithmeticThetaFormalNorm.twisted, map_fullGamma,
    evalAt_twistA, evalAt_twistB]

private theorem mapped_base (F : Type) [Field F] (a : F) (ha : a ≠ 0)
    (d : ℕ) :
    mappedHom a ha (ArithmeticThetaFormalNorm.baseGamma F d) =
      HahnSeries.ofPowerSeries ℤ F
        (ArithmeticThetaFormalNorm.fullGamma d 0 (a ^ d) (a ^ d)⁻¹) := by
  change mappedSeries a ha (ArithmeticThetaFormalNorm.baseGamma F d) = _
  simp only [mappedSeries, ArithmeticThetaFormalNorm.baseGamma, map_fullGamma,
    evalAt_T, zpow_natCast, zpow_neg]

private theorem IsGamma.unique {F : Type} [Field F] (d i : ℕ) (a : F)
    {g h : LaurentSeries F} (hg : IsGamma F d i a g)
    (hh : IsGamma F d i a h) : g = h := by
  apply HahnSeries.ext
  funext e
  obtain ⟨N, hN⟩ := hg e
  obtain ⟨M, hM⟩ := hh e
  exact (hN (max N M) (le_max_left _ _) e le_rfl).symm.trans
    (hM (max N M) (le_max_right _ _) e le_rfl)

/-- Evaluation of the accepted formal norm identifies its literal Laurent limits. -/
theorem transport_unpowered_norm : ∀ (F : Type) [Field F] [CharZero F]
    (d : ℕ) (ζ a : F), 0 < d → IsPrimitiveRoot ζ d → a ≠ 0 →
    ∀ (G : Fin d → Fin d → LaurentSeries F) (b : LaurentSeries F),
      (∀ i j : Fin d, IsGamma F d i.val (ζ ^ j.val * a) (G i j)) →
      IsGamma F d 0 (a ^ d) b →
      (∏ i : Fin d, ∏ j : Fin d, G i j) = b := by
  intro F _ _ d ζ a hd hζ ha G b hG hb
  have hfull :
      (∏ i : Fin d, ∏ j : Fin d,
        ArithmeticThetaFormalNorm.twisted d ζ i.val j.val) =
      ArithmeticThetaFormalNorm.baseGamma F d := by
    calc
      _ = ∏ i : Fin d, ∏ j ∈ Finset.range d,
          ArithmeticThetaFormalNorm.twisted d ζ i.val j := by
            apply Finset.prod_congr rfl
            intro i _
            exact Fin.prod_univ_eq_prod_range
              (fun j => ArithmeticThetaFormalNorm.twisted d ζ i.val j) d
      _ = ∏ i ∈ Finset.range d, ∏ j ∈ Finset.range d,
          ArithmeticThetaFormalNorm.twisted d ζ i j := by
            exact Fin.prod_univ_eq_prod_range
              (fun i => ∏ j ∈ Finset.range d,
                ArithmeticThetaFormalNorm.twisted d ζ i j) d
      _ = _ := ArithmeticThetaFormalNorm.full_norm F d ζ hd hζ
  have hnorm := congrArg (mappedHom a ha)
    hfull
  simp only [map_prod] at hnorm
  have hleft (i j : Fin d) :
      mappedHom a ha (ArithmeticThetaFormalNorm.twisted d ζ i.val j.val) = G i j := by
    rw [mapped_twisted]
    exact IsGamma.unique d i.val (ζ ^ j.val * a)
      (isGamma_of_fullGamma F d i.val (ζ ^ j.val * a) hd i.isLt) (hG i j)
  have hright : mappedHom a ha (ArithmeticThetaFormalNorm.baseGamma F d) = b := by
    rw [mapped_base]
    exact IsGamma.unique d 0 (a ^ d)
      (isGamma_of_fullGamma F d 0 (a ^ d) hd hd) hb
  simp_rw [hleft] at hnorm
  rwa [hright] at hnorm

end ArithmeticThetaLaurentNormR0064
