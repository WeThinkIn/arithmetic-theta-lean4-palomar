import CompleteMillerDivisorR0116
import EllipticTameReciprocityR0116

/-! The moved-support calculation for the normalized fourth-order Miller functions. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open WeierstrassCurve.Affine

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

private lemma labelled_half_nonzero (i : Fin 3) (P : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e i P) : P ≠ 0 := by
  intro h
  obtain ⟨hp, hd⟩ := hP
  rw [h, smul_zero] at hd
  exact (Point.some_ne_zero hp) hd.symm

private lemma labelled_half_four (i : Fin 3) (P : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e i P) : 4 • P = 0 := by
  obtain ⟨hp, hd⟩ := hP
  calc
    4 • P = 2 • (2 • P) := by rw [← mul_nsmul]
    _ = 2 • Point.some (e i) 0 hp := by rw [hd]
    _ = 0 := by
      rw [two_nsmul]
      apply Point.add_self_of_Y_eq
      simp [WeierstrassCurve.Affine.negY, Curve,
        ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve]

private lemma labelled_halves_independent (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    P ≠ Q ∧ P ≠ 2 • Q ∧ 2 • Q ≠ P := by
  obtain ⟨hp, hdP⟩ := hP
  obtain ⟨hq, hdQ⟩ := hQ
  have hd : 2 • P ≠ 2 • Q := by
    rw [hdP, hdQ]
    intro h
    have hx := (Point.some.inj h).1
    exact (by decide : (0 : Fin 3) ≠ 1) (he hx)
  have hP2 : 2 • P ≠ 0 := by rw [hdP]; exact Point.some_ne_zero hp
  have hQ4 : 4 • Q = 0 := labelled_half_four k e 1 Q ⟨hq, hdQ⟩
  have hQ2 : 2 • (2 • Q) = 0 := by
    rw [← mul_nsmul]
    norm_num at hQ4 ⊢
    exact hQ4
  refine ⟨fun h => hd (congrArg (2 • ·) h), ?_, ?_⟩
  · intro h
    exact hP2 (by rw [h, hQ2])
  · intro h
    exact hP2 (by rw [← h, hQ2])

private lemma goodShift_Q (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    GoodShift k e P Q Q := by
  have hN := labelled_halves_independent k e he P Q hP hQ
  have hQ0 := labelled_half_nonzero k e 1 Q hQ
  have h2Q0 : 2 • Q ≠ 0 := by
    obtain ⟨hq, hdQ⟩ := hQ
    rw [hdQ]
    exact Point.some_ne_zero hq
  simpa only [GoodShift, ← two_nsmul] using
    (show Q ≠ 0 ∧ Q ≠ P ∧ 2 • Q ≠ 0 ∧ 2 • Q ≠ P from
      ⟨hQ0, hN.1.symm, h2Q0, hN.2.2⟩)

private lemma localValue_ne_zero_of_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) (hf : f ≠ 0)
    (ho : pointOrder k e T E f P = 0) : localValue k e T E f P ≠ 0 := by
  have hn := localLeading_ne_zero k e T E P hf
  unfold localValue localLeading pointOrder expansion at *
  rw [HahnSeries.leadingCoeff_eq, ho] at hn
  exact hn

/-- Off its displayed denominator, the local value is the usual tangent quotient. -/
lemma miller_localValue_of_x_ne (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (i : Fin 3) (x y a b : k) (hp : (Curve k e).Nonsingular a b)
    (ha : a ≠ e i) :
    localValue k e T E (ArithmeticThetaMillerR0114.millerFunction k e i x y)
      (.some a b hp) = ArithmeticThetaMillerR0114.millerValue k e i x y a b := by
  let sx := localX k e h a b
  let sy := localY k e h a b
  let m := ArithmeticThetaMillerR0114.tangentSlope k e x y
  let L := algebraMap (PowerSeries k) (LaurentSeries k)
  have hxy := translated_coordinate_series k e T hT h E hh hE a b hp
  have hc := localXY_constant k e hh.1 a b
  change PowerSeries.constantCoeff sx = a ∧ PowerSeries.constantCoeff sy = b at hc
  have hden : PowerSeries.constantCoeff (sx - PowerSeries.C (e i)) ≠ 0 := by
    simpa [sx, hc.1] using (sub_ne_zero.mpr ha)
  have htan : algebraMap (ArithmeticThetaMillerR0114.Coord k e) (FF k e)
      (ArithmeticThetaMillerR0114.tangentClass k e x y) =
      ArithmeticThetaMillerR0114.yFunction k e - algebraMap k (FF k e) m *
        (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x) -
        algebraMap k (FF k e) y := by
    simp only [ArithmeticThetaMillerR0114.tangentClass,
      ArithmeticThetaMillerR0114.yFunction, ArithmeticThetaMillerR0114.xFunction,
      WeierstrassCurve.Affine.CoordinateRing.YClass,
      WeierstrassCurve.Affine.CoordinateRing.XClass,
      WeierstrassCurve.Affine.linePolynomial, map_zero, sub_zero,
      map_add, map_sub, map_mul]
    rw [sub_add_eq_sub_sub]
    rfl
  have hseries : expansion k e T E
      (.some a b hp) (ArithmeticThetaMillerR0114.millerFunction k e i x y) =
      L (((sy - PowerSeries.C m * (sx - PowerSeries.C x) - PowerSeries.C y) ^ 2) *
        (sx - PowerSeries.C (e i))⁻¹) := by
    unfold ArithmeticThetaMillerR0114.millerFunction expansion
    rw [htan, div_eq_mul_inv]
    simp only [map_mul, map_pow, map_sub, map_inv₀, AlgEquiv.commutes,
      AlgHom.commutes]
    change (expansion k e T E (.some a b hp)
      (ArithmeticThetaMillerR0114.yFunction k e) -
      algebraMap k (LaurentSeries k) m *
        (expansion k e T E (.some a b hp)
          (ArithmeticThetaMillerR0114.xFunction k e) - algebraMap k (LaurentSeries k) x) -
      algebraMap k (LaurentSeries k) y) ^ 2 *
      (expansion k e T E (.some a b hp)
        (ArithmeticThetaMillerR0114.xFunction k e) - algebraMap k (LaurentSeries k) (e i))⁻¹ = _
    rw [hxy.1, hxy.2]
    rw [series_inv_map k (sx - PowerSeries.C (e i)) hden]
    simp only [map_mul, map_sub, map_pow]
    rfl
  rw [localValue, hseries]
  change (HahnSeries.ofPowerSeries ℤ k
    ((sy - PowerSeries.C m * (sx - PowerSeries.C x) - PowerSeries.C y) ^ 2 *
      (sx - PowerSeries.C (e i))⁻¹)).coeff 0 = _
  have hcoeff := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
    ((sy - PowerSeries.C m * (sx - PowerSeries.C x) - PowerSeries.C y) ^ 2 *
      (sx - PowerSeries.C (e i))⁻¹) 0
  simp only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff] at hcoeff
  rw [hcoeff]
  simp only [map_mul, map_pow, map_sub, PowerSeries.constantCoeff_inv,
    PowerSeries.constantCoeff_C, hc.1, hc.2]
  change (b - m * (a - x) - y) ^ 2 * (a - e i)⁻¹ =
    ArithmeticThetaMillerR0114.millerValue k e i x y a b
  simp only [ArithmeticThetaMillerR0114.millerValue,
    ArithmeticThetaMillerR0114.tangentValue, div_eq_mul_inv]
  ring

private lemma moved_values_nonzero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z) :
    localValue k e T E (millerAt k e 0 P) (Q + Z) ≠ 0 ∧
    localValue k e T E (millerAt k e 0 P) Z ≠ 0 ∧
    localValue k e T E (millerAt k e 1 Q) (-Z) ≠ 0 ∧
    localValue k e T E (millerAt k e 1 Q) (P - Z) ≠ 0 := by
  have hdivP := complete_miller_divisor k e he T hT h E hh hE 0 P hP
  have hdivQ := complete_miller_divisor k e he T hT h E hh hE 1 Q hQ
  have hneg0 : -Z ≠ 0 := by
    intro hz
    exact hZ.1 (neg_eq_zero.mp hz)
  have hnegQ : -Z ≠ Q := by
    intro hz
    apply hZ.2.2.1
    calc
      Q + Z = -Z + Z := by rw [hz]
      _ = 0 := neg_add_cancel Z
  have hsub0 : P - Z ≠ 0 := by
    intro hz
    exact hZ.2.1 (sub_eq_zero.mp hz).symm
  have hsubQ : P - Z ≠ Q := by
    intro hz
    apply hZ.2.2.2
    calc
      Q + Z = (P - Z) + Z := by rw [hz]
      _ = P := sub_add_cancel P Z
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply localValue_ne_zero_of_order_zero k e T E _ _ hdivP.1
    rw [hdivP.2.1]
    simp [hZ.2.2.2, hZ.2.2.1]
  · apply localValue_ne_zero_of_order_zero k e T E _ _ hdivP.1
    rw [hdivP.2.1]
    simp [hZ.2.1, hZ.1]
  · apply localValue_ne_zero_of_order_zero k e T E _ _ hdivQ.1
    rw [hdivQ.2.1]
    simp [hnegQ, hneg0]
  · apply localValue_ne_zero_of_order_zero k e T E _ _ hdivQ.1
    rw [hdivQ.2.1]
    simp [hsubQ, hsub0]

private lemma fixed_phase_primitive (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    IsPrimitiveRoot (fixedLabelPhase k e P Q) 4 := by
  cases P with
  | zero => exact False.elim ((labelled_half_nonzero k e 0 0 hP) rfl)
  | @some x y hp =>
    cases Q with
    | zero => exact False.elim ((labelled_half_nonzero k e 1 0 hQ) rfl)
    | @some a b hq =>
      have hp' : ArithmeticThetaMillerR0114.IsHalf k e 0 x y :=
        ⟨hp, hP.1, hP.2⟩
      have hq' : ArithmeticThetaMillerR0114.IsHalf k e 1 a b :=
        ⟨hq, hQ.1, hQ.2⟩
      exact (ArithmeticThetaMillerR0114.actual_miller_phase k e he x y a b hp' hq').2

private lemma translated_miller_order (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (Q Z A : (Curve k e).Point)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    pointOrder k e T E (T (-Z) (millerAt k e 1 Q)) A =
      (if A = Q + Z then 4 else 0) - (if A = Z then 4 else 0) := by
  have hdivQ := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).2.1
  rw [(principal_divisor_support k e he T hT h E hh hE
    (millerAt k e 1 Q)
    (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).1).2]
  rw [hdivQ]
  have h1 : (A + -Z = Q) ↔ A = Q + Z := by
    constructor
    · intro ha
      calc
        A = (A + -Z) + Z := by abel
        _ = Q + Z := by rw [ha]
    · intro ha
      rw [ha]
      abel
  have h2 : (A + -Z = 0) ↔ A = Z := by
    constructor
    · intro ha
      calc
        A = (A + -Z) + Z := by abel
        _ = Z := by rw [ha]; abel
    · intro ha
      rw [ha]
      abel
  simp only [sub_eq_add_neg, h1, h2]

private lemma translated_miller_value (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (E : FF k e →ₐ[k] LaurentSeries k)
    (Q Z A : (Curve k e).Point) :
    localValue k e T E (T (-Z) (millerAt k e 1 Q)) A =
      localValue k e T E (millerAt k e 1 Q) (A - Z) := by
  simp only [localValue, expansion, sub_eq_add_neg]
  rw [(translation_composition k e he T hT).2.1 A (-Z)]

private lemma moved_tame_support (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    Function.mulSupport (fun A =>
      tameSymbol k e T E (millerAt k e 0 P)
        (T (-Z) (millerAt k e 1 Q)) A) ⊆
      ({P, 0, Q + Z, Z} : Set (Curve k e).Point) := by
  intro A hA
  by_contra hn
  have hne : A ≠ P ∧ A ≠ 0 ∧ A ≠ Q + Z ∧ A ≠ Z := by
    simpa using hn
  have hoP := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.1 A
  have hoQ := translated_miller_order k e he T hT h E hh hE Q Z A hQ
  have hzP : pointOrder k e T E (millerAt k e 0 P) A = 0 := by
    simpa [hne.1, hne.2.1] using hoP
  have hzQ : pointOrder k e T E (T (-Z) (millerAt k e 1 Q)) A = 0 := by
    simpa [hne.2.2.1, hne.2.2.2] using hoQ
  exact hA (tameSymbol_eq_one_of_orders_eq_zero k e T E A _ _ hzP hzQ)

private lemma localLeading_eq_localValue_of_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (A : (Curve k e).Point)
    (ho : pointOrder k e T E f A = 0) :
    localLeading k e T E f A = localValue k e T E f A := by
  unfold localLeading localValue pointOrder expansion at *
  rw [HahnSeries.leadingCoeff_eq, ho]

private lemma localValue_mul_of_orders_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (A : (Curve k e).Point)
    (hfm : f ≠ 0) (hgm : g ≠ 0)
    (hf : pointOrder k e T E f A = 0)
    (hg : pointOrder k e T E g A = 0) :
    localValue k e T E (f * g) A =
      localValue k e T E f A * localValue k e T E g A := by
  have hfg := pointOrder_mul k e T E A hfm hgm
  rw [hf, hg, add_zero] at hfg
  rw [← localLeading_eq_localValue_of_order_zero k e T E (f * g) A hfg,
    localLeading_mul,
    localLeading_eq_localValue_of_order_zero k e T E f A hf,
    localLeading_eq_localValue_of_order_zero k e T E g A hg]

private lemma localValue_div_of_orders_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (A : (Curve k e).Point)
    (hfm : f ≠ 0) (hgm : g ≠ 0)
    (hf : pointOrder k e T E f A = 0)
    (hg : pointOrder k e T E g A = 0) :
    localValue k e T E (f / g) A =
      localValue k e T E f A / localValue k e T E g A := by
  have hfg := pointOrder_div k e T E A f g hfm hgm
  rw [hf, hg, sub_zero] at hfg
  rw [← localLeading_eq_localValue_of_order_zero k e T E (f / g) A hfg,
    localLeading_div k e T E A f g hgm,
    localLeading_eq_localValue_of_order_zero k e T E f A hf,
    localLeading_eq_localValue_of_order_zero k e T E g A hg]

private lemma localValue_curveNegation_of_order_zero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (f : FF k e) (A : (Curve k e).Point)
    (hf : pointOrder k e T E f (-A) = 0) :
    localValue k e T E (curveNegation k e he f) A =
      localValue k e T E f (-A) := by
  have ho := pointOrder_curveNegation k e he T hT h E hh hE A f
  rw [hf] at ho
  rw [← localLeading_eq_localValue_of_order_zero k e T E _ A ho,
    localLeading_curveNegation k e he T hT h E hh hE A f, hf,
    zpow_zero, one_mul,
    localLeading_eq_localValue_of_order_zero k e T E f (-A) hf]

/-- The remaining phase calculation is a concrete identity of rational functions
in the moving point. This lemma transfers that identity to every good shift. -/
lemma moved_pairing_of_function_field_identity (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z)
    (hId :
      (T Q (millerAt k e 0 P) / millerAt k e 0 P) *
        (curveNegation k e he (millerAt k e 1 Q) /
          curveNegation k e he (T P (millerAt k e 1 Q))) =
        algebraMap k (FF k e) (fixedLabelPhase k e P Q)) :
    movedPairing k e T E P Q Z = fixedLabelPhase k e P Q := by
  let f := millerAt k e 0 P
  let g := millerAt k e 1 Q
  have hf := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).1
  have hg := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).1
  have hfo := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.1
  have hgo := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).2.1
  have hfZ : pointOrder k e T E f Z = 0 := by
    simpa [f, hZ.1, hZ.2.1] using hfo Z
  have hfQZ : pointOrder k e T E f (Q + Z) = 0 := by
    simpa [f, hZ.2.2.1, hZ.2.2.2] using hfo (Q + Z)
  have hnegZ0 : -Z ≠ 0 := by
    intro hz
    exact hZ.1 (neg_eq_zero.mp hz)
  have hnegZQ : -Z ≠ Q := by
    intro hz
    exact hZ.2.2.1 (by rw [← hz]; abel)
  have hPsubZ0 : P - Z ≠ 0 := by
    intro hz
    exact hZ.2.1 (sub_eq_zero.mp hz).symm
  have hPsubZQ : P - Z ≠ Q := by
    intro hz
    exact hZ.2.2.2 (by rw [← hz]; abel)
  have hgNegZ : pointOrder k e T E g (-Z) = 0 := by
    simpa [g, hnegZQ, hnegZ0] using hgo (-Z)
  have hgPsubZ : pointOrder k e T E g (P - Z) = 0 := by
    simpa [g, hPsubZQ, hPsubZ0] using hgo (P - Z)
  let n := curveNegation k e he
  have hfT : T Q f ≠ 0 := by simpa [f] using (T Q).injective.ne hf
  have hgT : T P g ≠ 0 := by simpa [g] using (T P).injective.ne hg
  have hng : n g ≠ 0 := by simpa [g] using n.injective.ne hg
  have hngT : n (T P g) ≠ 0 := by simpa using n.injective.ne hgT
  have hfTZ : pointOrder k e T E (T Q f) Z = 0 := by
    rw [(principal_divisor_support k e he T hT h E hh hE f hf).2 Z Q]
    simpa only [add_comm] using hfQZ
  have hngZ : pointOrder k e T E (n g) Z = 0 := by
    rw [pointOrder_curveNegation k e he T hT h E hh hE]
    exact hgNegZ
  have hngTZ : pointOrder k e T E (n (T P g)) Z = 0 := by
    rw [pointOrder_curveNegation k e he T hT h E hh hE]
    rw [(principal_divisor_support k e he T hT h E hh hE g hg).2 (-Z) P]
    simpa only [sub_eq_add_neg, add_comm] using hgPsubZ
  have hfvT : localValue k e T E (T Q f) Z = localValue k e T E f (Q + Z) := by
    unfold localValue expansion
    rw [(translation_composition k e he T hT).2.1 Z Q f]
    simp only [add_comm]
  have hgvT : localValue k e T E (T P g) (-Z) =
      localValue k e T E g (P - Z) := by
    unfold localValue expansion
    rw [(translation_composition k e he T hT).2.1 (-Z) P g]
    congr 1
    abel
  have hnegv : localValue k e T E (n g) Z = localValue k e T E g (-Z) :=
    localValue_curveNegation_of_order_zero k e he T hT h E hh hE g Z hgNegZ
  have hnegTv : localValue k e T E (n (T P g)) Z =
      localValue k e T E g (P - Z) := by
    rw [localValue_curveNegation_of_order_zero k e he T hT h E hh hE
      (T P g) Z (by
        rw [(principal_divisor_support k e he T hT h E hh hE g hg).2 (-Z) P]
        simpa only [sub_eq_add_neg, add_comm] using hgPsubZ), hgvT]
  have hconst : localValue k e T E
      (algebraMap k (FF k e) (fixedLabelPhase k e P Q)) Z =
      fixedLabelPhase k e P Q := by
    rw [← localLeading_eq_localValue_of_order_zero k e T E _ Z
      (pointOrder_constant k e T E Z _), localLeading_constant]
  have hlocal := congrArg (fun a : FF k e => localValue k e T E a Z) hId
  rw [hconst] at hlocal
  change localValue k e T E ((T Q f / f) * (n g / n (T P g))) Z = _ at hlocal
  rw [localValue_mul_of_orders_zero k e T E _ _ Z
      (div_ne_zero hfT hf) (div_ne_zero hng hngT)
      (by rw [pointOrder_div k e T E Z _ _ hfT hf, hfTZ, hfZ, sub_self])
      (by rw [pointOrder_div k e T E Z _ _ hng hngT, hngZ, hngTZ, sub_self]),
    localValue_div_of_orders_zero k e T E _ _ Z hfT hf hfTZ hfZ,
    localValue_div_of_orders_zero k e T E _ _ Z hng hngT hngZ hngTZ,
    hfvT, hnegv, hnegTv] at hlocal
  exact hlocal

/-- The rational function of the moving point has no zero or pole. -/
lemma moved_quotient_order_zero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q A : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    pointOrder k e T E
      ((T Q (millerAt k e 0 P) / millerAt k e 0 P) *
        (curveNegation k e he (millerAt k e 1 Q) /
          curveNegation k e he (T P (millerAt k e 1 Q)))) A = 0 := by
  let f := millerAt k e 0 P
  let g := millerAt k e 1 Q
  let n := curveNegation k e he
  have hf := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).1
  have hg := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).1
  have hfo := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.1
  have hgo := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).2.1
  have hfT : T Q f ≠ 0 := by simpa [f] using (T Q).injective.ne hf
  have hgT : T P g ≠ 0 := by simpa [g] using (T P).injective.ne hg
  have hng : n g ≠ 0 := by simpa [g] using n.injective.ne hg
  have hngT : n (T P g) ≠ 0 := by simpa using n.injective.ne hgT
  have horder :
      pointOrder k e T E ((T Q f / f) * (n g / n (T P g))) A =
      (((if A + Q = P then (4 : ℤ) else 0) -
          (if A + Q = 0 then 4 else 0)) -
        ((if A = P then 4 else 0) - (if A = 0 then 4 else 0))) +
      (((if -A = Q then 4 else 0) - (if -A = 0 then 4 else 0)) -
        ((if -A + P = Q then 4 else 0) -
          (if -A + P = 0 then 4 else 0))) := by
    rw [pointOrder_mul k e T E A (div_ne_zero hfT hf) (div_ne_zero hng hngT),
      pointOrder_div k e T E A _ _ hfT hf,
      pointOrder_div k e T E A _ _ hng hngT,
      (principal_divisor_support k e he T hT h E hh hE f hf).2 A Q,
      pointOrder_curveNegation k e he T hT h E hh hE A g,
      pointOrder_curveNegation k e he T hT h E hh hE A (T P g),
      (principal_divisor_support k e he T hT h E hh hE g hg).2 (-A) P,
      hfo, hfo, hgo, hgo]
  have h1 : (A + Q = P) ↔ (-A + P = Q) := by
    constructor
    · intro hz
      calc -A + P = -A + (A + Q) := by rw [hz]
        _ = Q := by abel
    · intro hz
      calc A + Q = A + (-A + P) := by rw [hz]
        _ = P := by abel
  have h2 : (A + Q = 0) ↔ (-A = Q) := by
    constructor
    · intro hz
      calc -A = Q - (A + Q) := by abel
        _ = Q := by rw [hz]; abel
    · intro hz
      calc A + Q = A + -A := by rw [hz]
        _ = 0 := by abel
  have h3 : (A = P) ↔ (-A + P = 0) := by
    constructor
    · intro hz
      calc -A + P = -A + A := by rw [hz]
        _ = 0 := by abel
    · intro hz
      calc A = P - (-A + P) := by abel
        _ = P := by rw [hz]; abel
  have h4 : (A = 0) ↔ (-A = 0) := by
    constructor
    · intro hz; simp [hz]
    · exact neg_eq_zero.mp
  change pointOrder k e T E ((T Q f / f) * (n g / n (T P g))) A = 0
  rw [horder]
  simp only [h1, h2, h3, h4]
  ring

private lemma function_eq_constant_of_order_zero [IsAlgClosed k]
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (f : FF k e) (ho : ∀ A : (Curve k e).Point, pointOrder k e T E f A = 0) :
    f = algebraMap k (FF k e) (localValue k e T E f 0) := by
  let c := localValue k e T E f 0
  let d := f - algebraMap k (FF k e) c
  by_contra hd
  have hdn : d ≠ 0 := sub_ne_zero.mpr hd
  have hnonneg (A : (Curve k e).Point) :
      0 ≤ pointOrder k e T E d A := by
    have hex : expansion k e T E A d =
        expansion k e T E A f -
          expansion k e T E A (algebraMap k (FF k e) c) := by
      simp [d, expansion]
    have hne := expansion_ne_zero k e T E A hdn
    rw [hex] at hne
    have hm := HahnSeries.min_order_le_order_add
      (x := expansion k e T E A f)
      (y := -expansion k e T E A (algebraMap k (FF k e) c))
      (by simpa only [sub_eq_add_neg] using hne)
    simp only [← sub_eq_add_neg] at hm
    rw [← hex, show (expansion k e T E A f).order = 0 from ho A,
      HahnSeries.order_neg,
      show (expansion k e T E A (algebraMap k (FF k e) c)).order = 0
        from pointOrder_constant k e T E A c] at hm
    simpa [pointOrder] using hm
  have hc : localValue k e T E (algebraMap k (FF k e) c) 0 = c := by
    rw [← localLeading_eq_localValue_of_order_zero k e T E _ 0
      (pointOrder_constant k e T E 0 c), localLeading_constant]
  have hdv : localValue k e T E d 0 = 0 := by
    change localValue k e T E (f - algebraMap k (FF k e) c) 0 = 0
    have hs : localValue k e T E (f - algebraMap k (FF k e) c) 0 =
        localValue k e T E f 0 -
          localValue k e T E (algebraMap k (FF k e) c) 0 := by
      simp [localValue, expansion]
    rw [hs, hc]
    exact sub_self _
  have hpositive : 0 < pointOrder k e T E d 0 := by
    have hnot : pointOrder k e T E d 0 ≠ 0 := by
      intro hz
      exact (localLeading_ne_zero k e T E 0 hdn)
        ((localLeading_eq_localValue_of_order_zero k e T E d 0 hz).trans hdv)
    have hn := hnonneg 0
    omega
  have hsum : 0 < ∑ᶠ A : (Curve k e).Point, pointOrder k e T E d A :=
    finsum_pos hnonneg ⟨0, hpositive⟩
      (principal_divisor_support k e he T hT h E hh hE d hdn).1
  have hzero := principal_degree_zero k e T hT h E hh hE he d hdn
  change (∑ᶠ A : (Curve k e).Point, pointOrder k e T E d A) = 0 at hzero
  omega

private lemma moved_quotient_value_at_zero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    localValue k e T E
      ((T Q (millerAt k e 0 P) / millerAt k e 0 P) *
        (curveNegation k e he (millerAt k e 1 Q) /
          curveNegation k e he (T P (millerAt k e 1 Q)))) 0 =
      localValue k e T E (millerAt k e 0 P) Q /
        localValue k e T E (millerAt k e 1 Q) P := by
  let f := millerAt k e 0 P
  let g := millerAt k e 1 Q
  let n := curveNegation k e he
  have hf := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).1
  have hg := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).1
  have hfo := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.1
  have hgo := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).2.1
  have hfl := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.2
  have hgl := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).2.2
  have hn := labelled_halves_independent k e he P Q hP hQ
  have hp0 := labelled_half_nonzero k e 0 P hP
  have hq0 := labelled_half_nonzero k e 1 Q hQ
  have hfQ : pointOrder k e T E f Q = 0 := by
    simpa [f, hn.1.symm, hq0] using hfo Q
  have hgP : pointOrder k e T E g P = 0 := by
    simpa [g, hn.1, hp0] using hgo P
  have hf0 : pointOrder k e T E f 0 = -4 := by
    simpa [f, hp0.symm] using hfo 0
  have hg0 : pointOrder k e T E g 0 = -4 := by
    simpa [g, hq0.symm] using hgo 0
  have hfT : T Q f ≠ 0 := by simpa [f] using (T Q).injective.ne hf
  have hgT : T P g ≠ 0 := by simpa [g] using (T P).injective.ne hg
  have hng : n g ≠ 0 := by simpa [g] using n.injective.ne hg
  have hngT : n (T P g) ≠ 0 := by simpa using n.injective.ne hgT
  have hfT0 : pointOrder k e T E (T Q f) 0 = 0 := by
    rw [(principal_divisor_support k e he T hT h E hh hE f hf).2 0 Q]
    simpa using hfQ
  have hgTP : pointOrder k e T E (T P g) 0 = 0 := by
    rw [(principal_divisor_support k e he T hT h E hh hE g hg).2 0 P]
    simpa using hgP
  have hng0 : pointOrder k e T E (n g) 0 = -4 := by
    rw [pointOrder_curveNegation k e he T hT h E hh hE]
    simpa using hg0
  have hngT0 : pointOrder k e T E (n (T P g)) 0 = 0 := by
    rw [pointOrder_curveNegation k e he T hT h E hh hE]
    simpa using hgTP
  have hfv : localLeading k e T E (T Q f) 0 = localValue k e T E f Q := by
    rw [localLeading_eq_localValue_of_order_zero k e T E _ 0 hfT0]
    unfold localValue expansion
    rw [(translation_composition k e he T hT).2.1 0 Q f]
    simp
  have hgv : localLeading k e T E (n (T P g)) 0 = localValue k e T E g P := by
    rw [localLeading_eq_localValue_of_order_zero k e T E _ 0 hngT0]
    rw [localValue_curveNegation_of_order_zero k e he T hT h E hh hE
      (T P g) 0 (by simpa using hgTP)]
    unfold localValue expansion
    simp only [neg_zero]
    rw [(translation_composition k e he T hT).2.1 0 P g]
    simp
  have hgn : localLeading k e T E (n g) 0 = 1 := by
    rw [localLeading_curveNegation k e he T hT h E hh hE,
      show pointOrder k e T E g (-0) = -4 by simpa using hg0]
    simpa [g, hgl] using (show (-1 : k) ^ (-4 : ℤ) * 1 = 1 by norm_num)
  have hord := moved_quotient_order_zero k e he T hT h E hh hE P Q 0 hP hQ
  rw [← localLeading_eq_localValue_of_order_zero k e T E _ 0 hord]
  change localLeading k e T E ((T Q f / f) * (n g / n (T P g))) 0 = _
  rw [localLeading_mul, localLeading_div k e T E 0 (T Q f) f hf,
    localLeading_div k e T E 0 (n g) (n (T P g)) hngT,
    hfv, hgv, hgn]
  simp [f, g, hfl, div_eq_mul_inv]

private lemma tameSymbol_left_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (A : (Curve k e).Point)
    (ho : pointOrder k e T E f A = 0) :
    tameSymbol k e T E f g A =
      localValue k e T E f A ^ pointOrder k e T E g A := by
  rw [tameSymbol, ho,
    localLeading_eq_localValue_of_order_zero k e T E f A ho]
  simp

private lemma tameSymbol_right_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f g : FF k e) (A : (Curve k e).Point)
    (ho : pointOrder k e T E g A = 0) :
    tameSymbol k e T E f g A =
      (localValue k e T E g A ^ pointOrder k e T E f A)⁻¹ := by
  rw [tameSymbol, ho,
    localLeading_eq_localValue_of_order_zero k e T E g A ho]
  simp

private lemma moved_tame_product_four_points (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z) :
    (∏ᶠ A : (Curve k e).Point,
      tameSymbol k e T E (millerAt k e 0 P)
        (T (-Z) (millerAt k e 1 Q)) A) =
      tameSymbol k e T E (millerAt k e 0 P) (T (-Z) (millerAt k e 1 Q)) P *
      tameSymbol k e T E (millerAt k e 0 P) (T (-Z) (millerAt k e 1 Q)) 0 *
      tameSymbol k e T E (millerAt k e 0 P) (T (-Z) (millerAt k e 1 Q)) (Q + Z) *
      tameSymbol k e T E (millerAt k e 0 P) (T (-Z) (millerAt k e 1 Q)) Z := by
  classical
  let F : (Curve k e).Point → k := fun A =>
    tameSymbol k e T E (millerAt k e 0 P)
      (T (-Z) (millerAt k e 1 Q)) A
  have hP0 : P ≠ 0 := labelled_half_nonzero k e 0 P hP
  have hQ0 : Q ≠ 0 := labelled_half_nonzero k e 1 Q hQ
  have hQZneZ : Q + Z ≠ Z := by
    intro hz
    apply hQ0
    have h := congrArg (fun A : (Curve k e).Point => A - Z) hz
    simpa using h
  have hPQZ : P ≠ Q + Z := hZ.2.2.2.symm
  have hPZ : P ≠ Z := hZ.2.1.symm
  have h0QZ : (0 : (Curve k e).Point) ≠ Q + Z := hZ.2.2.1.symm
  have h0Z : (0 : (Curve k e).Point) ≠ Z := hZ.1.symm
  have hsupp : Function.mulSupport F ⊆ ({P, 0, Q + Z, Z} : Finset (Curve k e).Point) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      moved_tame_support k e he T hT h E hh hE P Q Z hP hQ
  change (∏ᶠ A, F A) = F P * F 0 * F (Q + Z) * F Z
  rw [finprod_eq_prod_of_mulSupport_subset F hsupp]
  simp [Finset.prod_insert, hP0, hPQZ, hPZ, h0QZ, h0Z, hQZneZ,
    mul_assoc]

private lemma moved_tame_product_eq_power (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z) :
    (∏ᶠ A : (Curve k e).Point,
      tameSymbol k e T E (millerAt k e 0 P)
        (T (-Z) (millerAt k e 1 Q)) A) =
      movedPairing k e T E P Q Z ^ 4 := by
  let f := millerAt k e 0 P
  let g := T (-Z) (millerAt k e 1 Q)
  let a := localValue k e T E f (Q + Z)
  let b := localValue k e T E f Z
  let c := localValue k e T E (millerAt k e 1 Q) (-Z)
  let d := localValue k e T E (millerAt k e 1 Q) (P - Z)
  obtain ⟨ha, hb, hc, hd⟩ := moved_values_nonzero k e he T hT h E hh hE P Q Z hP hQ hZ
  have hP0 : P ≠ 0 := labelled_half_nonzero k e 0 P hP
  have hQ0 : Q ≠ 0 := labelled_half_nonzero k e 1 Q hQ
  have hQZneZ : Q + Z ≠ Z := by
    intro hz
    apply hQ0
    have ht := congrArg (fun A : (Curve k e).Point => A - Z) hz
    simpa using ht
  have hf := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).2.1
  have hg := translated_miller_order k e he T hT h E hh hE Q Z
  have hfP : pointOrder k e T E f P = 4 := by simpa [f, hP0] using hf P
  have hf0 : pointOrder k e T E f 0 = -4 := by simpa [f, hP0.symm] using hf 0
  have hfQZ : pointOrder k e T E f (Q + Z) = 0 := by
    simpa [f, hZ.2.2.1, hZ.2.2.2] using hf (Q + Z)
  have hfZ : pointOrder k e T E f Z = 0 := by
    simpa [f, hZ.1, hZ.2.1] using hf Z
  have hgP : pointOrder k e T E g P = 0 := by
    simpa [g, hZ.2.1.symm, hZ.2.2.2.symm] using hg P hQ
  have hg0 : pointOrder k e T E g 0 = 0 := by
    simpa [g, hZ.1.symm, hZ.2.2.1.symm] using hg 0 hQ
  have hgQZ : pointOrder k e T E g (Q + Z) = 4 := by
    simpa [g, hQZneZ] using hg (Q + Z) hQ
  have hgZ : pointOrder k e T E g Z = -4 := by
    simpa [g, hQZneZ.symm] using hg Z hQ
  have hgvP : localValue k e T E g P = d := by
    simpa [g, d] using translated_miller_value k e he T hT E Q Z P
  have hgv0 : localValue k e T E g 0 = c := by
    simpa [g, c] using translated_miller_value k e he T hT E Q Z 0
  have hsymP : tameSymbol k e T E f g P = (d ^ 4)⁻¹ := by
    rw [tameSymbol_right_order_zero k e T E f g P hgP, hfP, hgvP]
    norm_num
  have hsym0 : tameSymbol k e T E f g 0 = c ^ 4 := by
    rw [tameSymbol_right_order_zero k e T E f g 0 hg0, hf0, hgv0]
    simp [zpow_neg, hc]
  have hsymQZ : tameSymbol k e T E f g (Q + Z) = a ^ 4 := by
    rw [tameSymbol_left_order_zero k e T E f g (Q + Z) hfQZ, hgQZ]
    norm_num [a]
  have hsymZ : tameSymbol k e T E f g Z = (b ^ 4)⁻¹ := by
    rw [tameSymbol_left_order_zero k e T E f g Z hfZ, hgZ]
    simp [zpow_neg, b]
  calc
    _ = (d ^ 4)⁻¹ * c ^ 4 * a ^ 4 * (b ^ 4)⁻¹ := by
      rw [moved_tame_product_four_points k e he T hT h E hh hE P Q Z hP hQ hZ]
      change tameSymbol k e T E f g P * tameSymbol k e T E f g 0 *
        tameSymbol k e T E f g (Q + Z) * tameSymbol k e T E f g Z = _
      rw [hsymP, hsym0, hsymQZ, hsymZ]
    _ = movedPairing k e T E P Q Z ^ 4 := by
      dsimp [movedPairing, a, b, c, d, f]
      rw [mul_pow, div_pow, div_pow]
      simp only [div_eq_mul_inv]
      ring

/-- Reciprocity places every admissible moved evaluation in fourth roots of unity. -/
theorem moved_pairing_fourth_power [IsAlgClosed k]
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z) :
    movedPairing k e T E P Q Z ^ 4 = 1 := by
  have hf := (complete_miller_divisor k e he T hT h E hh hE 0 P hP).1
  have hq := (complete_miller_divisor k e he T hT h E hh hE 1 Q hQ).1
  have hg : T (-Z) (millerAt k e 1 Q) ≠ 0 := by
    simpa using (T (-Z)).injective.ne hq
  have hr := (elliptic_tame_reciprocity k e he T hT h E hh hE
    (millerAt k e 0 P) (T (-Z) (millerAt k e 1 Q)) hf hg).2
  rw [moved_tame_product_eq_power k e he T hT h E hh hE P Q Z hP hQ hZ] at hr
  exact hr

/-- The admissible moved values are defined and lie in the fourth roots of unity. -/
theorem moved_support_miller_pairing_power [IsAlgClosed k]
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    (∃ Z : (Curve k e).Point, GoodShift k e P Q Z) ∧
    (∀ Z : (Curve k e).Point, GoodShift k e P Q Z →
      localValue k e T E (millerAt k e 0 P) (Q + Z) ≠ 0 ∧
      localValue k e T E (millerAt k e 0 P) Z ≠ 0 ∧
      localValue k e T E (millerAt k e 1 Q) (-Z) ≠ 0 ∧
      localValue k e T E (millerAt k e 1 Q) (P - Z) ≠ 0 ∧
      movedPairing k e T E P Q Z ^ 4 = 1) ∧
    IsPrimitiveRoot (fixedLabelPhase k e P Q) 4 := by
  refine ⟨⟨Q, goodShift_Q k e he P Q hP hQ⟩, ?_,
    fixed_phase_primitive k e he P Q hP hQ⟩
  intro Z hZ
  obtain ⟨ha, hb, hc, hd⟩ :=
    moved_values_nonzero k e he T hT h E hh hE P Q Z hP hQ hZ
  exact ⟨ha, hb, hc, hd,
    moved_pairing_fourth_power k e he T hT h E hh hE P Q Z hP hQ hZ⟩

/-- The moved divisor evaluation has the normalized fixed-label phase. -/
theorem moved_support_miller_pairing
    (k : Type u) [Field k] [CharZero k] [DecidableEq k] [IsAlgClosed k]
    (e : Fin 3 → k)
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    (∃ Z : (Curve k e).Point, GoodShift k e P Q Z) ∧
    (∀ Z : (Curve k e).Point, GoodShift k e P Q Z →
      localValue k e T E (millerAt k e 0 P) (Q + Z) ≠ 0 ∧
      localValue k e T E (millerAt k e 0 P) Z ≠ 0 ∧
      localValue k e T E (millerAt k e 1 Q) (-Z) ≠ 0 ∧
      localValue k e T E (millerAt k e 1 Q) (P - Z) ≠ 0 ∧
      movedPairing k e T E P Q Z = fixedLabelPhase k e P Q) ∧
    IsPrimitiveRoot (fixedLabelPhase k e P Q) 4 := by
  let F : FF k e :=
    (T Q (millerAt k e 0 P) / millerAt k e 0 P) *
      (curveNegation k e he (millerAt k e 1 Q) /
        curveNegation k e he (T P (millerAt k e 1 Q)))
  have hphase : localValue k e T E F 0 = fixedLabelPhase k e P Q := by
    rw [show localValue k e T E F 0 =
      localValue k e T E (millerAt k e 0 P) Q /
        localValue k e T E (millerAt k e 1 Q) P from
      moved_quotient_value_at_zero k e he T hT h E hh hE P Q hP hQ]
    cases P with
    | zero => exact False.elim ((labelled_half_nonzero k e 0 0 hP) rfl)
    | @some x y hp =>
      cases Q with
      | zero => exact False.elim ((labelled_half_nonzero k e 1 0 hQ) rfl)
      | @some a b hq =>
        have hp' : ArithmeticThetaMillerR0114.IsHalf k e 0 x y :=
          ⟨hp, hP.1, hP.2⟩
        have hq' : ArithmeticThetaMillerR0114.IsHalf k e 1 a b :=
          ⟨hq, hQ.1, hQ.2⟩
        have havoid := (ArithmeticThetaMillerR0114.half_tangent_evaluation_nonzero
          k e he x y a b hp' hq').2.2.1
        change localValue k e T E
            (ArithmeticThetaMillerR0114.millerFunction k e 0 x y) (.some a b hq) /
          localValue k e T E
            (ArithmeticThetaMillerR0114.millerFunction k e 1 a b) (.some x y hp) =
          ArithmeticThetaMillerR0114.millerRatio k e x y a b
        rw [miller_localValue_of_x_ne k e he T hT h E hh hE
          0 x y a b hq (havoid 0).2,
          miller_localValue_of_x_ne k e he T hT h E hh hE
          1 a b x y hp (havoid 1).1]
        rfl
  have hId : F = algebraMap k (FF k e) (fixedLabelPhase k e P Q) := by
    rw [← hphase]
    exact function_eq_constant_of_order_zero k e he T hT h E hh hE F
      (fun A => moved_quotient_order_zero k e he T hT h E hh hE P Q A hP hQ)
  refine ⟨⟨Q, goodShift_Q k e he P Q hP hQ⟩, ?_,
    fixed_phase_primitive k e he P Q hP hQ⟩
  intro Z hZ
  obtain ⟨ha, hb, hc, hd⟩ :=
    moved_values_nonzero k e he T hT h E hh hE P Q Z hP hQ hZ
  exact ⟨ha, hb, hc, hd,
    moved_pairing_of_function_field_identity k e he T hT h E hh hE
      P Q Z hP hQ hZ hId⟩

end ArithmeticThetaReciprocityR0116
