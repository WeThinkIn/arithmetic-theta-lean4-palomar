module

public import AllFourMillerProviderR0118
import all MovedSupportMillerPairingR0116

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Shift and local-data independence for the actual four-torsion Miller functions. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open WeierstrassCurve.Affine
open ArithmeticThetaReciprocityR0116
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

private lemma general_divisor (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P : (Curve k e).Point) (hP : 4 • P = 0) :
    fourFunction k e P ≠ 0 ∧
    (∀ Z : (Curve k e).Point, pointOrder k e T E (fourFunction k e P) Z =
      (if Z = P then 4 else 0) - (if Z = 0 then 4 else 0)) ∧
    localLeading k e T E (fourFunction k e P) 0 = 1 :=
  four_function_provider k e he ⟨T, h, E, hT, hh, hE⟩ P hP

private lemma localValue_ne_zero_of_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) (hf : f ≠ 0)
    (ho : pointOrder k e T E f P = 0) : localValue k e T E f P ≠ 0 := by
  have hn := localLeading_ne_zero k e T E P hf
  unfold localValue localLeading pointOrder expansion at *
  rw [HahnSeries.leadingCoeff_eq, ho] at hn
  exact hn

/-- Off its displayed denominator, the local value is the usual tangent quotient. -/
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

/-- Reuse the original order-zero lemma through its defining module. -/
macro "acceptedOrderZeroConstant" : term =>
  `(ArithmeticThetaReciprocityR0116.function_eq_constant_of_order_zero)

private lemma function_eq_constant_of_order_zero [IsAlgClosed k]
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (f : FF k e) (ho : ∀ A : (Curve k e).Point, pointOrder k e T E f A = 0) :
    f = algebraMap k (FF k e) (localValue k e T E f 0) :=
  acceptedOrderZeroConstant
    k e he T hT h E hh hE f ho

/-- All four evaluations in the moved expression are units at a good shift. -/
theorem general_arithmetic_moved_values_nonzero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z) :
    localValue k e T E (fourFunction k e P) (Q + Z) ≠ 0 ∧
    localValue k e T E (fourFunction k e P) Z ≠ 0 ∧
    localValue k e T E (fourFunction k e Q) (-Z) ≠ 0 ∧
    localValue k e T E (fourFunction k e Q) (P - Z) ≠ 0 := by
  have hdivP := general_divisor k e he T hT h E hh hE P hP
  have hdivQ := general_divisor k e he T hT h E hh hE Q hQ
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

private lemma general_translated_miller_order (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (Q Z A : (Curve k e).Point)
    (hQ : 4 • Q = 0) :
    pointOrder k e T E (T (-Z) (fourFunction k e Q)) A =
      (if A = Q + Z then 4 else 0) - (if A = Z then 4 else 0) := by
  have hdivQ := (general_divisor k e he T hT h E hh hE Q hQ).2.1
  rw [(principal_divisor_support k e he T hT h E hh hE
    (fourFunction k e Q)
    (general_divisor k e he T hT h E hh hE Q hQ).1).2]
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

private lemma general_translated_miller_value (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (E : FF k e →ₐ[k] LaurentSeries k)
    (Q Z A : (Curve k e).Point) :
    localValue k e T E (T (-Z) (fourFunction k e Q)) A =
      localValue k e T E (fourFunction k e Q) (A - Z) := by
  simp only [localValue, expansion, sub_eq_add_neg]
  rw [(translation_composition k e he T hT).2.1 A (-Z)]

private lemma general_moved_tame_support (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0) :
    Function.mulSupport (fun A =>
      tameSymbol k e T E (fourFunction k e P)
        (T (-Z) (fourFunction k e Q)) A) ⊆
      ({P, 0, Q + Z, Z} : Set (Curve k e).Point) := by
  intro A hA
  by_contra hn
  have hne : A ≠ P ∧ A ≠ 0 ∧ A ≠ Q + Z ∧ A ≠ Z := by
    simpa using hn
  have hoP := (general_divisor k e he T hT h E hh hE P hP).2.1 A
  have hoQ := general_translated_miller_order k e he T hT h E hh hE Q Z A hQ
  have hzP : pointOrder k e T E (fourFunction k e P) A = 0 := by
    simpa [hne.1, hne.2.1] using hoP
  have hzQ : pointOrder k e T E (T (-Z) (fourFunction k e Q)) A = 0 := by
    simpa [hne.2.2.1, hne.2.2.2] using hoQ
  exact hA (tameSymbol_eq_one_of_orders_eq_zero k e T E A _ _ hzP hzQ)

lemma general_moved_pairing_of_function_field_identity (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z)
    (c : k) (hId :
      (T Q (fourFunction k e P) / fourFunction k e P) *
        (curveNegation k e he (fourFunction k e Q) /
          curveNegation k e he (T P (fourFunction k e Q))) =
        algebraMap k (FF k e) (c)) :
    movedValue k e ⟨T, h, E, hT, hh, hE⟩ P Q Z = c := by
  let f := fourFunction k e P
  let g := fourFunction k e Q
  have hf := (general_divisor k e he T hT h E hh hE P hP).1
  have hg := (general_divisor k e he T hT h E hh hE Q hQ).1
  have hfo := (general_divisor k e he T hT h E hh hE P hP).2.1
  have hgo := (general_divisor k e he T hT h E hh hE Q hQ).2.1
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
      (algebraMap k (FF k e) (c)) Z =
      c := by
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
lemma general_moved_quotient_order_zero (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q A : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0) :
    pointOrder k e T E
      ((T Q (fourFunction k e P) / fourFunction k e P) *
        (curveNegation k e he (fourFunction k e Q) /
          curveNegation k e he (T P (fourFunction k e Q)))) A = 0 := by
  let f := fourFunction k e P
  let g := fourFunction k e Q
  let n := curveNegation k e he
  have hf := (general_divisor k e he T hT h E hh hE P hP).1
  have hg := (general_divisor k e he T hT h E hh hE Q hQ).1
  have hfo := (general_divisor k e he T hT h E hh hE P hP).2.1
  have hgo := (general_divisor k e he T hT h E hh hE Q hQ).2.1
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

private lemma general_moved_tame_product_four_points (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    (∏ᶠ A : (Curve k e).Point,
      tameSymbol k e T E (fourFunction k e P)
        (T (-Z) (fourFunction k e Q)) A) =
      tameSymbol k e T E (fourFunction k e P) (T (-Z) (fourFunction k e Q)) P *
      tameSymbol k e T E (fourFunction k e P) (T (-Z) (fourFunction k e Q)) 0 *
      tameSymbol k e T E (fourFunction k e P) (T (-Z) (fourFunction k e Q)) (Q + Z) *
      tameSymbol k e T E (fourFunction k e P) (T (-Z) (fourFunction k e Q)) Z := by
  classical
  let F : (Curve k e).Point → k := fun A =>
    tameSymbol k e T E (fourFunction k e P)
      (T (-Z) (fourFunction k e Q)) A
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
      general_moved_tame_support k e he T hT h E hh hE P Q Z hP hQ
  change (∏ᶠ A, F A) = F P * F 0 * F (Q + Z) * F Z
  rw [finprod_eq_prod_of_mulSupport_subset F hsupp]
  simp [Finset.prod_insert, hP0, hPQZ, hPZ, h0QZ, h0Z, hQZneZ,
    mul_assoc]

private lemma general_moved_tame_product_eq_power (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    (∏ᶠ A : (Curve k e).Point,
      tameSymbol k e T E (fourFunction k e P)
        (T (-Z) (fourFunction k e Q)) A) =
      movedValue k e ⟨T, h, E, hT, hh, hE⟩ P Q Z ^ 4 := by
  let f := fourFunction k e P
  let g := T (-Z) (fourFunction k e Q)
  let a := localValue k e T E f (Q + Z)
  let b := localValue k e T E f Z
  let c := localValue k e T E (fourFunction k e Q) (-Z)
  let d := localValue k e T E (fourFunction k e Q) (P - Z)
  obtain ⟨ha, hb, hc, hd⟩ := general_arithmetic_moved_values_nonzero k e he T hT h E hh hE P Q Z hP hQ hZ
  have hQZneZ : Q + Z ≠ Z := by
    intro hz
    apply hQ0
    have ht := congrArg (fun A : (Curve k e).Point => A - Z) hz
    simpa using ht
  have hf := (general_divisor k e he T hT h E hh hE P hP).2.1
  have hg := general_translated_miller_order k e he T hT h E hh hE Q Z
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
    simpa [g, d] using general_translated_miller_value k e he T hT E Q Z P
  have hgv0 : localValue k e T E g 0 = c := by
    simpa [g, c] using general_translated_miller_value k e he T hT E Q Z 0
  have hsymP : tameSymbol k e T E f g P = (d ^ 4)⁻¹ := by
    rw [tameSymbol_right_order_zero k e T E f g P hgP, hfP, hgvP]
    norm_num
  have hsym0 : tameSymbol k e T E f g 0 = c ^ 4 := by
    rw [tameSymbol_right_order_zero k e T E f g 0 hg0, hf0, hgv0]
    simp [zpow_neg]
  have hsymQZ : tameSymbol k e T E f g (Q + Z) = a ^ 4 := by
    rw [tameSymbol_left_order_zero k e T E f g (Q + Z) hfQZ, hgQZ]
    norm_num [a]
  have hsymZ : tameSymbol k e T E f g Z = (b ^ 4)⁻¹ := by
    rw [tameSymbol_left_order_zero k e T E f g Z hfZ, hgZ]
    simp [zpow_neg, b]
  calc
    _ = (d ^ 4)⁻¹ * c ^ 4 * a ^ 4 * (b ^ 4)⁻¹ := by
      rw [general_moved_tame_product_four_points k e he T hT h E hh hE P Q Z hP hQ hZ hP0 hQ0]
      change tameSymbol k e T E f g P * tameSymbol k e T E f g 0 *
        tameSymbol k e T E f g (Q + Z) * tameSymbol k e T E f g Z = _
      rw [hsymP, hsym0, hsymQZ, hsymZ]
    _ = movedValue k e ⟨T, h, E, hT, hh, hE⟩ P Q Z ^ 4 := by
      dsimp [movedValue, value, a, b, c, d, f]
      rw [mul_pow, div_pow, div_pow]
      simp only [div_eq_mul_inv]
      ring

/-- Reciprocity places every admissible moved evaluation in fourth roots of unity. -/
theorem general_moved_pairing_fourth_power [IsAlgClosed k]
    (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0)
    (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    movedValue k e ⟨T, h, E, hT, hh, hE⟩ P Q Z ^ 4 = 1 := by
  have hf := (general_divisor k e he T hT h E hh hE P hP).1
  have hq := (general_divisor k e he T hT h E hh hE Q hQ).1
  have hg : T (-Z) (fourFunction k e Q) ≠ 0 := by
    simpa using (T (-Z)).injective.ne hq
  have hr := (elliptic_tame_reciprocity k e he T hT h E hh hE
    (fourFunction k e P) (T (-Z) (fourFunction k e Q)) hf hg).2
  rw [general_moved_tame_product_eq_power k e he T hT h E hh hE P Q Z hP hQ hZ hP0 hQ0] at hr
  exact hr


/-- Zero entries give the unit even before any support-independence argument. -/
lemma moved_zero_left (he : Function.Injective e) (D : LocalData k e)
    (Q Z : (Curve k e).Point) (hQ : 4 • Q = 0)
    (hZ : GoodShift k e 0 Q Z) : movedValue k e D 0 Q Z = 1 := by
  have hn := general_arithmetic_moved_values_nonzero k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec
    0 Q Z (by simp) hQ hZ
  simpa [movedValue, fourFunction, value, localValue, expansion] using
    (div_self hn.2.2.1)

lemma moved_zero_right (he : Function.Injective e) (D : LocalData k e)
    (P Z : (Curve k e).Point) (hP : 4 • P = 0)
    (hZ : GoodShift k e P 0 Z) : movedValue k e D P 0 Z = 1 := by
  have hn := general_arithmetic_moved_values_nonzero k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec
    P 0 Z hP (by simp) hZ
  simpa [movedValue, fourFunction, value, localValue, expansion] using
    (div_self hn.2.1)

/-- Over an algebraically closed field the quotient in the moving point is constant. -/
lemma closed_shift_independence [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q Z W : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z) (hW : GoodShift k e P Q W) :
    movedValue k e D P Q Z = movedValue k e D P Q W := by
  let F := (D.translations Q (fourFunction k e P) / fourFunction k e P) *
    (curveNegation k e he (fourFunction k e Q) /
      curveNegation k e he (D.translations P (fourFunction k e Q)))
  have hc := function_eq_constant_of_order_zero k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec F
    (general_moved_quotient_order_zero k e he D.translations D.translations_spec
      D.branch D.embedding D.branch_spec D.embedding_spec P Q · hP hQ)
  have hz := general_moved_pairing_of_function_field_identity k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec P Q Z
    hP hQ hZ _ hc
  have hw := general_moved_pairing_of_function_field_identity k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec P Q W
    hP hQ hW _ hc
  exact hz.trans hw.symm

lemma closed_fourth_power [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) (hZ : GoodShift k e P Q Z) :
    movedValue k e D P Q Z ^ 4 = 1 := by
  by_cases hp : P = 0
  · subst P; rw [moved_zero_left k e he D Q Z hQ hZ]; simp
  by_cases hq : Q = 0
  · subst Q; rw [moved_zero_right k e he D P Z hP hZ]; simp
  exact general_moved_pairing_fourth_power k e he D.translations D.translations_spec
    D.branch D.embedding D.branch_spec D.embedding_spec P Q Z hP hQ hZ hp hq

/-- The geometric predicates uniquely determine the complete local data. -/
lemma local_data_unique (D D' : LocalData k e) : D = D' := by
  have ht : D.translations = D'.translations := by
    funext P
    apply AlgEquiv.coe_toAlgHom_injective
    apply ff_ext k e
    · exact (D.translations_spec P).1.trans (D'.translations_spec P).1.symm
    · exact (D.translations_spec P).2.trans (D'.translations_spec P).2.symm
  have hh : D.branch = D'.branch :=
    (ArithmeticThetaMillerR0114.infinity_branch k e).unique D.branch_spec D'.branch_spec
  have hemb : D.embedding = D'.embedding := by
    apply ff_ext k e
    · rw [D.embedding_spec.1, D'.embedding_spec.1, hh]
    · rw [D.embedding_spec.2, D'.embedding_spec.2, hh]
  cases D
  cases D'
  simp_all
private lemma tangentFunction_eq (x y : k) :
    algebraMap (ArithmeticThetaMillerR0114.Coord k e) (FF k e)
      (ArithmeticThetaMillerR0114.tangentClass k e x y) =
      ArithmeticThetaMillerR0114.yFunction k e -
        algebraMap k (FF k e) (ArithmeticThetaMillerR0114.tangentSlope k e x y) *
          (ArithmeticThetaMillerR0114.xFunction k e - algebraMap k (FF k e) x) -
        algebraMap k (FF k e) y := by
  simp only [ArithmeticThetaMillerR0114.tangentClass,
    ArithmeticThetaMillerR0114.yFunction,
    ArithmeticThetaMillerR0114.xFunction,
    WeierstrassCurve.Affine.CoordinateRing.YClass,
    WeierstrassCurve.Affine.CoordinateRing.XClass,
    WeierstrassCurve.Affine.linePolynomial,
    map_zero, sub_zero, map_add, map_sub, map_mul]
  rw [sub_add_eq_sub_sub]
  rfl


/-- The displayed tangent/vertical formulas commute with the coefficient-induced map. -/
lemma fourFunction_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (P : (Curve k e).Point) :
    functionFieldBaseChange k e he K (fourFunction k e P) =
      fourFunction K (fun j => algebraMap k K (e j))
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P) := by
  cases P with
  | zero => simp [fourFunction, ArithmeticThetaMarkingR0115.fieldMap]
  | some x y hp =>
    have hs : ArithmeticThetaMillerR0114.tangentSlope K
        (fun j => algebraMap k K (e j))
        (algebraMap k K x) (algebraMap k K y) =
        algebraMap k K (ArithmeticThetaMillerR0114.tangentSlope k e x y) := by
      have hm := (Curve k e).map_slope (algebraMap k K) x x y y
      rw [ArithmeticThetaMarkingR0115.curve_map e (algebraMap k K)] at hm
      exact hm
    have hx : ArithmeticThetaMarkingR0115.pointX K
        (fun j => algebraMap k K (e j))
        (2 • ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K)
          (Point.some x y hp)) =
        algebraMap k K (ArithmeticThetaMarkingR0115.pointX k e
          (2 • Point.some x y hp)) := by
      rw [← map_nsmul]
      exact ArithmeticThetaMarkingR0115.pointX_fieldMap e (algebraMap k K) _
    simp only [ArithmeticThetaMarkingR0115.fieldMap_some] at hx ⊢
    simp only [fourFunction, map_eq_zero]
    split_ifs <;>
      simp only [map_pow, map_sub, map_div₀, map_mul, tangentFunction_eq,
        functionFieldBaseChange_x, functionFieldBaseChange_y, AlgHom.commutes, hs,
        hx, ← IsScalarTower.algebraMap_apply k K
          (FF K (fun j => algebraMap k K (e j)))]

/-- Base change for every actual moved evaluation, without torsion hypotheses. -/
lemma movedValue_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (D : LocalData k e) (D' : LocalData K (fun j => algebraMap k K (e j)))
    (hh : D'.branch = PowerSeries.map (algebraMap k K) D.branch)
    (P Q Z : (Curve k e).Point) :
    algebraMap k K (movedValue k e D P Q Z) =
      movedValue K (fun j => algebraMap k K (e j)) D'
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P)
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) Q)
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) Z) := by
  have hE' := D'.embedding_spec
  rw [hh] at hE'
  have hv (R A : (Curve k e).Point) :
      algebraMap k K (value k e D (fourFunction k e R) A) =
        value K (fun j => algebraMap k K (e j)) D'
          (fourFunction K (fun j => algebraMap k K (e j))
            (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) R))
          (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) A) := by
    unfold value
    rw [localValue_baseChange k e he K D.translations D.translations_spec
      D'.translations D'.translations_spec D.branch D.embedding D.embedding_spec
      D'.embedding hE', fourFunction_baseChange k e he K]
  simp only [movedValue, map_mul, map_div₀, hv, map_add, map_neg, map_sub]

/-- Both geometric conclusions descend along the injective map to the algebraic closure. -/
lemma arithmetic_shift_and_power (he : Function.Injective e) (D : LocalData k e)
    (P Q Z W : (Curve k e).Point) (hP : 4 • P = 0) (hQ : 4 • Q = 0)
    (hZ : GoodShift k e P Q Z) (hW : GoodShift k e P Q W) :
    movedValue k e D P Q Z = movedValue k e D P Q W ∧
      movedValue k e D P Q Z ^ 4 = 1 := by
  let K := AlgebraicClosure k
  let : DecidableEq K := Classical.decEq K
  let c : k →+* K := algebraMap k K
  let eK : Fin 3 → K := c ∘ e
  let b := ArithmeticThetaMarkingR0115.fieldMap e c
  let hK : PowerSeries K := PowerSeries.map c D.branch
  have heK : Function.Injective eK := c.injective.comp he
  have hhK : ArithmeticThetaMillerR0114.branchEquation K eK hK :=
    branchEquation_baseChange k e K D.branch D.branch_spec
  obtain ⟨T', hT', _⟩ := function_field_translations K eK heK
  obtain ⟨E', hE', _⟩ := ArithmeticThetaMillerR0114.infinity_function_field_embedding
    K eK heK hK hhK
  let D' : LocalData K eK := ⟨T', hK, E', hT', hhK, hE'⟩
  have hp : 4 • b P = 0 := by rw [← map_nsmul, hP, map_zero]
  have hq : 4 • b Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hz : GoodShift K eK (b P) (b Q) (b Z) := goodShift_baseChange k e K P Q Z hZ
  have hw : GoodShift K eK (b P) (b Q) (b W) := goodShift_baseChange k e K P Q W hW
  have hv (A : (Curve k e).Point) :
      c (movedValue k e D P Q A) = movedValue K eK D' (b P) (b Q) (b A) :=
    movedValue_baseChange k e he K D D' rfl P Q A
  constructor
  · apply c.injective
    rw [hv, hv]
    exact closed_shift_independence K eK heK D' (b P) (b Q) (b Z) (b W) hp hq hz hw
  · apply c.injective
    rw [map_pow, map_one, hv]
    exact closed_fourth_power K eK heK D' (b P) (b Q) (b Z) hp hq hz

/-- The frozen all-pair support-independence theorem, including zero and two-torsion. -/
theorem pairing_shift_independence :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e,
    ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
    ArithmeticThetaMarkingR0115.IsBasis k e b →
    ∀ P Q : (Curve k e).Point, 4 • P = 0 → 4 • Q = 0 →
    (∀ Z : (Curve k e).Point, GoodShift k e P Q Z →
      value k e D (fourFunction k e P) (Q + Z) ≠ 0 ∧
      value k e D (fourFunction k e P) Z ≠ 0 ∧
      value k e D (fourFunction k e Q) (-Z) ≠ 0 ∧
      value k e D (fourFunction k e Q) (P - Z) ≠ 0 ∧
      movedValue k e D P Q Z = pairing k e D P Q) ∧
    pairing k e D P Q ^ 4 = 1 ∧
    (∀ D' : LocalData k e, pairing k e D' P Q = pairing k e D P Q) := by
  intro k _ _ _ e he D b hb P Q hP hQ
  obtain ⟨z, hz⟩ := (all_four_miller_provider k e he D).2 b hb P Q hP hQ
  have hex : ∃ Z : (Curve k e).Point, GoodShift k e P Q Z := ⟨_, hz⟩
  have hchosen := Classical.choose_spec hex
  have heq : pairing k e D P Q = movedValue k e D P Q (Classical.choose hex) := by
    simp only [pairing, dif_pos hex]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨ha, hb, hc, hd⟩ := general_arithmetic_moved_values_nonzero k e he
      D.translations D.translations_spec D.branch D.embedding D.branch_spec
      D.embedding_spec P Q Z hP hQ hZ
    refine ⟨ha, hb, hc, hd, ?_⟩
    rw [heq]
    exact (arithmetic_shift_and_power k e he D P Q Z (Classical.choose hex)
      hP hQ hZ hchosen).1
  · rw [heq]
    exact (arithmetic_shift_and_power k e he D P Q (Classical.choose hex)
      (Classical.choose hex) hP hQ hchosen hchosen).2
  · intro D'
    rw [local_data_unique k e D' D]

end ArithmeticThetaGeometricPairingR0118
