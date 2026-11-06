import AdditionFunctionDivisorR0118
import PairingShiftIndependenceR0118

/-! Bilinearity of the actual moved-divisor evaluation. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open ArithmeticThetaReciprocityR0116
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

private def quotient (he : Function.Injective e) (D : LocalData k e)
    (P Q : (Curve k e).Point) : FF k e :=
  (D.translations Q (fourFunction k e P) / fourFunction k e P) *
    (curveNegation k e he (fourFunction k e Q) /
      curveNegation k e he (D.translations P (fourFunction k e Q)))

private def symbol (he : Function.Injective e) (D : LocalData k e)
    (P Q : (Curve k e).Point) : k :=
  value k e D (quotient k e he D P Q) 0

private lemma quotient_constant [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q : (Curve k e).Point) (hP : 4 • P = 0) (hQ : 4 • Q = 0) :
    quotient k e he D P Q = algebraMap k (FF k e) (symbol k e he D P Q) := by
  exact acceptedOrderZeroConstant k e he D.translations D.translations_spec
    D.branch D.embedding D.branch_spec D.embedding_spec _
    (general_moved_quotient_order_zero k e he D.translations D.translations_spec
      D.branch D.embedding D.branch_spec D.embedding_spec P Q · hP hQ)

private lemma moved_eq_symbol [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q Z : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) (hZ : GoodShift k e P Q Z) :
    movedValue k e D P Q Z = symbol k e he D P Q :=
  general_moved_pairing_of_function_field_identity k e he D.translations
    D.translations_spec D.branch D.embedding D.branch_spec D.embedding_spec
    P Q Z hP hQ hZ _ (quotient_constant k e he D P Q hP hQ)

/-- The chord divisor measures the discrepancy before translation. -/
private lemma addition_order_discrepancy (he : Function.Injective e) (D : LocalData k e)
    (P Q A : (Curve k e).Point) (hP : 4 • P = 0) (hQ : 4 • Q = 0) :
    order k e D (fourFunction k e P) A + order k e D (fourFunction k e Q) A -
      order k e D (fourFunction k e (P + Q)) A =
        4 * order k e D (additionFunction k e P Q) A := by
  have hPQ : 4 • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  rw [(four_function_provider k e he D P hP).2.1,
    (four_function_provider k e he D Q hQ).2.1,
    (four_function_provider k e he D (P + Q) hPQ).2.1,
    (addition_function_divisor k e he D P Q).2]
  split_ifs <;> omega

/-- Translation cancels precisely the chord-divisor discrepancy. -/
private lemma translated_product_constant [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q : (Curve k e).Point) (hP : 4 • P = 0) (hQ : 4 • Q = 0) :
    ∃ c : k, c ≠ 0 ∧ fourFunction k e (P + Q) =
      algebraMap k (FF k e) c *
        (fourFunction k e P * D.translations (-P) (fourFunction k e Q)) := by
  let T := D.translations
  let f := fourFunction k e
  have hPQ : 4 • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  have hp := (four_function_provider k e he D P hP).1
  have hq := (four_function_provider k e he D Q hQ).1
  have hpq := (four_function_provider k e he D (P + Q) hPQ).1
  have ht : T (-P) (f Q) ≠ 0 := by simpa using (T (-P)).injective.ne hq
  have hden : f P * T (-P) (f Q) ≠ 0 := mul_ne_zero hp ht
  let H := f (P + Q) / (f P * T (-P) (f Q))
  have ho (A : (Curve k e).Point) : pointOrder k e T D.embedding H A = 0 := by
    have hdisc := addition_order_discrepancy k e he D P Q A hP hQ
    have htrans : order k e D (T (-P) (f Q)) A - order k e D (f Q) A =
        -(4 * order k e D (additionFunction k e P Q) A) := by
      change pointOrder k e T D.embedding (T (-P) (f Q)) A - _ = _
      rw [(principal_divisor_support k e he T D.translations_spec D.branch D.embedding
        D.branch_spec D.embedding_spec (f Q) hq).2]
      change order k e D (f Q) (A + -P) - order k e D (f Q) A = _
      rw [(four_function_provider k e he D Q hQ).2.1,
        (four_function_provider k e he D Q hQ).2.1,
        (addition_function_divisor k e he D P Q).2]
      have h1 : (A + -P = Q) ↔ A = P + Q := by
        constructor
        · intro h
          calc A = P + (A + -P) := by abel
               _ = P + Q := by rw [h]
        · intro h; rw [h]; abel
      have h2 : (A + -P = 0) ↔ A = P := by rw [← sub_eq_add_neg, sub_eq_zero]
      simp only [h1, h2]
      split_ifs <;> omega
    dsimp [H]
    rw [pointOrder_div k e T D.embedding A _ _ hpq hden,
      pointOrder_mul k e T D.embedding A hp ht]
    change order k e D (f (P + Q)) A -
      (order k e D (f P) A + order k e D (T (-P) (f Q)) A) = 0
    linarith
  have hc := acceptedOrderZeroConstant k e he T D.translations_spec D.branch
    D.embedding D.branch_spec D.embedding_spec H ho
  let c := localValue k e T D.embedding H 0
  have hcn : c ≠ 0 := by
    intro hz
    have hn : H ≠ 0 := div_ne_zero hpq hden
    exact hn (hc.trans (by change algebraMap k (FF k e) c = 0; rw [hz, map_zero]))
  refine ⟨c, hcn, ?_⟩
  exact (div_eq_iff hden).mp hc

private lemma symbol_add_left [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q R : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) (hR : 4 • R = 0) :
    symbol k e he D (P + Q) R = symbol k e he D P R * symbol k e he D Q R := by
  have hPQ : 4 • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  obtain ⟨c, hc, hsum⟩ := translated_product_constant k e he D P Q hP hQ
  have hp := (four_function_provider k e he D P hP).1
  have hq := (four_function_provider k e he D Q hQ).1
  have hr := (four_function_provider k e he D R hR).1
  have hcf : algebraMap k (FF k e) c ≠ 0 := by simpa using (algebraMap k (FF k e)).injective.ne hc
  have htq : D.translations (-P) (fourFunction k e Q) ≠ 0 := by simpa using (D.translations (-P)).injective.ne hq
  have hnpr : curveNegation k e he (D.translations P (fourFunction k e R)) ≠ 0 := by
    simpa using (curveNegation k e he).injective.ne ((D.translations P).injective.ne hr)
  have hnpqr : curveNegation k e he (D.translations (P + Q) (fourFunction k e R)) ≠ 0 := by
    simpa using (curveNegation k e he).injective.ne ((D.translations (P + Q)).injective.ne hr)
  have hprod : quotient k e he D (P + Q) R =
      quotient k e he D P R * D.translations (-P) (quotient k e he D Q R) := by
    simp only [quotient, hsum, map_mul, map_div₀, AlgEquiv.commutes,
      curveNegation_translation k e he D.translations D.translations_spec,
      neg_neg, (translation_composition k e he D.translations D.translations_spec).2.1]
    rw [show R + -P = -P + R by abel]
    field_simp [hcf, hp, htq, hnpr, hnpqr]
  apply (algebraMap k (FF k e)).injective
  rw [map_mul, ← quotient_constant k e he D (P + Q) R hPQ hR,
    ← quotient_constant k e he D P R hP hR]
  rw [hprod, quotient_constant k e he D Q R hQ hR, AlgEquiv.commutes]

private lemma symbol_swap [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) :
    symbol k e he D P Q * symbol k e he D Q P = 1 := by
  have hp := (four_function_provider k e he D P hP).1
  have hq := (four_function_provider k e he D Q hQ).1
  have hnq : curveNegation k e he (fourFunction k e Q) ≠ 0 := by
    simpa using (curveNegation k e he).injective.ne hq
  have hnpq : curveNegation k e he (D.translations P (fourFunction k e Q)) ≠ 0 := by
    simpa using (curveNegation k e he).injective.ne ((D.translations P).injective.ne hq)
  have htqp : D.translations Q (fourFunction k e P) ≠ 0 := by
    simpa using (D.translations Q).injective.ne hp
  have hprod : quotient k e he D P Q *
      curveNegation k e he (quotient k e he D Q P) = 1 := by
    simp only [quotient, map_mul, map_div₀]
    rw [curveNegation_involutive k e he _, curveNegation_involutive k e he _]
    field_simp [hp, hnq, hnpq, htqp]
  apply (algebraMap k (FF k e)).injective
  rw [map_mul, map_one, ← quotient_constant k e he D P Q hP hQ]
  rw [quotient_constant k e he D Q P hQ hP, AlgEquiv.commutes] at hprod
  exact hprod

private lemma symbol_add_right [IsAlgClosed k] (he : Function.Injective e)
    (D : LocalData k e) (P Q R : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) (hR : 4 • R = 0) :
    symbol k e he D P (Q + R) = symbol k e he D P Q * symbol k e he D P R := by
  have hQR : 4 • (Q + R) = 0 := by rw [nsmul_add, hQ, hR, add_zero]
  have h1 := symbol_swap k e he D P (Q + R) hP hQR
  have h2 := symbol_swap k e he D P Q hP hQ
  have h3 := symbol_swap k e he D P R hP hR
  rw [symbol_add_left k e he D Q R P hQ hR hP] at h1
  have hn : symbol k e he D Q P * symbol k e he D R P ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  apply mul_right_cancel₀ hn
  calc
    _ = 1 := h1
    _ = (symbol k e he D P Q * symbol k e he D Q P) *
        (symbol k e he D P R * symbol k e he D R P) := by rw [h2, h3, one_mul]
    _ = _ := by ring

/-- Descent uses the coefficient-induced function-field and expansion maps. -/
private lemma arithmetic_moved_bilinearity (he : Function.Injective e) (D : LocalData k e)
    (P Q R A B C F G : (Curve k e).Point)
    (hP : 4 • P = 0) (hQ : 4 • Q = 0) (hR : 4 • R = 0)
    (hA : GoodShift k e (P + Q) R A)
    (hB : GoodShift k e P R B) (hC : GoodShift k e Q R C)
    (hF : GoodShift k e P (Q + R) F) (hG : GoodShift k e P Q G) :
    movedValue k e D (P + Q) R A = movedValue k e D P R B * movedValue k e D Q R C ∧
    movedValue k e D P (Q + R) F = movedValue k e D P Q G * movedValue k e D P R B := by
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
  have hr : 4 • b R = 0 := by rw [← map_nsmul, hR, map_zero]
  have hpq : 4 • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  have hqr : 4 • (Q + R) = 0 := by rw [nsmul_add, hQ, hR, add_zero]
  have hv (X Y Z : (Curve k e).Point) (hx : 4 • X = 0) (hy : 4 • Y = 0)
      (hz : GoodShift k e X Y Z) :
      c (movedValue k e D X Y Z) = symbol K eK heK D' (b X) (b Y) := by
    rw [show c (movedValue k e D X Y Z) = movedValue K eK D' (b X) (b Y) (b Z) from
      movedValue_baseChange k e he K D D' rfl X Y Z]
    exact moved_eq_symbol K eK heK D' (b X) (b Y) (b Z)
      (by rw [← map_nsmul, hx, map_zero]) (by rw [← map_nsmul, hy, map_zero])
      (goodShift_baseChange k e K X Y Z hz)
  constructor
  · apply c.injective
    rw [map_mul, hv (P + Q) R A hpq hR hA, hv P R B hP hR hB, hv Q R C hQ hR hC,
      map_add]
    exact symbol_add_left K eK heK D' (b P) (b Q) (b R) hp hq hr
  · apply c.injective
    rw [map_mul, hv P (Q + R) F hP hqr hF, hv P Q G hP hQ hG, hv P R B hP hR hB,
      map_add]
    exact symbol_add_right K eK heK D' (b P) (b Q) (b R) hp hq hr

/-- Both laws for the unchanged rational-function evaluation pairing. -/
theorem pairing_bilinearity :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e,
    ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
    ArithmeticThetaMarkingR0115.IsBasis k e b →
    ∀ P Q R : (Curve k e).Point, 4 • P = 0 → 4 • Q = 0 → 4 • R = 0 →
    pairing k e D (P + Q) R = pairing k e D P R * pairing k e D Q R ∧
    pairing k e D P (Q + R) = pairing k e D P Q * pairing k e D P R := by
  intro k _ _ _ e he D b hb P Q R hP hQ hR
  have hpq : 4 • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  have hqr : 4 • (Q + R) = 0 := by rw [nsmul_add, hQ, hR, add_zero]
  have hex (X Y : (Curve k e).Point) (hx : 4 • X = 0) (hy : 4 • Y = 0) :
      ∃ Z, GoodShift k e X Y Z := by
    obtain ⟨z, hz⟩ := (all_four_miller_provider k e he D).2 b hb X Y hx hy
    exact ⟨_, hz⟩
  obtain ⟨A, hA⟩ := hex (P + Q) R hpq hR
  obtain ⟨B, hB⟩ := hex P R hP hR
  obtain ⟨C, hC⟩ := hex Q R hQ hR
  obtain ⟨F, hF⟩ := hex P (Q + R) hP hqr
  obtain ⟨G, hG⟩ := hex P Q hP hQ
  have hm (X Y Z : (Curve k e).Point) (hx : 4 • X = 0) (hy : 4 • Y = 0)
      (hz : GoodShift k e X Y Z) : movedValue k e D X Y Z = pairing k e D X Y :=
    ((pairing_shift_independence k e he D b hb X Y hx hy).1 Z hz).2.2.2.2
  have H := arithmetic_moved_bilinearity k e he D P Q R A B C F G hP hQ hR hA hB hC hF hG
  rw [hm (P + Q) R A hpq hR hA, hm P R B hP hR hB, hm Q R C hQ hR hC,
    hm P (Q + R) F hP hqr hF, hm P Q G hP hQ hG] at H
  exact H

end ArithmeticThetaGeometricPairingR0118
