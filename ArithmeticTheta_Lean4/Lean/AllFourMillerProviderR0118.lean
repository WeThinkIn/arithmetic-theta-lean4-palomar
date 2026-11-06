import GeometricFourPairingDefinitionsR0118

/-! Complete normalized Miller providers, including zero and two-torsion,
and admissible shifts among the sixteen points of any full marking. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open WeierstrassCurve.Affine
open ArithmeticThetaReciprocityR0116
open ArithmeticThetaMillerR0114 (xFunction)

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

/-- Classify nonidentity rational two-torsion on the actual split cubic. -/
lemma two_torsion_label (P : (Curve k e).Point) (hP : 2 • P = 0) (hn : P ≠ 0) :
    ∃ (i : Fin 3) (hi : (Curve k e).Nonsingular (e i) 0),
      P = Point.some (e i) 0 hi := by
  cases P with
  | zero => exact False.elim (hn rfl)
  | some x y hp =>
    have hneg : Point.some x y hp = -Point.some x y hp := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [two_nsmul] using hP
    have hy : y = 0 := by
      have hh := (Point.some.inj hneg).2
      simp only [negY, Curve, ArithmeticThetaMillerR0114.Curve,
        ArithmeticThetaFourTorsion.splitCurve, zero_mul, sub_zero] at hh
      linear_combination (1/2 : k) * hh
    subst y
    have hx := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) x 0).mp hp.1
    simp only [zero_pow (by decide : 2 ≠ 0), eq_comm (a := (0 : k)),
      mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (hx | hx) | hx
    · subst x; exact ⟨0, hp, rfl⟩
    · subst x; exact ⟨1, hp, rfl⟩
    · subst x; exact ⟨2, hp, rfl⟩

/-- Squaring the actual vertical function gives the normalized two-torsion provider. -/
lemma vertical_square_provider (D : LocalData k e) (x : k)
    (hp : (Curve k e).Nonsingular x 0) :
    (xFunction k e - algebraMap k (FF k e) x)^2 ≠ 0 ∧
    (∀ Z : (Curve k e).Point,
      order k e D ((xFunction k e - algebraMap k (FF k e) x)^2) Z =
        (if Z = Point.some x 0 hp then 4 else 0) - (if Z = 0 then 4 else 0)) ∧
    localLeading k e D.translations D.embedding
      ((xFunction k e - algebraMap k (FF k e) x)^2) 0 = 1 := by
  have hi := vertical_at_infinity k e D.translations D.translations_spec
    D.branch D.embedding D.branch_spec D.embedding_spec x
  refine ⟨pow_ne_zero _ (x_sub_ne_zero k e x), ?_, ?_⟩
  · intro Z
    have hv := vertical_order_formula k e D.translations D.translations_spec
      D.branch D.embedding D.branch_spec D.embedding_spec x 0 hp Z
    have hn : -Point.some x 0 hp = Point.some x 0 hp := by
      rw [affine_neg]; simp
    rw [hn] at hv
    simp only [order, pointOrder, expansion, map_pow, HahnSeries.order_pow]
    change (2 : ℕ) • pointOrder k e D.translations D.embedding
      (xFunction k e - algebraMap k (FF k e) x) Z = _
    rw [hv]
    split_ifs <;> norm_num
  · simpa only [localLeading, expansion, map_pow, pow_two, map_mul, HahnSeries.leadingCoeff_mul,
      hi.2, one_mul] using congrArg (fun a : k => a * a) hi.2

/-- The explicit formula agrees with the accepted half-Miller function whenever
its point has exact order four. -/
lemma four_function_half (x y : k) (hp : (Curve k e).Nonsingular x y)
    (hy : y ≠ 0) (i : Fin 3) (hi : (Curve k e).Nonsingular (e i) 0)
    (hd : 2 • Point.some x y hp = Point.some (e i) 0 hi) :
    fourFunction k e (Point.some x y hp) = millerAt k e i (Point.some x y hp) := by
  simp only [fourFunction, if_neg hy, hd, ArithmeticThetaMarkingR0115.pointX,
    millerAt, ArithmeticThetaMillerR0114.millerFunction]

/-- Complete all-point divisor and infinity normalization without an exact-order hypothesis. -/
lemma four_function_provider (he : Function.Injective e) (D : LocalData k e)
    (P : (Curve k e).Point) (hP : 4 • P = 0) :
    fourFunction k e P ≠ 0 ∧
    (∀ Z : (Curve k e).Point, order k e D (fourFunction k e P) Z =
      (if Z = P then 4 else 0) - (if Z = 0 then 4 else 0)) ∧
    localLeading k e D.translations D.embedding (fourFunction k e P) 0 = 1 := by
  cases P with
  | zero =>
    change (1 : FF k e) ≠ 0 ∧
      (∀ Z, order k e D 1 Z = (if Z = 0 then 4 else 0) - (if Z = 0 then 4 else 0)) ∧ _
    simp [order, pointOrder, localLeading, expansion, fourFunction]
  | some x y hp =>
    by_cases hy : y = 0
    · subst y
      simpa only [fourFunction, ite_true] using vertical_square_provider k e D x hp
    · have hd : 2 • Point.some x y hp ≠ 0 := by
        intro hd
        obtain ⟨i, hi, heq⟩ := two_torsion_label k e _ hd (Point.some_ne_zero hp)
        exact hy (Point.some.inj heq).2
      have hfour : 2 • (2 • Point.some x y hp) = 0 := by
        simpa only [← mul_nsmul] using hP
      obtain ⟨i, hi, heq⟩ := two_torsion_label k e _ hfour hd
      rw [four_function_half k e x y hp hy i hi heq]
      exact complete_miller_divisor k e he D.translations D.translations_spec
        D.branch D.embedding D.branch_spec D.embedding_spec i _ ⟨hi, heq⟩

/-- At most four points are forbidden, whereas a full marking has sixteen distinct points.
This argument applies to arbitrary P and Q, and thus includes every degeneracy. -/
lemma basis_good_shift (b : ArithmeticThetaMarkingR0115.Marking k e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis k e b)
    (P Q : (Curve k e).Point) :
    ∃ z : Fin 2 → ZMod 4,
      GoodShift k e P Q (ArithmeticThetaMarkingR0115.coordinates k e b z) := by
  classical
  let S := Finset.univ.image (ArithmeticThetaMarkingR0115.coordinates k e b)
  let B : Finset (Curve k e).Point := {0, P, -Q, P-Q}
  have hs : S.card = 16 := by
    rw [Finset.card_image_of_injective _ hb.2.1]
    decide
  have hB : B.card ≤ 4 := Finset.card_le_four
  have hn : ¬ S ⊆ B := by
    intro h
    have hc := Finset.card_le_card h
    omega
  obtain ⟨Z, hZ, hZB⟩ := Finset.not_subset.mp hn
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hZ
  simp only [B, Finset.mem_insert, Finset.mem_singleton, not_or] at hZB
  refine ⟨z, hZB.1, hZB.2.1, ?_, ?_⟩
  · intro h
    apply hZB.2.2.1
    exact eq_neg_of_add_eq_zero_right h
  · intro h
    apply hZB.2.2.2
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

/-- The complete provider required by the geometric four-pairing construction. -/
theorem all_four_miller_provider :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e,
    (∀ P : (Curve k e).Point, 4 • P = 0 →
      fourFunction k e P ≠ 0 ∧
      (∀ Z : (Curve k e).Point, order k e D (fourFunction k e P) Z =
        (if Z = P then 4 else 0) - (if Z = 0 then 4 else 0)) ∧
      localLeading k e D.translations D.embedding (fourFunction k e P) 0 = 1) ∧
    (∀ b : ArithmeticThetaMarkingR0115.Marking k e,
      ArithmeticThetaMarkingR0115.IsBasis k e b →
      ∀ P Q : (Curve k e).Point, 4 • P = 0 → 4 • Q = 0 →
      ∃ z : Fin 2 → ZMod 4,
        GoodShift k e P Q (ArithmeticThetaMarkingR0115.coordinates k e b z)) := by
  intro k _ _ _ e he D
  exact ⟨four_function_provider k e he D, fun b hb P Q _ _ => basis_good_shift k e b hb P Q⟩

end ArithmeticThetaGeometricPairingR0118
