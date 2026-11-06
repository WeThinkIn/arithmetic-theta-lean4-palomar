import GeometricFourPairingDefinitionsR0118

noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord pointIdeal xFunction yFunction)
open ArithmeticThetaReciprocityR0116
set_option maxHeartbeats 800000

private lemma span_series_parameter {k : Type u} [Field k] (s : PowerSeries k)
    (hs : (algebraMap (PowerSeries k) (LaurentSeries k) s).order = 1) :
    Ideal.span {s} = Ideal.span {PowerSeries.X} := by
  have sn : s ≠ 0 := by intro h; simp [h] at hs
  have hd : PowerSeries.X ∣ s := by
    simpa using (series_order_iff_dvd s sn 1).mp (by omega)
  obtain ⟨v, hv⟩ := hd
  have hvu : IsUnit v := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.mpr hz
    have h2 : PowerSeries.X^2 ∣ s := ⟨w, by rw [hv, hw]; ring⟩
    have := (series_order_iff_dvd s sn 2).mpr h2
    omega
  apply Ideal.span_singleton_eq_span_singleton.mpr
  rw [hv]
  exact (associated_mul_unit_right _ _ hvu).symm

private lemma series_order_of_span {k : Type u} [Field k] (s t : PowerSeries k)
    (hs : s ≠ 0) (_ht : t ≠ 0) (H : Ideal.span {s} = Ideal.span {t}) :
    (algebraMap (PowerSeries k) (LaurentSeries k) s).order =
      (algebraMap (PowerSeries k) (LaurentSeries k) t).order := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp H
  have hv0 : PowerSeries.constantCoeff (v : PowerSeries k) ≠ 0 :=
    isUnit_iff_ne_zero.mp (PowerSeries.isUnit_iff_constantCoeff.mp v.isUnit)
  have sn : algebraMap (PowerSeries k) (LaurentSeries k) s ≠ 0 :=
    fun hz => hs (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using hz))
  have vn : algebraMap (PowerSeries k) (LaurentSeries k) (v : PowerSeries k) ≠ 0 :=
    fun hz => v.ne_zero (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using hz))
  rw [← hv, map_mul, HahnSeries.order_mul sn vn, series_order_zero k _ hv0, add_zero]

section
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (D : LocalData k e)
variable (z w : k) (hz : (Curve k e).Nonsingular z w)

private abbrev φ := localSeriesHom k e D.translations D.translations_spec
  D.branch D.embedding D.branch_spec D.embedding_spec z w hz

include he in
private lemma map_pointIdeal (a b : k) :
    Ideal.map (φ k e D z w hz) (pointIdeal k e a b) =
      Ideal.span {(PowerSeries.X : PowerSeries k) ^ (if z = a ∧ w = b then 1 else 0)} := by
  let F := φ k e D z w hz
  have hk := localSeriesHom_kernel k e D.translations D.translations_spec
    D.branch D.embedding D.branch_spec D.embedding_spec z w hz
  by_cases hab : z = a ∧ w = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [and_self, ↓reduceIte, pow_one]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro t ht
      apply Ideal.mem_span_singleton.mpr
      apply PowerSeries.X_dvd_iff.mpr
      simpa [hk, RingHom.mem_ker] using ht
    · obtain ⟨t, ht, htm, hto⟩ := affine_parameter k e he D.translations D.translations_spec
        D.branch D.embedding D.branch_spec D.embedding_spec z w hz
      have hto' : (algebraMap (PowerSeries k) (LaurentSeries k) (F t)).order = 1 := by
        rw [localSeriesHom_spec]
        exact hto
      rw [← span_series_parameter (F t) hto']
      exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem F htm)
  · simp only [hab, ↓reduceIte, pow_zero, Ideal.span_singleton_one]
    have hn : ¬ pointIdeal k e a b ≤ pointIdeal k e z w := by
      intro hle
      obtain ⟨ha, hb⟩ := pointIdeal_coordinates_of_le k e D.translations D.translations_spec
        D.branch D.embedding D.branch_spec D.embedding_spec a b z w hz hle
      exact hab ⟨ha.symm, hb.symm⟩
    obtain ⟨t, htm, ht⟩ := SetLike.not_le_iff_exists.mp hn
    have htu : IsUnit (F t) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      apply isUnit_iff_ne_zero.mpr
      simpa [hk, RingHom.mem_ker] using ht
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem F htm) htu

omit [CharZero k] [DecidableEq k] in
private lemma field_line (a b m : k) :
    algebraMap (Coord k e) (FF k e)
      (CoordinateRing.YClass (Curve k e) (linePolynomial a b m)) =
    yFunction k e - algebraMap k (FF k e) b -
      algebraMap k (FF k e) m * (xFunction k e - algebraMap k (FF k e) a) := by
  simp [CoordinateRing.YClass, CoordinateRing.XClass, yFunction, xFunction,
    linePolynomial, CoordinateRing.mk, map_sub, map_add, map_mul,
    IsScalarTower.algebraMap_eq k (Coord k e) (FF k e), AdjoinRoot.algebraMap_eq']
  ring

include he in
private lemma chord_affine_order (a b c d : k)
    (hp : (Curve k e).Nonsingular a b) (hq : (Curve k e).Nonsingular c d)
    (hne : ¬ (a = c ∧ b = (Curve k e).negY c d)) :
    order k e D
      (algebraMap (Coord k e) (FF k e)
        (CoordinateRing.YClass (Curve k e) (linePolynomial a b ((Curve k e).slope a c b d))))
      (.some z w hz) -
    order k e D
      (algebraMap (Coord k e) (FF k e)
        (CoordinateRing.XClass (Curve k e) ((Curve k e).addX a c ((Curve k e).slope a c b d))))
      (.some z w hz) =
      (if z = a ∧ w = b then 1 else 0) + (if z = c ∧ w = d then 1 else 0) -
      (if z = (Curve k e).addX a c ((Curve k e).slope a c b d) ∧
        w = (Curve k e).addY a c b ((Curve k e).slope a c b d) then 1 else 0) := by
  let F := φ k e D z w hz
  let j := algebraMap (PowerSeries k) (LaurentSeries k)
  let A := (Curve k e).addX a c ((Curve k e).slope a c b d)
  let B := (Curve k e).addY a c b ((Curve k e).slope a c b d)
  let V := CoordinateRing.XClass (Curve k e) A
  let L := CoordinateRing.YClass (Curve k e) (linePolynomial a b ((Curve k e).slope a c b d))
  let np : ℕ := if z = a ∧ w = b then 1 else 0
  let nq : ℕ := if z = c ∧ w = d then 1 else 0
  let nr : ℕ := if z = A ∧ w = B then 1 else 0
  have hi := congrArg (Ideal.map F) (CoordinateRing.XYIdeal_mul_XYIdeal hp.1 hq.1 hne)
  change Ideal.map F (Ideal.span {V} * (pointIdeal k e a b * pointIdeal k e c d)) =
    Ideal.map F (Ideal.span {L} * pointIdeal k e A B) at hi
  simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hi
  rw [map_pointIdeal k e he D z w hz a b, map_pointIdeal k e he D z w hz c d,
    map_pointIdeal k e he D z w hz A B] at hi
  change Ideal.span {F V} * (Ideal.span {PowerSeries.X^np} * Ideal.span {PowerSeries.X^nq}) =
    Ideal.span {F L} * Ideal.span {PowerSeries.X^nr} at hi
  simp only [Ideal.span_singleton_mul_span_singleton] at hi
  have Fn (t : Coord k e) (ht : t ≠ 0) : F t ≠ 0 :=
    fun h => ht (localSeriesHom_injective k e D.translations D.translations_spec
      D.branch D.embedding D.branch_spec D.embedding_spec z w hz (by simpa using h))
  have jn (s : PowerSeries k) (hs : s ≠ 0) : j s ≠ 0 :=
    fun h => hs (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [j] using h))
  have hnV := Fn V (CoordinateRing.XClass_ne_zero _)
  have hnL := Fn L (CoordinateRing.YClass_ne_zero _)
  have hnX (n : ℕ) : (PowerSeries.X : PowerSeries k)^n ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  have H := series_order_of_span _ _ (mul_ne_zero hnV (mul_ne_zero (hnX np) (hnX nq)))
    (mul_ne_zero hnL (hnX nr)) hi
  simp only [map_mul] at H
  change (j (F V) * (j (PowerSeries.X^np) * j (PowerSeries.X^nq))).order =
    (j (F L) * j (PowerSeries.X^nr)).order at H
  rw [HahnSeries.order_mul (jn _ hnV) (mul_ne_zero (jn _ (hnX np)) (jn _ (hnX nq))),
    HahnSeries.order_mul (jn _ (hnX np)) (jn _ (hnX nq)),
    HahnSeries.order_mul (jn _ hnL) (jn _ (hnX nr))] at H
  have hX (n : ℕ) : (j (PowerSeries.X^n)).order = n := by
    simp only [j, map_pow, HahnSeries.order_pow]
    change n • (HahnSeries.ofPowerSeries ℤ k PowerSeries.X).order = _
    rw [HahnSeries.ofPowerSeries_X, HahnSeries.order_single one_ne_zero]
    simp
  change (j (F V)).order + ((j (PowerSeries.X^np)).order + (j (PowerSeries.X^nq)).order) =
    (j (F L)).order + (j (PowerSeries.X^nr)).order at H
  rw [hX, hX, hX] at H
  have hF (t : Coord k e) : (j (F t)).order =
      order k e D (algebraMap (Coord k e) (FF k e) t) (.some z w hz) := by
    rw [localSeriesHom_spec]; rfl
  rw [hF, hF] at H
  dsimp only [V, L, np, nq, nr, A, B] at H
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at H
  omega

omit [DecidableEq k] in
private lemma line_infinity_order (a b m : k) :
    order k e D (yFunction k e - algebraMap k (FF k e) b -
      algebraMap k (FF k e) m * (xFunction k e - algebraMap k (FF k e) a)) 0 = -3 := by
  let s : PowerSeries k := -D.branch - PowerSeries.C b * PowerSeries.X^3 -
    PowerSeries.C m * PowerSeries.X * (D.branch - PowerSeries.C a * PowerSeries.X^2)
  have hc : PowerSeries.constantCoeff s = -1 := by simp [s, D.branch_spec.1]
  have hn : algebraMap (PowerSeries k) (LaurentSeries k) s ≠ 0 := by
    intro h
    have hs : s = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using h)
    simp [hs] at hc
  have ht : ArithmeticThetaMillerR0114.parameter k ^ (-3 : ℤ) =
      HahnSeries.single (-3 : ℤ) (1 : k) := by
    rw [RatFunc.single_zpow]
    congr 1
    exact HahnSeries.ofPowerSeries_X
  have H : expansion k e D.translations D.embedding 0
      (yFunction k e - algebraMap k (FF k e) b -
        algebraMap k (FF k e) m * (xFunction k e - algebraMap k (FF k e) a)) =
      HahnSeries.single (-3 : ℤ) (1 : k) * algebraMap (PowerSeries k) (LaurentSeries k) s := by
    unfold expansion
    rw [translation_zero k e D.translations D.translations_spec]
    change D.embedding (_ - _ - _ * (_ - _)) = _
    rw [map_sub, map_sub, map_mul, map_sub, D.embedding.commutes,
      D.embedding.commutes, D.embedding.commutes, D.embedding_spec.1, D.embedding_spec.2]
    simp only [s, map_sub, map_neg, map_mul, map_pow, ← ht,
      ArithmeticThetaMillerR0114.infinityX, ArithmeticThetaMillerR0114.infinityY,
      zpow_neg, zpow_ofNat]
    change -((ArithmeticThetaMillerR0114.parameter k ^ 3)⁻¹ * _) - _ - _ *
      ((ArithmeticThetaMillerR0114.parameter k ^ 2)⁻¹ * _ - _) =
      (ArithmeticThetaMillerR0114.parameter k ^ 3)⁻¹ *
        (-_ - algebraMap k (LaurentSeries k) b * ArithmeticThetaMillerR0114.parameter k ^ 3 -
         algebraMap k (LaurentSeries k) m * ArithmeticThetaMillerR0114.parameter k *
           (_ - algebraMap k (LaurentSeries k) a * ArithmeticThetaMillerR0114.parameter k ^ 2))
    field_simp [ArithmeticThetaMillerR0114.parameter_ne_zero k]
  unfold order pointOrder
  rw [H, HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero) hn,
    HahnSeries.order_single one_ne_zero, series_order_zero k s (by rw [hc]; exact neg_ne_zero.mpr one_ne_zero)]
  norm_num

end
/-- The divisor of the actual addition function, including all repeated-point cases. -/
theorem addition_function_divisor :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e, ∀ P Q : (Curve k e).Point,
    additionFunction k e P Q ≠ 0 ∧ ∀ Z : (Curve k e).Point,
    order k e D (additionFunction k e P Q) Z =
      (if Z = P then 1 else 0) + (if Z = Q then 1 else 0) -
      (if Z = P + Q then 1 else 0) - (if Z = 0 then 1 else 0) := by
  intro k _ _ _ e he D P Q
  have oneord (Z : (Curve k e).Point) : order k e D 1 Z = 0 := by
    simp [order, pointOrder, expansion]
  cases P with
  | zero =>
    constructor
    · exact one_ne_zero
    · intro Z
      simp only [additionFunction, oneord, show (Point.zero : (Curve k e).Point) = 0 from rfl, zero_add]
      omega
  | some a b hp =>
    cases Q with
    | zero =>
      constructor
      · exact one_ne_zero
      · intro Z
        simp only [additionFunction, oneord, show (Point.zero : (Curve k e).Point) = 0 from rfl, add_zero]
        omega
    | some c d hq =>
      have hvn (x : k) : xFunction k e - algebraMap k (FF k e) x ≠ 0 := by
        rw [← field_XClass]
        simpa only [map_zero] using (IsFractionRing.injective (Coord k e) (FF k e)).ne (CoordinateRing.XClass_ne_zero x)
      have hln (x y m : k) : yFunction k e - algebraMap k (FF k e) y -
          algebraMap k (FF k e) m * (xFunction k e - algebraMap k (FF k e) x) ≠ 0 := by
        rw [← field_line]
        simpa only [map_zero] using (IsFractionRing.injective (Coord k e) (FF k e)).ne
          (CoordinateRing.YClass_ne_zero (W' := Curve k e) (linePolynomial x y m))
      by_cases hanti : a = c ∧ b = -d
      · have hneg : b = (Curve k e).negY c d := by
          simpa [negY, Curve, ArithmeticThetaMillerR0114.Curve,
            ArithmeticThetaFourTorsion.splitCurve] using hanti.2
        have hsum : Point.some a b hp + Point.some c d hq = 0 := Point.add_of_Y_eq hanti.1 hneg
        have hqp : Point.some c d hq = -Point.some a b hp := eq_neg_of_add_eq_zero_right hsum
        simp only [additionFunction, if_pos hanti]
        refine ⟨hvn a, ?_⟩
        intro Z
        have H := vertical_order_formula k e D.translations D.translations_spec D.branch D.embedding
          D.branch_spec D.embedding_spec a b hp Z
        change order k e D (xFunction k e - algebraMap k (FF k e) a) Z = _ at H
        rw [hsum, hqp]
        rw [H]
        split_ifs <;> omega
      · have hne : ¬ (a = c ∧ b = (Curve k e).negY c d) := by
          simpa [negY, Curve, ArithmeticThetaMillerR0114.Curve,
            ArithmeticThetaFourTorsion.splitCurve] using hanti
        have hs := Point.add_some (h₁ := hp) (h₂ := hq) hne
        let A := (Curve k e).addX a c ((Curve k e).slope a c b d)
        let B := (Curve k e).addY a c b ((Curve k e).slope a c b d)
        have hden : ArithmeticThetaMarkingR0115.pointX k e
            (Point.some a b hp + Point.some c d hq) = A := by
          rw [hs]; rfl
        simp only [additionFunction, if_neg hanti, hden]
        refine ⟨div_ne_zero (hln _ _ _) (hvn _), ?_⟩
        intro Z
        change pointOrder k e D.translations D.embedding (_ / _) Z = _
        rw [pointOrder_div k e D.translations D.embedding Z _ _ (hln _ _ _) (hvn _)]
        cases Z with
        | zero =>
          change order k e D _ 0 - order k e D _ 0 = _
          rw [line_infinity_order]
          have hv := (vertical_at_infinity k e D.translations D.translations_spec
            D.branch D.embedding D.branch_spec D.embedding_spec A).1
          change order k e D _ 0 = -2 at hv
          rw [hv, hs]
          simp [show (Point.zero : (Curve k e).Point) = 0 from rfl]
        | some z w hz =>
          have H := chord_affine_order k e he D z w hz a b c d hp hq hne
          rw [field_line, field_XClass] at H
          change order k e D _ (.some z w hz) - order k e D _ (.some z w hz) = _
          rw [H, hs]
          simp only [Point.some.injEq, Point.some_ne_zero, if_false, sub_zero]

end ArithmeticThetaGeometricPairingR0118
