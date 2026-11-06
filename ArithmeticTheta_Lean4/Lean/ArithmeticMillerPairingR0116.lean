import MovedSupportMillerPairingR0116
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Arithmetic-field components of the moved Miller pairing. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open WeierstrassCurve.Affine

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

private lemma half_nonzero (i : Fin 3) (P : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e i P) : P ≠ 0 := by
  intro h
  obtain ⟨hp, hd⟩ := hP
  rw [h, smul_zero] at hd
  exact (Point.some_ne_zero hp) hd.symm

private lemma half_four (i : Fin 3) (P : (Curve k e).Point)
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

private lemma halves_independent (he : Function.Injective e)
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
  have hQ4 : 4 • Q = 0 := half_four k e 1 Q ⟨hq, hdQ⟩
  have hQ2 : 2 • (2 • Q) = 0 := by
    rw [← mul_nsmul]
    norm_num at hQ4 ⊢
    exact hQ4
  refine ⟨fun h => hd (congrArg (2 • ·) h), ?_, ?_⟩
  · intro h
    exact hP2 (by rw [h, hQ2])
  · intro h
    exact hP2 (by rw [← h, hQ2])

/-- The second half itself is an admissible rational shift. -/
theorem arithmetic_good_shift (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    GoodShift k e P Q Q := by
  have hN := halves_independent k e he P Q hP hQ
  have hQ0 := half_nonzero k e 1 Q hQ
  have h2Q0 : 2 • Q ≠ 0 := by
    obtain ⟨hq, hdQ⟩ := hQ
    rw [hdQ]
    exact Point.some_ne_zero hq
  simpa only [GoodShift, ← two_nsmul] using
    (show Q ≠ 0 ∧ Q ≠ P ∧ 2 • Q ≠ 0 ∧ 2 • Q ≠ P from
      ⟨hQ0, hN.1.symm, h2Q0, hN.2.2⟩)

private lemma local_value_ne_zero_of_order_zero
    (T : Translations k e) (E : FF k e →ₐ[k] LaurentSeries k)
    (f : FF k e) (P : (Curve k e).Point) (hf : f ≠ 0)
    (ho : pointOrder k e T E f P = 0) : localValue k e T E f P ≠ 0 := by
  have hn := localLeading_ne_zero k e T E P hf
  unfold localValue localLeading pointOrder expansion at *
  rw [HahnSeries.leadingCoeff_eq, ho] at hn
  exact hn

/-- All four evaluations in the moved expression are units at a good shift. -/
theorem arithmetic_moved_values_nonzero (he : Function.Injective e)
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
  · apply local_value_ne_zero_of_order_zero k e T E _ _ hdivP.1
    rw [hdivP.2.1]
    simp [hZ.2.2.2, hZ.2.2.1]
  · apply local_value_ne_zero_of_order_zero k e T E _ _ hdivP.1
    rw [hdivP.2.1]
    simp [hZ.2.1, hZ.1]
  · apply local_value_ne_zero_of_order_zero k e T E _ _ hdivQ.1
    rw [hdivQ.2.1]
    simp [hnegQ, hneg0]
  · apply local_value_ne_zero_of_order_zero k e T E _ _ hdivQ.1
    rw [hdivQ.2.1]
    simp [hsubQ, hsub0]

/-- The fixed-label phase is primitive over the original field. -/
theorem arithmetic_fixed_phase_primitive (he : Function.Injective e)
    (P Q : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q) :
    IsPrimitiveRoot (fixedLabelPhase k e P Q) 4 := by
  cases P with
  | zero => exact False.elim ((half_nonzero k e 0 0 hP) rfl)
  | @some x y hp =>
    cases Q with
    | zero => exact False.elim ((half_nonzero k e 1 0 hQ) rfl)
    | @some a b hq =>
      have hp' : ArithmeticThetaMillerR0114.IsHalf k e 0 x y :=
        ⟨hp, hP.1, hP.2⟩
      have hq' : ArithmeticThetaMillerR0114.IsHalf k e 1 a b :=
        ⟨hq, hQ.1, hQ.2⟩
      exact (ArithmeticThetaMillerR0114.actual_miller_phase k e he x y a b hp' hq').2

/-- The two base-changed coordinates define a map of actual function fields. -/
private lemma baseCoordinates (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    ∃ F : FF k e →ₐ[k] FF K (fun i => algebraMap k K (e i)),
      F (ArithmeticThetaMillerR0114.xFunction k e) =
        ArithmeticThetaMillerR0114.xFunction K (fun i => algebraMap k K (e i)) ∧
      F (ArithmeticThetaMillerR0114.yFunction k e) =
        ArithmeticThetaMillerR0114.yFunction K (fun i => algebraMap k K (e i)) := by
  let eK : Fin 3 → K := fun i => algebraMap k K (e i)
  have heK : Function.Injective eK := (algebraMap k K).injective.comp he
  have ht : Transcendental k (ArithmeticThetaMillerR0114.xFunction K eK) :=
    (x_transcendental K eK heK).of_tower_top k
  have hq := generic_equation K eK heK
  have hq' :
      (ArithmeticThetaMillerR0114.yFunction K eK)^2 =
        (ArithmeticThetaMillerR0114.xFunction K eK)^3 -
          algebraMap k (FF K eK) (e 0 + e 1 + e 2) *
            (ArithmeticThetaMillerR0114.xFunction K eK)^2 +
          algebraMap k (FF K eK) (e 0 * e 1 + e 0 * e 2 + e 1 * e 2) *
            ArithmeticThetaMillerR0114.xFunction K eK -
          algebraMap k (FF K eK) (e 0 * e 1 * e 2) := by
    simpa only [eK, ← map_add, ← map_mul,
      IsScalarTower.algebraMap_apply k K (FF K eK)] using hq
  exact lift_coordinates k e
    (ArithmeticThetaMillerR0114.xFunction K eK)
    (ArithmeticThetaMillerR0114.yFunction K eK) ht hq'

/-- Base change of the actual function field, determined by its two coordinates. -/
def functionFieldBaseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    FF k e →ₐ[k] FF K (fun i => algebraMap k K (e i)) :=
  (baseCoordinates k e he K).choose

@[simp] theorem functionFieldBaseChange_x (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.xFunction k e) =
      ArithmeticThetaMillerR0114.xFunction K (fun i => algebraMap k K (e i)) := by
  exact (baseCoordinates k e he K).choose_spec.1

@[simp] theorem functionFieldBaseChange_y (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.yFunction k e) =
      ArithmeticThetaMillerR0114.yFunction K (fun i => algebraMap k K (e i)) := by
  exact (baseCoordinates k e he K).choose_spec.2

/-- Apply the coefficient embedding to each Laurent coefficient. -/
def laurentBaseChange (K : Type u) [Field K] [Algebra k K] :
    LaurentSeries k →+* LaurentSeries K where
  toFun s := s.map (algebraMap k K)
  map_zero' := HahnSeries.map_zero (algebraMap k K).toZeroHom
  map_one' := HahnSeries.map_one (algebraMap k K).toMonoidWithZeroHom
  map_add' s t := HahnSeries.map_add (algebraMap k K).toAddMonoidHom
  map_mul' s t := HahnSeries.map_mul (algebraMap k K).toNonUnitalRingHom

@[simp] theorem laurentBaseChange_coeff (K : Type u) [Field K] [Algebra k K]
    (s : LaurentSeries k) (n : ℤ) :
    (laurentBaseChange k K s).coeff n = algebraMap k K (s.coeff n) := rfl

theorem laurentBaseChange_injective (K : Type u) [Field K] [Algebra k K] :
    Function.Injective (laurentBaseChange k K) := RingHom.injective _

theorem laurentBaseChange_support (K : Type u) [Field K] [Algebra k K]
    (s : LaurentSeries k) :
    (laurentBaseChange k K s).support = s.support := by
  ext n
  simp only [HahnSeries.mem_support, laurentBaseChange_coeff]
  exact (map_ne_zero_iff (algebraMap k K) (algebraMap k K).injective)

theorem laurentBaseChange_order (K : Type u) [Field K] [Algebra k K]
    (s : LaurentSeries k) :
    (laurentBaseChange k K s).order = s.order := by
  have hs := laurentBaseChange_support k K s
  by_cases hz : s = 0
  · subst s
    simp
  · have hm : laurentBaseChange k K s ≠ 0 :=
      by simpa using (laurentBaseChange_injective k K).ne hz
    simp only [HahnSeries.order, dif_neg hm, dif_neg hz]
    simp only [hs]

/-- The explicit generic chord coordinates commute with coefficient extension. -/
theorem translatedCoordinates_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (P : (Curve k e).Point) :
    let b := functionFieldBaseChange k e he K
    let c := algebraMap k K
    let P' := ArithmeticThetaMarkingR0115.fieldMap e c P
    b (translatedCoordinates k e P).1 =
      (translatedCoordinates K (c ∘ e) P').1 ∧
    b (translatedCoordinates k e P).2 =
      (translatedCoordinates K (c ∘ e) P').2 := by
  cases P with
  | zero =>
      simp [translatedCoordinates, ArithmeticThetaMarkingR0115.fieldMap,
        functionFieldBaseChange_x, functionFieldBaseChange_y, Function.comp_def]
  | some a b hp =>
      simp [translatedCoordinates, ArithmeticThetaMarkingR0115.fieldMap,
        functionFieldBaseChange_x, functionFieldBaseChange_y, Function.comp_def]
      simp only [← IsScalarTower.algebraMap_apply k K
        (FF K (fun i => algebraMap k K (e i)))]
      simp

/-- Pullback by a rational point commutes with the coefficient-induced map. -/
theorem translation_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (T' : Translations K (fun i => algebraMap k K (e i)))
    (hT' : IsTranslationSystem K (fun i => algebraMap k K (e i)) T')
    (P : (Curve k e).Point) (f : FF k e) :
    functionFieldBaseChange k e he K (T P f) =
      T' (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P)
        (functionFieldBaseChange k e he K f) := by
  let b := functionFieldBaseChange k e he K
  let P' := ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P
  have h : b.comp (T P).toAlgHom =
      ((T' P').toAlgHom.restrictScalars k).comp b := by
    apply ff_ext k e
    · change b (T P (ArithmeticThetaMillerR0114.xFunction k e)) =
          T' P' (b (ArithmeticThetaMillerR0114.xFunction k e))
      rw [(hT P).1, show b (ArithmeticThetaMillerR0114.xFunction k e) =
        ArithmeticThetaMillerR0114.xFunction K (fun i => algebraMap k K (e i)) from
          functionFieldBaseChange_x k e he K, (hT' P').1]
      exact (translatedCoordinates_baseChange k e he K P).1
    · change b (T P (ArithmeticThetaMillerR0114.yFunction k e)) =
          T' P' (b (ArithmeticThetaMillerR0114.yFunction k e))
      rw [(hT P).2, show b (ArithmeticThetaMillerR0114.yFunction k e) =
        ArithmeticThetaMillerR0114.yFunction K (fun i => algebraMap k K (e i)) from
          functionFieldBaseChange_y k e he K, (hT' P').2]
      exact (translatedCoordinates_baseChange k e he K P).2
  exact DFunLike.congr_fun h f

/-- The full infinity branch remains a branch after coefficient extension. -/
theorem branchEquation_baseChange
    (K : Type u) [Field K] [Algebra k K]
    (h : PowerSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h) :
    ArithmeticThetaMillerR0114.branchEquation K
      (fun i => algebraMap k K (e i))
      (PowerSeries.map (algebraMap k K) h) := by
  rcases hh with ⟨h0, heq⟩
  constructor
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_one] using
      congrArg (algebraMap k K) h0
  · have hm := congrArg (PowerSeries.map (algebraMap k K)) heq
    simpa only [map_pow, map_prod, map_sub, map_mul,
      PowerSeries.map_C, PowerSeries.map_X, Function.comp_def] using hm

theorem laurentBaseChange_powerSeries
    (K : Type u) [Field K] [Algebra k K] (s : PowerSeries k) :
    laurentBaseChange k K (algebraMap (PowerSeries k) (LaurentSeries k) s) =
      algebraMap (PowerSeries K) (LaurentSeries K)
        (PowerSeries.map (algebraMap k K) s) := by
  apply HahnSeries.ext
  funext n
  simp only [LaurentSeries.coe_algebraMap, laurentBaseChange_coeff,
    PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem laurentBaseChange_parameter
    (K : Type u) [Field K] [Algebra k K] :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.parameter k) =
      ArithmeticThetaMillerR0114.parameter K := by
  simp only [ArithmeticThetaMillerR0114.parameter,
    laurentBaseChange_powerSeries, PowerSeries.map_X]

def laurentBaseChangeAlgHom
    (K : Type u) [Field K] [Algebra k K] :
    LaurentSeries k →ₐ[k] LaurentSeries K where
  toRingHom := laurentBaseChange k K
  commutes' a := by
    have hk : algebraMap k (LaurentSeries K) a =
        HahnSeries.C ((algebraMap k K) a) := by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        HahnSeries.ofPowerSeries_C]
    apply HahnSeries.ext
    funext n
    change ((laurentBaseChange k K) (algebraMap k (LaurentSeries k) a)).coeff n =
      (algebraMap k (LaurentSeries K) a).coeff n
    rw [laurentBaseChange_coeff]
    rw [LaurentSeries.algebraMap_apply]
    rw [hk]
    simp only [HahnSeries.C, HahnSeries.coeff_single]
    by_cases hn : n = 0 <;> simp [hn]

theorem infinityX_baseChange
    (K : Type u) [Field K] [Algebra k K] (h : PowerSeries k) :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.infinityX k h) =
      ArithmeticThetaMillerR0114.infinityX K
        (PowerSeries.map (algebraMap k K) h) := by
  simp only [ArithmeticThetaMillerR0114.infinityX, map_mul,
    map_zpow₀, laurentBaseChange_parameter,
    laurentBaseChange_powerSeries]

theorem infinityY_baseChange
    (K : Type u) [Field K] [Algebra k K] (h : PowerSeries k) :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.infinityY k h) =
      ArithmeticThetaMillerR0114.infinityY K
        (PowerSeries.map (algebraMap k K) h) := by
  simp only [ArithmeticThetaMillerR0114.infinityY, map_neg,
    map_mul, map_zpow₀, laurentBaseChange_parameter,
    laurentBaseChange_powerSeries]

theorem infinityEmbedding_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (E' : FF K (fun i => algebraMap k K (e i)) →ₐ[K] LaurentSeries K)
    (hE' : ArithmeticThetaMillerR0114.IsInfinityEmbedding K
      (fun i => algebraMap k K (e i))
      (PowerSeries.map (algebraMap k K) h) E')
    (f : FF k e) :
    laurentBaseChange k K (E f) =
      E' (functionFieldBaseChange k e he K f) := by
  let E0 : FF K (fun i => algebraMap k K (e i)) →ₐ[k] LaurentSeries K :=
    { E'.toRingHom with
      commutes' := by
        intro a
        rw [IsScalarTower.algebraMap_apply k K
          (FF K (fun i => algebraMap k K (e i)))]
        change E' (algebraMap K _ (algebraMap k K a)) = _
        rw [E'.commutes]
        simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          HahnSeries.ofPowerSeries_C, Algebra.algebraMap_self, RingHom.id_apply] }
  have hm : (laurentBaseChangeAlgHom k K).comp E =
      E0.comp (functionFieldBaseChange k e he K) := by
    apply ff_ext k e
    · change laurentBaseChange k K (E (ArithmeticThetaMillerR0114.xFunction k e)) =
        E' (functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.xFunction k e))
      rw [functionFieldBaseChange_x, hE.1, hE'.1]
      exact infinityX_baseChange k K h
    · change laurentBaseChange k K (E (ArithmeticThetaMillerR0114.yFunction k e)) =
        E' (functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.yFunction k e))
      rw [functionFieldBaseChange_y, hE.2, hE'.2]
      exact infinityY_baseChange k K h
  exact DFunLike.congr_fun hm f

theorem localValue_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (T' : Translations K (fun i => algebraMap k K (e i)))
    (hT' : IsTranslationSystem K (fun i => algebraMap k K (e i)) T')
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (E' : FF K (fun i => algebraMap k K (e i)) →ₐ[K] LaurentSeries K)
    (hE' : ArithmeticThetaMillerR0114.IsInfinityEmbedding K
      (fun i => algebraMap k K (e i))
      (PowerSeries.map (algebraMap k K) h) E')
    (f : FF k e) (P : (Curve k e).Point) :
    algebraMap k K (localValue k e T E f P) =
      localValue K (fun i => algebraMap k K (e i)) T' E'
        (functionFieldBaseChange k e he K f)
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P) := by
  unfold localValue expansion
  rw [← laurentBaseChange_coeff k K (E (T P f)) 0,
    infinityEmbedding_baseChange k e he K h E hE E' hE',
    translation_baseChange k e he K T hT T' hT' P f]

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

theorem millerAt_baseChange (he : Function.Injective e)
    (K : Type u) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
    (i : Fin 3) (P : (Curve k e).Point) :
    functionFieldBaseChange k e he K (millerAt k e i P) =
      millerAt K (fun j => algebraMap k K (e j)) i
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P) := by
  cases P with
  | zero => simp [millerAt, ArithmeticThetaMarkingR0115.fieldMap]
  | some x y hp =>
      have hs : ArithmeticThetaMillerR0114.tangentSlope K
          (fun j => algebraMap k K (e j))
          (algebraMap k K x) (algebraMap k K y) =
          algebraMap k K (ArithmeticThetaMillerR0114.tangentSlope k e x y) := by
        have hm := (Curve k e).map_slope (algebraMap k K) x x y y
        rw [ArithmeticThetaMarkingR0115.curve_map e (algebraMap k K)] at hm
        exact hm
      change functionFieldBaseChange k e he K
          (ArithmeticThetaMillerR0114.millerFunction k e i x y) =
        ArithmeticThetaMillerR0114.millerFunction K
          (fun j => algebraMap k K (e j)) i
          (algebraMap k K x) (algebraMap k K y)
      simp only [ArithmeticThetaMillerR0114.millerFunction,
        tangentFunction_eq, map_div₀, map_pow, map_sub, map_mul,
        functionFieldBaseChange_x, functionFieldBaseChange_y,
        AlgHom.commutes, hs]
      simp only [← IsScalarTower.algebraMap_apply k K
        (FF K (fun j => algebraMap k K (e j)))]

private lemma millerValue_baseChange
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K]
    (i : Fin 3) (x y a b : k) :
    algebraMap k K (ArithmeticThetaMillerR0114.millerValue k e i x y a b) =
      ArithmeticThetaMillerR0114.millerValue K
        (fun j => algebraMap k K (e j)) i
        (algebraMap k K x) (algebraMap k K y)
        (algebraMap k K a) (algebraMap k K b) := by
  have hs : ArithmeticThetaMillerR0114.tangentSlope K
      (fun j => algebraMap k K (e j))
      (algebraMap k K x) (algebraMap k K y) =
      algebraMap k K (ArithmeticThetaMillerR0114.tangentSlope k e x y) := by
    have hm := (Curve k e).map_slope (algebraMap k K) x x y y
    rw [ArithmeticThetaMarkingR0115.curve_map e (algebraMap k K)] at hm
    exact hm
  simp [ArithmeticThetaMillerR0114.millerValue,
    ArithmeticThetaMillerR0114.tangentValue, hs]

theorem fixedLabelPhase_baseChange
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K]
    (P Q : (Curve k e).Point) :
    algebraMap k K (fixedLabelPhase k e P Q) =
      fixedLabelPhase K (fun j => algebraMap k K (e j))
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P)
        (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) Q) := by
  cases P with
  | zero => simp [fixedLabelPhase, ArithmeticThetaMarkingR0115.fieldMap]
  | some x y hp =>
    cases Q with
    | zero => simp [fixedLabelPhase, ArithmeticThetaMarkingR0115.fieldMap]
    | some a b hq =>
      change algebraMap k K (ArithmeticThetaMillerR0114.millerRatio k e x y a b) =
        ArithmeticThetaMillerR0114.millerRatio K
          (fun j => algebraMap k K (e j))
          (algebraMap k K x) (algebraMap k K y)
          (algebraMap k K a) (algebraMap k K b)
      simp only [ArithmeticThetaMillerR0114.millerRatio, map_div₀,
        millerValue_baseChange]

theorem goodShift_baseChange
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K]
    (P Q Z : (Curve k e).Point) (hZ : GoodShift k e P Q Z) :
    GoodShift K (fun j => algebraMap k K (e j))
      (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P)
      (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) Q)
      (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) Z) := by
  have hinj := ArithmeticThetaMarkingR0115.fieldMap_injective e (algebraMap k K)
  rcases hZ with ⟨h0, hP, hQ0, hQP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    exact h0 (hinj (by simpa using hz))
  · exact hinj.ne hP
  · intro hz
    exact hQ0 (hinj (by simpa only [map_add, map_zero] using hz))
  · intro hz
    exact hQP (hinj (by simpa only [map_add] using hz))

theorem halfPoint_baseChange
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K]
    (i : Fin 3) (P : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e i P) :
    ArithmeticThetaMillerR0114.IsHalfPoint K
      (fun j => algebraMap k K (e j)) i
      (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K) P) := by
  obtain ⟨hp, hd⟩ := hP
  have hm := congrArg (ArithmeticThetaMarkingR0115.fieldMap e (algebraMap k K)) hd
  simp only [map_nsmul, ArithmeticThetaMarkingR0115.fieldMap_some] at hm
  have hn : (Curve K (fun j => algebraMap k K (e j))).Nonsingular
      (algebraMap k K (e i)) 0 := by
    have hs := ((Curve k e).map_nonsingular (algebraMap k K).injective (e i) 0).mpr hp
    rw [ArithmeticThetaMarkingR0115.curve_map e (algebraMap k K)] at hs
    simpa only [map_zero, Function.comp_def] using hs
  exact ⟨hn, by simpa only [map_zero] using hm⟩

theorem arithmetic_moved_phase (he : Function.Injective e)
    (T : Translations k e) (hT : IsTranslationSystem k e T)
    (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (P Q Z : (Curve k e).Point)
    (hP : ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P)
    (hQ : ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q)
    (hZ : GoodShift k e P Q Z) :
    movedPairing k e T E P Q Z = fixedLabelPhase k e P Q := by
  let K := AlgebraicClosure k
  letI : DecidableEq K := Classical.decEq K
  let c : k →+* K := algebraMap k K
  let eK : Fin 3 → K := c ∘ e
  let b := ArithmeticThetaMarkingR0115.fieldMap e c
  let hK : PowerSeries K := PowerSeries.map c h
  have heK : Function.Injective eK := c.injective.comp he
  have hhK : ArithmeticThetaMillerR0114.branchEquation K eK hK :=
    branchEquation_baseChange k e K h hh
  obtain ⟨T', hT', _⟩ := function_field_translations K eK heK
  obtain ⟨E', hE', _⟩ := ArithmeticThetaMillerR0114.infinity_function_field_embedding
    K eK heK hK hhK
  have hPK : ArithmeticThetaMillerR0114.IsHalfPoint K eK 0 (b P) := by
    simpa only [eK, b, c, Function.comp_def] using
      halfPoint_baseChange k e K 0 P hP
  have hQK : ArithmeticThetaMillerR0114.IsHalfPoint K eK 1 (b Q) := by
    simpa only [eK, b, c, Function.comp_def] using
      halfPoint_baseChange k e K 1 Q hQ
  have hZK : GoodShift K eK (b P) (b Q) (b Z) := by
    simpa only [eK, b, c, Function.comp_def] using
      goodShift_baseChange k e K P Q Z hZ
  have hgeom := (moved_support_miller_pairing K eK heK T' hT'
    hK E' hhK hE' (b P) (b Q) hPK hQK).2.1 (b Z) hZK
  have hval (i : Fin 3) (R A : (Curve k e).Point) :
      c (localValue k e T E (millerAt k e i R) A) =
        localValue K eK T' E' (millerAt K eK i (b R)) (b A) := by
    rw [localValue_baseChange k e he K T hT T' hT' h E hE E' hE'
      (millerAt k e i R) A, millerAt_baseChange k e he K i R]
    rfl
  apply c.injective
  change c (movedPairing k e T E P Q Z) = c (fixedLabelPhase k e P Q)
  rw [fixedLabelPhase_baseChange k e K P Q]
  have hp : c (movedPairing k e T E P Q Z) =
      movedPairing K eK T' E' (b P) (b Q) (b Z) := by
    simp only [movedPairing, map_mul, map_div₀, hval]
    rw [b.map_add, b.map_neg, b.map_sub]
  rw [hp]
  simpa only [eK, b, c, Function.comp_def] using hgeom.2.2.2.2

/-- The moved Miller pairing identity descends to every characteristic-zero field. -/
theorem arithmetic_miller_pairing (he : Function.Injective e) :
    ∃ (T : Translations k e) (h : PowerSeries k)
      (E : FF k e →ₐ[k] LaurentSeries k),
      IsTranslationSystem k e T ∧
      ArithmeticThetaMillerR0114.branchEquation k e h ∧
      ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E ∧
      (∀ P Q : (Curve k e).Point,
        ArithmeticThetaMillerR0114.IsHalfPoint k e 0 P →
        ArithmeticThetaMillerR0114.IsHalfPoint k e 1 Q →
        (∃ Z : (Curve k e).Point, GoodShift k e P Q Z) ∧
        (∀ Z : (Curve k e).Point, GoodShift k e P Q Z →
          localValue k e T E (millerAt k e 0 P) (Q + Z) ≠ 0 ∧
          localValue k e T E (millerAt k e 0 P) Z ≠ 0 ∧
          localValue k e T E (millerAt k e 1 Q) (-Z) ≠ 0 ∧
          localValue k e T E (millerAt k e 1 Q) (P - Z) ≠ 0 ∧
          movedPairing k e T E P Q Z = fixedLabelPhase k e P Q) ∧
        IsPrimitiveRoot (fixedLabelPhase k e P Q) 4) := by
  obtain ⟨T, hT, _⟩ := function_field_translations k e he
  obtain ⟨h, E, hh, hE, _⟩ :=
    ArithmeticThetaMillerR0114.exists_infinity_embedding k e he
  refine ⟨T, h, E, hT, hh, hE, ?_⟩
  intro P Q hP hQ
  refine ⟨⟨Q, arithmetic_good_shift k e he P Q hP hQ⟩, ?_,
    arithmetic_fixed_phase_primitive k e he P Q hP hQ⟩
  intro Z hZ
  obtain ⟨ha, hb, hc, hd⟩ :=
    arithmetic_moved_values_nonzero k e he T hT h E hh hE P Q Z hP hQ hZ
  exact ⟨ha, hb, hc, hd,
    arithmetic_moved_phase k e he T hT h E hh hE P Q Z hP hQ hZ⟩

end ArithmeticThetaReciprocityR0116
