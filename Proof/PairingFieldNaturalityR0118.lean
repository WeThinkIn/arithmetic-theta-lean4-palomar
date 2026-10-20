module

public import PairingShiftIndependenceR0118

@[expose] public section
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Naturality of the actual moved-divisor pairing across arbitrary field universes.
The bridge below extends the accepted coordinate and Laurent-coefficient
constructions to two independent universes; accepted sources remain unchanged. -/
noncomputable section
universe u v
namespace ArithmeticThetaGeometricPairingR0118
open WeierstrassCurve.Affine
open ArithmeticThetaReciprocityR0116
namespace UniverseBridge
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

/-- The two base-changed coordinates define a map of actual function fields. -/
private lemma baseCoordinates (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
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
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    FF k e →ₐ[k] FF K (fun i => algebraMap k K (e i)) :=
  (baseCoordinates k e he K).choose

@[simp] theorem functionFieldBaseChange_x (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.xFunction k e) =
      ArithmeticThetaMillerR0114.xFunction K (fun i => algebraMap k K (e i)) := by
  exact (baseCoordinates k e he K).choose_spec.1

@[simp] theorem functionFieldBaseChange_y (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K] :
    functionFieldBaseChange k e he K (ArithmeticThetaMillerR0114.yFunction k e) =
      ArithmeticThetaMillerR0114.yFunction K (fun i => algebraMap k K (e i)) := by
  exact (baseCoordinates k e he K).choose_spec.2

/-- Apply the coefficient embedding to each Laurent coefficient. -/
def laurentBaseChange (K : Type v) [Field K] [Algebra k K] :
    LaurentSeries k →+* LaurentSeries K where
  toFun s := s.map (algebraMap k K)
  map_zero' := HahnSeries.map_zero (algebraMap k K).toZeroHom
  map_one' := HahnSeries.map_one (algebraMap k K).toMonoidWithZeroHom
  map_add' s t := HahnSeries.map_add (algebraMap k K).toAddMonoidHom
  map_mul' s t := HahnSeries.map_mul (algebraMap k K).toNonUnitalRingHom

@[simp] theorem laurentBaseChange_coeff (K : Type v) [Field K] [Algebra k K]
    (s : LaurentSeries k) (n : ℤ) :
    (laurentBaseChange k K s).coeff n = algebraMap k K (s.coeff n) := rfl

/-- The explicit generic chord coordinates commute with coefficient extension. -/
theorem translatedCoordinates_baseChange (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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
      have hsum :
          algebraMap k (FF K (fun i => algebraMap k K (e i))) (e 0) +
            algebraMap k (FF K (fun i => algebraMap k K (e i))) (e 1) +
            algebraMap k (FF K (fun i => algebraMap k K (e i))) (e 2) =
          algebraMap K (FF K (fun i => algebraMap k K (e i)))
            (algebraMap k K (e 0) + algebraMap k K (e 1) + algebraMap k K (e 2)) := by
        rw [map_add, map_add]
        simp only [← IsScalarTower.algebraMap_apply k K
          (FF K (fun i => algebraMap k K (e i)))]
      exact ⟨hsum, Or.inl hsum⟩

/-- Pullback by a rational point commutes with the coefficient-induced map. -/
theorem translation_baseChange (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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
    (K : Type v) [Field K] [Algebra k K]
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
    (K : Type v) [Field K] [Algebra k K] (s : PowerSeries k) :
    laurentBaseChange k K (algebraMap (PowerSeries k) (LaurentSeries k) s) =
      algebraMap (PowerSeries K) (LaurentSeries K)
        (PowerSeries.map (algebraMap k K) s) := by
  apply HahnSeries.ext
  funext n
  simp only [LaurentSeries.coe_algebraMap, laurentBaseChange_coeff,
    PowerSeries.coeff_coe, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem laurentBaseChange_parameter
    (K : Type v) [Field K] [Algebra k K] :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.parameter k) =
      ArithmeticThetaMillerR0114.parameter K := by
  simp only [ArithmeticThetaMillerR0114.parameter,
    laurentBaseChange_powerSeries, PowerSeries.map_X]

def laurentBaseChangeAlgHom
    (K : Type v) [Field K] [Algebra k K] :
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
    (K : Type v) [Field K] [Algebra k K] (h : PowerSeries k) :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.infinityX k h) =
      ArithmeticThetaMillerR0114.infinityX K
        (PowerSeries.map (algebraMap k K) h) := by
  simp only [ArithmeticThetaMillerR0114.infinityX, map_mul,
    map_zpow₀, laurentBaseChange_parameter,
    laurentBaseChange_powerSeries]

theorem infinityY_baseChange
    (K : Type v) [Field K] [Algebra k K] (h : PowerSeries k) :
    laurentBaseChange k K (ArithmeticThetaMillerR0114.infinityY k h) =
      ArithmeticThetaMillerR0114.infinityY K
        (PowerSeries.map (algebraMap k K) h) := by
  simp only [ArithmeticThetaMillerR0114.infinityY, map_neg,
    map_mul, map_zpow₀, laurentBaseChange_parameter,
    laurentBaseChange_powerSeries]

theorem infinityEmbedding_baseChange (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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


/-- The displayed tangent/vertical formulas commute with the coefficient-induced map. -/
lemma fourFunction_baseChange (he : Function.Injective e)
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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
    (K : Type v) [Field K] [CharZero K] [DecidableEq K] [Algebra k K]
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


end UniverseBridge

/-- Every characteristic-zero coefficient embedding preserves the actual pairing,
including pairs containing zero or nonzero two-torsion. -/
theorem pairing_field_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ D : LocalData k e,
    ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
    ArithmeticThetaMarkingR0115.IsBasis k e b →
    ∀ (K : Type v) [Field K] [CharZero K] [DecidableEq K]
      (f : k →+* K)
      (F : (Curve k e).Point →+ (Curve K (f ∘ e)).Point),
    ArithmeticThetaMarkingR0115.IsCoordinateMap k K e f F →
    ∀ D' : LocalData K (f ∘ e),
    ∀ P Q : (Curve k e).Point, 4 • P = 0 → 4 • Q = 0 →
    f (pairing k e D P Q) = pairing K (f ∘ e) D' (F P) (F Q) := by
  intro k _ _ _ e he D b hb K _ _ _ f F hF D' P Q hP hQ
  rw [ArithmeticThetaMarkingR0115.coordinateMap_unique e f F hF]
  letI : Algebra k K := f.toAlgebra
  have heK : Function.Injective (f ∘ e) := f.injective.comp he
  have hbK := ArithmeticThetaMarkingR0115.fieldMap_basis e he f b hb
  let B := ArithmeticThetaMarkingR0115.fieldMap e f
  have hp : 4 • B P = 0 := by rw [← map_nsmul, hP, map_zero]
  have hq : 4 • B Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  obtain ⟨z, hz⟩ := (all_four_miller_provider k e he D).2 b hb P Q hP hQ
  let Z := ArithmeticThetaMarkingR0115.coordinates k e b z
  have hzK : GoodShift K (f ∘ e) (B P) (B Q) (B Z) := by
    have hi : Function.Injective B := ArithmeticThetaMarkingR0115.fieldMap_injective e f
    change Z ≠ 0 ∧ Z ≠ P ∧ Q + Z ≠ 0 ∧ Q + Z ≠ P at hz
    change B Z ≠ 0 ∧ B Z ≠ B P ∧ B Q + B Z ≠ 0 ∧ B Q + B Z ≠ B P
    simpa only [← map_zero B, ← map_add B, hi.ne_iff] using hz
  have hh : D'.branch = PowerSeries.map (algebraMap k K) D.branch :=
    (ArithmeticThetaMillerR0114.infinity_branch K (f ∘ e)).unique
      D'.branch_spec (UniverseBridge.branchEquation_baseChange k e K D.branch D.branch_spec)
  have hs := (pairing_shift_independence k e he D b hb P Q hP hQ).1 Z hz
  have ht := (pairing_shift_independence K (f ∘ e) heK D'
    (B ∘ b) hbK (B P) (B Q) hp hq).1 (B Z) hzK
  rw [← hs.2.2.2.2, ← ht.2.2.2.2]
  exact UniverseBridge.movedValue_baseChange k e he K D D' hh P Q Z

end ArithmeticThetaGeometricPairingR0118
