module

public import RelativeSplitFiberBasisR0211

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativeGeometricPhase
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaMillerR0114 WeierstrassCurve.Affine

/-- Polynomial numerators of the normalized tangent evaluations. -/
def tangentNumerator {A : Type u} [CommRing A] (e : Fin 3 → A)
    (x y : Fin 2 → A) (i j : Fin 2) : A :=
  y j * (x i - e i.castSucc) - y i * (x j - e i.castSucc)

def numerator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) : A :=
  tangentNumerator e x y 0 1 ^ 2 * (x 1 - e 1)^2 * (x 0 - e 1)

def denominator {A : Type u} [CommRing A] (e : Fin 3 → A) (x y : Fin 2 → A) : A :=
  (x 0 - e 0)^2 * (x 1 - e 0) * tangentNumerator e x y 1 0 ^ 2

lemma map_numerator {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (e : Fin 3 → A) (x y : Fin 2 → A) :
    f (numerator e x y) = numerator (f ∘ e) (f ∘ x) (f ∘ y) := by
  simp [numerator, tangentNumerator]

lemma map_denominator {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (e : Fin 3 → A) (x y : Fin 2 → A) :
    f (denominator e x y) = denominator (f ∘ e) (f ∘ x) (f ∘ y) := by
  simp [denominator, tangentNumerator]

lemma half_slope {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    {e : Fin 3 → F} {i : Fin 3} {x y : F} (h : IsHalf F e i x y)
    (hx : x ≠ e i) : tangentSlope F e x y = y / (x - e i) := by
  obtain ⟨hR, hP, hd⟩ := h
  have hn : y ≠ (Curve F e).negY x y := by
    intro heq
    have hz : 2 • Point.some x y hR = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq heq]
    exact Point.some_ne_zero hP (hd.symm.trans hz)
  rw [two_nsmul, Point.add_self_of_Y_ne hn] at hd
  obtain ⟨hX, hY⟩ := Point.some.inj hd
  simp only [addY, negAddY, negY, hX] at hY
  change -(tangentSlope F e x y * (e i - x) + y) - 0 * e i - 0 = 0 at hY
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  linear_combination hY

/-- Clear only geometrically nonzero denominators in the normalized Miller ratio. -/
lemma field_formula {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (e : Fin 3 → F) (x y : Fin 2 → F) (he : Function.Injective e)
    (h0 : IsHalf F e 0 (x 0) (y 0)) (h1 : IsHalf F e 1 (x 1) (y 1)) :
    denominator e x y ≠ 0 ∧
    millerRatio F e (x 0) (y 0) (x 1) (y 1) = numerator e x y / denominator e x y := by
  obtain ⟨_, _, hx, _, hL⟩ := half_tangent_evaluation_nonzero F e he _ _ _ _ h0 h1
  have ht0 : tangentValue F e (x 0) (y 0) (x 1) (y 1) =
      tangentNumerator e x y 0 1 / (x 0 - e 0) := by
    rw [tangentValue, half_slope h0 (hx 0).1]
    dsimp [tangentNumerator]
    field_simp [sub_ne_zero.mpr (hx 0).1]
    <;> ring
  have ht1 : tangentValue F e (x 1) (y 1) (x 0) (y 0) =
      tangentNumerator e x y 1 0 / (x 1 - e 1) := by
    rw [tangentValue, half_slope h1 (hx 1).2]
    dsimp [tangentNumerator]
    field_simp [sub_ne_zero.mpr (hx 1).2]
    <;> ring
  have hN : tangentNumerator e x y 1 0 ≠ 0 := by
    intro hz
    apply hL
    rw [ht1, hz, zero_div]
  refine ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (hx 0).1))
    (sub_ne_zero.mpr (hx 0).2)) (pow_ne_zero _ hN), ?_⟩
  simp only [millerRatio, millerValue, ht0, ht1, numerator, denominator]
  field_simp

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

lemma coordinate_unique {P : Base R ⟶ ArithmeticThetaRelativeKatoR0169.Curve R W}
    {a b c d : R} (h : HasCoordinates R W P a b) (h' : HasCoordinates R W P c d) :
    a = c ∧ b = d := by
  exact ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    W.toProjective).2 ⟨P, h.1⟩ ⟨P, h'.1⟩ a b c d
      (TwoTorsionSplitCubicR0177.sectionThrough h)
      (TwoTorsionSplitCubicR0177.sectionThrough h')).mp rfl

lemma coordinates_unique (M : FullLevel R W G 4 (𝟙 (Base R)))
    {e e' : Fin 3 → R} {x y x' y' : Fin 2 → R}
    (h : Coordinates R W G M e x y) (h' : Coordinates R W G M e' x' y') :
    e = e' ∧ x = x' ∧ y = y' := by
  refine ⟨funext (fun i => (coordinate_unique W (h.1 i) (h'.1 i)).1), ?_, ?_⟩
  · funext i
    fin_cases i
    · exact (coordinate_unique W h.2.2.1 h'.2.2.1).1
    · exact (coordinate_unique W h.2.2.2 h'.2.2.2).1
  · funext i
    fin_cases i
    · exact (coordinate_unique W h.2.2.1 h'.2.2.1).2
    · exact (coordinate_unique W h.2.2.2 h'.2.2.2).2

include hG in
lemma pairing_formula (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F)
    (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e))
    (hb : FiberCoordinates R W e x y F ι b)
    (D : ArithmeticThetaGeometricPairingR0118.LocalData F (ι ∘ e)) :
    let Y := fun i => completedY R W (x i) (y i)
    ι (denominator e x Y) ≠ 0 ∧
    ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1) =
      ι (numerator e x Y) / ι (denominator e x Y) := by
  let Y := fun i => completedY R W (x i) (y i)
  obtain ⟨he, _, hbas⟩ := (relative_split_fiber_basis R W G hG M).2 e x y hC F ι
  obtain ⟨hB, hl⟩ := hbas b hb
  have hh := RelativeSplitFiberBasis.fiber_half W G hG M e x y hC F ι
  have hhalf (i : Fin 2) : IsHalf F (ι ∘ e) i.castSucc (ι (x i)) (ι (Y i)) := by
    obtain ⟨h, hp, hd⟩ := hh i
    exact ⟨h, hp, hd⟩
  have hf := field_formula (ι ∘ e) (ι ∘ x) (ι ∘ Y) he (hhalf 0) (hhalf 1)
  rw [← map_denominator, ← map_numerator] at hf
  refine ⟨hf.1, ?_⟩
  rw [ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F (ι ∘ e) he D b hB]
  have hp : ArithmeticThetaMarkingR0115.phase F (ι ∘ e) b =
      millerRatio F (ι ∘ e) (ι (x 0)) (ι (Y 0)) (ι (x 1)) (ι (Y 1)) := by
    simp only [ArithmeticThetaMarkingR0115.phase, ArithmeticThetaMarkingR0115.tangent,
      hl, (hb 0).2.1, (hb 0).2.2, (hb 1).2.1, (hb 1).2.2,
      millerRatio, millerValue, Function.comp_apply, Y]
  exact hp.trans hf.2

end RelativeGeometricPhase

/-- The primitive moved-divisor phase extends uniquely from the generic fiber
and agrees with the same pairing on every field-valued point of the base. -/
theorem relative_geometric_phase :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∃! z : R, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z ∧ IsUnit z ∧ IsPrimitiveRoot z 4 := by
  intro R _ _ _ _ _ W _ G hG M
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero K := charZero_of_injective_algebraMap hf
  obtain ⟨e, x, y, hC⟩ := (relative_split_fiber_basis R W G hG M).1
  obtain ⟨he, ⟨b, hb, _⟩, hB⟩ :=
    (relative_split_fiber_basis R W G hG M).2 e x y hC K f
  obtain ⟨D, hD⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character K (f ∘ e) he
  let q := ArithmeticThetaGeometricPairingR0118.pairing K (f ∘ e) D (b 0) (b 1)
  have hq : IsPrimitiveRoot q 4 := (hD b (hB b hb).1).1
  have hInt : IsIntegral R (q^4) := by
    rw [hq.pow_eq_one]
    exact isIntegral_one
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (K := K) (by decide : 0 < 4) hInt
  have hzroot : IsPrimitiveRoot z 4 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := f) _ hf
    change IsPrimitiveRoot (algebraMap R K z) 4
    rw [hz]
    exact hq
  let Y := fun i => ArithmeticThetaGlobalFourTorsionR0190.completedY R W (x i) (y i)
  have hformula := RelativeGeometricPhase.pairing_formula W G hG M e x y hC K f b hb D
  have hregular : z * RelativeGeometricPhase.denominator e x Y =
      RelativeGeometricPhase.numerator e x Y := by
    apply hf
    rw [map_mul]
    change algebraMap R K z * f (RelativeGeometricPhase.denominator e x Y) = _
    rw [hz]
    exact (eq_div_iff hformula.1).mp hformula.2
  refine ⟨z, ⟨⟨⟨e, x, y, hC⟩, ?_⟩, hzroot.isUnit (by decide), hzroot⟩, ?_⟩
  · intro e' x' y' hC' F _ _ _ ι b' hb' D'
    obtain ⟨rfl, rfl, rfl⟩ := RelativeGeometricPhase.coordinates_unique W G M hC hC'
    obtain ⟨hden, hpair⟩ := RelativeGeometricPhase.pairing_formula W G hG M e x y hC F ι b' hb' D'
    rw [hpair]
    apply (eq_div_iff hden).mpr
    simpa only [map_mul] using congrArg ι hregular
  · intro z' hz'
    apply hf
    calc
      f z' = q := hz'.1.2 e x y hC K f b hb D
      _ = f z := hz.symm

#print axioms relative_geometric_phase

end ArithmeticThetaRelativeFourCharacterR0211
