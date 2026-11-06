module

public import LocalIdealOrderR0116
public import TranslationCompositionR0116

@[expose] public section

/-! Finite support and translation covariance of the actual principal divisor. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord pointIdeal)
variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)
variable (he : Function.Injective e) (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
variable (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)

omit [CharZero k] [DecidableEq k] in
include hT hh hE in
lemma norm_vanishes_of_mem (a : Coord k e) (x y : k)
    (hp : (Curve k e).Nonsingular x y) (ha : a ∈ pointIdeal k e x y) :
    (Algebra.norm (Polynomial k) a).eval x = 0 := by
  let φ := (PowerSeries.constantCoeff.comp (localSeriesHom k e T hT h E hh hE x y hp))
  have hv : φ a = 0 := by
    simpa only [localSeriesHom_kernel k e T hT h E hh hE x y hp, RingHom.mem_ker] using ha
  obtain ⟨p,q,rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  have hn := CoordinateRing.coe_norm_smul_basis (W' := Curve k e) p q
  have hmul : CoordinateRing.mk (Curve k e) (C p + C q * X) =
      p • (1 : Coord k e) + q • CoordinateRing.mk (Curve k e) X := by
    simp [CoordinateRing.smul]
  have hz : φ (algebraMap (Polynomial k) (Coord k e)
      (Algebra.norm (Polynomial k) (p • 1 + q • CoordinateRing.mk (Curve k e) X))) = 0 := by
    change φ (AdjoinRoot.of (Curve k e).polynomial _) = 0
    rw [hn, map_mul, map_mul, hmul, hv, zero_mul]
  change PowerSeries.constantCoeff (localSeriesHom k e T hT h E hh hE x y hp
    (CoordinateRing.mk (Curve k e) (C _))) = 0 at hz
  rw [localSeriesHom_constant] at hz
  simpa using hz

omit [CharZero k] [DecidableEq k] in
include hT hh hE in
lemma finite_affine_zeros (a : Coord k e) (ha : a ≠ 0) :
    Set.Finite {z : k × k | ∃ _hp : (Curve k e).Nonsingular z.1 z.2,
      a ∈ pointIdeal k e z.1 z.2} := by
  let S := {z : k × k | ∃ _hp : (Curve k e).Nonsingular z.1 z.2,
      a ∈ pointIdeal k e z.1 z.2}
  have hn : Algebra.norm (Polynomial k) a ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis (Curve k e))).mpr ha
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply (Polynomial.finite_setOfPred_isRoot hn).subset
    rintro x ⟨⟨x,y⟩, ⟨hp, hz⟩, rfl⟩
    exact norm_vanishes_of_mem k e T hT h E hh hE a x y hp hz
  · rintro x ⟨⟨x₀,y₀⟩, ⟨hp₀, hz₀⟩, rfl⟩
    apply (Set.toFinite ({(x₀,y₀), (x₀,-y₀)} : Set (k × k))).subset
    rintro ⟨x,y⟩ ⟨⟨hp, hz⟩, hxy⟩
    have hx : x = x₀ := hxy
    subst x
    have hy : y^2 = y₀^2 := by
      have h1 := (equation_iff x₀ y).mp hp.1
      have h2 := (equation_iff x₀ y₀).mp hp₀.1
      dsimp [Curve, ArithmeticThetaMillerR0114.Curve,
        ArithmeticThetaFourTorsion.splitCurve] at h1 h2
      linear_combination h1 - h2
    rcases eq_or_eq_neg_of_sq_eq_sq y y₀ hy with rfl | rfl <;> simp

include he hT hh hE in
lemma finite_coordinate_support (a : Coord k e) (ha : a ≠ 0) :
    Set.Finite {P : (Curve k e).Point |
      pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) P ≠ 0} := by
  classical
  let toPoint : k × k → (Curve k e).Point := fun z =>
    if hp : (Curve k e).Nonsingular z.1 z.2 then .some z.1 z.2 hp else 0
  have hfin := (finite_affine_zeros k e T hT h E hh hE a ha).image toPoint
  apply (hfin.insert 0).subset
  intro P hP
  cases P with
  | zero => exact Set.mem_insert 0 _
  | some x y hp =>
    apply Set.mem_insert_of_mem
    have hnonneg := (local_ideal_order k e he T hT h E hh hE x y hp a ha 0).mpr
      (by simp)
    have hpos : (1 : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) a)
        (.some x y hp) := by
      change pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) ≠ 0 at hP
      omega
    have hm := (local_ideal_order k e he T hT h E hh hE x y hp a ha 1).mp hpos
    refine ⟨(x,y), ⟨hp, by simpa using hm⟩, ?_⟩
    simp [toPoint, hp]

/-- Every nonzero rational function has finite principal support, and pullback
by Q moves its order at P to the order at P+Q. -/
theorem principal_divisor_support :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ T : Translations k e, IsTranslationSystem k e T →
    ∀ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
    ArithmeticThetaMillerR0114.branchEquation k e h →
    ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E →
    ∀ f : FF k e, f ≠ 0 →
      Set.Finite {P : (Curve k e).Point | pointOrder k e T E f P ≠ 0} ∧
      (∀ P Q : (Curve k e).Point, pointOrder k e T E (T Q f) P =
        pointOrder k e T E f (P + Q)) := by
  intro k _ _ _ e he T hT h E hh hE f hf
  constructor
  · obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective (Coord k e) f
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      intro hz
      apply hf
      rw [← hab, hz, map_zero, zero_div]
    have hfa := finite_coordinate_support k e he T hT h E hh hE a ha0
    have hfb := finite_coordinate_support k e he T hT h E hh hE b hb0
    apply (hfa.union hfb).subset
    intro P hP
    by_contra hn
    have hz := not_or.mp hn
    have haord : pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) P = 0 :=
      not_ne_iff.mp hz.1
    have hbord : pointOrder k e T E (algebraMap (Coord k e) (FF k e) b) P = 0 :=
      not_ne_iff.mp hz.2
    have hbn : algebraMap (Coord k e) (FF k e) b ≠ 0 :=
      by simpa using (IsFractionRing.injective (Coord k e) (FF k e)).ne hb0
    have hmul : f * algebraMap (Coord k e) (FF k e) b =
        algebraMap (Coord k e) (FF k e) a := by
      rw [← hab, div_mul_cancel₀ _ hbn]
    have hex := congrArg (fun z => (E (T P z)).order) hmul
    rw [map_mul, map_mul, HahnSeries.order_mul
      (by simpa using E.injective.ne ((T P).injective.ne hf))
      (by simpa using E.injective.ne ((T P).injective.ne hbn))] at hex
    change pointOrder k e T E f P +
      pointOrder k e T E (algebraMap (Coord k e) (FF k e) b) P =
      pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) P at hex
    rw [haord, hbord, add_zero] at hex
    exact hP hex
  · intro P Q
    unfold pointOrder expansion
    rw [(translation_composition k e he T hT).2.1 P Q f]

end ArithmeticThetaReciprocityR0116
