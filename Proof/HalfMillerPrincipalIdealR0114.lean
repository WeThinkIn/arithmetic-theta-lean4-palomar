module

public import HalfTangentIdealR0114

@[expose] public section

noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
open WeierstrassCurve.Affine
set_option autoImplicit false

/-- The denominator is the image of the actual vertical-line class. -/
theorem miller_denominator_eq (k : Type u) [Field k] (e : Fin 3 → k) (i : Fin 3) :
    xFunction k e - algebraMap k (FF k e) (e i) =
      algebraMap (Coord k e) (FF k e) (CoordinateRing.XClass (Curve k e) (e i)) := by
  simp only [xFunction, CoordinateRing.XClass, map_sub, Polynomial.C_0, sub_zero]
  congr 1

/-- Squaring the point ideal at a labelled two-torsion point gives its vertical line. -/
theorem half_label_vertical_ideal (k : Type u) [Field k] [DecidableEq k]
    (e : Fin 3 → k) (i : Fin 3) (x y : k) (hh : IsHalf k e i x y) :
    pointIdeal k e (e i) 0 ^ 2 =
      Ideal.span ({CoordinateRing.XClass (Curve k e) (e i)} : Set (Coord k e)) := by
  obtain ⟨hR, hP, hd⟩ := hh
  have h := CoordinateRing.XYIdeal_neg_mul (W := Curve k e) hP
  rw [pow_two]
  have hn : (Curve k e).negY (e i) 0 = 0 := by
    simp [Curve, ArithmeticThetaFourTorsion.splitCurve, WeierstrassCurve.Affine.negY]
  rw [hn] at h
  exact h

/-- The actual Miller function is nonzero and generates the fourth power of the half's ideal. -/
theorem half_miller_principal_ideal :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      ArithmeticThetaMillerR0114.Distinct k e → ∀ (i : Fin 3) (x y : k),
      ArithmeticThetaMillerR0114.IsHalf k e i x y →
      ArithmeticThetaMillerR0114.millerFunction k e i x y ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (ArithmeticThetaMillerR0114.Coord k e))
        (ArithmeticThetaMillerR0114.millerFunction k e i x y) =
        ArithmeticThetaMillerR0114.pointFraction k e x y ^ 4 := by
  intro k _ _ _ e he i x y hh
  let A := Coord k e
  let K := FF k e
  let S := nonZeroDivisors A
  let t : K := algebraMap A K (tangentClass k e x y)
  let d : K := algebraMap A K (CoordinateRing.XClass (Curve k e) (e i))
  have ht : t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
    (CoordinateRing.YClass_ne_zero _)
  have hd : d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr
    (CoordinateRing.XClass_ne_zero _)
  have hf : millerFunction k e i x y = t ^ 2 / d := by
    rw [millerFunction, miller_denominator_eq]
  refine ⟨by rw [hf]; exact div_ne_zero (pow_ne_zero _ ht) hd, ?_⟩
  have htan : FractionalIdeal.spanSingleton S t =
      pointFraction k e x y ^ 2 * pointFraction k e (e i) 0 := by
    have h := congrArg (fun I : Ideal A => (I : FractionalIdeal S K))
      (half_tangent_ideal k e he i x y hh).1
    simpa only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow, pointFraction] using h
  have hvert : pointFraction k e (e i) 0 ^ 2 = FractionalIdeal.spanSingleton S d := by
    have h := congrArg (fun I : Ideal A => (I : FractionalIdeal S K))
      (half_label_vertical_ideal k e i x y hh)
    simpa only [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_pow, pointFraction] using h
  rw [hf, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_pow, htan, mul_pow, ← pow_mul, hvert]
  rw [show (2 : ℕ) * 2 = 4 by decide, mul_assoc,
    FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hd,
    FractionalIdeal.spanSingleton_one, mul_one]

end ArithmeticThetaMillerR0114
