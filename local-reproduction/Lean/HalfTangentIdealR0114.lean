import MillerGeometryDefinitionsR0114
import FourTorsionRoot
open WeierstrassCurve
open ArithmeticThetaMillerR0114
open ArithmeticThetaFourTorsion
noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
set_option autoImplicit false
private theorem half_tangent_ideal_equality : ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k), Distinct k e → ∀ (i : Fin 3) (x y : k), IsHalf k e i x y → Ideal.span ({tangentClass k e x y} : Set (Coord k e)) = pointIdeal k e x y ^ 2 * pointIdeal k e (e i) 0 := by
  intro k _ _ _ e he i x y hh
  rcases hh with ⟨hR, hP, hd⟩
  let W := Curve k e
  have hne : y ≠ W.negY x y := by
    intro hneg
    have hz : 2 • WeierstrassCurve.Affine.Point.some x y hR = 0 := by
      rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hneg]
    apply WeierstrassCurve.Affine.Point.some_ne_zero hP
    calc
      WeierstrassCurve.Affine.Point.some (e i) 0 hP = 2 • WeierstrassCurve.Affine.Point.some x y hR := hd.symm
      _ = 0 := hz
  have hd' := hd
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at hd'
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hd'
  have hax : W.addX x x (W.slope x x y y) = e i := hcoords.1
  have hay : W.addY x x y (W.slope x x y y) = 0 := hcoords.2
  have hxy : ¬(x = x ∧ y = W.negY x y) := by intro h; exact hne h.2
  have hmul := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal (W := W)
      hR.1 hR.1 hxy
  rw [hax, hay] at hmul
  have hmul' : WeierstrassCurve.Affine.CoordinateRing.XIdeal W (e i) *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y) *
       WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y)) =
      WeierstrassCurve.Affine.CoordinateRing.YIdeal W
        (WeierstrassCurve.Affine.linePolynomial x y (W.slope x x y y)) *
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal W (e i) (Polynomial.C 0) := by
    exact hmul
  have hsq : WeierstrassCurve.Affine.CoordinateRing.XYIdeal W (e i) (Polynomial.C 0) *
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal W (e i) (Polynomial.C 0) =
      WeierstrassCurve.Affine.CoordinateRing.XIdeal W (e i) := by
    have hp := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul (W := W) hP
    simpa [W, Curve, ArithmeticThetaFourTorsion.splitCurve, WeierstrassCurve.Affine.negY] using hp
  have hmulF := congrArg (fun I : Ideal (Coord k e) =>
      (I : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))) hmul'
  have hsqF := congrArg (fun I : Ideal (Coord k e) =>
      (I : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))) hsq
  simp only [FractionalIdeal.coeIdeal_mul] at hmulF hsqF
  let u : (FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))ˣ :=
    WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hP
  have hu : (u : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W (e i) (Polynomial.C 0) :
      FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) := by
    exact WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq hP
  rw [← hsqF] at hmulF
  rw [← hu] at hmulF
  let U : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e) := (u : _)
  let Ui : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e) :=
    (↑(u⁻¹) : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))
  have hU : U * Ui = 1 := by
    dsimp [U, Ui]
    exact Units.mul_inv u
  let V : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e) :=
    (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y) :
      FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) *
    (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y) :
      FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))
  change U * U * V = _ * U at hmulF
  have htargetF :
      (WeierstrassCurve.Affine.CoordinateRing.YIdeal W
        (WeierstrassCurve.Affine.linePolynomial x y (W.slope x x y y)) :
        FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y) :
        FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (Polynomial.C y) :
        FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W (e i) (Polynomial.C 0) :
        FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e)) := by
    rw [← hu]
    change _ = V * U
    let YI : FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e) :=
      (WeierstrassCurve.Affine.CoordinateRing.YIdeal W
        (WeierstrassCurve.Affine.linePolynomial x y (W.slope x x y y)) :
        FractionalIdeal (nonZeroDivisors (Coord k e)) (FF k e))
    change YI = V * U
    calc
      YI = YI * (U * Ui) := by rw [hU, mul_one]
      _ = (YI * U) * Ui := by ac_rfl
      _ = (U * U * V) * Ui := by rw [hmulF]
      _ = (U * Ui) * (U * V) := by ac_rfl
      _ = U * V := by rw [hU, one_mul]
      _ = V * U := by ac_rfl
  apply (FractionalIdeal.coeIdeal_inj (R := Coord k e) (K := FF k e)).mp
  rw [FractionalIdeal.coeIdeal_mul]
  rw [show pointIdeal k e x y ^ 2 = pointIdeal k e x y * pointIdeal k e x y by rw [pow_two]]
  rw [FractionalIdeal.coeIdeal_mul]
  rw [FractionalIdeal.coeIdeal_span_singleton]
  simpa [tangentClass, tangentSlope, pointIdeal, W, Curve, WeierstrassCurve.Affine.CoordinateRing.YIdeal,
    WeierstrassCurve.Affine.CoordinateRing.XYIdeal, V] using htargetF

private theorem half_tangent_norm : ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k), Distinct k e → ∀ (i : Fin 3) (x y : k), IsHalf k e i x y → Algebra.norm (Polynomial k) (tangentClass k e x y) = -((Polynomial.X - Polynomial.C x) ^ 2 * (Polynomial.X - Polynomial.C (e i))) := by
  intro k _ _ _ e he i x y hh
  rcases hh with ⟨hR, hP, hd⟩
  let W := Curve k e
  have hne : y ≠ W.negY x y := by
    intro hneg
    have hz : 2 • WeierstrassCurve.Affine.Point.some x y hR = 0 := by
      rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hneg]
    apply WeierstrassCurve.Affine.Point.some_ne_zero hP
    calc
      WeierstrassCurve.Affine.Point.some (e i) 0 hP = 2 • WeierstrassCurve.Affine.Point.some x y hR := hd.symm
      _ = 0 := hz
  have hd' := hd
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at hd'
  have hcoords := WeierstrassCurve.Affine.Point.some.inj hd'
  have hax : W.addX x x (W.slope x x y y) = e i := hcoords.1
  have hay : W.addY x x y (W.slope x x y y) = 0 := hcoords.2
  let L : Polynomial k := WeierstrassCurve.Affine.linePolynomial x y (W.slope x x y y)
  have helem : tangentClass k e x y =
      (-L) • (1 : Coord k e) + (1 : Polynomial k) •
        WeierstrassCurve.Affine.CoordinateRing.mk W Polynomial.X := by
    unfold tangentClass
    unfold WeierstrassCurve.Affine.CoordinateRing.YClass
    dsimp [L, tangentSlope, W]
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul]
    simp [Polynomial.C_1, AdjoinRoot.mk_X]
    ring
  rw [helem]
  have hnorm := WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis (W' := W)
      (-L) (1 : Polynomial k)
  rw [hnorm]
  calc
    _ = W.addPolynomial x y (W.slope x x y y) := by
      simp only [L, WeierstrassCurve.Affine.addPolynomial,
        WeierstrassCurve.Affine.polynomial, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.eval_X]
      ring
    _ = _ := by
      rw [WeierstrassCurve.Affine.addPolynomial_slope hR.1 hR.1 (by
        intro h; exact hne h.2), hax, pow_two]

/-- The tangent to an actual half has affine ideal multiplicities two and one,
and its polynomial norm has the corresponding signed factorization. -/
theorem half_tangent_ideal :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k), ArithmeticThetaMillerR0114.Distinct k e → ∀ (i : Fin 3) (x y : k), ArithmeticThetaMillerR0114.IsHalf k e i x y → (Ideal.span ({ArithmeticThetaMillerR0114.tangentClass k e x y} : Set (ArithmeticThetaMillerR0114.Coord k e)) = ArithmeticThetaMillerR0114.pointIdeal k e x y ^ 2 * ArithmeticThetaMillerR0114.pointIdeal k e (e i) 0) ∧ Algebra.norm (Polynomial k) (ArithmeticThetaMillerR0114.tangentClass k e x y) = -((Polynomial.X - Polynomial.C x) ^ 2 * (Polynomial.X - Polynomial.C (e i))) := by
  intro k _ _ _ e he i x y hh
  exact ⟨half_tangent_ideal_equality k e he i x y hh, half_tangent_norm k e he i x y hh⟩

end ArithmeticThetaMillerR0114
