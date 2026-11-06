import MillerGeometryDefinitionsR0114

noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
open WeierstrassCurve.Affine.CoordinateRing
open Polynomial

variable (k : Type u) [Field k] (e : Fin 3 → k)

/-- Evaluation of the actual coordinate quotient at a point on the curve. -/
def coordinateEvaluation (a b : k) (h : (Curve k e).Equation a b) :
    Coord k e →ₐ[k] k :=
  AdjoinRoot.liftAlgHom (Curve k e).polynomial (Polynomial.aeval a) b (by
    change (Curve k e).polynomial.eval₂ (evalRingHom a) b = 0
    rwa [eval₂_evalRingHom])

lemma coordinateEvaluation_X (a b : k) (h : (Curve k e).Equation a b) (c : k) :
    coordinateEvaluation k e a b h (XClass (Curve k e) c) = a - c := by
  simp [coordinateEvaluation, XClass, AdjoinRoot.liftAlgHom]

lemma coordinateEvaluation_Y (a b : k) (h : (Curve k e).Equation a b) (p : k[X]) :
    coordinateEvaluation k e a b h (YClass (Curve k e) p) = b - p.eval a := by
  simp [coordinateEvaluation, YClass, AdjoinRoot.liftAlgHom]

lemma coordinate_hom_ext {B : Type*} [CommRing B] [Algebra k B]
    (f g : Coord k e →ₐ[k] B)
    (hx : f (XClass (Curve k e) 0) = g (XClass (Curve k e) 0))
    (hy : f (YClass (Curve k e) 0) = g (YClass (Curve k e) 0)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    simpa [XClass, AdjoinRoot.ofAlgHom, AdjoinRoot.mk_C] using hx
  · simpa only [YClass, map_zero, sub_zero, mk, AdjoinRoot.mk_X] using hy

lemma map_open_inverse {B : Type*} [Field B] [Algebra k B] (i : Fin 3)
    (f : MillerOpen k e i →ₐ[k] B) :
    f (IsLocalization.Away.invSelf (XClass (Curve k e) (e i))) =
      (f (algebraMap (Coord k e) (MillerOpen k e i) (XClass (Curve k e) (e i))))⁻¹ := by
  have h := congrArg f (IsLocalization.Away.mul_invSelf
    (S := MillerOpen k e i) (XClass (Curve k e) (e i)))
  simp only [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h


/-- The canonical function-field embedding and unique evaluation on the principal open. -/
theorem miller_open_evaluation :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Distinct k e → ∀ (i : Fin 3) (x y a b : k),
    (Curve k e).Equation a b → a ≠ e i →
    ∃ J : MillerOpen k e i →ₐ[k] FF k e,
      Function.Injective J ∧
      (∀ c : Coord k e, J (algebraMap (Coord k e) (MillerOpen k e i) c) =
        algebraMap (Coord k e) (FF k e) c) ∧
      J (localMiller k e i x y) = millerFunction k e i x y ∧
      ∃! V : MillerOpen k e i →ₐ[k] k,
        V (algebraMap (Coord k e) (MillerOpen k e i) (XClass (Curve k e) 0)) = a ∧
        V (algebraMap (Coord k e) (MillerOpen k e i) (YClass (Curve k e) 0)) = b ∧
        V (localMiller k e i x y) = millerValue k e i x y a b := by
  intro k _ _ _ e _hd i x y a b hab ha
  let d : Coord k e := XClass (Curve k e) (e i)
  let f : Coord k e →ₐ[k] FF k e := IsScalarTower.toAlgHom k (Coord k e) (FF k e)
  have hf : Function.Injective f := IsFractionRing.injective (Coord k e) (FF k e)
  have hd : f d ≠ 0 := by
    exact fun h => XClass_ne_zero (e i) (hf (h.trans (map_zero f).symm))
  let J : MillerOpen k e i →ₐ[k] FF k e :=
    IsLocalization.Away.liftAlgHom d (isUnit_iff_ne_zero.mpr hd)
  have hJ (c : Coord k e) :
      J (algebraMap (Coord k e) (MillerOpen k e i) c) = f c :=
    by exact IsLocalization.Away.lift_eq d (isUnit_iff_ne_zero.mpr hd) c
  have hJi : Function.Injective J := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) J.toRingHom).mpr
    intro c c'
    constructor
    · exact congrArg J
    · intro h
      apply congrArg (algebraMap (Coord k e) (MillerOpen k e i))
      apply hf
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hJ] using h
  have hdF : f d = xFunction k e - algebraMap k (FF k e) (e i) := by
    change algebraMap (Coord k e) (FF k e) (XClass (Curve k e) (e i)) = _
    simp only [XClass, xFunction, map_sub, map_zero, sub_zero, AdjoinRoot.mk_C]
    congr 1
  refine ⟨J, hJi, hJ, ?_, ?_⟩
  · simp only [localMiller, map_mul, map_pow, hJ, map_open_inverse,
      millerFunction, div_eq_mul_inv]
    rw [hdF]
    rfl
  · let E := coordinateEvaluation k e a b hab
    have hE : E d = a - e i := coordinateEvaluation_X k e a b hab (e i)
    let V : MillerOpen k e i →ₐ[k] k :=
      IsLocalization.Away.liftAlgHom d (show IsUnit (E d) by
        rw [hE]; exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha))
    have hV (c : Coord k e) : V (algebraMap (Coord k e) (MillerOpen k e i) c) = E c :=
      by
        dsimp [V, IsLocalization.Away.liftAlgHom]
        apply IsLocalization.Away.lift_eq
        change IsUnit (E d)
        rw [hE]; exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha)
    have hVX : V (algebraMap (Coord k e) (MillerOpen k e i) (XClass (Curve k e) 0)) = a := by
      rw [hV, coordinateEvaluation_X]; exact sub_zero a
    have hVY : V (algebraMap (Coord k e) (MillerOpen k e i) (YClass (Curve k e) 0)) = b := by
      rw [hV, coordinateEvaluation_Y]; simp
    refine ⟨V, ⟨hVX, hVY, ?_⟩, ?_⟩
    · simp only [localMiller, map_mul, map_pow, map_open_inverse, hV]
      rw [show E (XClass (Curve k e) (e i)) = a - e i from hE]
      unfold tangentClass
      rw [show E (YClass (Curve k e) (WeierstrassCurve.Affine.linePolynomial x y
        (tangentSlope k e x y))) = b - _ from coordinateEvaluation_Y k e a b hab _]
      simp [millerValue, tangentValue, WeierstrassCurve.Affine.linePolynomial, div_eq_mul_inv]
      ring_nf
      simp
    · intro V' hV'
      apply IsLocalization.algHom_ext (Submonoid.powers d)
      apply coordinate_hom_ext k e
      · exact hV'.1.trans hVX.symm
      · exact hV'.2.1.trans hVY.symm

end ArithmeticThetaMillerR0114
