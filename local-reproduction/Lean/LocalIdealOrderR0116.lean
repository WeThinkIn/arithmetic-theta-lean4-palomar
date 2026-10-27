import LocalAffineExpansionR0116

/-! The translated Laurent order detects powers of the actual affine point ideal. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord xFunction yFunction pointIdeal)

section General
variable {R k : Type*} [CommRing R] [Field k]

/-- Lift a regular Laurent-valued ring map to power series. -/
def regularLift (L : R →+* LaurentSeries k)
    (hL : ∀ a, ∃ s : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) s = L a) :
    R →+* PowerSeries k where
  toFun a := (hL a).choose
  map_one' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries k) (LaurentSeries k) _ = algebraMap (PowerSeries k) (LaurentSeries k) _
    rw [(hL 1).choose_spec, map_one, map_one]
  map_zero' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries k) (LaurentSeries k) _ = algebraMap (PowerSeries k) (LaurentSeries k) _
    rw [(hL 0).choose_spec, map_zero, map_zero]
  map_add' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries k) (LaurentSeries k) _ = algebraMap (PowerSeries k) (LaurentSeries k) _
    rw [(hL (a+b)).choose_spec, map_add, map_add, (hL a).choose_spec, (hL b).choose_spec]
  map_mul' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries k) (LaurentSeries k) _ = algebraMap (PowerSeries k) (LaurentSeries k) _
    rw [(hL (a*b)).choose_spec, map_mul, map_mul, (hL a).choose_spec, (hL b).choose_spec]

lemma regularLift_spec (L : R →+* LaurentSeries k) (hL) (a : R) :
    algebraMap (PowerSeries k) (LaurentSeries k) (regularLift L hL a) = L a :=
  (hL a).choose_spec

lemma series_order_iff_dvd (s : PowerSeries k) (hs : s ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ (algebraMap (PowerSeries k) (LaurentSeries k) s).order ↔
      PowerSeries.X^n ∣ s := by
  have hsn : algebraMap (PowerSeries k) (LaurentSeries k) s ≠ 0 :=
    fun hz => hs (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa using hz))
  rw [HahnSeries.le_order_iff_forall hsn, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro H m hm
    exact (HahnSeries.ofPowerSeries_apply_coeff s m).symm.trans (H m (by omega))
  · intro H z hz
    by_cases hneg : z < 0
    · change (s : LaurentSeries k).coeff z = 0
      simp [PowerSeries.coeff_coe, hneg]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
      rw [show algebraMap (PowerSeries k) (LaurentSeries k) s =
        HahnSeries.ofPowerSeries ℤ k s from rfl, HahnSeries.ofPowerSeries_apply_coeff]
      exact H m (by omega)

/-- A parameter of Laurent order one generates every power after cancelling a
factor outside the maximal ideal. The denominator condition is explicit. -/
lemma ideal_power_order (φ : R →+* PowerSeries k) (hφ : Function.Injective φ)
    (m : Ideal R) [m.IsMaximal]
    (hm : m = RingHom.ker (PowerSeries.constantCoeff.comp φ))
    (t c : R) (ht : t ∈ m) (hc : c ∉ m)
    (hdiv : ∀ a ∈ m, t ∣ c*a)
    (htord : (algebraMap (PowerSeries k) (LaurentSeries k) (φ t)).order = 1)
    (a : R) (ha : a ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ (algebraMap (PowerSeries k) (LaurentSeries k) (φ a)).order ↔ a ∈ m^n := by
  let j := algebraMap (PowerSeries k) (LaurentSeries k)
  have hn (b : R) (hb : b ≠ 0) : j (φ b) ≠ 0 := by
    exact fun hz => hb (hφ (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [j] using hz)))
  have hc0 : PowerSeries.constantCoeff (φ c) ≠ 0 := by
    simpa [hm, RingHom.mem_ker] using hc
  have hcn : c ≠ 0 := fun hz => hc0 (by simp [hz])
  have ht0 : t ≠ 0 := by intro hz; simp [hz] at htord
  have hforward (b : R) (hb : b ≠ 0) (r : ℕ) (hbr : b ∈ m^r) :
      (r : ℤ) ≤ (j (φ b)).order := by
    apply (series_order_iff_dvd (φ b) (fun hz => hb (hφ (by simpa using hz))) r).mpr
    apply Ideal.mem_span_singleton.mp
    have hmX : Ideal.map φ m ≤ Ideal.span {PowerSeries.X} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      apply Ideal.mem_span_singleton.mpr
      apply PowerSeries.X_dvd_iff.mpr
      simpa [hm, RingHom.mem_ker] using hb
    have hp := pow_le_pow_left' hmX r
    rw [← Ideal.map_pow, Ideal.span_singleton_pow] at hp
    exact hp (Ideal.mem_map_of_mem φ hbr)
  refine ⟨?_, hforward a ha n⟩
  induction n generalizing a with
  | zero => intro _; simp
  | succ n ih =>
    intro horder
    have ha1 : a ∈ m := by
      rw [hm, RingHom.mem_ker]
      change PowerSeries.constantCoeff (φ a) = 0
      apply PowerSeries.X_dvd_iff.mp
      simpa only [pow_one] using (series_order_iff_dvd (φ a) (fun hz => ha (hφ (by simpa using hz))) 1).mp
        (by omega)
    obtain ⟨b, hb⟩ := hdiv a ha1
    have hbn : b ≠ 0 := by
      intro hz
      have hz' : j (φ c) * j (φ a) = 0 := by rw [← map_mul, ← map_mul, hb, hz]; simp
      exact mul_ne_zero (hn c hcn) (hn a ha) hz'
    have he : j (φ c) * j (φ a) = j (φ t) * j (φ b) := by
      rw [← map_mul, ← map_mul, hb, map_mul, map_mul]
    have hord := congrArg HahnSeries.order he
    rw [HahnSeries.order_mul (hn c hcn) (hn a ha),
      HahnSeries.order_mul (hn t ht0) (hn b hbn), series_order_zero k (φ c) hc0,
      htord] at hord
    change (0 : ℤ) + (algebraMap (PowerSeries k) (LaurentSeries k) (φ a)).order =
      1 + (algebraMap (PowerSeries k) (LaurentSeries k) (φ b)).order at hord
    have hbm : b ∈ m^n := ih b hbn (by omega)
    have hcam : c*a ∈ m^(n+1) := by
      rw [hb, pow_succ']
      exact Ideal.mul_mem_mul ht hbm
    exact (Ideal.IsMaximal.mul_mem_pow m hcam).resolve_left hc
end General

section Geometry
variable (k : Type u) [Field k] (e : Fin 3 → k)
variable (T : Translations k e) (hT : IsTranslationSystem k e T)
variable (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k)
variable (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
variable (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
variable (x y : k) (hp : (Curve k e).Nonsingular x y)

abbrev coordinateExpansion : Coord k e →+* LaurentSeries k :=
  E.toRingHom.comp ((T (.some x y hp)).toRingHom.comp (algebraMap (Coord k e) (FF k e)))

include hT hh hE in
lemma coordinateExpansion_regular (a : Coord k e) :
    ∃ s : PowerSeries k, algebraMap (PowerSeries k) (LaurentSeries k) s =
      coordinateExpansion k e T E x y hp a := by
  obtain ⟨F, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨s, hs, _⟩ := coordinate_polynomial_series k e T hT h E hh hE x y hp F
  exact ⟨s, hs.symm⟩

def localSeriesHom : Coord k e →+* PowerSeries k :=
  regularLift (coordinateExpansion k e T E x y hp)
    (coordinateExpansion_regular k e T hT h E hh hE x y hp)

lemma localSeriesHom_spec (a : Coord k e) :
    algebraMap (PowerSeries k) (LaurentSeries k) (localSeriesHom k e T hT h E hh hE x y hp a) =
      coordinateExpansion k e T E x y hp a :=
  regularLift_spec _ _ _

lemma localSeriesHom_injective : Function.Injective (localSeriesHom k e T hT h E hh hE x y hp) := by
  intro a b hab
  have hj := congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hab
  rw [localSeriesHom_spec, localSeriesHom_spec] at hj
  exact (IsFractionRing.injective (Coord k e) (FF k e))
    ((T (.some x y hp)).injective (E.injective hj))

lemma localSeriesHom_constant (F : Polynomial (Polynomial k)) :
    PowerSeries.constantCoeff
      (localSeriesHom k e T hT h E hh hE x y hp (CoordinateRing.mk (Curve k e) F)) =
      Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) F) := by
  obtain ⟨s, hs, hc⟩ := coordinate_polynomial_series k e T hT h E hh hE x y hp F
  have he : localSeriesHom k e T hT h E hh hE x y hp (CoordinateRing.mk (Curve k e) F) = s := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    exact (localSeriesHom_spec k e T hT h E hh hE x y hp _).trans hs
  rw [he, hc]

include hp in
lemma pointIdeal_maximal : (pointIdeal k e x y).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  have he : ((Curve k e).polynomial.eval (C y)).eval x = 0 := by
    exact hp.1
  exact MulEquiv.isField (Field.toIsField k)
    (CoordinateRing.quotientXYIdealEquiv he).toRingEquiv.toMulEquiv

lemma localSeriesHom_kernel : pointIdeal k e x y =
    RingHom.ker (PowerSeries.constantCoeff.comp (localSeriesHom k e T hT h E hh hE x y hp)) := by
  apply (pointIdeal_maximal k e x y hp).eq_of_le (RingHom.ker_ne_top _)
  apply Ideal.span_le.mpr
  intro a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · change PowerSeries.constantCoeff (localSeriesHom k e T hT h E hh hE x y hp
      (CoordinateRing.mk (Curve k e) (C (X-C x)))) = 0
    rw [localSeriesHom_constant]
    simp
  · have he : a = CoordinateRing.YClass (Curve k e) (C y) := Set.mem_singleton_iff.mp ha
    rw [he]
    change PowerSeries.constantCoeff (localSeriesHom k e T hT h E hh hE x y hp
      (CoordinateRing.mk (Curve k e) (X-C (C y)))) = 0
    rw [localSeriesHom_constant]
    simp

/-- The divided difference of the cubic at the chosen affine X coordinate. -/
def secantPolynomial : Polynomial k :=
  X^2+C x*X+C (x^2)-C (e 0+e 1+e 2)*(X+C x)+C (e 0*e 1+e 0*e 2+e 1*e 2)

include hp in
lemma secant_relation :
    CoordinateRing.XClass (Curve k e) x *
      CoordinateRing.mk (Curve k e) (C (secantPolynomial k e x)) =
    CoordinateRing.YClass (Curve k e) (C y) *
      CoordinateRing.YClass (Curve k e) (C (-y)) := by
  have he : y^2 = x^3-(e 0+e 1+e 2)*x^2+
      (e 0*e 1+e 0*e 2+e 1*e 2)*x-e 0*e 1*e 2 := by
    have hq := (equation_iff x y).mp hp.1
    dsimp [Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve] at hq
    linear_combination hq
  have hc := congrArg (fun z : k => (C (C z) : Polynomial (Polynomial k))) he
  simp only [map_pow, map_sub, map_add, map_mul] at hc
  unfold CoordinateRing.XClass CoordinateRing.YClass
  rw [← map_mul, ← map_mul]
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨-1, ?_⟩
  dsimp [secantPolynomial, Curve, ArithmeticThetaMillerR0114.Curve,
    ArithmeticThetaFourTorsion.splitCurve, polynomial]
  simp only [map_pow, map_sub, map_add, map_mul, map_neg, map_zero, zero_mul, add_zero]
  linear_combination hc

lemma secant_constant :
    PowerSeries.constantCoeff (localSeriesHom k e T hT h E hh hE x y hp
      (CoordinateRing.mk (Curve k e) (C (secantPolynomial k e x)))) = localDerivative k e x := by
  rw [localSeriesHom_constant]
  simp [secantPolynomial, localDerivative]
  ring

lemma field_XClass :
    algebraMap (Coord k e) (FF k e) (CoordinateRing.XClass (Curve k e) x) =
      xFunction k e - algebraMap k (FF k e) x := by
  simp [xFunction, CoordinateRing.XClass, CoordinateRing.mk, map_sub,
    IsScalarTower.algebraMap_eq k (Coord k e) (FF k e), AdjoinRoot.algebraMap_eq']

end Geometry

/-- The local order of a nonzero coordinate function equals its actual point-ideal multiplicity. -/
theorem local_ideal_order :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ T : Translations k e, IsTranslationSystem k e T →
    ∀ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
    ArithmeticThetaMillerR0114.branchEquation k e h →
    ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E →
    ∀ (x y : k) (hp : (Curve k e).Nonsingular x y) (a : Coord k e), a ≠ 0 → ∀ n : ℕ,
    ((n : ℤ) ≤ pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) ↔
      a ∈ (pointIdeal k e x y)^n) := by
  intro k _ _ _ e he T hT h E hh hE x y hp a ha n
  have hlocal := local_affine_expansion k e he T hT h E hh hE x y hp
  let φ := localSeriesHom k e T hT h E hh hE x y hp
  let m := pointIdeal k e x y
  let u := CoordinateRing.XClass (Curve k e) x
  let v := CoordinateRing.YClass (Curve k e) (C y)
  let w := CoordinateRing.YClass (Curve k e) (C (-y))
  let d := CoordinateRing.mk (Curve k e) (C (secantPolynomial k e x))
  have hm : m = RingHom.ker (PowerSeries.constantCoeff.comp φ) :=
    localSeriesHom_kernel k e T hT h E hh hE x y hp
  let : m.IsMaximal := pointIdeal_maximal k e x y hp
  have hφ := localSeriesHom_injective k e T hT h E hh hE x y hp
  have hu : u ∈ m := Ideal.subset_span (by simp [u])
  have hv : v ∈ m := Ideal.subset_span (by simp [v])
  have hrel : u*d = v*w := secant_relation k e x y hp
  have htarget : pointOrder k e T E (algebraMap (Coord k e) (FF k e) a) (.some x y hp) =
      (algebraMap (PowerSeries k) (LaurentSeries k) (φ a)).order := by
    rw [localSeriesHom_spec]; rfl
  rw [htarget]
  by_cases hy : y = 0
  · have hw : w = v := by simp [w, v, hy]
    have hd0 : PowerSeries.constantCoeff (φ d) ≠ 0 := by
      rw [secant_constant]
      exact localDerivative_ne_zero k e x (by simpa [hy] using hp)
    have hd : d ∉ m := by simpa [hm, RingHom.mem_ker] using hd0
    have hdiv : ∀ b ∈ m, v ∣ d*b := by
      intro b hb
      obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.mp hb
      refine ⟨r*v+d*s, ?_⟩
      rw [hw] at hrel
      linear_combination r*hrel
    have hord : (algebraMap (PowerSeries k) (LaurentSeries k) (φ v)).order = 1 := by
      rw [localSeriesHom_spec]
      have heq := hlocal.2.2 hy
      simpa [pointOrder, expansion, coordinateExpansion, v, hy, yFunction, CoordinateRing.YClass] using heq
    exact ideal_power_order φ hφ m hm v d hv hd hdiv hord a ha n
  · have hw0 : PowerSeries.constantCoeff (φ w) = 2*y := by
      change PowerSeries.constantCoeff (localSeriesHom k e T hT h E hh hE x y hp
        (CoordinateRing.mk (Curve k e) (X-C (C (-y))))) = _
      rw [localSeriesHom_constant]
      simp
      ring
    have hw : w ∉ m := by
      rw [hm, RingHom.mem_ker]
      change PowerSeries.constantCoeff (φ w) ≠ 0
      rw [hw0]
      exact mul_ne_zero (by norm_num) hy
    have hdiv : ∀ b ∈ m, u ∣ w*b := by
      intro b hb
      obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.mp hb
      refine ⟨w*r+s*d, ?_⟩
      linear_combination -s*hrel
    have hord : (algebraMap (PowerSeries k) (LaurentSeries k) (φ u)).order = 1 := by
      rw [localSeriesHom_spec]
      change (expansion k e T E (.some x y hp)
        (algebraMap (Coord k e) (FF k e) u)).order = 1
      rw [field_XClass]
      exact hlocal.2.1.trans (if_neg hy)
    exact ideal_power_order φ hφ m hm u w hu hw hdiv hord a ha n

end ArithmeticThetaReciprocityR0116
