module

public import FunctionFieldTranslationsR0116

@[expose] public section

/-! Genuine affine expansions obtained by cancellation in the generic chord formulas. -/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord xFunction yFunction parameter infinityX infinityY)
variable (k : Type u) [Field k]

/-- The unit denominator of the translated expansion. -/
def localD (h : PowerSeries k) (a : k) : PowerSeries k :=
  h - PowerSeries.C a * PowerSeries.X ^ 2

def localDerivative (e : Fin 3 → k) (a : k) : k :=
  3*a^2 - 2*(e 0+e 1+e 2)*a + (e 0*e 1+e 0*e 2+e 1*e 2)

def localRemainder (e : Fin 3 → k) (a b : k) : k :=
  b^2 + (e 0+e 1+e 2-2*a)*a^2 - e 0*e 1*e 2

def localR (e : Fin 3 → k) (h : PowerSeries k) (a b : k) : PowerSeries k :=
  (PowerSeries.C (2*b)*h + PowerSeries.C (localDerivative k e a)*h*PowerSeries.X +
    PowerSeries.C (localRemainder k e a b)*PowerSeries.X^3) * (localD k h a)⁻¹^2

def localX (e : Fin 3 → k) (h : PowerSeries k) (a b : k) : PowerSeries k :=
  PowerSeries.C a + PowerSeries.X * localR k e h a b

def localY (e : Fin 3 → k) (h : PowerSeries k) (a b : k) : PowerSeries k :=
  -PowerSeries.C b + (h + PowerSeries.C b*PowerSeries.X^3) *
    localR k e h a b * (localD k h a)⁻¹

lemma localD_constant {h : PowerSeries k} (hh : PowerSeries.constantCoeff h = 1) (a : k) :
    PowerSeries.constantCoeff (localD k h a) = 1 := by simp [localD, hh]

lemma localR_constant (e : Fin 3 → k) {h : PowerSeries k}
    (hh : PowerSeries.constantCoeff h = 1) (a b : k) :
    PowerSeries.constantCoeff (localR k e h a b) = 2*b := by
  simp [localR, PowerSeries.constantCoeff_inv, localD_constant k hh, hh]

lemma localXY_constant (e : Fin 3 → k) {h : PowerSeries k}
    (hh : PowerSeries.constantCoeff h = 1) (a b : k) :
    PowerSeries.constantCoeff (localX k e h a b) = a ∧
    PowerSeries.constantCoeff (localY k e h a b) = b := by
  simp [localX, localY, hh, localR_constant k e hh, PowerSeries.constantCoeff_inv,
    localD_constant k hh]
  ring

lemma series_inv_map (s : PowerSeries k) (hs : PowerSeries.constantCoeff s ≠ 0) :
    algebraMap (PowerSeries k) (LaurentSeries k) s⁻¹ =
      (algebraMap (PowerSeries k) (LaurentSeries k) s)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, PowerSeries.inv_mul_cancel s hs, map_one]

section Algebra
variable {K : Type*} [Field K]
lemma chord_series_x (S V U a b t H : K) (ht : t ≠ 0) (hD : H-a*t^2 ≠ 0)
    (hH : H^2 = H^3-S*H^2*t^2+V*H*t^4-U*t^6) :
    ((-(t^(-3 : ℤ)*H)-b)/(t^(-2 : ℤ)*H-a))^2+S-t^(-2 : ℤ)*H-a =
    a+t*((2*b*H+(3*a^2-2*S*a+V)*H*t+(b^2+(S-2*a)*a^2-U)*t^3)*
      (H-a*t^2)⁻¹^2) := by
  simp only [zpow_neg, zpow_ofNat]
  have hd : (t^2)⁻¹*H-a ≠ 0 := by
    intro hz
    apply hD
    field_simp at hz
    linear_combination hz
  field_simp [ht, hD, hd]
  field_simp [show H-t^2*a ≠ 0 by simpa [mul_comm] using hD]
  linear_combination hH

lemma chord_series_y (a b t H R : K) (ht : t ≠ 0) (hD : H-a*t^2 ≠ 0) :
    -(-(t^(-3 : ℤ)*H)) + ((-(t^(-3 : ℤ)*H)-b)/(t^(-2 : ℤ)*H-a))*
      (t^(-2 : ℤ)*H-(a+t*R)) =
    -b+(H+b*t^3)*R*(H-a*t^2)⁻¹ := by
  simp only [zpow_neg, zpow_ofNat]
  have hd : (t^2)⁻¹*H-a ≠ 0 := by
    intro hz
    apply hD
    field_simp at hz
    linear_combination hz
  field_simp [ht, hD, hd]
  field_simp [show H-t^2*a ≠ 0 by simpa [mul_comm] using hD]
  ring
end Algebra

lemma translated_coordinate_series (e : Fin 3 → k) (T : Translations k e)
    (hT : IsTranslationSystem k e T) (h : PowerSeries k)
    (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (a b : k) (hp : (Curve k e).Nonsingular a b) :
    expansion k e T E (.some a b hp) (xFunction k e) =
      algebraMap (PowerSeries k) (LaurentSeries k) (localX k e h a b) ∧
    expansion k e T E (.some a b hp) (yFunction k e) =
      algebraMap (PowerSeries k) (LaurentSeries k) (localY k e h a b) := by
  let c := algebraMap k (LaurentSeries k)
  let j := algebraMap (PowerSeries k) (LaurentSeries k)
  have hc (z : k) : j (PowerSeries.C z) = c z := rfl
  have hD0 : PowerSeries.constantCoeff (localD k h a) ≠ 0 := by
    rw [localD_constant k hh.1]; exact one_ne_zero
  have hjX : j PowerSeries.X = parameter k := rfl
  have hjD : j (localD k h a) = j h-c a*parameter k^2 := by
    simp only [localD, map_sub, map_mul, map_pow, hc, hjX]
  have hinv : j (localD k h a)⁻¹ = (j h-c a*parameter k^2)⁻¹ :=
    (series_inv_map k (localD k h a) hD0).trans (congrArg Inv.inv hjD)
  have hD : j h-c a*parameter k^2 ≠ 0 := by
    have hn : localD k h a ≠ 0 := fun hz => hD0 (by rw [hz, map_zero])
    have hj := (HahnSeries.ofPowerSeries_injective (Γ := ℤ)).ne hn
    change j (localD k h a) ≠ j 0 at hj
    rwa [map_zero, hjD] at hj
  have heq : (j h)^2 = (j h)^3-c (e 0+e 1+e 2)*(j h)^2*parameter k^2 +
      c (e 0*e 1+e 0*e 2+e 1*e 2)*(j h)*parameter k^4 -
      c (e 0*e 1*e 2)*parameter k^6 := by
    have heq := congrArg j hh.2
    simp only [map_pow, map_sub, map_mul, hc,
      Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at heq
    dsimp [parameter, j, c] at *
    simp only [map_add, map_mul]
    linear_combination heq
  have hR : j (localR k e h a b) =
      (2*c b*j h + (3*(c a)^2-2*c (e 0+e 1+e 2)*c a+
        c (e 0*e 1+e 0*e 2+e 1*e 2))*j h*parameter k +
        ((c b)^2+(c (e 0+e 1+e 2)-2*c a)*(c a)^2-c (e 0*e 1*e 2))*parameter k^3)*
        (j h-c a*parameter k^2)⁻¹^2 := by
    simp only [localR, map_mul, map_add, map_pow, hc, hinv, hjX,
      localDerivative, localRemainder, map_sub, map_ofNat]
  have hx := chord_series_x (c (e 0+e 1+e 2)) (c (e 0*e 1+e 0*e 2+e 1*e 2))
    (c (e 0*e 1*e 2)) (c a) (c b) (parameter k) (j h)
    (ArithmeticThetaMillerR0114.parameter_ne_zero k) hD heq
  rw [← hR] at hx
  simp only [map_add] at hx
  have hx' : expansion k e T E (.some a b hp) (xFunction k e) = j (localX k e h a b) := by
    unfold expansion
    rw [(hT _).1]
    simp only [translatedCoordinates, map_sub, map_add, map_pow, map_div₀,
      AlgHom.commutes, hE.1, hE.2]
    simpa only [infinityX, infinityY, localX, map_add, map_mul, hc, hjX] using hx
  refine ⟨hx', ?_⟩
  have hy := chord_series_y (c a) (c b) (parameter k) (j h) (j (localR k e h a b))
    (ArithmeticThetaMillerR0114.parameter_ne_zero k) hD
  unfold expansion
  rw [(hT _).2]
  simp only [translatedCoordinates, map_sub, map_add, map_pow, map_div₀, map_mul,
    map_neg, AlgHom.commutes, hE.1, hE.2, infinityX, infinityY]
  rw [hx]
  change _ = j (localY k e h a b)
  simpa only [localY, map_add, map_neg, map_mul, map_pow, hc, hinv,
    hjX] using hy

/-- A power series with nonzero constant coefficient is a Laurent unit of order zero. -/
lemma series_order_zero (s : PowerSeries k) (hs : PowerSeries.constantCoeff s ≠ 0) :
    (algebraMap (PowerSeries k) (LaurentSeries k) s).order = 0 := by
  have hc : (algebraMap (PowerSeries k) (LaurentSeries k) s).coeff 0 ≠ 0 := by
    change (HahnSeries.ofPowerSeries ℤ k s).coeff (0 : ℕ) ≠ 0
    simpa only [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff] using hs
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc)
  apply (HahnSeries.le_order_iff_forall (HahnSeries.ne_zero_of_coeff_ne_zero hc)).mpr
  intro n hn
  apply LaurentSeries.coeff_zero_of_lt_valuation k (D := 0) _ hn
  rw [ArithmeticThetaMillerR0114.branch_valuation k hs]
  simp

lemma series_order_X_pow_mul (s : PowerSeries k)
    (hs : PowerSeries.constantCoeff s ≠ 0) (n : ℕ) :
    (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^n*s)).order = n := by
  have hn : algebraMap (PowerSeries k) (LaurentSeries k) s ≠ 0 := by
    have hsn : s ≠ 0 := fun hz => hs (by rw [hz, map_zero])
    simpa only [← LaurentSeries.coe_algebraMap, map_zero] using
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ)).ne hsn
  rw [map_mul, map_pow]
  change (parameter k ^ n * _).order = _
  rw [HahnSeries.order_mul
    (pow_ne_zero n (ArithmeticThetaMillerR0114.parameter_ne_zero k)) hn,
    HahnSeries.order_pow, series_order_zero k s hs]
  have ht : (parameter k).order = 1 := by
    change (HahnSeries.ofPowerSeries ℤ k PowerSeries.X).order = 1
    rw [HahnSeries.ofPowerSeries_X, HahnSeries.order_single one_ne_zero]
  simp [ht]

/-- The derivative does not vanish at a nonsingular point with zero Y coordinate. -/
lemma localDerivative_ne_zero (e : Fin 3 → k) (a : k)
    (hp : (Curve k e).Nonsingular a 0) : localDerivative k e a ≠ 0 := by
  have hn := hp.2
  simp only [evalEval_polynomialX, evalEval_polynomialY, Curve,
    ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
    zero_mul, mul_zero, zero_sub, add_zero, ne_eq, not_true_eq_false,
    or_false] at hn
  intro hz
  apply hn
  dsimp [localDerivative] at hz
  linear_combination -hz

/-- Naturality of evaluation of bivariate polynomials. -/
lemma bivariate_natural {A B : Type*} [CommRing A] [CommRing B]
    (f : k →+* A) (g : A →+* B) (v w : A) (F : Polynomial (Polynomial k)) :
    g (F.eval₂ (Polynomial.eval₂RingHom f v) w) =
      F.eval₂ (Polynomial.eval₂RingHom (g.comp f) (g v)) (g w) := by
  rw [Polynomial.hom_eval₂]
  have he : g.comp (Polynomial.eval₂RingHom f v) =
      Polynomial.eval₂RingHom (g.comp f) (g v) := by
    apply RingHom.ext
    intro p
    exact Polynomial.hom_eval₂ p f g v
  rw [he]

lemma coordinate_eval {K : Type*} [Field K] [Algebra k K] (e : Fin 3 → k)
    (M : FF k e →ₐ[k] K) (F : Polynomial (Polynomial k)) :
    M (algebraMap (Coord k e) (FF k e) (CoordinateRing.mk (Curve k e) F)) =
      F.eval₂ (Polynomial.eval₂RingHom (algebraMap k K) (M (xFunction k e)))
        (M (yFunction k e)) := by
  let L := M.toRingHom.comp ((algebraMap (Coord k e) (FF k e)).comp
    (CoordinateRing.mk (Curve k e)))
  have hL : L = Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap k K) (M (xFunction k e))) (M (yFunction k e)) := by
    apply Polynomial.ringHom_ext
    · intro p
      have hc : L.comp Polynomial.C =
          Polynomial.eval₂RingHom (algebraMap k K) (M (xFunction k e)) := by
        apply Polynomial.ringHom_ext
        · intro a
          simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
          change M (algebraMap (Coord k e) (FF k e)
            (AdjoinRoot.mk _ (C (C a)))) = algebraMap k K a
          rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
            ← IsScalarTower.algebraMap_apply k k[X] (Coord k e),
            ← IsScalarTower.algebraMap_apply k (Coord k e) (FF k e), M.commutes]
        · simp [L, xFunction, CoordinateRing.XClass, map_zero, sub_zero]
      exact (DFunLike.congr_fun hc p).trans (Polynomial.eval₂_C ..).symm
    · simp only [Polynomial.eval₂RingHom]
      simp [L, yFunction, CoordinateRing.YClass]
  exact DFunLike.congr_fun hL F

lemma coordinate_polynomial_series (e : Fin 3 → k) (T : Translations k e)
    (hT : IsTranslationSystem k e T) (h : PowerSeries k)
    (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (a b : k) (hp : (Curve k e).Nonsingular a b) (F : Polynomial (Polynomial k)) :
    ∃ s : PowerSeries k,
      expansion k e T E (.some a b hp)
        (algebraMap (Coord k e) (FF k e) (CoordinateRing.mk (Curve k e) F)) =
          algebraMap (PowerSeries k) (LaurentSeries k) s ∧
      PowerSeries.constantCoeff s = Polynomial.eval b (Polynomial.map (Polynomial.evalRingHom a) F) := by
  let sx := localX k e h a b
  let sy := localY k e h a b
  let s := F.eval₂ (Polynomial.eval₂RingHom PowerSeries.C sx) sy
  refine ⟨s, ?_, ?_⟩
  · have hxy := translated_coordinate_series k e T hT h E hh hE a b hp
    have he := coordinate_eval k e (E.comp (T (.some a b hp)).toAlgHom) F
    change expansion k e T E (.some a b hp) _ = _ at he
    rw [he]
    change F.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k))
      (expansion k e T E (.some a b hp) (xFunction k e)))
      (expansion k e T E (.some a b hp) (yFunction k e)) = _
    rw [hxy.1, hxy.2]
    exact (bivariate_natural k PowerSeries.C
      (algebraMap (PowerSeries k) (LaurentSeries k)) sx sy F).symm
  · have hxy := localXY_constant k e hh.1 a b
    change PowerSeries.constantCoeff (F.eval₂ (Polynomial.eval₂RingHom PowerSeries.C sx) sy) = _
    rw [bivariate_natural k]
    change F.eval₂ (Polynomial.eval₂RingHom (RingHom.id k)
      (PowerSeries.constantCoeff (localX k e h a b)))
      (PowerSeries.constantCoeff (localY k e h a b)) = _
    rw [hxy.1, hxy.2]
    exact (Polynomial.eval_map _ _).symm

lemma local_orders [CharZero k] [DecidableEq k] (e : Fin 3 → k) (T : Translations k e)
    (hT : IsTranslationSystem k e T) (h : PowerSeries k)
    (E : FF k e →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k e h)
    (hE : ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E)
    (a b : k) (hp : (Curve k e).Nonsingular a b) :
    pointOrder k e T E (xFunction k e-algebraMap k (FF k e) a) (.some a b hp) =
      (if b = 0 then 2 else 1) ∧
    (b = 0 → pointOrder k e T E (yFunction k e) (.some a b hp) = 1) := by
  have hxy := translated_coordinate_series k e T hT h E hh hE a b hp
  have hx : expansion k e T E (.some a b hp)
      (xFunction k e-algebraMap k (FF k e) a) =
        algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X * localR k e h a b) := by
    have hc : algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a) =
      algebraMap k (LaurentSeries k) a := rfl
    change E (T (.some a b hp) (_-_)) = _
    rw [map_sub, AlgEquiv.commutes, map_sub, E.commutes]
    change expansion k e T E (.some a b hp) (xFunction k e) - _ = _
    rw [hxy.1]
    simp only [localX, map_add, hc, add_sub_cancel_left]
  by_cases hb : b = 0
  · subst b
    let q : PowerSeries k := (PowerSeries.C (localDerivative k e a)*h +
      PowerSeries.C (localRemainder k e a 0)*PowerSeries.X^2) * (localD k h a)⁻¹^2
    have hq : localR k e h a 0 = PowerSeries.X*q := by
      dsimp [localR, q]
      simp only [mul_zero, map_zero, zero_mul, zero_add]
      ring
    have hq0 : PowerSeries.constantCoeff q = localDerivative k e a := by
      simp [q, hh.1, PowerSeries.constantCoeff_inv, localD_constant k hh.1]
    have hd := localDerivative_ne_zero k e a hp
    constructor
    · simp only [pointOrder, hx, hq]
      rw [show PowerSeries.X*(PowerSeries.X*q) = PowerSeries.X^2*q by ring]
      exact series_order_X_pow_mul k q (by rwa [hq0]) 2
    · intro _
      simp only [pointOrder, hxy.2]
      have hy : localY k e h a 0 = PowerSeries.X * (h*q*(localD k h a)⁻¹) := by
        simp only [localY, map_zero, neg_zero, zero_mul, add_zero, zero_add, hq]
        ring
      rw [hy, ← pow_one PowerSeries.X]
      apply series_order_X_pow_mul k _ _ 1
      simpa [hq0, hh.1, PowerSeries.constantCoeff_inv, localD_constant k hh.1] using hd
  · constructor
    · simp only [pointOrder, hx, if_neg hb]
      rw [← pow_one PowerSeries.X]
      apply series_order_X_pow_mul k _ _ 1
      rw [localR_constant k e hh.1]
      exact mul_ne_zero (by norm_num) hb
    · exact fun hz => (hb hz).elim

/-- The actual translated expansion is regular at every affine point and detects
both unramified and ramified local parameters. -/
theorem local_affine_expansion :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
    Function.Injective e → ∀ T : Translations k e, IsTranslationSystem k e T →
    ∀ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
    ArithmeticThetaMillerR0114.branchEquation k e h →
    ArithmeticThetaMillerR0114.IsInfinityEmbedding k e h E →
    ∀ (x y : k) (hp : (Curve k e).Nonsingular x y),
    (∀ F : Polynomial (Polynomial k), ∃ s : PowerSeries k,
      expansion k e T E (.some x y hp)
        (algebraMap (Coord k e) (FF k e) (CoordinateRing.mk (Curve k e) F)) =
        algebraMap (PowerSeries k) (LaurentSeries k) s ∧
      PowerSeries.constantCoeff s = Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom x) F)) ∧
    pointOrder k e T E (xFunction k e-algebraMap k (FF k e) x) (.some x y hp) =
      (if y = 0 then 2 else 1) ∧
    (y = 0 → pointOrder k e T E (yFunction k e) (.some x y hp) = 1) := by
  intro k _ _ _ e _ T hT h E hh hE x y hp
  exact ⟨coordinate_polynomial_series k e T hT h E hh hE x y hp,
    local_orders k e T hT h E hh hE x y hp⟩

end ArithmeticThetaReciprocityR0116
