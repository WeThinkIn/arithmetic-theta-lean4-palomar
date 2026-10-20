module

public import MillerReciprocityDefinitionsR0116
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

/-!
# Translations of the actual split-cubic function field

The generic chord substitution preserves the cubic and has the negative-point
substitution as inverse. Transcendence proves injectivity of coordinate-ring
substitution via its concrete rank-two norm, then localization extends it to
an algebra automorphism. Coordinates determine the unique family.
-/
noncomputable section
universe u
namespace ArithmeticThetaReciprocityR0116
open Polynomial WeierstrassCurve.Affine
open ArithmeticThetaMillerR0114 (Coord xFunction yFunction)

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k)

omit [CharZero k] [DecidableEq k] in
lemma ff_ext {K : Type*} [Field K] [Algebra k K] {E F : FF k e →ₐ[k] K}
    (hx : E (xFunction k e) = F (xFunction k e))
    (hy : E (yFunction k e) = F (yFunction k e)) : E = F := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Coord k e)
  have hc : E.comp (IsScalarTower.toAlgHom k (Coord k e) (FF k e)) =
      F.comp (IsScalarTower.toAlgHom k (Coord k e) (FF k e)) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simpa [xFunction, CoordinateRing.XClass, CoordinateRing.mk, AdjoinRoot.mk_C] using hx
    · change E (algebraMap (Coord k e) (FF k e) (AdjoinRoot.root _)) =
        F (algebraMap (Coord k e) (FF k e) (AdjoinRoot.root _))
      simpa only [yFunction, CoordinateRing.YClass, map_zero, sub_zero, CoordinateRing.mk,
        AdjoinRoot.mk_X] using hy
  exact fun a => DFunLike.congr_fun hc a

lemma x_transcendental (he : Function.Injective e) : Transcendental k (xFunction k e) := by
  obtain ⟨h, E, hh, hE, _⟩ := ArithmeticThetaMillerR0114.exists_infinity_embedding k e he
  intro hx
  have := hx.algHom E
  rw [hE.1] at this
  exact ArithmeticThetaMillerR0114.infinityX_transcendental k hh.1 this

omit [CharZero k] [DecidableEq k] in
lemma x_sub_ne_zero (a : k) : xFunction k e - algebraMap k (FF k e) a ≠ 0 := by
  have h := (IsFractionRing.injective (Coord k e) (FF k e)).ne
    (CoordinateRing.XClass_ne_zero (W' := Curve k e) a)
  simpa [xFunction, CoordinateRing.XClass, CoordinateRing.mk, map_sub,
    IsScalarTower.algebraMap_eq k (Coord k e) (FF k e), AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq', Polynomial.algebraMap_apply] using h

lemma generic_equation (he : Function.Injective e) :
    (yFunction k e)^2 = (xFunction k e)^3 -
      algebraMap k (FF k e) (e 0 + e 1 + e 2) * (xFunction k e)^2 +
      algebraMap k (FF k e) (e 0 * e 1 + e 0 * e 2 + e 1 * e 2) * xFunction k e -
      algebraMap k (FF k e) (e 0 * e 1 * e 2) := by
  obtain ⟨h, E, hh, hE, _⟩ := ArithmeticThetaMillerR0114.exists_infinity_embedding k e he
  have hq := ArithmeticThetaMillerR0114.infinity_equation k e hh
  simp [ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
    polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    aeval_def, eval₂_neg, map_add, map_mul, map_neg, AlgHom.toRingHom_eq_coe] at hq
  have hxE : E.toRingHom (xFunction k e) = ArithmeticThetaMillerR0114.infinityX k h := hE.1
  have hyE : E.toRingHom (yFunction k e) = ArithmeticThetaMillerR0114.infinityY k h := hE.2
  have hc (a : k) : E.toRingHom (algebraMap k (FF k e) a) =
      algebraMap k (LaurentSeries k) a := E.commutes a
  apply E.injective
  simp only [map_pow, map_sub, map_add, map_mul, hxE, hyE, hc]
  linear_combination hq

section ChordAlgebra
variable {K : Type*} [Field K]

lemma chord_relation (S T U x y a b s : K)
    (hx : y^2 = x^3-S*x^2+T*x-U)
    (ha : b^2 = a^3-S*a^2+T*a-U)
    (hd : x-a ≠ 0) (hs : s*(x-a) = y-b) :
    (x-a)*(s^2+S-x-a-a) = 3*a^2-2*S*a+T-2*b*s := by
  apply (mul_left_cancel₀ hd)
  linear_combination hx - ha + (s*(x-a)+y+b)*hs

lemma chord_equation (S T U x y a b s : K)
    (hx : y^2 = x^3-S*x^2+T*x-U)
    (ha : b^2 = a^3-S*a^2+T*a-U)
    (hd : x-a ≠ 0) (hs : s*(x-a) = y-b) :
    let v := s^2+S-x-a
    let w := -y+s*(x-v)
    w^2 = v^3-S*v^2+T*v-U := by
  dsimp only
  have hr := chord_relation S T U x y a b s hx ha hd hs
  linear_combination ha + (s^2+S-x-a-a)*hr -
    (y-b-s*(x-a)+2*b+2*s*(s^2+S-x-a-a))*hs

lemma chord_inverse (S x y a b s : K) (hs : s*(x-a)=y-b)
    (hd' : s^2+S-x-a-a ≠ 0) :
    let v := s^2+S-x-a
    let w := -y+s*(x-v)
    ((w+b)/(v-a))^2+S-v-a = x ∧
      -w+((w+b)/(v-a))*(v-x) = y := by
  dsimp only
  have ht : (-y+s*(x-(s^2+S-x-a))+b)/(s^2+S-x-a-a) = -s := by
    apply (div_eq_iff hd').mpr
    linear_combination hs
  rw [ht]
  constructor <;> ring

omit [CharZero k] [DecidableEq k] in
lemma chord_transcendental [Algebra k K] [CharZero K]
    (S T U x y a b s : K)
    (hS : IsAlgebraic k S) (hT : IsAlgebraic k T) (hU : IsAlgebraic k U)
    (ha' : IsAlgebraic k a) (hb' : IsAlgebraic k b)
    (hx : y^2 = x^3-S*x^2+T*x-U)
    (ha : b^2 = a^3-S*a^2+T*a-U)
    (hd : x-a ≠ 0) (hs : s*(x-a)=y-b)
    (ht : Transcendental k x) (hn : b ≠ 0 ∨ 3*a^2-2*S*a+T ≠ 0) :
    s^2+S-x-a-a ≠ 0 ∧ Transcendental k (s^2+S-x-a) := by
  have hr := chord_relation S T U x y a b s hx ha hd hs
  have hd' : s^2+S-x-a-a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    have heq : 3*a^2-2*S*a+T = 2*b*s := by linear_combination -hr
    have hb : b ≠ 0 := by
      rcases hn with hb | hn
      · exact hb
      · intro hb
        apply hn
        simpa [hb] using heq
    have hs' : s = (3*a^2-2*S*a+T) * (2*b)⁻¹ := by
      field_simp
      linear_combination -heq
    have halg : IsAlgebraic k s := by
      rw [hs']
      have h2 : IsAlgebraic k (2 : K) := by
        convert (isAlgebraic_one (R := k) (A := K)).add isAlgebraic_one using 1 <;> first | rfl | norm_num
      have h3 : IsAlgebraic k (3 : K) := by
        convert h2.add isAlgebraic_one using 1 <;> first | rfl | norm_num
      exact ((((h3.mul (ha'.pow 2)).sub ((h2.mul hS).mul ha')).add hT).mul
        ((h2.mul hb').inv))
    apply ht
    have hx' : x = s^2+S-a-a := by linear_combination -hz
    rw [hx']
    exact (((halg.pow 2).add hS).sub ha').sub ha'
  refine ⟨hd', ?_⟩
  intro hv
  have hw : IsAlgebraic k (-y+s*(x-(s^2+S-x-a))) := by
    apply IsAlgebraic.of_pow (n := 2) (by norm_num)
    rw [chord_equation S T U x y a b s hx ha hd hs]
    exact (((hv.pow 3).sub (hS.mul (hv.pow 2))).add (hT.mul hv)).sub hU
  have hinv := (chord_inverse S x y a b s hs hd').1
  apply ht
  rw [← hinv]
  simpa only [div_eq_mul_inv] using (((((hw.add hb').mul ((hv.sub ha').inv)).pow 2).add hS).sub hv).sub ha'

end ChordAlgebra

omit [CharZero k] [DecidableEq k] in
lemma lift_coordinates {K : Type*} [Field K] [Algebra k K] (v w : K)
    (ht : Transcendental k v)
    (hq : w^2 = v^3 - algebraMap k K (e 0+e 1+e 2)*v^2 +
      algebraMap k K (e 0*e 1+e 0*e 2+e 1*e 2)*v - algebraMap k K (e 0*e 1*e 2)) :
    ∃ E : FF k e →ₐ[k] K, E (xFunction k e) = v ∧ E (yFunction k e) = w := by
  have hpoly : (Curve k e).polynomial.eval₂ (aeval v).toRingHom w = 0 := by
    simp [Curve, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      aeval_def, eval₂_neg, map_add, map_mul, map_neg, AlgHom.toRingHom_eq_coe]
    simp only [map_add, map_mul] at hq
    linear_combination hq
  let Cmap : Coord k e →ₐ[k] K :=
    AdjoinRoot.liftAlgHom (Curve k e).polynomial (aeval v) w hpoly
  have hof (p : k[X]) : Cmap (algebraMap k[X] (Coord k e) p) = aeval v p :=
    AdjoinRoot.liftAlgHom_of _ _ _ _ _
  have hinj : Function.Injective Cmap := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    apply (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis (Curve k e))).mp
    apply (transcendental_iff_injective.mp ht)
    rw [map_zero, ← hof]
    rw [AdjoinRoot.algebraMap_eq, CoordinateRing.coe_norm_smul_basis]
    simp only [map_mul]
    have hf : Cmap (CoordinateRing.mk (Curve k e) (C p + C q * X)) = 0 := by
      simpa [CoordinateRing.smul, map_add, map_mul] using ha
    rw [hf, zero_mul]
  let E : FF k e →ₐ[k] K := IsFractionRing.liftAlgHom hinj
  refine ⟨E, ?_, ?_⟩
  · simp only [E, xFunction, IsFractionRing.lift_algebraMap, CoordinateRing.XClass,
      CoordinateRing.mk, Cmap, IsFractionRing.coe_liftAlgHom, map_zero, sub_zero, AdjoinRoot.mk_C]
    exact (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (aeval_X _)
  · simp only [E, yFunction, IsFractionRing.lift_algebraMap, CoordinateRing.YClass,
      CoordinateRing.mk, Cmap, IsFractionRing.coe_liftAlgHom, map_zero, sub_zero, AdjoinRoot.mk_X]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

def affineX (a b : k) : FF k e :=
  ((yFunction k e-algebraMap k (FF k e) b)/(xFunction k e-algebraMap k (FF k e) a))^2 +
    algebraMap k (FF k e) (e 0+e 1+e 2)-xFunction k e-algebraMap k (FF k e) a

def affineY (a b : k) : FF k e :=
  -yFunction k e +
    ((yFunction k e-algebraMap k (FF k e) b)/(xFunction k e-algebraMap k (FF k e) a))*
      (xFunction k e-affineX k e a b)

lemma affine_properties (he : Function.Injective e) (a b : k)
    (hn : (Curve k e).Nonsingular a b) :
    affineX k e a b - algebraMap k (FF k e) a ≠ 0 ∧
    Transcendental k (affineX k e a b) ∧
    (affineY k e a b)^2 = (affineX k e a b)^3 -
      algebraMap k (FF k e) (e 0+e 1+e 2)*(affineX k e a b)^2 +
      algebraMap k (FF k e) (e 0*e 1+e 0*e 2+e 1*e 2)*affineX k e a b -
      algebraMap k (FF k e) (e 0*e 1*e 2) := by
  let : CharZero (FF k e) := charZero_of_injective_algebraMap (algebraMap k (FF k e)).injective
  let c := algebraMap k (FF k e)
  let S := c (e 0+e 1+e 2)
  let T := c (e 0*e 1+e 0*e 2+e 1*e 2)
  let U := c (e 0*e 1*e 2)
  let x := xFunction k e
  let y := yFunction k e
  let s := (y-c b)/(x-c a)
  have hd : x-c a ≠ 0 := x_sub_ne_zero k e a
  have hs : s*(x-c a)=y-c b := div_mul_cancel₀ _ hd
  have ha : (c b)^2 = (c a)^3-S*(c a)^2+T*(c a)-U := by
    have hp := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) a b).mp hn.1
    have hp' := congrArg c hp
    dsimp [S, T, U]
    simp only [map_pow, map_mul, map_sub, map_add] at hp' ⊢
    linear_combination hp'
  have hns : c b ≠ 0 ∨ 3*(c a)^2-2*S*(c a)+T ≠ 0 := by
    have hp := hn.2
    simp only [evalEval_polynomialX, evalEval_polynomialY, Curve,
      ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      zero_mul, zero_sub, add_zero] at hp
    rcases hp with hx | hy
    · right
      have hD : 3*a^2-2*(e 0+e 1+e 2)*a+(e 0*e 1+e 0*e 2+e 1*e 2) ≠ 0 := by
        intro hz
        apply hx
        linear_combination -hz
      have hc := (map_ne_zero_iff c c.injective).mpr hD
      simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, S, T] using hc
    · left
      have hb : b ≠ 0 := fun hb => hy (by simp [hb])
      simpa only [map_zero] using c.injective.ne hb
  have ht := chord_transcendental k S T U x y (c a) (c b) s
    (isAlgebraic_algebraMap _) (isAlgebraic_algebraMap _) (isAlgebraic_algebraMap _)
    (isAlgebraic_algebraMap _) (isAlgebraic_algebraMap _)
    (generic_equation k e he) ha hd hs (x_transcendental k e he) hns
  exact ⟨ht.1, ht.2, chord_equation S T U x y (c a) (c b) s
    (generic_equation k e he) ha hd hs⟩

lemma affine_hom_exists (he : Function.Injective e) (a b : k)
    (hn : (Curve k e).Nonsingular a b) :
    ∃ E : FF k e →ₐ[k] FF k e,
      E (xFunction k e) = affineX k e a b ∧ E (yFunction k e) = affineY k e a b :=
  lift_coordinates k e _ _ (affine_properties k e he a b hn).2.1
    (affine_properties k e he a b hn).2.2

lemma affine_inverse (he : Function.Injective e) (a b : k)
    (hn : (Curve k e).Nonsingular a b) :
    ((affineY k e a b + algebraMap k (FF k e) b) /
      (affineX k e a b - algebraMap k (FF k e) a))^2 +
      algebraMap k (FF k e) (e 0+e 1+e 2) - affineX k e a b -
      algebraMap k (FF k e) a = xFunction k e ∧
    -affineY k e a b + ((affineY k e a b + algebraMap k (FF k e) b) /
      (affineX k e a b - algebraMap k (FF k e) a)) *
      (affineX k e a b - xFunction k e) = yFunction k e := by
  exact chord_inverse _ _ _ _ _ _ (div_mul_cancel₀ _ (x_sub_ne_zero k e a))
    (affine_properties k e he a b hn).1

lemma affine_equiv_exists (he : Function.Injective e) (a b : k)
    (hn : (Curve k e).Nonsingular a b) :
    ∃ E : FF k e ≃ₐ[k] FF k e,
      E (xFunction k e) = affineX k e a b ∧ E (yFunction k e) = affineY k e a b := by
  have hn' : (Curve k e).Nonsingular a (-b) := by
    simpa [negY, Curve, ArithmeticThetaMillerR0114.Curve,
      ArithmeticThetaFourTorsion.splitCurve] using (nonsingular_neg (W' := Curve k e) a b).mpr hn
  obtain ⟨E, hEx, hEy⟩ := affine_hom_exists k e he a b hn
  obtain ⟨F, hFx, hFy⟩ := affine_hom_exists k e he a (-b) hn'
  have hi := affine_inverse k e he a b hn
  simp only [map_add] at hi
  have hcomp : E.comp F = AlgHom.id k (FF k e) := by
    apply ff_ext k e
    · change E (F (xFunction k e)) = xFunction k e
      rw [hFx]
      simp only [affineX, map_pow, map_div₀, map_sub, map_add, AlgHom.commutes]
      rw [hEx, hEy]
      simpa only [map_neg, sub_neg_eq_add] using hi.1
    · change E (F (yFunction k e)) = yFunction k e
      rw [hFy]
      simp only [affineY, affineX, map_neg, map_mul, map_div₀, map_sub, map_add,
        map_pow, AlgHom.commutes]
      rw [hEx, hEy]
      simp only [sub_neg_eq_add]
      rw [hi.1]
      exact hi.2
  let A : FF k e ≃ₐ[k] FF k e := AlgEquiv.ofBijective E
    ⟨E.injective, fun z => ⟨F z, DFunLike.congr_fun hcomp z⟩⟩
  exact ⟨A, hEx, hEy⟩

/-- Unique translations with the frozen generic chord coordinates, on the actual
Mathlib Weierstrass function field over every characteristic-zero base field. -/
theorem function_field_translations :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Function.Injective e → ∃! T : Translations k e, IsTranslationSystem k e T := by
  intro k _ _ _ e he
  have hP (P : (Curve k e).Point) :
      ∃ A : FF k e ≃ₐ[k] FF k e,
        A (xFunction k e) = (translatedCoordinates k e P).1 ∧
        A (yFunction k e) = (translatedCoordinates k e P).2 := by
    cases P with
    | zero => exact ⟨AlgEquiv.refl, rfl, rfl⟩
    | some a b hn => exact affine_equiv_exists k e he a b hn
  choose T hT using hP
  refine ⟨T, hT, ?_⟩
  intro U hU
  funext P
  apply AlgEquiv.coe_toAlgHom_injective
  exact ff_ext k e ((hU P).1.trans ((hT P).1.symm))
    ((hU P).2.trans ((hT P).2.symm))

end ArithmeticThetaReciprocityR0116
