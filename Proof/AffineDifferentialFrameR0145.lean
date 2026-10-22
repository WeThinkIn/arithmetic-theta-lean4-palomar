module

public import CompactifiedDifferentialDefinitionsR0145
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TateGeneralSplitCubic

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace AffineFrame
open ArithmeticThetaCubicModelR0144
open MvPolynomial
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)

lemma roots_distinct (h3 : 3 ≤ r) (he : Even r) :
    root k r 0 ≠ root k r 1 ∧ root k r 0 ≠ root k r 2 ∧
      root k r 1 ≠ root k r 2 := by
  obtain ⟨m, hm⟩ := he
  have hr : r = 2 * m := by omega
  rw [hr]
  have hmpos : 0 < m := by omega
  have h := ArithmeticThetaTateIdentities.general_two_torsion_distinct (k := k) m hmpos
  have hinj : Function.Injective (algebraMap (PowerSeries k) (LaurentSeries k)) :=
    HahnSeries.ofPowerSeries_injective
  simpa only [root, rootSeries, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from rfl,
    if_true, if_pos rfl, if_neg (by decide : ¬ (1 : ℕ) = 0),
    if_neg (by decide : ¬ (2 : ℕ) = 0), if_neg (by decide : ¬ (2 : ℕ) = 1),
    Nat.mul_div_right m (by decide : 0 < 2)] using
      (show (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) 0 (-1)) ≠
          (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) m 1) ∧
        (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) 0 (-1)) ≠
          (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) m (-1)) ∧
        (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) m 1) ≠
          (algebraMap (PowerSeries k) (LaurentSeries k)) (ArithmeticThetaTateSeries.tateX (2*m) m (-1)) from
        ⟨fun h01 => h.1 (hinj h01), fun h02 => h.2.1 (hinj h02), fun h12 => h.2.2 (hinj h12)⟩)

lemma equation :
    cubicCoordinate k r true ^ 2 =
      (cubicCoordinate k r false - algebraMap _ _ (root k r 0)) *
      (cubicCoordinate k r false - algebraMap _ _ (root k r 1)) *
      (cubicCoordinate k r false - algebraMap _ _ (root k r 2)) := by
  have h : Ideal.Quotient.mk (Ideal.span {cubicPolynomial k r}) (cubicPolynomial k r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (MvPolynomial.X 1) ^ 2 -
    (Ideal.Quotient.mk _ (MvPolynomial.X 0) - Ideal.Quotient.mk _ (C (root k r 0))) *
    (Ideal.Quotient.mk _ (MvPolynomial.X 0) - Ideal.Quotient.mk _ (C (root k r 1))) *
    (Ideal.Quotient.mk _ (MvPolynomial.X 0) - Ideal.Quotient.mk _ (C (root k r 2))) = 0
  rw [← map_pow, ← map_sub, ← map_sub, ← map_sub, ← map_mul, ← map_mul, ← map_sub]
  convert h using 2 <;> simp [cubicPolynomial, Fin.prod_univ_succ, root, mul_assoc]

lemma coprime (h3 : 3 ≤ r) (he : Even r) :
    IsCoprime (2 * cubicCoordinate k r true) (cubicDerivative k r) := by
  let a := root k r 0
  let b := root k r 1
  let c := root k r 2
  let f : Polynomial (LaurentSeries k) :=
    (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) *
      (Polynomial.X - Polynomial.C c)
  obtain ⟨hab, hac, hbc⟩ := roots_distinct k r h3 he
  have hab' := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))
  have hac' := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hac))
  have hbc' := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hbc))
  have hf : f.Separable :=
    (Polynomial.separable_X_sub_C.mul Polynomial.separable_X_sub_C hab').mul
      Polynomial.separable_X_sub_C (hac'.mul_left hbc')
  have h := IsCoprime.map (S := CubicRing k r) hf (Polynomial.aeval (R := LaurentSeries k) (cubicCoordinate k r false)).toRingHom
  have hfe : Polynomial.aeval (R := LaurentSeries k) (cubicCoordinate k r false) f = cubicCoordinate k r true ^ 2 := by
    simpa [f, a, b, c] using (equation k r).symm
  have hde : Polynomial.aeval (R := LaurentSeries k) (cubicCoordinate k r false) f.derivative = cubicDerivative k r := by
    simp [f, Polynomial.derivative_mul, cubicDerivative, a, b, c]
    ring
  change IsCoprime (Polynomial.aeval (R := LaurentSeries k) (cubicCoordinate k r false) f)
    (Polynomial.aeval (R := LaurentSeries k) (cubicCoordinate k r false) f.derivative) at h
  rw [hfe, hde] at h
  have hy := (IsCoprime.pow_left_iff (by omega : 0 < 2)).mp h
  have ht : IsUnit (2 : CubicRing k r) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by
        intro hz
        have hz' : algebraMap k (LaurentSeries k) 2 = algebraMap k (LaurentSeries k) 0 := by
          simpa only [map_ofNat, map_zero] using hz
        have := (algebraMap k (LaurentSeries k)).injective hz'
        norm_num at this : (2 : LaurentSeries k) ≠ 0)).map
      (algebraMap (LaurentSeries k) (CubicRing k r))
  exact (isCoprime_mul_unit_left_left ht _ _).mpr hy

abbrev P := MvPolynomial (Fin 2) (LaurentSeries k)
abbrev I := Ideal.span {cubicPolynomial k r}
abbrev Q : P k →ₐ[LaurentSeries k] CubicRing k r := Ideal.Quotient.mkₐ _ _

def dp : P k :=
  3 * X 0 ^ 2 - 2 * C (root k r 0 + root k r 1 + root k r 2) * X 0 +
    C (root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2)

lemma Q_dp : Q k r (dp k r) = cubicDerivative k r := by
  change Q k r (dp k r) =
    3 * Q k r (X 0) ^ 2 -
    2 * Q k r (C (root k r 0 + root k r 1 + root k r 2)) * Q k r (X 0) +
    Q k r (C (root k r 0 * root k r 1 + root k r 0 * root k r 2 + root k r 1 * root k r 2))
  simp only [dp, map_add, map_sub, map_mul, map_ofNat, map_pow]

def polyDer : Derivation (LaurentSeries k) (P k) (P k) :=
  MvPolynomial.mkDerivation _ (fun i => if i = 0 then 2 * X 1 else dp k r)

lemma polyDer_relation : polyDer k r (cubicPolynomial k r) = 0 := by
  simp [cubicPolynomial, Fin.prod_univ_succ, polyDer, pow_two, Derivation.leibniz,
    dp, root, smul_eq_mul]
  ring

lemma polyDer_preserves (p : P k) (hp : Q k r p = 0) : Q k r (polyDer k r p) = 0 := by
  have hp' : p ∈ I k r := Ideal.Quotient.eq_zero_iff_mem.mp hp
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hp'
  have hrel : Q k r (cubicPolynomial k r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simp [Derivation.leibniz, polyDer_relation, hrel, smul_eq_mul]

def tangent : Derivation (LaurentSeries k) (CubicRing k r) (CubicRing k r) :=
  Derivation.liftOfSurjective (f := Q k r) Ideal.Quotient.mk_surjective (polyDer_preserves k r)

lemma tangent_x : tangent k r (cubicCoordinate k r false) = 2 * cubicCoordinate k r true := by
  change tangent k r (Q k r (X 0)) = _
  rw [tangent, Derivation.liftOfSurjective_apply]
  change Q k r ((MvPolynomial.mkDerivation _ (fun i : Fin 2 => if i = 0 then 2 * X 1 else dp k r)) (X 0)) = _
  rw [MvPolynomial.mkDerivation_X, if_pos rfl, map_mul, map_ofNat]
  rfl

lemma tangent_y : tangent k r (cubicCoordinate k r true) = cubicDerivative k r := by
  change tangent k r (Q k r (X 1)) = _
  rw [tangent, Derivation.liftOfSurjective_apply]
  simpa [polyDer] using Q_dp k r

lemma derivation_ext {M : Type*} [AddCommGroup M] [Module (CubicRing k r) M]
    [Module (LaurentSeries k) M] [IsScalarTower (LaurentSeries k) (CubicRing k r) M]
    (d e : Derivation (LaurentSeries k) (CubicRing k r) M)
    (hx : d (cubicCoordinate k r false) = e (cubicCoordinate k r false))
    (hy : d (cubicCoordinate k r true) = e (cubicCoordinate k r true)) : d = e := by
  apply Derivation.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change d (Q k r p) = e (Q k r p)
  induction p using MvPolynomial.induction_on with
  | C c =>
    change d (algebraMap (LaurentSeries k) (CubicRing k r) c) =
      e (algebraMap (LaurentSeries k) (CubicRing k r) c)
    simp only [Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have hi : d (Q k r (X i)) = e (Q k r (X i)) := by
      fin_cases i
      · exact hx
      · exact hy
    simp only [map_mul, Derivation.leibniz, hp, hi]

lemma differential_relation :
    (2 * cubicCoordinate k r true) • KaehlerDifferential.D (LaurentSeries k) (CubicRing k r) (cubicCoordinate k r true) =
    cubicDerivative k r • KaehlerDifferential.D (LaurentSeries k) (CubicRing k r) (cubicCoordinate k r false) := by
  have h := congrArg (KaehlerDifferential.D (LaurentSeries k) (CubicRing k r)) (equation k r)
  simp only [pow_two, Derivation.leibniz, map_sub, Derivation.map_algebraMap, sub_zero] at h
  simp only [smul_add, smul_smul, ← add_smul] at h
  convert h using 1
  · congr 1
    ring
  · congr 1
    simp only [cubicDerivative, map_add, map_mul]
    ring

lemma bezout_pair {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    (a b p q : B) (u v : M) (h : a * p + b * q = 1)
    (hr : p • v = q • u) :
    p • (a • u + b • v) = u ∧ q • (a • u + b • v) = v := by
  constructor
  · calc
      p • (a • u + b • v) = a • (p • u) + b • (p • v) := by module
      _ = a • (p • u) + b • (q • u) := by rw [hr]
      _ = (a * p + b * q) • u := by module
      _ = u := by rw [h, one_smul]
  · calc
      q • (a • u + b • v) = a • (q • u) + b • (q • v) := by module
      _ = a • (p • v) + b • (q • v) := by rw [hr]
      _ = (a * p + b * q) • v := by module
      _ = v := by rw [h, one_smul]

/-- A general Bézout construction using a genuine derivation and its universal module. -/
lemma normalized_frame {F B : Type u} [CommRing F] [CommRing B] [Algebra F B]
    (x y q : B) (hcp : IsCoprime (2*y) q)
    (d : Derivation F B B) (dx : d x = 2*y) (dy : d y = q)
    (hrel : (2*y) • KaehlerDifferential.D F B y = q • KaehlerDifferential.D F B x)
    (hext : ∀ d e : Derivation F B (KaehlerDifferential F B),
      d x = e x → d y = e y → d = e) :
    ∃! e : DifferentialFrame F B, NormalizedAffineFrame F B x y q e := by
  let Ω := KaehlerDifferential F B
  let D := KaehlerDifferential.D F B
  obtain ⟨a, b, hab⟩ := hcp
  let δ : Ω := a • D x + b • D y
  obtain ⟨hx, hy⟩ := bezout_pair a b (2*y) q (D x) (D y) hab hrel
  change (2*y) • δ = D x at hx
  change q • δ = D y at hy
  let L : Ω →ₗ[B] B := d.liftKaehlerDifferential
  have Lx : L (D x) = 2*y := (d.liftKaehlerDifferential_comp_D x).trans dx
  have Ly : L (D y) = q := (d.liftKaehlerDifferential_comp_D y).trans dy
  have Lδ : L δ = 1 := by
    change L (a • D x + b • D y) = 1
    rw [map_add, map_smul, map_smul, Lx, Ly]
    exact hab
  let E : B →ₗ[B] Ω := LinearMap.toSpanSingleton B Ω δ
  have hLE : L.comp E = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change L (z • δ) = z
    rw [map_smul, Lδ, smul_eq_mul, mul_one]
  have hEL : E.comp L = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply hext
    · change E (L (D x)) = D x
      rw [Lx]
      exact hx
    · change E (L (D y)) = D y
      rw [Ly]
      exact hy
  let e : DifferentialFrame F B := LinearEquiv.ofLinearMap E L hEL hLE
  have he1 : e 1 = δ := one_smul B δ
  refine ⟨e, ?_, ?_⟩
  · change D x = (2*y) • e 1 ∧ D y = q • e 1
    rw [he1]
    exact ⟨hx.symm, hy.symm⟩
  · intro e' he'
    change D x = (2*y) • e' 1 ∧ D y = q • e' 1 at he'
    have hδ : δ = e' 1 := by
      change a • D x + b • D y = e' 1
      rw [he'.1, he'.2, smul_smul, smul_smul, ← add_smul, hab, one_smul]
    apply LinearEquiv.ext
    intro z
    calc
      e' z = z • e' 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      _ = z • δ := by rw [hδ]
      _ = e z := rfl

end AffineFrame

open ArithmeticThetaCubicModelR0144

/-- The normalized affine frame, including the branch points where Y vanishes. -/
theorem affine_differential_frame (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (h3 : 3 ≤ r) (he : Even r) :
    ∃! e : DifferentialFrame (LaurentSeries k) (CubicRing k r),
      IsAffineDifferentialFrame k r e := by
  letI : CommRing (CubicRing k r) := inferInstance
  exact AffineFrame.normalized_frame
    (cubicCoordinate k r false) (cubicCoordinate k r true) (cubicDerivative k r)
    (AffineFrame.coprime k r h3 he) (AffineFrame.tangent k r)
    (AffineFrame.tangent_x k r) (AffineFrame.tangent_y k r)
    (AffineFrame.differential_relation k r) (AffineFrame.derivation_ext k r)

end ArithmeticThetaCompactifiedDifferentialR0145
