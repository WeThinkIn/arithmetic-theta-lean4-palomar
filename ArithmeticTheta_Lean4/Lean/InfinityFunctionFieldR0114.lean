import InfinityBranchR0114
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.RingTheory.Norm.Basic

/-!
# The actual function field in the full branch at infinity

The Laurent image of X has nontrivial valuation and is therefore transcendental.
The coordinate-ring norm then proves injectivity of the quotient evaluation map.
Fraction-field localization supplies existence; the two coordinates determine
uniqueness. No completion isomorphism or geometric pairing is assumed.
-/

noncomputable section
universe u
namespace ArithmeticThetaMillerR0114
open Polynomial WeierstrassCurve.Affine

variable (k : Type u) [Field k]

lemma parameter_ne_zero : parameter k ≠ 0 := by
  simpa [parameter, ← LaurentSeries.coe_algebraMap] using
    (HahnSeries.ofPowerSeries_injective.ne PowerSeries.X_ne_zero)

lemma branch_valuation {h : PowerSeries k} (hh : PowerSeries.constantCoeff h ≠ 0) :
    Valued.v (algebraMap (PowerSeries k) (LaurentSeries k) h) = 1 := by
  rw [LaurentSeries.valuation_def, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  simpa [PowerSeries.idealX, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] using hh

lemma infinityX_transcendental {h : PowerSeries k} (hh : PowerSeries.constantCoeff h = 1) :
    Transcendental k (infinityX k h) := by
  let : (Valued.v : Valuation (LaurentSeries k) (WithZero (Multiplicative ℤ))).IsTrivialOn k :=
    ⟨fun a ha => by
      change Valued.v (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a)) = 1
      apply branch_valuation
      simpa using ha⟩
  have hz : Valued.v (parameter k) = WithZero.exp (-1 : ℤ) := by
    simpa [parameter] using LaurentSeries.valuation_X_pow k 1
  have hx : Valued.v (infinityX k h) = WithZero.exp (2 : ℤ) := by
    rw [infinityX, map_mul, map_zpow₀, branch_valuation k (by simp [hh]), mul_one, hz]
    norm_num [← WithZero.exp_zsmul]
  apply Valuation.transcendental_of_ne_one (v := Valued.v) k
  · intro he
    rw [he, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  · rw [hx]
    norm_num [WithZero.exp_eq_one]

lemma infinity_equation (e : Fin 3 → k) {h : PowerSeries k}
    (hh : branchEquation k e h) :
    (Curve k e).polynomial.eval₂ (aeval (infinityX k h)).toRingHom (infinityY k h) = 0 := by
  have he := congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hh.2
  simp only [map_pow, map_prod, map_sub, map_mul] at he
  have hc (a : k) : algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a) =
      algebraMap k (LaurentSeries k) a := rfl
  simp only [hc, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at he
  simp [Curve, ArithmeticThetaFourTorsion.splitCurve, polynomial, eval₂_add,
    eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, aeval_def,
    eval₂_neg, map_add, map_mul, map_neg, AlgHom.toRingHom_eq_coe]
  simp only [infinityX, infinityY, zpow_neg, zpow_ofNat]
  field_simp [parameter_ne_zero k]
  dsimp [parameter] at *
  linear_combination he

/-- Evaluation on the actual affine coordinate quotient. -/
def infinityCoord (e : Fin 3 → k) (h : PowerSeries k) (hh : branchEquation k e h) :
    Coord k e →ₐ[k] LaurentSeries k :=
  AdjoinRoot.liftAlgHom (Curve k e).polynomial (aeval (infinityX k h))
    (infinityY k h) (infinity_equation k e hh)

lemma infinityCoord_of (e : Fin 3 → k) (h : PowerSeries k) (hh : branchEquation k e h)
    (p : k[X]) :
    infinityCoord k e h hh (algebraMap k[X] (Coord k e) p) = aeval (infinityX k h) p := by
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ _

lemma infinityCoord_injective (e : Fin 3 → k) (h : PowerSeries k)
    (hh : branchEquation k e h) : Function.Injective (infinityCoord k e h hh) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  apply (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis (Curve k e))).mp
  apply (transcendental_iff_injective.mp (infinityX_transcendental k hh.1))
  rw [map_zero, ← infinityCoord_of k e h hh]
  rw [AdjoinRoot.algebraMap_eq, CoordinateRing.coe_norm_smul_basis]
  simp only [map_mul]
  have hf : infinityCoord k e h hh
      (CoordinateRing.mk (Curve k e) (C p + C q * X)) = 0 := by
    simpa [CoordinateRing.smul, map_add, map_mul] using ha
  rw [hf, zero_mul]

lemma functionField_ext (e : Fin 3 → k) {E F : FF k e →ₐ[k] LaurentSeries k}
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

/-- The unique algebra map with the prescribed full Laurent expansions. -/
theorem infinity_function_field_embedding :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Distinct k e → ∀ h : PowerSeries k, branchEquation k e h →
        ∃! E : FF k e →ₐ[k] LaurentSeries k, IsInfinityEmbedding k e h E := by
  intro k _ _ _ e _ h hh
  let E : FF k e →ₐ[k] LaurentSeries k :=
    IsFractionRing.liftAlgHom (infinityCoord_injective k e h hh)
  have hx : E (xFunction k e) = infinityX k h := by
    simp only [E, xFunction, IsFractionRing.lift_algebraMap, CoordinateRing.XClass,
      CoordinateRing.mk, infinityCoord, IsFractionRing.coe_liftAlgHom, map_zero, sub_zero, AdjoinRoot.mk_C]
    exact (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (aeval_X _)
  have hy : E (yFunction k e) = infinityY k h := by
    simp only [E, yFunction, IsFractionRing.lift_algebraMap, CoordinateRing.YClass,
      CoordinateRing.mk, infinityCoord, IsFractionRing.coe_liftAlgHom, map_zero, sub_zero, AdjoinRoot.mk_X]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  refine ⟨E, ⟨hx, hy⟩, ?_⟩
  intro F hF
  exact functionField_ext k e (hF.1.trans hx.symm) (hF.2.trans hy.symm)

/-- Every such map is an injection, since its domain is the actual fraction field. -/
lemma infinity_embedding_injective (e : Fin 3 → k) (E : FF k e →ₐ[k] LaurentSeries k) :
    Function.Injective E := E.injective

/-- Instantiate the universal consumer with the accepted full branch provider. -/
lemma exists_infinity_embedding [CharZero k] [DecidableEq k] (e : Fin 3 → k)
    (he : Distinct k e) :
    ∃ (h : PowerSeries k) (E : FF k e →ₐ[k] LaurentSeries k),
      branchEquation k e h ∧ IsInfinityEmbedding k e h E ∧ Function.Injective E := by
  obtain ⟨h, hh, _⟩ := infinity_branch k e
  obtain ⟨E, hE, _⟩ := infinity_function_field_embedding k e he h hh
  exact ⟨h, E, hh, hE, infinity_embedding_injective k e E⟩

end ArithmeticThetaMillerR0114
