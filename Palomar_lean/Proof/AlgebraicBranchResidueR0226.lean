module

public import AlgebraicBranchDefinitionsR0226
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

/-! Residue fields of algebraic extensions of the punctured formal disk. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAlgebraicBranchesR0226
namespace AlgebraicBranchResidueR0226
open Polynomial IsLocalRing
variable {k E : Type} [Field k] [Field E] [Algebra (LaurentSeries k) E]

/-- Constants enter the residue field through the specified disk inclusion. -/
def constants (V : ValuationExtension k E) : k →+* ResidueField V.ring :=
  ((residue V.ring).comp V.inclusion).comp PowerSeries.C

lemma residue_inclusion (V : ValuationExtension k E) (f : PowerSeries k) :
    residue V.ring (V.inclusion f) = constants V (PowerSeries.constantCoeff f) := by
  let := V.isLocal
  have hf : f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
      maximalIdeal (PowerSeries k) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker]
    simp
  have hm := map_nonunit V.inclusion _ hf
  have hz := (residue_eq_zero_iff _).mpr hm
  simpa only [map_sub, sub_eq_zero, constants, RingHom.comp_apply] using hz

lemma primitive_reduction_ne_zero (p : Polynomial (PowerSeries k)) (hp : p.IsPrimitive) :
    p.map PowerSeries.constantCoeff ≠ 0 := by
  intro hz
  have hd : Polynomial.C (PowerSeries.X : PowerSeries k) ∣ p := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [PowerSeries.X_dvd_iff]
    have hi := congrArg (fun q : Polynomial k => q.coeff i) hz
    simpa using hi
  have hu := hp _ hd
  have hc := hu.map (PowerSeries.constantCoeff : PowerSeries k →+* k)
  simp at hc

lemma integral_relation [Algebra.IsAlgebraic (LaurentSeries k) E]
    (V : ValuationExtension k E) (x : V.ring) :
    ∃ p : Polynomial (PowerSeries k), p.IsPrimitive ∧ p.eval₂ V.inclusion x = 0 := by
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (PowerSeries k)
  obtain ⟨q, hq, hx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := LaurentSeries k) (x : E)
  let p := IsLocalization.integerNormalization (nonZeroDivisors (PowerSeries k)) q
  have hp : p ≠ 0 := mt IsFractionRing.integerNormalization_eq_zero_iff.mp hq
  have he : p.eval₂ (seriesMap k E) (x : E) = 0 :=
    IsLocalization.integerNormalization_eval₂_eq_zero _ _ q hx
  have hinj : Function.Injective (seriesMap k E) :=
    (algebraMap (LaurentSeries k) E).injective.comp (IsFractionRing.injective _ _)
  have he' := Polynomial.eval₂_primPart_eq_zero hinj hp he
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  apply (show Function.Injective (algebraMap V.ring E) from Subtype.val_injective)
  rw [map_zero, Polynomial.hom_eval₂, V.compatible]
  exact he'

lemma constants_surjective [IsAlgClosed k] [Algebra.IsAlgebraic (LaurentSeries k) E]
    (V : ValuationExtension k E) : Function.Surjective (constants V) := by
  let : Algebra k (ResidueField V.ring) := (constants V).toAlgebra
  have halg (y : ResidueField V.ring) : IsAlgebraic k y := by
    obtain ⟨x, rfl⟩ := residue_surjective (R := V.ring) y
    obtain ⟨p, hp, hx⟩ := integral_relation V x
    refine ⟨p.map PowerSeries.constantCoeff, primitive_reduction_ne_zero p hp, ?_⟩
    change (p.map PowerSeries.constantCoeff).eval₂ (constants V) (residue V.ring x) = 0
    rw [Polynomial.eval₂_map]
    have hc : (constants V).comp PowerSeries.constantCoeff =
        (residue V.ring).comp V.inclusion := by
      ext f
      exact (residue_inclusion V f).symm
    rw [hc, ← Polynomial.hom_eval₂, hx, map_zero]
  let : Algebra.IsAlgebraic k (ResidueField V.ring) := ⟨halg⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

end AlgebraicBranchResidueR0226

/-- The prescribed local extension has exactly the original constant residue field,
without any degree restriction on the algebraic field extension. -/
theorem algebraic_branch_residue
    (k E : Type) [Field k] [IsAlgClosed k] [Field E]
    [Algebra (LaurentSeries k) E] [Algebra.IsAlgebraic (LaurentSeries k) E]
    (V : ValuationExtension k E) :
    ∃! σ : V.ring →+* k,
      σ.comp V.inclusion = (PowerSeries.constantCoeff : PowerSeries k →+* k) ∧
      RingHom.ker σ = IsLocalRing.maximalIdeal V.ring := by
  classical
  let τ := AlgebraicBranchResidueR0226.constants V
  have hτ : Function.Bijective τ :=
    ⟨τ.injective, AlgebraicBranchResidueR0226.constants_surjective V⟩
  let e : k ≃+* IsLocalRing.ResidueField V.ring := RingEquiv.ofBijective τ hτ
  let σ : V.ring →+* k := e.symm.toRingHom.comp (IsLocalRing.residue V.ring)
  have hσ : σ.comp V.inclusion = PowerSeries.constantCoeff := by
    ext f
    change e.symm (IsLocalRing.residue V.ring (V.inclusion f)) = _
    rw [AlgebraicBranchResidueR0226.residue_inclusion]
    exact e.symm_apply_apply _
  have hker : RingHom.ker σ = IsLocalRing.maximalIdeal V.ring := by
    ext x
    change e.symm (IsLocalRing.residue V.ring x) = 0 ↔ _
    rw [e.symm.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]
  refine ⟨σ, ⟨hσ, hker⟩, ?_⟩
  intro ρ hρ
  ext x
  obtain ⟨c, hc⟩ := hτ.2 (IsLocalRing.residue V.ring x)
  have hm : x - V.inclusion (PowerSeries.C c) ∈ IsLocalRing.maximalIdeal V.ring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hc.symm
  have hρx : ρ x = c := by
    have hz : ρ (x - V.inclusion (PowerSeries.C c)) = 0 := by
      rw [← RingHom.mem_ker, hρ.2]
      exact hm
    have hρc : ρ (V.inclusion (PowerSeries.C c)) = c := by
      simpa only [RingHom.comp_apply, PowerSeries.constantCoeff_C] using
        DFunLike.congr_fun hρ.1 (PowerSeries.C c)
    simpa only [map_sub, RingHom.comp_apply, PowerSeries.constantCoeff_C,
      sub_eq_zero, hρc] using hz
  have hσx : σ x = c := by
    change e.symm (IsLocalRing.residue V.ring x) = c
    rw [← hc]
    exact e.symm_apply_apply c
  exact hρx.trans hσx.symm

end ArithmeticThetaAlgebraicBranchesR0226
