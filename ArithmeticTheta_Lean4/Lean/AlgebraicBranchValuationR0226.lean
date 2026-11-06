import AlgebraicBranchResidueR0226

/-! A valuation extension and rational closed centre for the original formal disk. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAlgebraicBranchesR0226
open CategoryTheory AlgebraicGeometry

/-- Local valuation factorization of the specified inclusion, with the residue
map supplied by algebraicity and algebraic closedness of the constant field. -/
theorem algebraic_branch_valuation
    (k E : Type) [Field k] [IsAlgClosed k] [Field E]
    [Algebra (LaurentSeries k) E] [Algebra.IsAlgebraic (LaurentSeries k) E] :
    ∃ B : BranchValuation k E,
      B.centre (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint B.ring ∧
      B.centre ≫ Spec.map (CommRingCat.ofHom B.inclusion) =
        Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries k →+* k)) := by
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing (seriesMap k E)
  let V : ValuationExtension k E :=
    { ring := A
      inclusion := (seriesMap k E).codRestrict A.toSubring hA
      compatible := rfl
      isLocal := hlocal }
  obtain ⟨σ, hσ, _⟩ := algebraic_branch_residue k E V
  let B : BranchValuation k E :=
    { toValuationExtension := V
      residue := σ
      residue_comp := hσ.1
      residue_kernel := hσ.2 }
  refine ⟨B, ?_, ?_⟩
  · change PrimeSpectrum.comap σ (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint V.ring
    apply PrimeSpectrum.ext
    change Ideal.comap σ (IsLocalRing.maximalIdeal k) = IsLocalRing.maximalIdeal V.ring
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact hσ.2
  · change Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom V.inclusion) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f : PowerSeries k →+* k => Spec.map (CommRingCat.ofHom f)) hσ.1

end ArithmeticThetaAlgebraicBranchesR0226
