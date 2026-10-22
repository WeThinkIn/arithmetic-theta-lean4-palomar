module

public import IsogenyAlphaDesignatedExpansionR0193
public import IsogenyAlphaAllCuspOrdersR0193
public import CompactFullLevelAlphaR0190

@[expose] public section

/-! Unique compact extension of the actual normalized isogeny alpha. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaIsogenyHalfLinesR0193
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.CompactFullLevelAlpha

namespace CompactIsogenyAlpha

/-- Restriction through the open base uses the same geometric Tate comparison
as the ambient normalized isogeny section. -/
lemma open_test_eq (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (A : OpenAlpha k L m D)
    (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    transportSection V.base _ _ (openTestIso k L V) (openAlpha k L m D A) =
      testAlpha k L m D A V := by
  have h := transportSection_comp D.quotient.inclusion V.base
    (hodge D.atlas.descent.family) (openHodge k L D)
    (Hodge (LaurentSeries k) (TateCurve k L)) (Iso.refl _) (openTestIso k L V)
    (ambientAlpha k L m D A)
  rw [compose_openTestIso] at h
  simpa [IsogenyAlphaAllCuspOrders.transport_top_eq, openAlpha, testAlpha] using h.symm

end CompactIsogenyAlpha

/-- The prescribed normalized section extends uniquely, retaining the actual
kernel-label order and the complete signed canonical theta-square coefficient. -/
theorem compact_isogeny_alpha :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L →
    ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L),
    ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D)
      (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X),
    ArithmeticThetaBoundaryHodgeR0182.Canonical k L H →
    ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D,
    ∃! a : (H.line).presheaf.obj (Opposite.op ⊤),
      ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes k L m D X H A a := by
  intro k _ _ _ L m hL hm hmEven hdiv D X H hH A
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  have hord := isogeny_alpha_all_cusp_orders k L m hL hm hmEven hdiv D A
  have hexp := isogeny_alpha_designated_expansion k L m hL hm hmEven hdiv D A
  let d := openAlpha k L m D A
  have ht (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
      transportSection V.base _ _ (openTestIso k L V) d = testAlpha k L m D A V :=
    CompactIsogenyAlpha.open_test_eq k L m D A V
  letI := X.openImmersion
  letI := compact_noetherian k L D X
  letI := inclusion_schematic k L D X
  obtain ⟨a, ha, _⟩ := existsUnique_extension_of_local_lifts X.inclusion
    H.line H.invertible (openHodge k L D) H.onOpen d
    (alpha_local_lifts k L hb.1 hb.2.1 D X H hH d (by
      intro V
      obtain ⟨i, z, j, v, _, _, hv⟩ := hord V
      exact ⟨PowerSeries.X^j * (v : PowerSeries k), (ht V).trans hv⟩))
  have har : restrictAlpha L k D X H a = d := (restrict_eq_transport k L H a).trans ha
  refine ⟨a, ⟨har, ?_, ?_⟩, ?_⟩
  · intro V η hη
    obtain ⟨i, z, j, v, hcoord, horder, hv⟩ := hord V.toTest
    exact ⟨i, z, j, v, hcoord, horder,
      disk_coefficient_of_restrict k L H d a har V _ ((ht V.toTest).trans hv) η hη⟩
  · intro V ζ hζ hcan η hη
    exact disk_coefficient_of_restrict k L H d a har V _
      ((ht V.toTest).trans (hexp V.toTest ζ hζ hcan)) η hη
  · intro b hb
    apply restrict_injective k L H
    exact hb.1.trans har.symm

#print axioms CompactIsogenyAlpha.open_test_eq
#print axioms compact_isogeny_alpha
end ArithmeticThetaIsogenyHalfLinesR0193
