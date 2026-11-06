module

public import MatrixFamilyGlobalSectionsR0188
public import LegendreLevelFamilyConstructionR0176

@[expose] public section

/-! Existence of the actual geometric matrix family from arithmetic input alone. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConservativeKernelR0189
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaCompatibleLevelR0178 ArithmeticThetaOpenHodgeR0180

/-- All geometric inputs to the accepted section construction are produced
from the valid positive-rank matrix family. -/
theorem arithmetic_geometric_family_existence :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ∃ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by
  intro n h hn hh A hA
  classical
  obtain ⟨hN, _, _, _, _, _, _⟩ := indexed_full_unary_factorization n h hn hh A hA
  let L := level (commonN A)
  have hL : 3 ≤ L := by
    have hp : 0 < (commonN A)^2 := pow_pos hN 2
    dsimp [L, level]
    omega
  have heven : Even L := by
    refine ⟨12 * (commonN A)^2, ?_⟩
    dsimp [L, level]
    omega
  obtain ⟨atlas⟩ := legendre_level_family_construction ℂ L hL
  obtain ⟨two, htwo, cover, quotient, _⟩ :=
    normal_affine_classifying_construction ℂ L hL heven atlas
  let D : LevelData ℂ L := ⟨atlas, two, htwo, cover, quotient⟩
  obtain ⟨X⟩ := smooth_projective_level_completion ℂ L hL heven D
  obtain ⟨H, hH⟩ := compact_hodge_lattice_extension ℂ L hL heven D X
  obtain ⟨d, hd, _⟩ := global_family_discriminant ℂ D.atlas.quotient.ring
    D.atlas.quotient.smooth D.atlas.descent.family
  obtain ⟨d2, hd2, _⟩ := compact_discriminant_section ℂ L hL heven D X H hH d hd
  have hc : ArithmeticThetaComponentDegreeR0184.IsCompactD2 ℂ L D X H d2 :=
    ⟨d, hd, hd2.1⟩
  letI : NeZero L := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ L
  obtain ⟨E, hE⟩ := tate_full_level_marking ℂ L hL heven ζ hζ
  obtain ⟨b, hb, _⟩ :=
    TateLevelClassifyingParameter.classifying_exists_unique ℂ L hL heven D E
  obtain ⟨T, hTE, hTb⟩ := (tate_hodge_comparison_tests ℂ L hL heven D).1 E b hb
  obtain ⟨disk, hdisk, _⟩ := tate_cusp_disk_extension ℂ L hL heven D E X b hb
  let V : DiskTest ℂ L D X :=
    { toTest := T, disk := disk, extends_eq := hTb.symm ▸ hdisk }
  have hmark : CanonicalMarking ℂ L ζ V.level := by
    change CanonicalMarking ℂ L ζ T.level
    rw [hTE]
    exact hE
  obtain ⟨U, hU, hformal, hfamily⟩ :=
    matrix_family_global_sections n h hn hh A hA D X H hH d2 hc V ζ hζ hmark
  exact ⟨U, hU, hformal, D, X, H, hH, V, hfamily⟩

#print axioms arithmetic_geometric_family_existence
end ArithmeticThetaConservativeKernelR0189
