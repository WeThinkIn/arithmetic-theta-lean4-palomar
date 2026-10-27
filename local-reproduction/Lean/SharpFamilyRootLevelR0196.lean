import FiniteMetaplecticTestLevelR0196

/-! The original sharp theta cover, strengthened by its square-root test fibers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181

/-- Keep the accepted geometric witnesses and add finite representability for
all square-root tests of that same cover with its specified pulled-back root. -/
theorem sharp_family_root_level :
∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ArithmeticThetaMetaplecticTestsR0196.MetaplecticFamily A U H V := by
  intro n h hn hh A hA
  obtain ⟨U, hU, hformal, D, X, H, V, hH, J, C, het, hrest⟩ :=
    ArithmeticThetaSharpKernelR0195.sharp_matrix_geometric_family n h hn hh A hA
  have h2 : IsUnit (2 : (Component ℂ (level (commonN A)) D X
      (V.disk (closedPoint ℂ))).presheaf.obj (Opposite.op ⊤)) := by
    let a : ℂ →+* (Component ℂ (level (commonN A)) D X
        (V.disk (closedPoint ℂ))).presheaf.obj (Opposite.op ⊤) :=
      (projection ℂ (level (commonN A)) D X (V.disk (closedPoint ℂ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    have hu : IsUnit (2 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using hu.map a
  exact ⟨U, hU, hformal, D, X, H, V, hH, J, C,
    finite_metaplectic_test_level _ _ _ C.map (pullRoot C.map J)
      h2 C.finite het C.surjective, het, hrest⟩

#print axioms sharp_family_root_level
end ArithmeticThetaMetaplecticTestsR0196
