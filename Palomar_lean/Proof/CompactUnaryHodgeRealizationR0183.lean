module

public import CompactNormalizedPowerExtensionR0183

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaCompactUnaryR0183
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaOpenHodgeR0180

/-- The open normalized section supplied by the arithmetic level data has a
unique compact regular realization, with the literal complete unary expansion. -/
theorem compact_unary_hodge_realization :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH ν hν
  have hL : 3 ≤ level N := by
    have := Nat.one_le_pow 2 N hN
    dsimp [level]
    omega
  have hLeven : Even (level N) := ⟨12*N^2, by dsimp [level]; omega⟩
  have hmNL : m*N ∣ level N := (period_parameters m N hm hN hmN).2.2.2
  let a : Fin N := ⟨unaryResidue m N ν, residue_lt m N hm hN hNeven hmN ν hν⟩
  let b : Fin N := ⟨N/2, (half_nonzero N hN hNeven).2⟩
  have hab : a.val ≠ 0 ∨ b.val ≠ 0 := Or.inr (half_nonzero N hN hNeven).1
  obtain ⟨Q, d, hd, _, hvalues⟩ := open_level_normalized_hodge_power
    k (level N) hL hLeven D.atlas m N hm hmeven hN hNeven hmN hmNL
  obtain ⟨z, ⟨hv, hframe, hnormalized⟩, _⟩ := hvalues a b hab
  let A : OpenPower k m N D a b :=
    ⟨Q, d, hd, z.1, hv, z.2, hnormalized⟩
  obtain ⟨s, ⟨hs, hdisks⟩, _⟩ := compact_normalized_power_extension
    k m N hm hmeven hN hNeven hmN D X H hH a b hab A
  refine ⟨a, b, rfl, rfl, A, s, ⟨hs, hframe, hdisks, ?_⟩, ?_⟩
  · intro V ζ hζ hmark
    obtain ⟨f, _, hf⟩ := all_cusp_normalized_power_integrality
      k m N hm hmeven hN hNeven hmN D a b hab A V.toTest
    have hexp := open_unary_designated_expansion k m N hm hmeven hN hNeven hmN
      D V.toTest ζ hζ hmark Q d hd ν hν z.1 z.2 hv hnormalized
    have hcoeff := tensorPower_frame _ (hodgeGenerator k (level N) V.differential)
      (hodgeGenerator_frame k (level N) V.differential) (weight N) ⊤ le_rfl
    rw [InitialHodgeSection.res_self] at hcoeff
    have heq := hcoeff.1 (hf.symm.trans hexp)
    have heq' : algebraMap (PowerSeries k) (LaurentSeries k) f =
        ArithmeticThetaUnaryKatoPowerR0160.unary k (N^2/m) m ν ^ exponent N := by
      exact (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).1 heq
    refine ⟨f, heq', ?_⟩
    intro η hη
    exact CompactNormalizedPowerExtensionR0183.disk_coefficient_of_restrict
      k (level N) H (weight N) A.section_ s hs V f hf η hη
  · intro t ht
    exact restrictPower_injective k (level N) H (weight N) (ht.1.trans hs.symm)

#print axioms compact_unary_hodge_realization
end ArithmeticThetaCompactUnaryR0183
