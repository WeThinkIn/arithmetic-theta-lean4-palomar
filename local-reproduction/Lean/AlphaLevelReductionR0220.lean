import KeyTateDefinitionsR0220
import ArbitraryFourTorsionRootR0214

/-! Signed alpha is unchanged by the actual reduction to level four. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaKeyTateR0220
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190

namespace AlphaLevelReduction

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)

/-- Existence uses the accepted reduction over arbitrary rational rings. -/
lemma exists_reduction (hG : IsOriginLaw R W G) (N : ℕ) (hN : 0 < N)
    (h4 : 4 ∣ N) (M : FullLevel R W G N (𝟙 (Base R))) :
    ∃ M4 : FullLevel R W G 4 (𝟙 (Base R)), ReducesFour R W G N M M4 := by
  exact ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryFourTorsionRoot.level_reduction
    W G hG N 4 hN (by decide) h4 M

lemma half_quarter (hG : IsOriginLaw R W G) (N : ℕ) (h4 : 4 ∣ N)
    (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    G.nsmul (𝟙 _) 2 (G.nsmul (𝟙 _) (N / 4) z) =
      G.nsmul (𝟙 _) (N / 2) z := by
  letI := FullLevelCyclicLiftsR0175.sectionGroup G hG
  have hn : N / 4 * 2 = N / 2 := by omega
  simp only [FullLevelTorsionSplittingR0175.nsmul_pow, ← pow_mul, hn]

lemma labels_eq (hG : IsOriginLaw R W G) (N : ℕ) (h4 : 4 ∣ N)
    (M : FullLevel R W G N (𝟙 (Base R)))
    (M4 : FullLevel R W G 4 (𝟙 (Base R)))
    (h : ReducesFour R W G N M M4) (i : Fin 3) :
    twoLabel R W G 4 M4 i = twoLabel R W G N M i := by
  simp only [twoLabel, h.1, h.2, show 4 / 2 = 2 from rfl,
    half_quarter R W G hG N h4]

lemma quarter_eq (N : ℕ)
    (M : FullLevel R W G N (𝟙 (Base R)))
    (M4 : FullLevel R W G 4 (𝟙 (Base R)))
    (h : ReducesFour R W G N M M4) :
    quarterPoint R W G 4 M4 = quarterPoint R W G N M := by
  simp only [quarterPoint, show 4 / 4 = 1 from rfl, G.nsmul_one_apply, h.2]

end AlphaLevelReduction

/-- Both directions retain the same signed root and the same differential frame. -/
theorem alpha_level_reduction
    (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (N : ℕ) (_hN : 0 < N) (h4 : 4 ∣ N)
    (M : FullLevel R W G N (𝟙 (Base R)))
    (M4 : FullLevel R W G 4 (𝟙 (Base R)))
    (h : ReducesFour R W G N M M4)
    (a : (Hodge R W).presheaf.obj (Opposite.op ⊤)) :
    RealizesAlpha R W G N M a ↔ RealizesAlpha R W G 4 M4 a := by
  simp only [RealizesAlpha, RootData, Labels,
    AlphaLevelReduction.labels_eq R W G hG N h4 M M4 h,
    AlphaLevelReduction.quarter_eq R W G N M M4 h]

end ArithmeticThetaKeyTateR0220

#print axioms ArithmeticThetaKeyTateR0220.alpha_level_reduction
