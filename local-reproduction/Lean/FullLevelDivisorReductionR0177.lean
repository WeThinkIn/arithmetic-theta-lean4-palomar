import FullLevelCyclicLiftsR0175

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreComparisonR0177
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaFullLevelCoverR0175

/-- Reducing both marked sections by the quotient of levels preserves full level,
including divisor one. Avoidance is inherited on the entire base. -/
theorem full_level_divisor_reduction :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L) (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), ∃ N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G d (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), N.x = G.nsmul (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (L / d) M.x ∧ N.y = G.nsmul (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (L / d) M.y := by
  intro R _ _ _ _ _ W _ G hG L d hL hd hdL M
  let := FullLevelCyclicLiftsR0175.sectionGroup G hG
  have hqd : L / d * d = L := Nat.div_mul_cancel hdL
  have hq : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
  have hlt (i : Fin d) : L / d * i.val < L := by
    have h := Nat.mul_lt_mul_of_pos_left i.isLt hq
    rwa [hqd] at h
  have hmul (n : ℕ) (z : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
      G.nsmul (𝟙 (Base R)) n (G.nsmul (𝟙 (Base R)) (L / d) z) =
        G.nsmul (𝟙 (Base R)) (L / d * n) z := by
    simp only [RelativeKatoFiberSpecialization.nsmul_pow, pow_mul]
  let N : FullLevel R W G d (𝟙 (Base R)) :=
    { x := G.nsmul (𝟙 (Base R)) (L / d) M.x
      y := G.nsmul (𝟙 (Base R)) (L / d) M.y
      killed_x := by rw [hmul, hqd, M.killed_x]
      killed_y := by rw [hmul, hqd, M.killed_y]
      avoids := by
        intro i j hij
        rw [hmul, hmul]
        apply M.avoids ⟨L / d * i.val, hlt i⟩ ⟨L / d * j.val, hlt j⟩
        rcases hij with hi | hj
        · exact Or.inl (Nat.mul_ne_zero (Nat.ne_of_gt hq) hi)
        · exact Or.inr (Nat.mul_ne_zero (Nat.ne_of_gt hq) hj) }
  exact ⟨N, rfl, rfl⟩

#print axioms full_level_divisor_reduction
end ArithmeticThetaLegendreComparisonR0177
