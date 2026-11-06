import IsogenyHalfLinesDefinitionsR0193

/-! The prescribed four-marking on every actual cyclic quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaIsogenyHalfLinesR0193
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180

/-- The labels are formed on the source and mapped by the supplied quotient.
The accepted family lift criterion certifies all nonzero four-torsion labels. -/
theorem quotient_four_marking :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : LevelData k L),
    ∀ (Q : CyclicQuotient k L m D),
    ∃ M : FamilyLevel D.atlas.quotient.ring Q.target 4,
      TargetMarking k L m D Q M := by
  intro k _ _ _ L m hL hm _ hdiv D Q
  let E := SourceFamily k L D
  let A := D.atlas.marking
  have hm4 : m * 4 ∣ L := dvd_trans (by use 2; omega) hdiv
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m 4) hm4
  obtain ⟨P, hP⟩ := cyclic_of_level E hL A m hm hmL
  have hP' : P.point = kernelPoint k L D.atlas m := hP
  letI := sectionGroup E
  letI := sectionGroup Q.target
  let F : sections E →* sections Q.target := pointHom E Q.arrow Q.hom (𝟙 _)
  let sx : sections E := A.x ^ (L / (m * 4))
  let sy : sections E := A.y ^ (L / 4)
  have hlift (a b : ℕ) :
      (F (sx ^ b * sy ^ a)).val = liftPoint k L D.atlas m 4 a b ≫ Q.arrow.map := by
    change (sx ^ b * sy ^ a).val ≫ Q.arrow.map = _
    dsimp [liftPoint, sx, sy]
    simp only [nsmul_pow, pow_mul]
    rfl
  have hpoint (a b : Fin 4) (hab : a.val ≠ 0 ∨ b.val ≠ 0) :
      (liftPoint k L D.atlas m 4 a.val b.val ≫ Q.arrow.map) ≫
          Q.target.law.schemeNsmul 4 = zero Q.target ∧
      Disjoint (Set.range (liftPoint k L D.atlas m 4 a.val b.val ≫ Q.arrow.map))
        (Set.range (zero Q.target)) := by
    have hl := level_lift_conditions E hL A m 4 hm (by decide) hm4 a b hab
    have hp : liftPoint k L D.atlas m 4 a.val b.val ≫ E.projection = 𝟙 _ :=
      (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*4)*b.val) A.x)
        (E.law.nsmul (𝟙 _) (L/4*a.val) A.y)).property
    exact quotient_lift E hm P (kernelPoint k L D.atlas m) hP' Q 4
      (liftPoint k L D.atlas m 4 a.val b.val) hp
      (by simpa only [hP', kernelPoint, liftPoint] using hl.1)
      (by simpa only [hP', kernelPoint, liftPoint] using hl.2)
  have hx : (F sx).val = liftPoint k L D.atlas m 4 0 1 ≫ Q.arrow.map := by
    simpa only [pow_one, pow_zero, mul_one] using hlift 0 1
  have hy : (F sy).val = liftPoint k L D.atlas m 4 1 0 ≫ Q.arrow.map := by
    simpa only [pow_one, pow_zero, one_mul] using hlift 1 0
  let M : FamilyLevel D.atlas.quotient.ring Q.target 4 := {
    x := F sx
    y := F sy
    killed_x := by rw [hx]; exact (hpoint 0 1 (by decide)).1
    killed_y := by rw [hy]; exact (hpoint 1 0 (by decide)).1
    avoids := by
      intro i j hij
      have he : (Q.target.law.mul (𝟙 _)
          (Q.target.law.nsmul (𝟙 _) i.val (F sx))
          (Q.target.law.nsmul (𝟙 _) j.val (F sy))).val =
            liftPoint k L D.atlas m 4 j.val i.val ≫ Q.arrow.map := by
        simp only [nsmul_pow]
        change ((F sx) ^ i.val * (F sy) ^ j.val).val = _
        simpa only [map_mul, map_pow] using hlift j.val i.val
      rw [he]
      exact (hpoint j i hij.symm).2 }
  exact ⟨M, hx, hy⟩

end ArithmeticThetaIsogenyHalfLinesR0193

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.quotient_four_marking
