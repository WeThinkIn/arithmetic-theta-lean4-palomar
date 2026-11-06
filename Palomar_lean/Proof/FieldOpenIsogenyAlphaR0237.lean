module

public import OpenIsogenyAlphaR0193

@[expose] public section

/-! Ordered quotient marking and normalized open alpha over every characteristic-zero field. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaArithmeticHalfLinesR0237
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaIsogenyHalfLinesR0193
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection
open ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- The labels are formed on the source and mapped by the supplied quotient.
The accepted family lift criterion certifies all nonzero four-torsion labels. -/
theorem field_quotient_four_marking :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : LevelData k L),
    ∀ (Q : CyclicQuotient k L m D),
    ∃ M : FamilyLevel D.atlas.quotient.ring Q.target 4,
      TargetMarking k L m D Q M := by
  intro k _ _ L m hL hm _ hdiv D Q
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


/-- The source section is exactly the inverse-degree multiple of the actual
quotient's Hodge pullback, and is a frame on the entire open ambient base. -/
theorem field_open_isogeny_alpha :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : LevelData k L),
    ∃ A : OpenAlpha k L m D,
      IsFrame (hodge D.atlas.descent.family) ⊤ (ambientAlpha k L m D A) := by
  intro k _ _ L m hL hm hmeven hdiv D
  have hmL : m ∣ L := dvd_trans (by use 8; omega) hdiv
  have hLeven : Even L := even_iff_two_dvd.mpr
    (dvd_trans (by use 4*m; omega) hdiv)
  have hL3 : 3 ≤ L := by
    have h := Nat.le_of_dvd hL hdiv
    omega
  obtain ⟨Q⟩ := global_level_cyclic_quotient k L hL3 hLeven D.atlas m hm hmL
  obtain ⟨M, hM⟩ := field_quotient_four_marking k L m hL hm hmeven hdiv D Q
  obtain ⟨T⟩ := elliptic_family_weierstrass_atlas k D.atlas.quotient.ring
    D.atlas.quotient.smooth Q.target
  obtain ⟨a, ha⟩ := OpenIsogenyAlpha.family_alpha_exists Q.target M T
  let A : OpenAlpha k L m D := ⟨Q, M, hM, a, ha⟩
  refine ⟨A, ?_⟩
  letI := Q.etale
  letI : IsIso (familyHodgeMap Q.arrow) := family_hodge_isIso Q.arrow
  have hf := frame_iso (asIso (familyHodgeMap Q.arrow)) a ha.1
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hu : IsUnit (scalar D.atlas.quotient.ring
      (algebraMap k D.atlas.quotient.ring (m : k)⁻¹)) := by
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hm0)).map
      (algebraMap k D.atlas.quotient.ring)).map
      (Scheme.ΓSpecIso (CommRingCat.of D.atlas.quotient.ring)).inv.hom
  exact unit_frame _ _ hf hu.unit


end ArithmeticThetaArithmeticHalfLinesR0237

#print axioms ArithmeticThetaArithmeticHalfLinesR0237.field_quotient_four_marking
#print axioms ArithmeticThetaArithmeticHalfLinesR0237.field_open_isogeny_alpha
