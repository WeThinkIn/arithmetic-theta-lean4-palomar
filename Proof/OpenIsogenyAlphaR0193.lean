module

public import QuotientFourMarkingR0193

@[expose] public section

/-! Intrinsic alpha on the actual quotient and its normalized Hodge pullback. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaIsogenyHalfLinesR0193
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaPullback
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaGlobalFourTorsionR0190.OpenFullLevelAlpha
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180

namespace OpenIsogenyAlpha

/-- The two transported labels determine the canonical Cartesian lift. -/
lemma transported_marking_eq {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (C : Test S E R W G)
    (M : FamilyLevel S E 4) (B : FullLevel R W G 4 (𝟙 (Base R)))
    (hx : B.x.val ≫ C.map = baseMap S R C.scalar ≫ M.x.val)
    (hy : B.y.val ≫ C.map = baseMap S R C.scalar ≫ M.y.val) :
    liftMarking G hG C M = B := by
  have hxe : (liftMarking G hG C M).x = B.x := by
    apply Subtype.ext
    apply C.cartesian.hom_ext
    · exact (liftMarkPoint_map G C M.x).trans hx.symm
    · exact (liftMarkPoint G C M.x).property.trans B.x.property.symm
  have hye : (liftMarking G hG C M).y = B.y := by
    apply Subtype.ext
    apply C.cartesian.hom_ext
    · exact (liftMarkPoint_map G C M.y).trans hy.symm
    · exact (liftMarkPoint G C M.y).property.trans B.y.property.symm
  have hext (P Q : FullLevel R W G 4 (𝟙 (Base R)))
      (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
    cases P
    cases Q
    cases hx
    cases hy
    rfl
  exact hext _ _ hxe hye

/-- Package accepted generic gluing with its formula for every transported marking. -/
lemma family_alpha_exists {S : Type} [CommRing S] (E : EllipticFamily S)
    (M : FamilyLevel S E 4) (T : Atlas S E) :
    ∃ a : Γ(hodge E, ⊤), IsFamilyAlpha S E M a := by
  obtain ⟨a, ha, hat⟩ := glue_alpha_sections M (by decide) (dvd_refl 4) T
  refine ⟨a, ha, ?_⟩
  intro R _ _ _ _ _ W _ G hG C B hx hy
  have hgeom := relative_curve_geometry R W
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  have he := glued_alpha_test M (by decide) (dvd_refl 4) T a hat R W G hG C
  have hs := (localAlpha_spec M (by decide) (dvd_refl 4) G hG C).1
  rw [transported_marking_eq G hG C M B hx hy] at hs
  have he' : (comparison C).hom.app ⊤
      (pullbackGlobalSection (baseMap S R C.scalar) (hodge E) a) =
      localAlpha M (by decide) (dvd_refl 4) G hG C := by
    simpa only [alphaPull, pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
      Scheme.Hom.preimage_top, res_self] using he
  rw [he']
  exact hs

end OpenIsogenyAlpha

/-- The source section is exactly the inverse-degree multiple of the actual
quotient's Hodge pullback, and is a frame on the entire open ambient base. -/
theorem open_isogeny_alpha :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L m : ℕ),
    0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : LevelData k L),
    ∃ A : OpenAlpha k L m D,
      IsFrame (hodge D.atlas.descent.family) ⊤ (ambientAlpha k L m D A) := by
  intro k _ _ _ L m hL hm hmeven hdiv D
  have hmL : m ∣ L := dvd_trans (by use 8; omega) hdiv
  have hLeven : Even L := even_iff_two_dvd.mpr
    (dvd_trans (by use 4*m; omega) hdiv)
  have hL3 : 3 ≤ L := by
    have h := Nat.le_of_dvd hL hdiv
    omega
  obtain ⟨Q⟩ := global_level_cyclic_quotient k L hL3 hLeven D.atlas m hm hmL
  obtain ⟨M, hM⟩ := quotient_four_marking k L m hL hm hmeven hdiv D Q
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

end ArithmeticThetaIsogenyHalfLinesR0193

#print axioms ArithmeticThetaIsogenyHalfLinesR0193.OpenIsogenyAlpha.transported_marking_eq
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.OpenIsogenyAlpha.family_alpha_exists
#print axioms ArithmeticThetaIsogenyHalfLinesR0193.open_isogeny_alpha
