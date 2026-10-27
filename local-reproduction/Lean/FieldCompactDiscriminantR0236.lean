import CompactPowerExtensionDescentR0236
import OpenDiscriminantConstantNaturalityR0236

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticSectionsR0236
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent
open ArithmeticThetaOpenHodgeR0180

/-- The intrinsic discriminant extends over the original coefficient field,
by descent of its actual algebraically closed compact extension. -/
theorem field_compact_discriminant :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ d : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d → ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤), ArithmeticThetaArithmeticSectionsR0236.RealizesDiscriminant k L H d s := by
  intro k _ _ L hL heven D X H _hH hgeom d hd
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  obtain ⟨A⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l L hL
  obtain ⟨B, hB, V, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l L hL heven A
  let E : LevelData l L := ⟨A, B, hB, V, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l L hL heven E
  let C : Comparison k L ι D E X Y := coefficientMap k L ι hL heven D E X Y
  obtain ⟨J, hJ⟩ := native_canonical_exists l L hL heven E Y
  obtain ⟨a, ha, _⟩ := hgeom l ι E Y C.openMap C.compactMap C.classifies
    C.extendsOpen C.hodgeMap C.normalized J hJ
  obtain ⟨e, he, _⟩ := global_family_discriminant l A.quotient.ring
    A.quotient.smooth A.descent.family
  obtain ⟨t, ht, _⟩ := compact_discriminant_section l L hL heven E Y J hJ e he
  have hn := open_discriminant_constant_naturality k l ι L hL heven D E X Y C d e hd he
  obtain ⟨s, hs, _⟩ := compact_power_extension_descent k l ι L hL heven D E X Y C H J a ha
    24 (pullToOpen k L 24 d) ⟨t, ht.1.trans hn.symm⟩
  refine ⟨s, ⟨hs.1, ?_⟩, ?_⟩
  · intro T η hη
    exact ⟨disk_expansion_of_restrict k L hL heven H d hd s hs.1 T η hη,
      discriminant_coefficients k L (by omega)⟩
  · intro z hz
    exact restrictPower_injective k L H 24 (hz.1.trans hs.1.symm)

#print axioms field_compact_discriminant
end ArithmeticThetaArithmeticSectionsR0236
