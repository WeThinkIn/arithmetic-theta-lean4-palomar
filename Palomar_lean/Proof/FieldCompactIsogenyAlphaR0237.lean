module

public import FieldOpenIsogenyAlphaR0237
public import OpenIsogenyAlphaConstantNaturalityR0237
public import FieldIsogenyAlphaLocalBehaviorR0237
public import CompactIsogenyAlphaR0193
public import CompactPowerExtensionDescentR0236
public import GeometricCompactHodgeComparisonR0236

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticHalfLinesR0237
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaArithmeticSectionsR0236
open ArithmeticThetaBoundaryConstantsR0235
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaGlobalFourTorsionR0190.CompactFullLevelAlpha
open ArithmeticThetaTensorPower
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

namespace FieldCompactIsogenyAlpha

/-- The tensor-one section map is a bijection, via the genuine tensor unit. -/
lemma one_bijective (S : Scheme.{0}) (M : S.Modules) :
    Function.Bijective (tensorPowerSection S M 1 ⊤) := by
  let e := ArithmeticThetaSheafTensor.tensorLeftUnitIso S M
  have he := ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)
  have h := tensorPowerSection_one S M ⊤
  constructor
  · intro x y hxy
    exact (h x).symm.trans ((congrArg (fun z => e.hom.app ⊤ z) hxy).trans (h y))
  · intro t
    refine ⟨e.hom.app ⊤ t, he.1 ?_⟩
    exact h _

lemma restrict_transport {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    {ι : k →+* l} {L : ℕ} {D : LevelData k L} {E : LevelData l L}
    {X : Compactification k L D} {Y : Compactification l L E}
    (C : Comparison k L ι D E X Y) (H : Extension k L D X) (J : Extension l L E Y)
    (e : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (he : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J e)
    (a : Γ(H.line, ⊤)) :
    restrictAlpha L l E Y J (transportSection C.compactMap H.line J.line e a) =
      transportSection C.openMap _ _ C.hodgeMap (restrictAlpha L k D X H a) := by
  rw [restrict_eq_transport, restrict_eq_transport]
  rw [← transportSection_comp,
    CompactPowerExtensionDescent.comparison_square C H J e he,
    transportSection_comp_eq]
  rfl

lemma extension_exists (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (hL : 0 < L) (hm : 0 < m) (hmeven : Even m) (hdiv : 8*m ∣ L)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (hH : Canonical k L H) (hgH : GeometricallyCanonical H) (A : OpenAlpha k L m D) :
    ∃ a : Γ(H.line, ⊤), restrictAlpha L k D X H a = openAlpha k L m D A := by
  have hb := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  obtain ⟨T⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l L hb.1
  obtain ⟨B, hB, V, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l L hb.1 hb.2.1 T
  let E : LevelData l L := ⟨T, B, hB, V, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l L hb.1 hb.2.1 E
  let C := GeometricCanonicalHodgeDescent.coefficientMap k L ι hb.1 hb.2.1 D E X Y
  obtain ⟨J, hJ, hgJ⟩ := geometric_canonical_hodge_descent l L hb.1 hb.2.1 E Y
  obtain ⟨e, he, _⟩ := geometric_compact_hodge_comparison k l ι L hb.1 hb.2.1
    D E X Y C H J hH hgH hJ hgJ
  obtain ⟨A', _⟩ := field_open_isogeny_alpha l L m hL hm hmeven hdiv E
  obtain ⟨b, hbreal, _⟩ := compact_isogeny_alpha l L m hL hm hmeven hdiv E Y J hJ A'
  have hn := open_isogeny_alpha_constant_naturality k l ι L m hL hm hmeven hdiv D E X Y C A A'
  let u := tensorPowerSection (OpenBase k L D) (openHodge k L D) 1 ⊤ (openAlpha k L m D A)
  have ht : ∃ t : Γ(tensorPower Y.space J.line 1, ⊤),
      restrictPower l L J 1 t = powerTransport C.openMap _ _ C.hodgeMap 1 u := by
    refine ⟨tensorPowerSection Y.space J.line 1 ⊤ b, ?_⟩
    have hb : transportSection Y.inclusion _ _ J.onOpen b = openAlpha l L m E A' :=
      (restrict_eq_transport l L J b).symm.trans hbreal.1
    exact (transportSection_tensor Y.inclusion J.line (openHodge l L E) J.onOpen 1 b).trans
      ((congrArg (tensorPowerSection (OpenBase l L E) (openHodge l L E) 1 ⊤)
        (hb.trans hn.symm)).trans
        (transportSection_tensor C.openMap (openHodge k L D) (openHodge l L E)
          C.hodgeMap 1 (openAlpha k L m D A)).symm)
  obtain ⟨s, hs, _⟩ := compact_power_extension_descent k l ι L hb.1 hb.2.1
    D E X Y C H J e he 1 u ht
  obtain ⟨a, ha⟩ := (one_bijective X.space H.line).2 s
  refine ⟨a, ?_⟩
  apply (one_bijective (OpenBase k L D) (openHodge k L D)).1
  rw [restrict_eq_transport]
  rw [← ha] at hs
  exact (transportSection_tensor X.inclusion H.line (openHodge k L D) H.onOpen 1 a).symm.trans hs.1

end FieldCompactIsogenyAlpha

theorem field_compact_isogeny_alpha :
    ∀ (k : Type) [Field k] [CharZero k] (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L), ∀ (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D, ∃! a : (H.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes k L m D X H A a := by
  intro k _ _ L m hL hm hmeven hdiv D X H hH hgH A
  obtain ⟨a, har⟩ := FieldCompactIsogenyAlpha.extension_exists k L m hL hm hmeven hdiv D X H hH hgH A
  obtain ⟨hord, hexp⟩ := field_isogeny_alpha_local_behavior k L m hL hm hmeven hdiv D A
  let d := openAlpha k L m D A
  have ht (V : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
      transportSection V.base _ _ (openTestIso k L V) d = testAlpha k L m D A V :=
    CompactIsogenyAlpha.open_test_eq k L m D A V
  refine ⟨a, ⟨har, ?_, ?_⟩, ?_⟩
  · intro V η hη
    obtain ⟨i, z, j, v, hcoord, horder, hv⟩ := hord V.toTest
    exact ⟨i, z, j, v, hcoord, horder,
      disk_coefficient_of_restrict k L H d a har V _ ((ht V.toTest).trans hv) η hη⟩
  · intro V ζ hζ hcan η hη
    exact disk_coefficient_of_restrict k L H d a har V _
      ((ht V.toTest).trans (hexp V.toTest ζ hζ hcan)) η hη
  · intro b hb
    exact restrict_injective k L H (hb.1.trans har.symm)

theorem compact_isogeny_alpha_constant_naturality :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L m : ℕ), 0 < L → 0 < m → Even m → 8*m ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l L E Y), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ArithmeticThetaBoundaryHodgeR0182.Canonical l L J → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical J → ∀ (A : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha k L m D) (B : ArithmeticThetaIsogenyHalfLinesR0193.OpenAlpha l L m E) (a : (H.line).presheaf.obj (Opposite.op ⊤)) (b : (J.line).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes k L m D X H A a → ArithmeticThetaIsogenyHalfLinesR0193.CompactRealizes l L m E Y J B b → ∃ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback C.compactMap).obj H.line) (J.line), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J e ∧ ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection C.compactMap H.line J.line e a = b := by
  intro k l _ _ _ _ ι L m hL hm hmeven hdiv D E X Y C H J hH hgH hJ hgJ A B a b ha hb
  have hbound := IsogenyAlphaAllCuspOrders.level_bounds L m hL hm hdiv
  obtain ⟨e, he, _⟩ := geometric_compact_hodge_comparison k l ι L hbound.1 hbound.2.1
    D E X Y C H J hH hgH hJ hgJ
  refine ⟨e, he, ?_⟩
  apply restrict_injective l L J
  rw [FieldCompactIsogenyAlpha.restrict_transport C H J e he, ha.1, hb.1]
  exact open_isogeny_alpha_constant_naturality k l ι L m hL hm hmeven hdiv D E X Y C A B

#print axioms field_compact_isogeny_alpha
#print axioms compact_isogeny_alpha_constant_naturality
end ArithmeticThetaArithmeticHalfLinesR0237
