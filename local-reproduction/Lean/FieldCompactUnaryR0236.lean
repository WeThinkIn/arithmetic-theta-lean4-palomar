import CompactPowerExtensionDescentR0236
import OpenUnaryConstantNaturalityR0236
import GeometricCompactHodgeComparisonR0236

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaArithmeticSectionsR0236
open CategoryTheory AlgebraicGeometry ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaCompactUnaryR0183
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

namespace FieldCompactUnary
/-- Descend the actual normalized open section from an algebraic closure. -/
lemma extension_exists (k : Type) [Field k] [CharZero k]
    (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N)
    (hNeven : Even N) (hmN : m ∣ N)
    (D : LevelData k (level N)) (X : Compactification k (level N) D)
    (H : Extension k (level N) D X)
    (hgH : ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H)
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0)
    (A : OpenPower k m N D a b) :
    ∃ s : Γ(tensorPower X.space H.line (weight N), ⊤),
      restrictPower k (level N) H (weight N) s =
        pullToOpen k (level N) (weight N) A.section_ := by
  have hL : 3 ≤ level N := by
    have := Nat.one_le_pow 2 N hN
    dsimp [level]
    omega
  have heven : Even (level N) := ⟨12*N^2, by dsimp [level]; omega⟩
  let l := AlgebraicClosure k
  let ι : k →+* l := algebraMap k l
  obtain ⟨B⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction l (level N) hL
  obtain ⟨R, hR, V, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction l (level N) hL heven B
  let E : LevelData l (level N) := ⟨B, R, hR, V, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion l (level N) hL heven E
  let C := ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent.coefficientMap
    k (level N) ι hL heven D E X Y
  obtain ⟨J, hJ⟩ := compact_hodge_lattice_extension l (level N) hL heven E Y
  obtain ⟨e, he, _⟩ := hgH l ι E Y C.openMap C.compactMap C.classifies
    C.extendsOpen C.hodgeMap C.normalized J hJ
  have hmNL : m*N ∣ level N := (period_parameters m N hm hN hmN).2.2.2
  obtain ⟨Q', d', hd', _, hvalues⟩ := open_level_normalized_hodge_power
    l (level N) hL heven E.atlas m N hm hmeven hN hNeven hmN hmNL
  obtain ⟨z, ⟨hv, _, hn⟩, _⟩ := hvalues a b hab
  let A' : OpenPower l m N E a b := ⟨Q', d', hd', z.1, hv, z.2, hn⟩
  obtain ⟨t, ⟨ht, _⟩, _⟩ := compact_normalized_power_extension
    l m N hm hmeven hN hNeven hmN E Y J hJ a b hab A'
  have hnat := open_unary_constant_naturality k l ι m N hm hmeven hN hNeven hmN
    D E X Y C a b hab A A'
  obtain ⟨s, ⟨hs, _⟩, _⟩ := compact_power_extension_descent
    k l ι (level N) hL heven D E X Y C H J e he (weight N)
    (pullToOpen k (level N) (weight N) A.section_) ⟨t, ht.trans hnat.symm⟩
  exact ⟨s, hs⟩
/-- A regular compact extension has an integral coefficient in its canonical
frame over the original field. Its open frame makes that coefficient nonzero. -/
lemma integral_of_extension (k : Type) [Field k] [CharZero k]
    (m N : ℕ) {D : LevelData k (level N)} {X : Compactification k (level N) D}
    (H : Extension k (level N) D X) (hH : Canonical k (level N) H)
    {a b : Fin N} (A : OpenPower k m N D a b)
    (hframe : IsFrame (power D.atlas.descent.family (weight N)) ⊤ A.section_)
    (s : Γ(tensorPower X.space H.line (weight N), ⊤))
    (hs : restrictPower k (level N) H (weight N) s =
      pullToOpen k (level N) (weight N) A.section_)
    (V : DiskTest k (level N) D X) : IntegralAtTest k m N A V.toTest := by
  let L := level N
  let n := weight N
  obtain ⟨η, hη, _⟩ := hH V
  have hfr := tensorPower_frame _ η hη.1 n ⊤ le_rfl
  rw [InitialHodgeSection.res_self] at hfr
  obtain ⟨c, hc⟩ := hfr.2 (diskPower k L H V n s)
  let f : PowerSeries k := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom c
  have hfc : scalar (PowerSeries k) f = c :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom_inv_id c
  have hdisk : diskPower k L H V n s = scalar (PowerSeries k) f •
      tensorPowerSection (Disk k) ((Scheme.Modules.pullback V.disk).obj H.line) n ⊤ η := by
    rw [hfc]
    exact hc.symm
  have hg := congrArg (transportSection (genericInclusion k) _ _
    (tensorComparison (genericInclusion k) _ _ (diskGenericIso k L H V) n)) hdisk
  rw [diskPower_generic, hs, pullToOpen_test, transportSection_smul,
    transportSection_tensor] at hg
  have hgen : transportSection (genericInclusion k) _ _ (diskGenericIso k L H V) η =
      hodgeGenerator k L V.differential := hη.2
  rw [hgen] at hg
  have hscalar : (genericInclusion k).appLE ⊤ ⊤ (by simp)
      (scalar (PowerSeries k) f) =
      scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) f) := by
    change (genericInclusion k).app ⊤ (scalar (PowerSeries k) f) = _
    exact ArithmeticThetaHodgeInitialR0163.IntegralDiscriminantHodgeR0163.scalar_restriction k _
  rw [hscalar] at hg
  refine ⟨f, ?_, hg⟩
  intro hf
  have hzero : pullAmbientPower k L V.toTest n A.section_ = 0 := by
    simpa only [hf, map_zero, scalar, zero_smul] using hg
  have hpf : IsFrame _ ⊤ (pullAmbientPower k L V.toTest n A.section_) := by
    rw [OpenDiscriminantFullTateExpansionR0182.pullAmbientPower_eq_pullSection]
    exact GlobalFamilyDiscriminantR0180.pullSection_frame _ n A.section_ hframe
  have hinj := (hpf ⊤ le_rfl).1
  rw [InitialHodgeSection.res_self, hzero] at hinj
  have heq : (0 : Γ(Puncture k, ⊤)) = 1 := hinj (by simp only [smul_zero])
  have hbad := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom heq
  exact zero_ne_one (by simpa only [map_zero, map_one] using hbad)

end FieldCompactUnary

theorem field_compact_unary :
    ∀ (k : Type) [Field k] [CharZero k] (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  intro k _ _ m N hm hmeven hN hNeven hmN D X H hH hgH ν hν
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
  obtain ⟨s, hs⟩ := FieldCompactUnary.extension_exists
    k m N hm hmeven hN hNeven hmN D X H hgH a b hab A
  have hdisks : ∀ V : DiskTest k (level N) D X,
      ∃ f : PowerSeries k, f ≠ 0 ∧ DiskCoefficient k N H V s f := by
    intro V
    obtain ⟨f, hf0, hf⟩ := FieldCompactUnary.integral_of_extension k m N H hH A hframe s hs V
    exact ⟨f, hf0, fun η hη =>
      CompactNormalizedPowerExtensionR0183.disk_coefficient_of_restrict
        k (level N) H (weight N) A.section_ s hs V f hf η hη⟩
  refine ⟨a, b, rfl, rfl, A, s, ⟨hs, hframe, hdisks, ?_⟩, ?_⟩
  · intro V ζ hζ hmark
    obtain ⟨f, _, hf⟩ := FieldCompactUnary.integral_of_extension k m N H hH A hframe s hs V
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


theorem field_unary_compact_naturality :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l (ArithmeticThetaCompactUnaryR0183.level N) E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k (ArithmeticThetaCompactUnaryR0183.level N) ι D E X Y) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l (ArithmeticThetaCompactUnaryR0183.level N) E Y), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ArithmeticThetaBoundaryHodgeR0182.Canonical l (ArithmeticThetaCompactUnaryR0183.level N) J → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical J → ∀ (a b : Fin N), (a.val ≠ 0 ∨ b.val ≠ 0) → ∀ (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (A' : ArithmeticThetaCompactUnaryR0183.OpenPower l m N E a b) (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤)) (t : (ArithmeticThetaTensorPower.tensorPower Y.space J.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaBoundaryHodgeR0182.restrictPower k (ArithmeticThetaCompactUnaryR0183.level N) H (ArithmeticThetaCompactUnaryR0183.weight N) s = ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ → ArithmeticThetaBoundaryHodgeR0182.restrictPower l (ArithmeticThetaCompactUnaryR0183.level N) J (ArithmeticThetaCompactUnaryR0183.weight N) t = ArithmeticThetaBoundaryHodgeR0182.pullToOpen l (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A'.section_ → ∃ eH : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback C.compactMap).obj H.line) (J.line), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J eH ∧ ArithmeticThetaArithmeticSectionsR0236.powerTransport C.compactMap H.line J.line eH (ArithmeticThetaCompactUnaryR0183.weight N) (s) = t := by
  intro k l _ _ _ _ ι m N hm hmeven hN hNeven hmN D E X Y C H J hH hgH hJ hgJ
    a b hab A A' s t hs ht
  have hL : 3 ≤ level N := by
    have := Nat.one_le_pow 2 N hN
    dsimp [level]
    omega
  have heven : Even (level N) := ⟨12*N^2, by dsimp [level]; omega⟩
  obtain ⟨e, he, _⟩ := geometric_compact_hodge_comparison
    k l ι (level N) hL heven D E X Y C H J hH hgH hJ hgJ
  refine ⟨e, he, ?_⟩
  apply CompactPowerExtensionDescent.upstairs_extension_unique C H J e he (weight N)
    (pullToOpen k (level N) (weight N) A.section_) s hs t
  exact ht.trans (open_unary_constant_naturality
    k l ι m N hm hmeven hN hNeven hmN D E X Y C a b hab A A').symm

#print axioms field_compact_unary
#print axioms field_unary_compact_naturality
end ArithmeticThetaArithmeticSectionsR0236
