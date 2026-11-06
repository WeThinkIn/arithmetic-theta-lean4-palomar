import CompactAlphaHalfDivisorR0192
import DiscriminantTwistUnitR0185
import CuspHalfDivisorLineR0185

/-! The canonical bounded-pole half line of the specified compact alpha. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

namespace ArithmeticThetaSquareLinesR0192.CompactAlphaCanonicalHalfLine
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaPullback ArithmeticThetaTensorPower
open ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaGeometricPrerequisites
open ArithmeticThetaDegreeAssembly

variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D)
    (H : Extension k L D X) (x : X.space)

lemma canonical_square (hL : 3 ≤ L) (heven : Even L)
    (a : Γ(H.line, ⊤)) (E : Component k L D X x →₀ ℤ)
    (hE : HalfAlphaDivisor k L D X H x a E)
    (hN : NormalAffine (Component k L D X x)) :
    Scheme.Modules.IsInvertible (canonicalDivisorData k L D X x E hE.1 hN).line ∧
    ∃ β : tensorPower (Component k L D X x)
        (canonicalDivisorData k L D X x E hE.1 hN).line 2 ≅ hodge k L D X x H,
      β.hom.app ⊤ (tensorPowerSection (Component k L D X x)
        (canonicalDivisorData k L D X x E hE.1 hN).line 2 ⊤
        (canonicalDivisorData k L D X x E hE.1 hN).section_) =
          componentAlpha k L D X H x a := by
  let Y := Component k L D X x
  have hg := component_curve_frames k L hL heven D X x
  have hco : ∀ y, E y ≠ 0 → Order.coheight y = 1 := by
    intro y hy
    apply CuspHalfDivisorLineR0185.cusp_coheight k L D X x hL heven y
    by_contra hn
    exact hy (hE.2.2.1 y hn)
  have hline := ArithmeticThetaCoverComparison.signed_divisor_line Y hg.2.2.1 hN E hco
  have hi := CuspHalfDivisorLineR0185.invertible_of_lineBundle Y _ hline
  obtain ⟨C⟩ := ComponentCurveFramesR0184.normalFrameCover_of_invertible Y hN _ hi
  have horders := DiscriminantTwistUnitR0185.canonical_divisor_orders Y hg.2.2.1 hN E hE.1 hco Y C
  have hs := divisorCanonicalSection_ne_zero Y hN E hE.1
  obtain ⟨hsq, hsqorder⟩ := tensor_power_divisor Y _ hline Y C 2 _ E hs horders
  obtain ⟨ι, ⟨B⟩⟩ := hE.2.2.2.2.1
  obtain ⟨β, hβ, _⟩ := equal_divisor_rigidified_isomorphism Y hg.2.2.1 hN _ _
    (tensorPower_isLineBundle Y _ C 2)
    (isLineBundle_of_normalFrameCover Y _ B) Y ι (powerCover Y _ C 2) B _ _
    (2 • E) hsq hE.2.2.2.1 hsqorder (hE.2.2.2.2.2 ι B)
  exact ⟨hi, β, hβ⟩

open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open OpenDiscriminantFullTateExpansionR0182
open CompactHodgeLatticeExtensionR0182

lemma disk_component_alpha (a : Γ(H.line, ⊤))
    (V : DiskTest k L D X) (f : Disk k ⟶ Component k L D X x)
    (hf : f ≫ inclusion k L D X x = V.disk) :
    (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      (pullbackGlobalSection f (hodge k L D X x H) (componentAlpha k L D X H x a)) =
        pullbackGlobalSection V.disk H.line a := by
  have hc : composeComparison (inclusion k L D X x) f V.disk hf.symm H.line
      (hodge k L D X x H) ((Scheme.Modules.pullback V.disk).obj H.line)
      (Iso.refl _) (diskHodgeIso k L D X x H V f hf) = Iso.refl _ := by
    apply Iso.ext
    simp [composeComparison, diskHodgeIso, pullbackEqIso, Scheme.Modules.pullbackCongr]
  have ht := CompactDiscriminantSectionR0182.transportSection_comp_eq
    (inclusion k L D X x) f V.disk hf.symm H.line
    (hodge k L D X x H) ((Scheme.Modules.pullback V.disk).obj H.line)
    (Iso.refl _) (diskHodgeIso k L D X x H V f hf) a
  rw [hc] at ht
  simpa only [transportSection, componentAlpha, Scheme.Modules.Hom.id_app,
    Iso.refl_hom, ConcreteCategory.id_apply, InitialHodgeSection.res_self,
    pullbackGlobalSection, Scheme.Modules.pullbackLocalSection, Scheme.Hom.preimage_top] using ht.symm

/-- On the original complete disk a line with a framed square is itself framed. -/
lemma disk_frame_of_square (M : (Disk k).Modules)
    (hM : Scheme.Modules.IsInvertible M) (s : Γ(M, ⊤))
    (hs : IsFrame (tensorPower (Disk k) M 2) ⊤
      (tensorPowerSection (Disk k) M 2 ⊤ s)) : IsFrame M ⊤ s := by
  obtain ⟨U, b, hy, hb⟩ := local_frame_exists hM (closedPoint k)
  have hU : U = ⊤ := by
    simpa using Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Disk k)) hy
  subst U
  obtain ⟨c, hc⟩ := (hb ⊤ le_rfl).2 s
  rw [InitialHodgeSection.res_self] at hc
  change c • b = s at hc
  have hu : IsUnit (c^2) := frame_coefficient_unit
    (tensorPowerSection (Disk k) M 2 ⊤ b) (tensorPower_frame M b hb 2) (c^2) (by
      rw [← InitialHodgeSection.tensor_smul, hc]
      exact hs)
  have hcu : IsUnit c := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu
  obtain ⟨u, hu⟩ := hcu
  rw [← hc, ← hu]
  exact InitialHodgeSection.unit_frame M b hb u

lemma normalized_branch (a : Γ(H.line, ⊤)) (ha : IsCompactAlpha k L D X H a)
    (A : DivisorLine (Component k L D X x)) (hA : Scheme.Modules.IsInvertible A.line)
    (β : tensorPower (Component k L D X x) A.line 2 ≅ hodge k L D X x H)
    (hβ : β.hom.app ⊤ (tensorPowerSection (Component k L D X x) A.line 2 ⊤ A.section_) =
      componentAlpha k L D X H x a) : AlphaHalfBranch k L D X H x A β := by
  intro V ζ hζ hmark f hf η hη
  let M := (Scheme.Modules.pullback f).obj A.line
  let s : Γ(M, ⊤) := pullbackGlobalSection f A.line A.section_
  let e : tensorPower (Disk k) M 2 ≅ (Scheme.Modules.pullback V.disk).obj H.line :=
    (pullback_tensorPower_iso _ _ f A.line 2).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ diskHodgeIso k L D X x H V f hf
  have he : e.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤ s) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L ^ 2) • η := by
    have ht : (pullback_tensorPower_iso _ _ f A.line 2).hom.app ⊤
        (pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_)) =
        tensorPowerSection (Disk k) M 2 ⊤ s := by
      simpa only [Scheme.Hom.preimage_top] using
        pullback_tensorPower_section (Disk k) (Component k L D X x) f A.line 2 A.section_
    have ht' : (pullback_tensorPower_iso _ _ f A.line 2).inv.app ⊤
        (tensorPowerSection (Disk k) M 2 ⊤ s) =
        pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_) := by
      rw [← ht]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => q.app ⊤) (pullback_tensorPower_iso _ _ f A.line 2).hom_inv_id) _
    change (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      (((Scheme.Modules.pullback f).map β.hom).app ⊤
        ((pullback_tensorPower_iso _ _ f A.line 2).inv.app ⊤
          (tensorPowerSection (Disk k) M 2 ⊤ s))) = _
    rw [ht']
    have hmap := Scheme.Modules.pullbackLocalSection_app f β.hom
      (tensorPowerSection _ A.line 2 ⊤ A.section_)
    have hmap' : pullbackGlobalSection f _ (β.hom.app ⊤
        (tensorPowerSection _ A.line 2 ⊤ A.section_)) =
        ((Scheme.Modules.pullback f).map β.hom).app ⊤
          (pullbackGlobalSection f _ (tensorPowerSection _ A.line 2 ⊤ A.section_)) := by
      simpa only [pullbackGlobalSection, Scheme.Modules.pullbackLocalSection,
        Scheme.Hom.preimage_top] using hmap
    rw [← hmap', hβ, disk_component_alpha k L D X H x a V f hf]
    exact ha.2.2 V ζ hζ hmark η hη
  obtain ⟨v, hv⟩ := FourTorsionTateBehavior.thetaAt_unit k L
  let u : Γ(Disk k, ⊤)ˣ :=
    v.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom.toMonoidHom
  have hu : (u : Γ(Disk k, ⊤)) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L) := by
    change (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (v : PowerSeries k) = _
    rw [hv]
    rfl
  have hu2 : ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) (thetaAt k L ^ 2) =
      (u : Γ(Disk k, ⊤)) ^ 2 := by
    rw [hu]
    exact map_pow (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom _ _
  rw [hu2] at he
  have hs : IsFrame M ⊤ s := by
    apply disk_frame_of_square k M (hA.pullback f) s
    apply (ComponentDiscriminantDivisorR0184.frame_iso_iff e _).mp
    rw [he]
    exact InitialHodgeSection.unit_frame _ η hη.1 (u^2)
  refine ⟨(↑(u⁻¹) : Γ(Disk k, ⊤)) • s,
    InitialHodgeSection.unit_frame M s hs u⁻¹, ?_, ?_⟩
  · rw [← hu, smul_smul, Units.mul_inv, one_smul]
  · change e.hom.app ⊤ (tensorPowerSection (Disk k) M 2 ⊤
      ((↑(u⁻¹) : Γ(Disk k, ⊤)) • s)) = η
    rw [InitialHodgeSection.tensor_smul, Scheme.Modules.Hom.app_smul, he, smul_smul]
    have huinv : (↑(u⁻¹) : Γ(Disk k, ⊤)) ^ 2 * (u : Γ(Disk k, ⊤)) ^ 2 = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [huinv, one_smul]

end ArithmeticThetaSquareLinesR0192.CompactAlphaCanonicalHalfLine

namespace ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaComponentDegreeR0184

/-- The specific O(E), its canonical section and its full normalized theta branch,
for every component and every positive level divisible by eight. -/
theorem compact_alpha_canonical_half_line :
        ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 8 ∣ L → ∀ (D :
    ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X :
    ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H :
    ArithmeticThetaBoundaryHodgeR0182.Extension k L D X),
    ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (a : (H.line).presheaf.obj (Opposite.op
    ⊤)), ArithmeticThetaSquareLinesR0192.IsCompactAlpha k L D X H a → ∀ x : X.space, ∃ (E :
    (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ) (hE : ∀ y, 0 ≤ E y) (hN :
    ArithmeticThetaNormalizedSections.NormalAffine (ArithmeticThetaComponentDegreeR0184.Component k
    L D X x)), ArithmeticThetaSquareLinesR0192.HalfAlphaDivisor k L D X H x a E ∧
    AlgebraicGeometry.Scheme.Modules.IsInvertible
    (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line ∧ ∃ β :
    CategoryTheory.Iso (ArithmeticThetaTensorPower.tensorPower
    (ArithmeticThetaComponentDegreeR0184.Component k L D X x)
    (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2)
    (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H), β.hom.app ⊤
    (ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaComponentDegreeR0184.Component k
    L D X x) (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).line 2 ⊤
    (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN).section_) =
    ArithmeticThetaSquareLinesR0192.componentAlpha k L D X H x a ∧
    ArithmeticThetaSquareLinesR0192.AlphaHalfBranch k L D X H x
    (ArithmeticThetaSquareLinesR0192.canonicalDivisorData k L D X x E hE hN) β := by
  intro k _ _ _ L hpos h8 D X H hH a ha x
  have h3 : 3 ≤ L := le_trans (by norm_num) (Nat.le_of_dvd hpos h8)
  have heven : Even L := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8)
  obtain ⟨E, hE⟩ := compact_alpha_half_divisor k L hpos h8 D X H hH a ha x
  have hN := (component_curve_frames k L h3 heven D X x).2.2.2.1
  obtain ⟨hi, β, hβ⟩ := CompactAlphaCanonicalHalfLine.canonical_square k L D X H x
    h3 heven a E hE hN
  exact ⟨E, hE.1, hN, hE, hi, β, hβ,
    CompactAlphaCanonicalHalfLine.normalized_branch k L D X H x a ha _ hi β hβ⟩

#print axioms compact_alpha_canonical_half_line
end ArithmeticThetaSquareLinesR0192
