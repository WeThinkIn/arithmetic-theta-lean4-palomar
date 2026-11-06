import DiskFrameComparisonAdapterR0192

/-! Prescribed disk-frame comparison over arbitrary characteristic-zero fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticCommonCoverR0238
open ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLineRoot
open ArithmeticThetaNormalizedSections ArithmeticThetaCoverComparison
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTwistUnitR0185
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

open ArithmeticThetaSquareLinesR0192.DiskFrameComparisonAdapterR0192

/-- The accepted simultaneous cover, expressed in the full disk-frame interface. -/
theorem field_disk_frame_comparison
    (k : Type) [Field k] [CharZero k]
    (Z : Scheme.{0}) [IsIntegral Z]
    (b : Z ⟶ Spec (CommRingCat.of k)) [IsProper b] [SmoothOfRelativeDimension 1 b]
    (W : Z.Modules) (s : ℕ) (A : Fin (s+1) → SquareLine Z W)
    (f : Disk k ⟶ Z) (_hf : f ≫ b = diskStructure k)
    (hd : IsDominant (genericInclusion k ≫ f))
    (η : Γ((Scheme.Modules.pullback f).obj W, ⊤))
    (h : ∀ i, Γ((Scheme.Modules.pullback f).obj (A i).line, ⊤))
    (frames : DiskFrames k f s A η h) : CommonComparison k Z b W s A f h := by
  classical
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian b
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace b
  letI : IsNoetherian Z := {}
  have hn : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z) := by
    letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
      IsIntegrallyClosed.of_equiv
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    intro z
    exact (Smooth.isDomain_and_isIntegrallyClosed_stalk b z).2
  have h2 : IsUnit (2 : Γ(Z, ⊤)) := by
    let a : k →+* Γ(Z, ⊤) := b.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have hu : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using hu.map a
  let w : ∀ i : Fin s, SquareIsos (A 0).square (A i.succ).square f := fun i =>
    ⟨frameComparison (h 0) (h i.succ) (frames.2 0).1 (frames.2 i.succ).1,
      framed_square f (A 0) (A i.succ) (h 0) (h i.succ)
        (frames.2 0).1 (frames.2 i.succ).1
        ((frames.2 0).2.trans (frames.2 i.succ).2.symm)⟩
  obtain ⟨Y, p, hi, hfin, het, hsur, hdeg, e, g, hbranch⟩ :=
    simultaneous_square_line_comparison Z hn h2 s (A 0).line W
      (fun i => (A i.succ).line) (line_of_invertible _ (A 0).invertible)
      (target_line (A 0)) (fun i => line_of_invertible _ (A i.succ).invertible)
      (A 0).square (fun i => (A i.succ).square) (PowerSeries k) f w
  letI := hi
  letI := hfin
  letI := het
  letI := hsur
  let C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k Z b (2^s) :=
    { space := Y
      map := p
      integral := hi
      finite := hfin
      flat := inferInstance
      surjective := hsur
      proper := inferInstance
      smooth := smoothOfRelativeDimension_comp 0 1 p b
      degree := hdeg }
  have hdg : IsDominant (genericInclusion k ≫ g.val) := by
    letI : IsDominant ((genericInclusion k ≫ g.val) ≫ p) := by
      simpa only [Category.assoc, g.property] using hd
    exact dominant_of_comp _ p
  let E : ∀ i : Fin (s+1), (Scheme.Modules.pullback p).obj (A i).line ≅
      (Scheme.Modules.pullback p).obj (A 0).line :=
    Fin.cases (Iso.refl _) (fun i => (e i).val.symm)
  refine ⟨C, het, g.val, g.property, hdg, E, rfl, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · constructor
    · intro U v
      rfl
    · change (transportIsometry p (A 0) (A 0) (Iso.refl _) f g.val g.property).hom.app ⊤
        (h 0) = h 0
      simp [transportIsometry]
  · refine ⟨square_inverse p (A 0) (A j.succ) (e j), ?_⟩
    change (pullbackIsoOver p f (A j.succ).line (A 0).line g (e j).val.symm).hom.app ⊤
      (h j.succ) = h 0
    rw [pullback_inverse, hbranch j]
    exact frameComparison_apply (h j.succ) (h 0) (frames.2 j.succ).1 (frames.2 0).1

#print axioms field_disk_frame_comparison
end ArithmeticThetaArithmeticCommonCoverR0238
