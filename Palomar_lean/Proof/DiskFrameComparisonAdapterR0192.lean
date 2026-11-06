module

public import SquareLineComparisonDefinitionsR0192
public import SimultaneousSquareLineComparison
public import DiscriminantTwistUnitR0185

@[expose] public section

/-! Adapt the accepted simultaneous square comparison to prescribed full disk frames. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSquareLinesR0192
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

namespace DiskFrameComparisonAdapterR0192

lemma line_of_invertible {Z : Scheme.{0}} (J : Z.Modules)
    (hJ : Scheme.Modules.IsInvertible J) : IsLineBundle Z J := by
  intro z
  obtain ⟨U, u, hz, hu⟩ := CompactHodgeLatticeExtensionR0182.local_frame_exists hJ z
  exact ⟨U, hz, ⟨localFrameIso Z J U (InitialHodgeSection.frame J u hu)⟩⟩

lemma target_line {Z : Scheme.{0}} {W : Z.Modules} (A : SquareLine Z W) :
    IsLineBundle Z W := by
  intro z
  have hi := CompactDiscriminantSectionR0182.tensorPower_invertible A.line A.invertible 2
  obtain ⟨U, u, hz, hu⟩ := CompactHodgeLatticeExtensionR0182.local_frame_exists hi z
  exact ⟨U, hz, ⟨localFrameIso Z W U
    (InitialHodgeSection.frame W (A.square.hom.app U u) (frame_iso A.square u hu))⟩⟩

def frameIso {X : Scheme.{0}} (M : X.Modules) (v : Γ(M, ⊤)) (hv : IsFrame M ⊤ v) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ M :=
  globalFrameIso X M (InitialHodgeSection.frame M v hv)

lemma frameIso_one {X : Scheme.{0}} (M : X.Modules) (v : Γ(M, ⊤)) (hv : IsFrame M ⊤ v) :
    (Scheme.Modules.Hom.app (frameIso M v hv).hom) ⊤ (1 : Γ(X, ⊤)) = v := by
  change (1 : Γ(X, ⊤)) • res M le_rfl v = v
  rw [one_smul, InitialHodgeSection.res_self]

def frameComparison {X : Scheme.{0}} {M N : X.Modules}
    (v : Γ(M, ⊤)) (w : Γ(N, ⊤)) (hv : IsFrame M ⊤ v) (hw : IsFrame N ⊤ w) : M ≅ N :=
  (frameIso M v hv).symm ≪≫ frameIso N w hw

lemma frameComparison_apply {X : Scheme.{0}} {M N : X.Modules}
    (v : Γ(M, ⊤)) (w : Γ(N, ⊤)) (hv : IsFrame M ⊤ v) (hw : IsFrame N ⊤ w) :
    (frameComparison v w hv hw).hom.app ⊤ v = w := by
  change (Scheme.Modules.Hom.app (frameIso N w hw).hom) ⊤ ((Scheme.Modules.Hom.app (frameIso M v hv).inv) ⊤ v) = w
  have hm : (Scheme.Modules.Hom.app (frameIso M v hv).inv) ⊤ v = (1 : Γ(X, ⊤)) := by
    calc
      _ = (Scheme.Modules.Hom.app (frameIso M v hv).inv) ⊤
          ((Scheme.Modules.Hom.app (frameIso M v hv).hom) ⊤ (1 : Γ(X, ⊤))) :=
        congrArg (fun z => (Scheme.Modules.Hom.app (frameIso M v hv).inv) ⊤ z)
          (frameIso_one M v hv).symm
      _ = _ := congrArg (fun a : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) =>
          Scheme.Modules.Hom.app a ⊤ (1 : Γ(X, ⊤)))
        (frameIso M v hv).hom_inv_id
  rw [hm, frameIso_one]

lemma framed_square {X Z : Scheme.{0}} {W : Z.Modules} (f : X ⟶ Z)
    (A B : SquareLine Z W)
    (v : Γ((Scheme.Modules.pullback f).obj A.line, ⊤))
    (w : Γ((Scheme.Modules.pullback f).obj B.line, ⊤))
    (hv : IsFrame _ ⊤ v) (hw : IsFrame _ ⊤ w)
    (he : (squarePull f A).hom.app ⊤ (tensorPowerSection X _ 2 ⊤ v) =
      (squarePull f B).hom.app ⊤ (tensorPowerSection X _ 2 ⊤ w)) :
    tensorPowerMap (frameComparison v w hv hw).hom 2 ≫
      (pullbackPowerIso f B.square).hom = (pullbackPowerIso f A.square).hom := by
  apply hom_ext_frames
  intro x
  refine ⟨⊤, tensorPowerSection X _ 2 ⊤ v, trivial,
    InitialHodgeSection.tensor_frame _ v hv 2, ?_⟩
  change (pullbackPowerIso f B.square).hom.app ⊤
    ((tensorPowerMap (frameComparison v w hv hw).hom 2).app ⊤
      (tensorPowerSection X _ 2 ⊤ v)) = _
  rw [tensorPowerMap_section, frameComparison_apply]
  exact he.symm

lemma square_inverse {Z Y : Scheme.{0}} {W : Z.Modules} (p : Y ⟶ Z)
    (A B : SquareLine Z W) (e : SquareIsos A.square B.square p) :
    IsSquareIsometry p B A e.val.symm := by
  rcases e with ⟨e, heq⟩
  have he : tensorPowerMap e.inv 2 ≫ (pullbackPowerIso p A.square).hom =
      (pullbackPowerIso p B.square).hom := by
    rw [← heq, ← Category.assoc, ← tensorPowerMap_comp, e.inv_hom_id,
      tensorPowerMap_id, Category.id_comp]
  intro U v
  have h := congrArg (fun a => a.app U (tensorPowerSection Y _ 2 U v)) he
  change (pullbackPowerIso p A.square).hom.app U
    ((tensorPowerMap e.inv 2).app U (tensorPowerSection Y _ 2 U v)) = _ at h
  rw [tensorPowerMap_section] at h
  exact h.symm

lemma pullback_inverse {Z Y S : Scheme.{0}} (p : Y ⟶ Z) (f : S ⟶ Z)
    (M N : Z.Modules) (g : {g : S ⟶ Y // g ≫ p = f})
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N) :
    pullbackIsoOver p f N M g e.symm = (pullbackIsoOver p f M N g e).symm := by
  apply Iso.ext
  simp [pullbackIsoOver]

lemma dominant_of_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite g] [IsDominant (f ≫ g)] :
    IsDominant f := by
  have generic {U V : Scheme.{0}} [IsIntegral U] [IsIntegral V]
      (q : U ⟶ V) [IsDominant q] : q (genericPoint U) = genericPoint V := by
    apply IsGenericPoint.eq _ (genericPoint_spec V)
    have h := (genericPoint_spec U).image q.continuous
    simpa only [Set.image_univ, q.denseRange.closure_range] using h
  letI : IsDominant g := IsDominant.of_comp f g
  have hg := generic g
  have hfg := generic (f ≫ g)
  have he : genericPoint Y = f (genericPoint X) :=
    (g.isDiscrete_preimage_singleton (genericPoint Z)).eq_of_specializes
      ((genericPoint_spec Y).specializes trivial) hg hfg
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨genericPoint X, he.symm⟩

end DiskFrameComparisonAdapterR0192

open DiskFrameComparisonAdapterR0192

/-- The accepted simultaneous cover, expressed in the full disk-frame interface. -/
theorem disk_frame_comparison_adapter
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
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

#print axioms disk_frame_comparison_adapter
end ArithmeticThetaSquareLinesR0192
