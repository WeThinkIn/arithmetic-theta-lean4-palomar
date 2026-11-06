module

public import SharpCoverRatiosDefinitionsR0194
public import DiskFrameComparisonAdapterR0192
public import OpenIsogenyAlphaR0193
public import SimultaneousUnaryCommonCoverR0187
public import IsogenyCanonicalHalfLineR0193
public import CompactIsogenyAlphaR0193

@[expose] public section

/-! Simultaneous arithmetic half-lines and their actual transported basic sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaSharpCoverR0194
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCommonHalfHodgeR0185 ArithmeticThetaSquareLinesR0192
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaNormalizedSections ArithmeticThetaLineRoot ArithmeticThetaSectionOrder
open ArithmeticThetaIsogenyHalfLinesR0193 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open CommonHalfHodgeCoverR0185 DiscriminantTateRootR0185

namespace CommonBasicUnaryCover

lemma squarePull_section {Y Z : Scheme.{0}} {W : Z.Modules} (p : Y ⟶ Z)
    (A : SquareLine Z W) (v : Γ(A.line, ⊤)) :
    (squarePull p A).hom.app ⊤ (tensorPowerSection Y _ 2 ⊤
      (pullbackGlobalSection p A.line v)) =
      pullbackGlobalSection p W (A.square.hom.app ⊤ (tensorPowerSection Z _ 2 ⊤ v)) := by
  have ht : (pullback_tensorPower_iso _ _ p A.line 2).hom.app ⊤
      (pullbackGlobalSection p _ (tensorPowerSection Z _ 2 ⊤ v)) =
      tensorPowerSection Y _ 2 ⊤ (pullbackGlobalSection p A.line v) := by
    simpa only [Scheme.Hom.preimage_top] using
      pullback_tensorPower_section Y Z p A.line 2 v
  change ((Scheme.Modules.pullback p).map A.square.hom).app ⊤
    ((pullback_tensorPower_iso _ _ p A.line 2).inv.app ⊤ _) = _
  rw [← ht, iso_inv_hom_apply, pullback_global_app]

lemma along_transport {Z Y S : Scheme.{0}} {W : Z.Modules} (p : Y ⟶ Z)
    (A B : SquareLine Z W)
    (e : (Scheme.Modules.pullback p).obj A.line ≅ (Scheme.Modules.pullback p).obj B.line)
    (f : S ⟶ Z) (g : S ⟶ Y) (hg : g ≫ p = f) (v : Γ(A.line, ⊤)) :
    (along g p f hg B.line).hom.app ⊤
      (pullbackGlobalSection g _ (e.hom.app ⊤ (pullbackGlobalSection p A.line v))) =
    (transportIsometry p A B e f g hg).hom.app ⊤ (pullbackGlobalSection f A.line v) := by
  have ha := along_global p g f hg A.line v
  rw [transport_as_app] at ha
  change _ = (along g p f hg B.line).hom.app ⊤
    (((Scheme.Modules.pullback g).map e.hom).app ⊤
      ((along g p f hg A.line).inv.app ⊤ (pullbackGlobalSection f A.line v)))
  rw [← ha, iso_inv_hom_apply, pullback_global_app]

lemma squareOnDisk_section (k : Type) [Field k] {B X : Scheme.{0}}
    (p : B ⟶ X) (J : B.Modules) (H : X.Modules)
    (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H)
    (g : Disk k ⟶ B) (d : Disk k ⟶ X) (hg : g ≫ p = d) (v : Γ(J, ⊤)) :
    (squareOnDisk k p J H β g d hg).hom.app ⊤
      (tensorPowerSection _ _ 2 ⊤ (pullbackGlobalSection g J v)) =
      (along g p d hg H).hom.app ⊤
        (pullbackGlobalSection g _ (β.hom.app ⊤ (tensorPowerSection B J 2 ⊤ v))) := by
  have ht : (pullback_tensorPower_iso _ _ g J 2).hom.app ⊤
      (pullbackGlobalSection g _ (tensorPowerSection B J 2 ⊤ v)) =
      tensorPowerSection _ _ 2 ⊤ (pullbackGlobalSection g J v) := by
    simpa only [Scheme.Hom.preimage_top] using
      pullback_tensorPower_section (Disk k) B g J 2 v
  change (along g p d hg H).hom.app ⊤
    (((Scheme.Modules.pullback g).map β.hom).app ⊤
      ((pullback_tensorPower_iso _ _ g J 2).inv.app ⊤ _)) = _
  rw [← ht, iso_inv_hom_apply, pullback_global_app]

lemma canonical_square_pull (k : Type) [Field k] [CharZero k] (L m : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)
    (x : X.space) (A : CanonicalHalf k L m D X H x) {Y : Scheme.{0}}
    (p : Y ⟶ Component k L D X x) :
    (squarePull p A.squareLine ≪≫
      (Scheme.Modules.pullbackComp p (inclusion k L D X x)).app H.line).hom.app ⊤
      (tensorPowerSection Y ((Scheme.Modules.pullback p).obj A.data.line) 2 ⊤
        (pullbackGlobalSection p A.data.line A.data.section_)) =
      pullbackGlobalSection (p ≫ inclusion k L D X x) H.line A.alpha := by
  have hs := squarePull_section p A.squareLine A.data.section_
  change (squarePull p A.squareLine).hom.app ⊤
    (tensorPowerSection Y ((Scheme.Modules.pullback p).obj A.data.line) 2 ⊤
      (pullbackGlobalSection p A.data.line A.data.section_)) =
    pullbackGlobalSection p _ (A.square.hom.app ⊤
      (tensorPowerSection _ A.data.line 2 ⊤ A.data.section_)) at hs
  have has : A.square.hom.app ⊤ (tensorPowerSection _ A.data.line 2 ⊤ A.data.section_) =
      componentAlpha k L D X H x A.alpha := A.square_section
  rw [has] at hs
  exact (congrArg
    (((Scheme.Modules.pullbackComp p (inclusion k L D X x)).app H.line).hom.app ⊤)
    hs).trans (by
      simpa [transport_as_app, along, componentAlpha, hodge, Scheme.Modules.pullbackCongr] using
        along_global (inclusion k L D X x) p (p ≫ inclusion k L D X x)
          rfl H.line A.alpha)

end CommonBasicUnaryCover


open CommonBasicUnaryCover

/-- Assemble the canonical isogeny half-lines on one finite etale square cover. -/
theorem common_basic_unary_cover :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L s : ℕ), 0 < L →
    ∀ m : Fin (s+1) → ℕ, (∀ i, 0 < m i ∧ Even (m i) ∧ 8*m i ∣ L) →
    ∀ (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X),
    Canonical k L H → ∀ (V : DiskTest k L D X) (ζ : k), IsPrimitiveRoot ζ L →
    CanonicalMarking k L ζ V.level → CommonBasic k L s m D X H V := by
  intro k _ _ _ L s hL m hm D X H hH V ζ hζ hmark
  classical
  let x := V.disk (closedPoint k)
  have hA : ∀ i, Nonempty (CanonicalHalf k L (m i) D X H x) := by
    intro i
    obtain ⟨O, _⟩ := open_isogeny_alpha k L (m i) hL (hm i).1 (hm i).2.1 (hm i).2.2 D
    obtain ⟨a, ha, _⟩ := compact_isogeny_alpha k L (m i) hL (hm i).1
      (hm i).2.1 (hm i).2.2 D X H hH O
    obtain ⟨E, hE, hN, hd, hi, β, hβ, hb⟩ := isogeny_canonical_half_line k L (m i)
      hL (hm i).1 (hm i).2.1 (hm i).2.2 D X H hH O a ha x
    exact ⟨⟨O, a, ha, E, hE, hN, hd, hi, β, hβ, hb⟩⟩
  let A : ∀ i, CanonicalHalf k L (m i) D X H x := fun i => Classical.choice (hA i)
  have hlev := IsogenyAlphaAllCuspOrders.level_bounds L (m 0) hL (hm 0).1 (hm 0).2.2
  have hc := component_curve_frames k L hlev.1 hlev.2.1 D X x
  letI := hc.1
  letI := hc.2.1
  obtain ⟨f, hf⟩ := component_disk_factor k L D X V
  have hfb : f ≫ projection k L D X x = diskStructure k := by
    change (f ≫ inclusion k L D X x) ≫ X.projection = _
    rw [hf]
    exact V.extends_eq.1
  have hfd := SimultaneousUnaryCommonCoverR0187.disk_dominant k L D X V
    (projection k L D X x) (inclusion k L D X x) f hf
  obtain ⟨η, hη, _⟩ := hH V
  have hbranch := fun i => (A i).branch V ζ hζ hmark f hf η hη
  choose hi hif his hisq using hbranch
  let ηc := (diskHodgeIso k L D X x H V f hf).inv.app ⊤ η
  have hframes : DiskFrames k f s (fun i => (A i).squareLine) ηc hi := by
    refine ⟨frame_iso (diskHodgeIso k L D X x H V f hf).symm η hη.1, ?_⟩
    intro i
    refine ⟨hif i, ?_⟩
    have he := congrArg ((diskHodgeIso k L D X x H V f hf).inv.app ⊤) (hisq i)
    simpa only [iso_inv_hom_apply, squarePull, CanonicalHalf.squareLine, CanonicalHalf.data, ηc] using he
  obtain ⟨C, het, g, hg, hgd, e, he0, he⟩ := disk_frame_comparison_adapter
    k (Component k L D X x) (projection k L D X x) (hodge k L D X x H)
    s (fun i => (A i).squareLine) f hfb hfd ηc hi hframes
  letI := C.finite
  letI := C.flat
  letI := het
  have hzero : s = 0 → IsIso C.map := by
    intro hs
    apply (Scheme.Hom.isIso_iff_finrank_eq C.map).mpr
    funext y
    have hy := C.degree y
    simp only [hs, pow_zero] at hy
    exact Nat.le_antisymm hy.2 hy.1
  have hgp : g ≫ (C.map ≫ inclusion k L D X x) = V.disk := by
    rw [← Category.assoc, hg, hf]
  let h := (along g C.map f hg (A 0).data.line).inv.app ⊤ (hi 0)
  have hh : IsFrame _ ⊤ h :=
    frame_iso (along g C.map f hg (A 0).data.line).symm (hi 0) (hif 0)
  let t := fun i => (e i).hom.app ⊤
    (pullbackGlobalSection C.map (A i).data.line (A i).data.section_)
  have htexp : ∀ i, pullbackGlobalSection g _ (t i) =
      ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
        (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m i)) • h := by
    intro i
    have heq := along_transport C.map (A i).squareLine (A 0).squareLine
      (e i) f g hg (A i).data.section_
    erw [his i, Scheme.Modules.Hom.app_smul, (he i).2] at heq
    have heq' := congrArg ((along g C.map f hg (A 0).data.line).inv.app ⊤) heq
    simpa only [iso_inv_hom_apply, Scheme.Modules.Hom.app_smul, Scheme.Hom.preimage_top, t, h, CanonicalHalf.squareLine, CanonicalHalf.data] using heq'
  have hun : ∀ i, IsUnit (ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
      (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m i))) := by
    intro i
    obtain ⟨u, hu⟩ := ArithmeticThetaGlobalFourTorsionR0190.FourTorsionTateBehavior.thetaAt_unit k (L*m i)
    rw [← hu]
    exact u.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom
  have htne : ∀ i, t i ≠ 0 := by
    letI : Nonempty (⊤ : (Disk k).Opens) := ⟨⟨closedPoint k, trivial⟩⟩
    intro i ht0
    have hz := htexp i
    rw [ht0] at hz
    have hz' : pullbackGlobalSection g _ (0 : Γ((Scheme.Modules.pullback C.map).obj (A 0).data.line, ⊤)) = 0 :=
      map_zero _
    erw [hz'] at hz
    obtain ⟨u, hu⟩ := hun i
    have hfr := InitialHodgeSection.unit_frame _ h hh u
    rw [hu] at hfr
    exact ComponentDiscriminantDivisorR0184.frame_ne_zero _ hfr hz.symm
  refine ⟨A, C, het, hzero, g, hgp, hgd, e, he0, fun i => (he i).1,
    h, η, t, hh, hη, ?_, fun i => ⟨rfl, htne i, htexp i⟩⟩
  let β := squarePull C.map (A 0).squareLine ≪≫
    (Scheme.Modules.pullbackComp C.map (inclusion k L D X x)).app H.line
  have ht0 : t 0 = pullbackGlobalSection C.map (A 0).data.line (A 0).data.section_ := by
    dsimp only [t]
    rw [he0]
    rfl
  have hβ : β.hom.app ⊤ (tensorPowerSection C.space _ 2 ⊤ (t 0)) =
      pullbackGlobalSection (C.map ≫ inclusion k L D X x) H.line (A 0).alpha := by
    rw [ht0]
    exact canonical_square_pull k L (m 0) D X H x (A 0) C.map
  have hsq := squareOnDisk_section k (C.map ≫ inclusion k L D X x)
    _ H.line β g V.disk hgp (t 0)
  rw [hβ] at hsq
  have hglobal := along_global (C.map ≫ inclusion k L D X x) g V.disk hgp H.line (A 0).alpha
  rw [transport_as_app] at hglobal
  rw [hglobal, (A 0).realizes.2.2 V ζ hζ hmark η hη, htexp 0,
    InitialHodgeSection.tensor_smul, Scheme.Modules.Hom.app_smul] at hsq
  have hpow : ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
      (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m 0) ^ 2) =
      (ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k)
      (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k (L*m 0))) ^ 2 :=
    map_pow (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv.hom _ _
  rw [hpow] at hsq
  exact (hun 0 |>.pow 2).smul_left_cancel.mp hsq

#print axioms common_basic_unary_cover
end ArithmeticThetaSharpCoverR0194
