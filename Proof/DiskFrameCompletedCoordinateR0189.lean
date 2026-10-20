module

public import ConservativeKernelDefinitionsR0189

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaConservativeKernelR0189
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaSectionCompletion
open ArithmeticThetaNormalizedSections ArithmeticThetaTensorPower ArithmeticThetaLineRoot
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

namespace DiskFrameCompletedCoordinate

lemma completion_eq_stalk (k : Type) [Field k] [CharZero k]
    (Y : Scheme) (g : Disk k ⟶ Y)
    (e : completedLocalRing (Y.presheaf.stalk (g (closedPoint k))) ≃+* PowerSeries k)
    (he : CompatibleCompletion k Y g e)
    (r : Y.presheaf.stalk (g (closedPoint k))) :
    completionExpansion _ k e r = (Scheme.stalkClosedPointTo g).hom r := by
  apply (CompletedLocalParameter.diskGerm_bijective k).1
  rw [show diskGerm k (completionExpansion _ k e r) =
    (g.stalkMap (closedPoint k)).hom r from RingHom.congr_fun he r]
  rw [CompletedLocalParameter.diskGerm_eq]
  change _ = ((g.stalkMap (closedPoint k) ≫
    (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).hom) ≫
    (stalkClosedPointIso (CommRingCat.of (PowerSeries k))).inv) r
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

lemma completed_coordinate (k : Type) [Field k] [CharZero k]
    (Y : Scheme) (M : Y.Modules) (ι : Type) (C : NormalFrameCover Y M ι)
    (i : ι) (g : Disk k ⟶ Y) (hx : g (closedPoint k) ∈ C.opens i)
    (e : completedLocalRing (Y.presheaf.stalk (g (closedPoint k))) ≃+* PowerSeries k)
    (he : CompatibleCompletion k Y g e) (s : Sections Y M) :
    completedSection Y M C s i (g (closedPoint k)) hx k e =
      specScalar g (C.opens i) (Scheme.preimage_eq_top_of_closedPoint_mem g hx).ge
        (sectionCoordinate Y M (C.opens i) (C.frame i) s) := by
  rw [completedSection, completion_eq_stalk k Y g e he]
  exact ConcreteCategory.congr_hom (Scheme.germ_stalkClosedPointTo g (C.opens i) hx) _

end DiskFrameCompletedCoordinate

/-- The same unit compares every section with its prescribed disk series. -/
theorem disk_frame_completed_coordinate :
∀ (k : Type) [Field k] [CharZero k] (Y : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Y] (J : Y.Modules) (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover Y (ArithmeticThetaTensorPower.tensorPower (Y) (J) (n)) ι) (i : ι) (g : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) (Y)) (hx : g (ArithmeticThetaTateCuspsR0181.closedPoint k) ∈ C.opens i) (e : ArithmeticThetaSectionCompletion.completedLocalRing (Y.presheaf.stalk (g (ArithmeticThetaTateCuspsR0181.closedPoint k))) ≃+* PowerSeries k), ArithmeticThetaConservativeKernelR0189.CompatibleCompletion k Y g e → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (J))), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (J)) ⊤ h → ∃ a : (PowerSeries k)ˣ, ∀ (s : ArithmeticThetaSimultaneousUnaryR0187.Sections (Y) (ArithmeticThetaTensorPower.tensorPower (Y) (J) (n))) (F : PowerSeries k), ArithmeticThetaNormalizedSections.pullbackPowerSection g J n s = ArithmeticThetaOpenHodgeR0180.scalar (PowerSeries k) F • ArithmeticThetaTensorPower.tensorPowerSection (ArithmeticThetaTateCuspsR0181.Disk k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (J)) n ⊤ h → ArithmeticThetaSectionCompletion.completedSection Y (ArithmeticThetaTensorPower.tensorPower (Y) (J) (n)) C s i (g (ArithmeticThetaTateCuspsR0181.closedPoint k)) hx k e = (a : PowerSeries k) * F := by
  intro k _ _ Y _ J n ι C i g hx e he h hh
  let M := tensorPower Y J n
  let P := (Scheme.Modules.pullback g).obj M
  let N := tensorPower (Disk k) ((Scheme.Modules.pullback g).obj J) n
  let E := ArithmeticThetaPullback.pullback_tensorPower_iso (Disk k) Y g J n
  let U := C.opens i
  let η := (C.frame i).equiv U le_rfl 1
  have hη : IsFrame M U η :=
    ArithmeticThetaCommonHalfHodgeR0185.CuspHalfDivisorLineR0185.frame_generator Y M U (C.frame i)
  let hd : (⊤ : (Disk k).Opens) ≤ g ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem g hx).ge
  let b := res P hd (Scheme.Modules.pullbackLocalSection g η)
  have hb : IsFrame P ⊤ b :=
    HodgeBaseChange.frame_restrict _ _ _ (HodgeBaseChange.pullback_frame g M η hη)
  let t := E.hom.app ⊤ b
  have ht : IsFrame N ⊤ t := GlobalFamilyDiscriminantR0180.frame_iso E b hb
  let v := tensorPowerSection (Disk k) ((Scheme.Modules.pullback g).obj J) n ⊤ h
  have hv : IsFrame N ⊤ v := InitialHodgeSection.tensor_frame _ h hh n
  have ht' : Function.Bijective (fun a : Γ(Disk k, ⊤) => a • t) := by
    simpa only [InitialHodgeSection.res_self] using ht ⊤ le_rfl
  obtain ⟨a, ha⟩ := ht'.2 v
  change a • t = v at ha
  have hau : IsUnit a := frame_coefficient_unit t ht a (by rw [ha]; exact hv)
  obtain ⟨aunit, haunit⟩ := hau
  let A := (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom.hom
  refine ⟨Units.map A.toMonoidHom aunit, ?_⟩
  intro s F hs
  let q := specScalar g U hd (sectionCoordinate Y M U (C.frame i) s)
  have hp : pullbackPowerSection g J n s = scalar (PowerSeries k) q • t := by
    have hc := pullback_coordinate g M U (C.frame i) hd s
    change E.hom.app ⊤ (ArithmeticThetaPullback.pullbackGlobalSection g M s) = _
    rw [hc, Scheme.Modules.Hom.app_smul]
  have hcoeff : scalar (PowerSeries k) q = scalar (PowerSeries k) F * a := by
    apply ht'.1
    change scalar (PowerSeries k) q • t = (scalar (PowerSeries k) F * a) • t
    rw [mul_smul, ha]
    exact hp.symm.trans hs
  have hq : q = F * A a := by
    have hc := congrArg A hcoeff
    have hA : ∀ z : PowerSeries k, A (scalar (PowerSeries k) z) = z := fun z =>
      (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).commRingCatIsoToRingEquiv.apply_symm_apply z
    simpa only [map_mul, hA] using hc
  rw [DiskFrameCompletedCoordinate.completed_coordinate k Y M ι C i g hx e he s]
  change q = A (aunit : Γ(Disk k, ⊤)) * F
  rw [haunit, hq, mul_comm]

#print axioms disk_frame_completed_coordinate
end ArithmeticThetaConservativeKernelR0189
