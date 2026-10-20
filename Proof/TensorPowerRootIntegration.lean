module

public import TensorPowerLaws

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open ArithmeticThetaLineRoot

universe u v

noncomputable section

namespace ArithmeticThetaTensorPower

theorem exists_powerFrames_comparison :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (H : X.Modules) [AlgebraicGeometry.IsIntegral X] (ι : Type v) (C : ArithmeticThetaLineRoot.NormalFrameCover X H ι) (n : ℕ), ∃ E : ArithmeticThetaLineRoot.PowerFrames C (ArithmeticThetaTensorPower.tensorPower X H n) n, (∀ i, E.frame i = ArithmeticThetaTensorPower.tensorPowerFrame X H (C.opens i) (C.frame i) n) ∧ ∀ s : (H.presheaf.obj (Opposite.op ⊤)), ArithmeticThetaLineRoot.powerSection C (ArithmeticThetaTensorPower.tensorPower X H n) n E s = ArithmeticThetaTensorPower.tensorPowerSection X H n ⊤ s := by
  intro X H _ ι C n
  let E : PowerFrames C (tensorPower X H n) n :=
    { frame := fun i => tensorPowerFrame X H (C.opens i) (C.frame i) n
      transition_eq := by
        intro i j
        have h := tensorPowerFrame_transition X H (C.opens i) (C.opens j)
          (C.frame i) (C.frame j) n (C.opens i ⊓ C.opens j) inf_le_left inf_le_right
        exact congrArg (fun a : Γ(X, C.opens i ⊓ C.opens j)ˣ =>
            (a : Γ(X, C.opens i ⊓ C.opens j))) h }
  refine ⟨E, fun _ => rfl, ?_⟩
  intro s
  apply (existsUnique_power_section C (tensorPower X H n) n E s).unique
  · exact (existsUnique_power_section C (tensorPower X H n) n E s).choose_spec.1
  · intro i
    rw [tensorPowerSection_restrict]
    change tensorPowerSection X H n (C.opens i)
        (H.presheaf.map (homOfLE le_top).op s) =
      (tensorPowerFrame X H (C.opens i) (C.frame i) n).equiv (C.opens i) le_rfl
        (coordinate C s i ^ n)
    rw [← tensorPowerSection_frame]
    simp only [coordinate, LinearEquiv.apply_symm_apply]

theorem existsUnique_regular_tensor_root :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (H : X.Modules) [AlgebraicGeometry.IsIntegral X] (ι : Type v) (C : ArithmeticThetaLineRoot.NormalFrameCover X H ι) (T : ArithmeticThetaLineRoot.RationalFrame C) (n : ℕ) (hn : 0 < n) (r : X.functionField) (F : ((ArithmeticThetaTensorPower.tensorPower X H n).presheaf.obj (Opposite.op ⊤))), (∀ i, (r / T.coeff i) ^ n = X.germToFunctionField (C.opens i) (((ArithmeticThetaTensorPower.tensorPowerFrame X H (C.opens i) (C.frame i) n).equiv (C.opens i) le_rfl).symm ((ArithmeticThetaTensorPower.tensorPower X H n).presheaf.map (CategoryTheory.homOfLE le_top).op F))) → ∃! s : (H.presheaf.obj (Opposite.op ⊤)), (∀ i, X.germToFunctionField (C.opens i) (ArithmeticThetaLineRoot.coordinate C s i) = r / T.coeff i) ∧ ArithmeticThetaTensorPower.tensorPowerSection X H n ⊤ s = F := by
  intro X H _ ι C T n hn r F hpow
  obtain ⟨E, hframe, hcompare⟩ := exists_powerFrames_comparison X H ι C n
  have hpowE : ∀ i, (r / T.coeff i) ^ n = X.germToFunctionField (C.opens i)
      (((E.frame i).equiv (C.opens i) le_rfl).symm
        ((tensorPower X H n).presheaf.map (homOfLE le_top).op F)) := by
    intro i
    rw [hframe i]
    exact hpow i
  obtain ⟨s, hs, hF⟩ := exists_regular_root_of_section C T
    (tensorPower X H n) n hn E r F hpowE
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [← hcompare s]
    exact hF
  · intro t ht
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.presheaf, H.isSheaf⟩ C.opens ⊤
      (fun _ => homOfLE le_top) C.covers
    intro i
    apply ((C.frame i).equiv (C.opens i) le_rfl).symm.injective
    change coordinate C t i = coordinate C s i
    apply X.germToFunctionField_injective (C.opens i)
    exact (ht.1 i).trans (hs i).symm

end ArithmeticThetaTensorPower
