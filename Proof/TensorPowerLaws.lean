module

public import TensorPowerDefinitions

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor

universe u

noncomputable section

namespace ArithmeticThetaTensorPower

theorem tensorPowerSection_one (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (s : (H.presheaf.obj (Opposite.op U))) :
    (ArithmeticThetaSheafTensor.tensorLeftUnitIso X H).hom.app U
      (tensorPowerSection X H 1 U s) = s := by
  simpa [tensorPowerSection, tensorPower] using
    (ArithmeticThetaSheafTensor.tensorLeftUnitIso_section X H U s)

theorem tensorPowerSection_restrict (X : Scheme.{u}) (H : X.Modules) (n : ℕ)
    (U V : X.Opens) (hVU : V ≤ U) (s : (H.presheaf.obj (Opposite.op U))) :
    (tensorPower X H n).presheaf.map (CategoryTheory.homOfLE hVU).op
        (tensorPowerSection X H n U s) =
      tensorPowerSection X H n V
        (H.presheaf.map (CategoryTheory.homOfLE hVU).op s) := by
  induction n with
  | zero =>
      change X.presheaf.map (CategoryTheory.homOfLE hVU).op (1 : Γ(X, U)) = 1
      simp
  | succ n ih =>
      change (sheafTensor X (tensorPower X H n) H).presheaf.map
          (CategoryTheory.homOfLE hVU).op
          (tensorSection X (tensorPower X H n) H U
            (tensorPowerSection X H n U s) s) =
        tensorSection X (tensorPower X H n) H V
          (tensorPowerSection X H n V (H.presheaf.map
            (CategoryTheory.homOfLE hVU).op s))
          (H.presheaf.map (CategoryTheory.homOfLE hVU).op s)
      rw [tensorSection_restrict, ih]

theorem tensorPowerSection_frame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : ArithmeticThetaLineRoot.LocalFrame X H U) (n : ℕ) (V : X.Opens)
    (hVU : V ≤ U) (a : (X.presheaf.obj (Opposite.op V))) :
    tensorPowerSection X H n V (e.equiv V hVU a) =
      (tensorPowerFrame X H U e n).equiv V hVU (a ^ n) := by
  induction n with
  | zero =>
      simp only [tensorPowerSection, tensorPower, tensorPowerFrame, unitFrame, pow_zero]
      rfl
  | succ n ih =>
      change tensorSection X (tensorPower X H n) H V
          (tensorPowerSection X H n V (e.equiv V hVU a))
          (e.equiv V hVU a) =
        (tensorFrame X (tensorPower X H n) H U
          (tensorPowerFrame X H U e n) e).equiv V hVU (a ^ (n + 1))
      rw [ih]
      rw [ArithmeticThetaSheafTensor.tensorSection_frame]
      rw [pow_succ]

theorem tensorPowerFrame_transition (X : Scheme.{u}) (H : X.Modules)
    (U U' : X.Opens) (e : ArithmeticThetaLineRoot.LocalFrame X H U)
    (e' : ArithmeticThetaLineRoot.LocalFrame X H U') (n : ℕ) (V : X.Opens)
    (hVU : V ≤ U) (hVU' : V ≤ U') :
    ArithmeticThetaLineRoot.transitionUnit
        ((tensorPowerFrame X H U e n).equiv V hVU)
        ((tensorPowerFrame X H U' e' n).equiv V hVU') =
      (ArithmeticThetaLineRoot.transitionUnit (e.equiv V hVU)
        (e'.equiv V hVU')) ^ n := by
  induction n with
  | zero =>
      apply Units.ext
      simp only [tensorPower, tensorPowerFrame, unitFrame, transitionUnit, transition, pow_zero,
        Units.val_one]
      rfl
  | succ n ih =>
      change ArithmeticThetaLineRoot.transitionUnit
          ((tensorFrame X (tensorPower X H n) H U
            (tensorPowerFrame X H U e n) e).equiv V hVU)
          ((tensorFrame X (tensorPower X H n) H U'
            (tensorPowerFrame X H U' e' n) e').equiv V hVU') =
        (ArithmeticThetaLineRoot.transitionUnit (e.equiv V hVU)
          (e'.equiv V hVU')) ^ (n + 1)
      rw [ArithmeticThetaSheafTensor.tensorFrame_transitionUnit, ih,
        pow_succ]

end ArithmeticThetaTensorPower
