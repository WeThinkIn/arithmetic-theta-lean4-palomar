module

public import TensorPowerLaws

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor

universe u

noncomputable section

namespace ArithmeticThetaTensorPower

/-- Ordered actual tensor products commute with restriction, including the empty product. -/
theorem tensorProductSection_restrict (X : Scheme.{u}) (H : X.Modules) (n : ℕ)
    (U V : X.Opens) (hVU : V ≤ U) (s : Fin n → H.presheaf.obj (op U)) :
    (tensorPower X H n).presheaf.map (homOfLE hVU).op
        (tensorProductSection X H n U s) =
      tensorProductSection X H n V
        (fun i => H.presheaf.map (homOfLE hVU).op (s i)) := by
  induction n with
  | zero =>
      change X.presheaf.map (homOfLE hVU).op (1 : Γ(X, U)) = 1
      simp
  | succ n ih =>
      change (sheafTensor X (tensorPower X H n) H).presheaf.map (homOfLE hVU).op
          (tensorSection X (tensorPower X H n) H U
            (tensorProductSection X H n U (fun i => s i.castSucc)) (s (Fin.last n))) =
        tensorSection X (tensorPower X H n) H V
          (tensorProductSection X H n V
            (fun i => H.presheaf.map (homOfLE hVU).op (s i.castSucc)))
          (H.presheaf.map (homOfLE hVU).op (s (Fin.last n)))
      rw [tensorSection_restrict, ih]

/-- The recursive tensor frame sends the product of coordinates to the ordered tensor. -/
theorem tensorProductSection_frame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) (n : ℕ) (V : X.Opens) (hVU : V ≤ U)
    (a : Fin n → X.presheaf.obj (op V)) :
    tensorProductSection X H n V (fun i => e.equiv V hVU (a i)) =
      (tensorPowerFrame X H U e n).equiv V hVU (∏ i, a i) := by
  induction n with
  | zero =>
      simp only [tensorProductSection, tensorPowerFrame, unitFrame, Fin.prod_univ_zero]
      rfl
  | succ n ih =>
      change tensorSection X (tensorPower X H n) H V
          (tensorProductSection X H n V (fun i => e.equiv V hVU (a i.castSucc)))
          (e.equiv V hVU (a (Fin.last n))) =
        (tensorFrame X (tensorPower X H n) H U (tensorPowerFrame X H U e n) e).equiv
          V hVU (∏ i, a i)
      rw [ih, tensorSection_frame, Fin.prod_univ_castSucc]

/-- The constant tuple gives precisely the frame-independent recursive power section. -/
theorem tensorProductSection_diagonal (X : Scheme.{u}) (H : X.Modules) (n : ℕ)
    (U : X.Opens) (s : H.presheaf.obj (op U)) :
    tensorProductSection X H n U (fun _ => s) = tensorPowerSection X H n U s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change tensorSection X (tensorPower X H n) H U
          (tensorProductSection X H n U (fun _ => s)) s =
        tensorSection X (tensorPower X H n) H U (tensorPowerSection X H n U s) s
      rw [ih]

/-- Finite linear combinations have the sum-of-products coordinate in one actual frame. -/
theorem tensorProductSection_linearCombination_frame (X : Scheme.{u}) (H : X.Modules)
    (U : X.Opens) (e : LocalFrame X H U) (n h : ℕ) (V : X.Opens) (hVU : V ≤ U)
    (a : Fin h → Fin n → X.presheaf.obj (op V)) (c : Fin h → X.presheaf.obj (op V)) :
    (∑ j, c j • tensorProductSection X H n V (fun i => e.equiv V hVU (a j i))) =
      (tensorPowerFrame X H U e n).equiv V hVU (∑ j, c j * ∏ i, a j i) := by
  simp only [tensorProductSection_frame, map_sum, ← smul_eq_mul, map_smul]

end ArithmeticThetaTensorPower
