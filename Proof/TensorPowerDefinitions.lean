module

public import LocalTensorFrame

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaSheafTensor

universe u

noncomputable section

namespace ArithmeticThetaTensorPower

/-- Iterated genuine sheaf tensor, starting with the structure sheaf.
The exponent-one identification is the accepted genuine left unit isomorphism. -/
def tensorPower (X : Scheme.{u}) (H : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => sheafTensor X (tensorPower X H n) H

/-- The unit sheaf's ordinary local frame. -/
def unitFrame (X : Scheme.{u}) (U : X.Opens) :
    LocalFrame X (SheafOfModules.unit X.ringCatSheaf) U where
  equiv V _ := LinearEquiv.refl Γ(X, V) Γ(X, V)
  naturality _ _ _ _ _ := rfl

/-- Local frames of the actual iterated tensor, constructed from the binary frame. -/
def tensorPowerFrame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens)
    (e : LocalFrame X H U) : (n : ℕ) → LocalFrame X (tensorPower X H n) U
  | 0 => unitFrame X U
  | n + 1 => tensorFrame X (tensorPower X H n) H U (tensorPowerFrame X H U e n) e

/-- Actual tensor power of a section; it does not refer to a chosen local frame. -/
def tensorPowerSection (X : Scheme.{u}) (H : X.Modules) :
    (n : ℕ) → (U : X.Opens) → Γ(H, U) → Γ(tensorPower X H n, U)
  | 0, U, _ => (1 : Γ(X, U))
  | n + 1, U, s => tensorSection X (tensorPower X H n) H U
      (tensorPowerSection X H n U s) s

/-- Ordered product of n possibly different sections in one actual tensor power. -/
def tensorProductSection (X : Scheme.{u}) (H : X.Modules) :
    (n : ℕ) → (U : X.Opens) → (Fin n → Γ(H, U)) → Γ(tensorPower X H n, U)
  | 0, U, _ => (1 : Γ(X, U))
  | n + 1, U, s => tensorSection X (tensorPower X H n) H U
      (tensorProductSection X H n U (fun i => s i.castSucc)) (s (Fin.last n))

end ArithmeticThetaTensorPower
