import SectionOrderDefinitions
import TensorProductLaws

open AlgebraicGeometry CategoryTheory
universe u v
noncomputable section
namespace ArithmeticThetaDegreeAssembly

/-- Actual tensor-power frame cover on exactly the original normal affine opens. -/
def powerCover (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    {ι : Type v} (C : ArithmeticThetaLineRoot.NormalFrameCover X H ι) (n : ℕ) :
    ArithmeticThetaLineRoot.NormalFrameCover X
      (ArithmeticThetaTensorPower.tensorPower X H n) ι where
  opens := C.opens
  covers := C.covers
  nonempty := C.nonempty
  affine := C.affine
  normal := C.normal
  frame := fun i => ArithmeticThetaTensorPower.tensorPowerFrame X H (C.opens i) (C.frame i) n

end ArithmeticThetaDegreeAssembly
