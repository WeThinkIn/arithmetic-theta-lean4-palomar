module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Filtered.Final

@[expose] public section
open AlgebraicGeometry CategoryTheory
universe u
noncomputable section

namespace ArithmeticThetaPullback

set_option backward.isDefEq.respectTransparency false in
/-- The canonical structure-sheaf comparison for the actual pullback functor.
Its forward map is adjoint to the structure-sheaf morphism of `p`. -/
def pullback_unit_iso (X Y : Scheme.{u}) (p : X ⟶ Y) :
    (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  -- The preimage functor is final: every open lies below the preimage of top.
  letI : (TopologicalSpace.Opens.map p.base).Final := by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e

end ArithmeticThetaPullback
