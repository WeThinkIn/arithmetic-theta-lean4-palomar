module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import Definitions.Def_SheafOfModules_MonoidalV2
public import Definitions.Def_PresheafOfModules_PullbackMonoidal
public import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
