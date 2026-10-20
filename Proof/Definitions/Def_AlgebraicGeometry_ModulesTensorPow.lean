module

public import Mathlib
public import Definitions.Def_SheafOfModules_Monoidal
public import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

end AlgebraicGeometry.Scheme.Modules

end
