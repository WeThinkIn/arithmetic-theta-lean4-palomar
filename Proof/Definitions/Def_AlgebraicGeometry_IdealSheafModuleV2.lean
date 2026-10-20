module

public import Definitions.Def_SheafOfModules_MonoidalV2
public import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
public import Definitions.Def_AlgebraicGeometry_IdealSheafModule

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme.IdealSheafData

end Scheme.IdealSheafData

end AlgebraicGeometry

end
