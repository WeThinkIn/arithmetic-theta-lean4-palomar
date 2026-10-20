module

public import Definitions.Def_AlgebraicGeometry_IdealSheafModuleV2
public import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
public import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

end Scheme.Modules

end AlgebraicGeometry

end
