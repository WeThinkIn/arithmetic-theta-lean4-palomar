module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType

@[expose] public section

theorem AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.FormallyUnramified f] [AlgebraicGeometry.LocallyOfFiniteType f] :
    AlgebraicGeometry.LocallyQuasiFinite f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.solution
