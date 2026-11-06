module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCover.nonempty_of_compactSpace (V : Scheme.{u}) [CompactSpace V] : Nonempty V.OrderedAffineCover := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace.solution
