module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Definitions.Def_AlgebraicCurve_RelCartier
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isInvertible_comap
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [Surjective π]
    (I : X.IdealSheafData) (h : (I.comap π).IsInvertible) : I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap.solution
