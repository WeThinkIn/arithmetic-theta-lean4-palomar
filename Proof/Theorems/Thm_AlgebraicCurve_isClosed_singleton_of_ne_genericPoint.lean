module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_CurveModel
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint.solution
