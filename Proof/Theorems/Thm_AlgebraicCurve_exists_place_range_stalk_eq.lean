module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_CurveModel
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_exists_place_range_stalk_eq

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.exists_place_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : IsClosed ({x} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ v : AlgebraicCurve.Place K C.functionField,
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq.solution
