module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_CurveModel
public import Definitions.Def_AlgebraicCurve_PlacesOf
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u
theorem AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.placesOf c U ∪ AlgebraicCurve.placesOf c V = Set.univ ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c U) ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.solution
