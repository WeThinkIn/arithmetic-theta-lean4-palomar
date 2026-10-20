module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_RelCartier
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of O)) [IsSeparated πY]
    (W : Y.Opens) [SmoothOfRelativeDimension 1 (W.ι ≫ πY)]
    (σ : Spec (CommRingCat.of O) ⟶ Y) (hσ : σ ≫ πY = 𝟙 _) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    σ.ker.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens.solution
