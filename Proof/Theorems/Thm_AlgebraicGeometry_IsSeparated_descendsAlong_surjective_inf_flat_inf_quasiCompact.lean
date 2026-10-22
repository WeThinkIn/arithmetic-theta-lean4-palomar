module

public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact

@[expose] public section

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.solution
