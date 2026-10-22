module

public import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens
    {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj M)) :
    Scheme.Modules.IsLocallyFreeOfRank n M := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.solution
