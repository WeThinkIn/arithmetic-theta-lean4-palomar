module

public import Definitions.Def_WeierstrassCurve_ProjModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_r0_isIntegral_pullbacks {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) :
    IsIntegral (projModelCR W.toProjective) ∧
    IsIntegral ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) ∧
    IsIntegral ↑(pullback
      (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫
        projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks.solution
