module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_RiemannRochRows
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

@[expose] public section

theorem AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hSG : AlgebraicCurve.StichtenothGenusExists K F) :
    AlgebraicCurve.WeilDualityAdelic K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.solution
