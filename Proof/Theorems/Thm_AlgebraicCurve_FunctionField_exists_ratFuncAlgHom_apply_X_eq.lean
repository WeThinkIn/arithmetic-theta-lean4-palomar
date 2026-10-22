module

public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq

@[expose] public section

theorem AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] {g : F} (hg : g ∉ Set.range (algebraMap K F)) : ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.solution
