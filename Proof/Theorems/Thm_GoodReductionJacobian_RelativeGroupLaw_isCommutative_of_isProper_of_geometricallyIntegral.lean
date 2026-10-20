module

public import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
public import P2M.Util
public import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral

@[expose] public section
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u
theorem GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f]
    [GeometricallyIntegral f] (G : RelativeGroupLaw K f) : G.IsCommutative := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral.solution
