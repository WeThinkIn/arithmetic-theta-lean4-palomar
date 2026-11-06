module

public import Definitions.Def_JacJ1Iface
public import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
public import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
public import P2M.Util
public import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one

@[expose] public section
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).cechFinrank 𝒦 0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one.solution
