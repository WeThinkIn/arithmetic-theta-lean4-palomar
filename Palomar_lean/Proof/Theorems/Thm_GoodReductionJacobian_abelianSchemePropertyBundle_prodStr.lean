module

public import Definitions.Def_JacJ1Iface
public import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
public import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
public import P2M.Util
public import P2M.Sol.S_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr

@[expose] public section
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.abelianSchemePropertyBundle_prodStr
    {K : Type u} [Field K] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of K)}
    {h : C ⟶ Spec (CommRingCat.of K)} (hB : AbelianSchemePropertyBundle K g)
    (hC : AbelianSchemePropertyBundle K h) :
    AbelianSchemePropertyBundle K (prodStr g h) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr.solution
