module

public import Mathlib
public import Definitions.Def_JacJ1Iface
public import P2M.Util
public import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral

@[expose] public section
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f) : GeometricallyIntegral f := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.solution
