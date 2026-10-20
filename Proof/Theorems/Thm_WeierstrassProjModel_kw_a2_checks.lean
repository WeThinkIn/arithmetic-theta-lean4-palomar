module

public import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
public import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
public import P2M.Util
public import P2M.Sol.S_WeierstrassProjModel_kw_a2_checks

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_a2_checks.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(kw_lrApt_WF W F).addX P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(kw_lrApt_WF W F).addY P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(kw_lrApt_WF W F).addZ P Q)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_X W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblX P)
    ∧ (∀ P : Fin 3 → F, (kw_lrApt_WF W F).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Y W) * (kw_lrApt_WF W F).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * (kw_lrApt_WF W F).dblY P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_checks.solution
