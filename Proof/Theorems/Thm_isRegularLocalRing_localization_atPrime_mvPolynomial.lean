module

public import P2M.Util
public import P2M.Sol.S_isRegularLocalRing_localization_atPrime_mvPolynomial

@[expose] public section
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_mvPolynomial
    (k : Type*) [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_isRegularLocalRing_localization_atPrime_mvPolynomial.solution
