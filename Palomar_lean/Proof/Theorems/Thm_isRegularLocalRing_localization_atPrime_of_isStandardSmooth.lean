module

public import Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks
public import Definitions.Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction
public import P2M.Util
public import P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth

@[expose] public section
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_of_isStandardSmooth
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.solution
