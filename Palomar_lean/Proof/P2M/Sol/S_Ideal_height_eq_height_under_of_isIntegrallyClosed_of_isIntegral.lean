module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

set_option autoImplicit false

universe u

namespace HeightAux

theorem eq_of_le_of_under_eq {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]
    [Algebra.IsIntegral P B] {Q q : Ideal B} [Q.IsPrime] [q.IsPrime] (hle : Q ≤ q)
    (hu : q.under P ≤ Q.under P) : Q = q := by
  by_contra hne
  have hlt : Q < q := lt_of_le_of_ne hle hne
  obtain ⟨x, hxq, hxQ⟩ := Set.exists_of_ssubset hlt
  have := Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxQ⟩
    (Algebra.IsIntegral.isIntegral (R := P) x)
  exact absurd (lt_of_lt_of_le this hu) (lt_irrefl _)

theorem height_eq_height_under (P B : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B]
    [FaithfulSMul P B] [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by
  set p := q.under P with hp
  set I := Ideal.map (algebraMap P B) p with hI
  have hIq : I ≤ q := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by rw [Ideal.mk_ker]; exact hIq
  haveI hQbar : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  suffices h0 : (Ideal.map (Ideal.Quotient.mk I) q).height = 0 by
    rw [key, ← hI, h0, add_zero]
  refine nonpos_iff_eq_zero.mp ?_
  rw [← ENat.coe_zero, Ideal.height_le_iff]
  intro Q' hQ' hQ'lt
  exfalso

  set Q := Ideal.comap (Ideal.Quotient.mk I) Q' with hQ
  have hIQ : I ≤ Q := (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap _)
  have hQq : Q ≤ q := by
    refine (Ideal.comap_mono hQ'lt.le).trans ?_
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_le le_rfl ?_
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact hIq
  have hunder : q.under P ≤ Q.under P := by
    change p ≤ Ideal.comap (algebraMap P B) Q
    exact Ideal.le_comap_of_map_le hIQ
  have hQeq : Q = q := eq_of_le_of_under_eq hQq hunder
  have hQ'eq : Ideal.map (Ideal.Quotient.mk I) Q = Q' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hQeq] at hQ'eq
  exact absurd (hQ'eq ▸ hQ'lt) (lt_irrefl _)

end HeightAux
theorem solution
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height :=
  HeightAux.height_eq_height_under P B q
