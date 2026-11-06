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
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_Tuple_succAbove_sort_comp_succAbove_eq

set_option autoImplicit false

theorem solution
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove k) := by
  classical
  set s : Equiv.Perm (Fin (n + 1)) := Tuple.sort u with hs
  set p : Fin (n + 1) := s.symm i with hp
  have hsp : s p = i := s.apply_symm_apply i

  let e : {x : Fin (n + 1) // x ≠ p} ≃ {x : Fin (n + 1) // x ≠ i} :=
    s.subtypeEquiv (fun x => by rw [← hsp]; exact s.injective.ne_iff.symm)
  let τ : Equiv.Perm (Fin n) := ((finSuccAboveEquiv p).trans e).trans (finSuccAboveEquiv i).symm
  have hτ : ∀ k : Fin n, i.succAbove (τ k) = s (p.succAbove k) := by
    intro k
    have h1 : finSuccAboveEquiv i (τ k) = e (finSuccAboveEquiv p k) :=
      (finSuccAboveEquiv i).apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    rw [finSuccAboveEquiv_apply] at h2
    simpa [e, Equiv.subtypeEquiv, finSuccAboveEquiv_apply] using h2
  have key : τ = Tuple.sort (u ∘ i.succAbove) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨?_, ?_⟩
    · intro a b hab
      show u (i.succAbove (τ a)) ≤ u (i.succAbove (τ b))
      rw [hτ, hτ]
      exact Tuple.monotone_sort u ((Fin.strictMono_succAbove p).monotone hab)
    · intro a b hab h
      exfalso
      have h' : i.succAbove (τ a) = i.succAbove (τ b) := hu h
      rw [hτ, hτ, s.apply_eq_iff_eq] at h'
      exact absurd (Fin.succAbove_right_injective h') hab.ne
  rw [← key, hτ]
