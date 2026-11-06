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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util
public import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq

@[expose] public section

theorem IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (μ : K →+* K) (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w) (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) → v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ))) (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1)) (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R, t₀.asIdeal = Ideal.span {r} := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.solution
