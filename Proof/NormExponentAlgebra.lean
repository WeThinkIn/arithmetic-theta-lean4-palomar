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

@[expose] public section

namespace ArithmeticThetaElementary

theorem norm_exponent_identities :
    ∀ (c d : ℚ),
      (d - 1) * (-c * (c - 1) / 2) + c * ((c - 1) * (d - 1) / 2) = 0 ∧
      (d ^ 2 - 1) * (c ^ 2 - 1) / 12 +
        (-c * (c - 1) / 2) * d * (d - 1) / 2 +
        ((c ^ 2 - 1) * (d - 1) * (2 * d - 1) / 12 -
          d * (c - 1) * (d - 1) / 4) = 0 ∧
      (d ^ 2 - 1) * (-c * (c - 1) / 2) + (c - 1) * (d - 1) / 2 =
        (c - 1) * (d - 1) * (1 - c * (d + 1)) / 2 := by
  intro c d
  constructor
  · ring
  constructor <;> ring

theorem norm_sign_exponent_even :
    ∀ (c d : ℤ), Odd c →
      Even ((c - 1) * (d - 1) * (1 - c * (d + 1)) / 2) := by
  rintro c d ⟨k, rfl⟩
  rcases Int.even_or_odd d with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · let w := -k * (2 * l - 1) * (2 * k * l + k + l)
    refine ⟨w, ?_⟩
    have hn : (2 * k + 1 - 1) * (l + l - 1) *
        (1 - (2 * k + 1) * (l + l + 1)) = (w + w) * 2 := by
      dsimp [w]
      ring
    rw [hn]
    omega
  · let w := k * l * (1 - (2 * k + 1) * (2 * l + 2))
    refine ⟨w, ?_⟩
    have hn : (2 * k + 1 - 1) * (2 * l + 1 - 1) *
        (1 - (2 * k + 1) * (2 * l + 1 + 1)) = (w + w) * 2 := by
      dsimp [w]
      ring
    rw [hn]
    omega

theorem norm_constant_rigidity :
    ∀ u : ℂ, u ^ 3 = 1 → u ^ 8 = 1 → u = 1 := by
  intro u h3 h8
  have h9 : u ^ 9 = 1 := by
    calc
      u ^ 9 = (u ^ 3) ^ 3 := by ring
      _ = 1 := by rw [h3]; norm_num
  calc
    u = u ^ 8 * u := by rw [h8]; ring
    _ = u ^ 9 := by ring
    _ = 1 := h9

end ArithmeticThetaElementary
