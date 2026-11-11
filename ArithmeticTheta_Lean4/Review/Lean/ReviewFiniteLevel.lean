import ReviewGeometryDefinitions

/-! Extract the actual finite-level property without its construction witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section

namespace ArithmeticThetaReview.Geometry
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 (Base)
open ArithmeticThetaMetaplecticStackR0207 (Coherence)
open ArithmeticThetaActualLevelR0208
open ArithmeticThetaSquareLinesR0192 (SquareLine)

/-- Forget only the geometric construction of the categorical fiber. Its
actual projections, equivalence on every test scheme and naturality remain.
The factor two is the exact square-root torsor rank in the original theorem. -/
theorem finite_level_of_original :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (P : Provider k L)
      (C : Coherence L (Base k)) (Y : Over (Base k)) (p : Y ⟶ base P)
      (H : SquareLine Y.left ((Scheme.Modules.pullback p.left).obj (hodge P)))
      (j : AnchoredMap C Y (object P p H)),
      Nonempty (PullbackComparison j) → FiniteEtaleLevel P p H j →
      ∀ bound : ℕ, (∀ z : (base P).left, p.left.finrank z ≤ bound) →
        FiniteLevel j (2 * bound) := by
  intro k _ _ L P C Y p H j hcomparison hlevel bound hbound
  refine ⟨hcomparison, ?_⟩
  intro T r
  obtain ⟨F, G, _hrep, _htorsor, _huses, hfinite, hetale, _hsurjective, hrank⟩ :=
    hlevel T r
  refine ⟨G, hfinite, hetale, ?_⟩
  intro t
  rw [hrank t]
  exact Nat.mul_le_mul_left 2 (hbound ((testRoot P r).map t))

end ArithmeticThetaReview.Geometry
