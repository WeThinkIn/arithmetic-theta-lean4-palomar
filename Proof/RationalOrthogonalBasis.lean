module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace ArithmeticThetaLattice

 theorem rational_orthogonal_basis :
    ∀ (n : ℕ) (Q : QuadraticForm ℚ (Fin n → ℚ)), Q.PosDef →
      ∃ b : Module.Basis (Fin n) ℚ (Fin n → ℚ),
        (QuadraticMap.associated Q).IsOrthoᵢ b ∧
          (∀ i, 0 < Q (b i)) ∧
            ∀ x : Fin n → ℚ, Q x = ∑ i : Fin n, Q (b i) * (b.repr x i) ^ 2 := by
  intro n Q hQ
  obtain ⟨b₀, hb₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm ℚ Q)
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n :=
    finCongr (Module.finrank_fin_fun ℚ)
  let b : Module.Basis (Fin n) ℚ (Fin n → ℚ) := b₀.reindex e
  have hb' : (QuadraticMap.associated Q).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def] at hb₀ ⊢
    intro i j hij
    simpa [b, Module.Basis.reindex_apply] using
      (hb₀ (e.symm i) (e.symm j) (by
        intro h
        apply hij
        exact e.symm.injective h))
  have hpos : ∀ i, 0 < Q (b i) := by
    intro i
    exact hQ (b i) (b.ne_zero i)
  have hcoord : ∀ x : (Fin n → ℚ), Q x = ∑ i : Fin n, Q (b i) * (b.repr x i) ^ 2 := by
    intro x
    have heq := QuadraticMap.basisRepr_eq_of_iIsOrtho Q b hb'
    have hx := congrArg (fun f : QuadraticMap ℚ ((Fin n) → ℚ) ℚ =>
      f (b.repr x : Fin n → ℚ)) heq
    simpa [QuadraticMap.basisRepr_apply, QuadraticMap.weightedSumSquares_apply,
      b.equivFun_symm_apply, pow_two, smul_eq_mul] using hx
  exact ⟨b, hb', hpos, hcoord⟩

end ArithmeticThetaLattice
