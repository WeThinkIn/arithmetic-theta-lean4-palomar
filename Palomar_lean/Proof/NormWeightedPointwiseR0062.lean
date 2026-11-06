module

public import Mathlib.Tactic.ENatToNat
public import NormQuotientDefinitionsR0062

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ArithmeticThetaNormQuotientsR0062

theorem weighted_pointwise :
    ∀ (c d i : ℕ), 0 < d →
      weightedTerm c d i =
        (((c : ℚ) * (i : ℚ)) ^ 2 - (residue c d i : ℚ) ^ 2) /
            (2 * (d : ℚ)) -
          ((c : ℚ) * (i : ℚ) - (residue c d i : ℚ)) / 2 := by
  intro c d i hd
  unfold weightedTerm residue quotient
  have hdiv : c * i = d * (c * i / d) + c * i % d :=
    (Nat.div_add_mod (c * i) d).symm
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hdivQ : (c : ℚ) * (i : ℚ) =
      (d : ℚ) * ((c * i / d : ℕ) : ℚ) + ((c * i % d : ℕ) : ℚ) := by
    exact_mod_cast hdiv
  rw [hdivQ]
  field_simp [hdq]
  ring

end ArithmeticThetaNormQuotientsR0062
