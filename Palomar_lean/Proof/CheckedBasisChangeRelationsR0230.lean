module

public import AdaptiveSolverDefinitionsR0230
public import ThetaBasisChange

@[expose] public section

open scoped BigOperators

namespace ArithmeticThetaAdaptiveSolverR0230

private theorem checked_theta_eq {n h : ℕ} (A : Matrices n h)
    (hv : ∀ i, ArithmeticThetaComputed.validGram (A i)) (c : Change n h)
    (hc : checkChange A c = true) :
    ArithmeticThetaComputed.theta (A c.left) = ArithmeticThetaComputed.theta (A c.right) := by
  have hc' : (c.matrix.det = 1 ∨ c.matrix.det = -1) ∧
      c.matrix.transpose * A c.left * c.matrix = A c.right := by
    simpa only [checkChange, decide_eq_true_eq] using hc
  have hu : IsUnit c.matrix.det := by
    rcases hc'.1 with hp | hp
    · rw [hp]; exact isUnit_one
    · rw [hp]; exact isUnit_one.neg
  have hs := (ArithmeticThetaCore.integral_basis_change n (A c.left) (A c.right)
    c.matrix (hv c.left).1 (hv c.right).1 (hv c.left).2.1 (hv c.right).2.1
    (hv c.left).2.2 (hv c.right).2.2 hu hc'.2).2
  ext m
  have hm := congrArg (PowerSeries.coeff m) hs
  simpa [ArithmeticThetaComputed.theta, PowerSeries.coeff_map, PowerSeries.coeff_mk] using hm

/-- Every checked change gives a complete theta relation; a failed check gives zero. -/
theorem checked_basis_change_relations :
    ∀ (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) →
      ∀ cs : List (Change n h), Relations A (changeRelations A cs) := by
  intro n h A hv cs j
  by_cases hc : checkChange A (cs.get j) = true
  · have ht := checked_theta_eq A hv (cs.get j) hc
    have he : (fun i => ((changeRelations A cs i j : ℚ) : ℂ)) =
        (fun i => (if i = (cs.get j).left then (1 : ℂ) else 0) -
          (if i = (cs.get j).right then 1 else 0)) := by
      funext i
      simp only [changeRelations, hc, ↓reduceIte]
      split_ifs <;> norm_num
    rw [he]
    simp only [ArithmeticThetaComputed.thetaMap, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply, sub_smul,
      ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sub_eq_zero] using ht
  · have hz : (fun i => ((changeRelations A cs i j : ℚ) : ℂ)) = 0 := by
      funext i
      simp only [changeRelations, hc, Bool.false_eq_true, ↓reduceIte, Rat.cast_zero, Pi.zero_apply]
    rw [hz, map_zero]

end ArithmeticThetaAdaptiveSolverR0230

#print axioms ArithmeticThetaAdaptiveSolverR0230.checked_basis_change_relations
