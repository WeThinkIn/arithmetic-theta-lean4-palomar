module

public import ResidueDegrees
public import PrincipalDegreeZero

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

/-- Each coefficient of an effective divisor is bounded by its actual residue-weighted degree. -/
theorem effective_divisor_point_le_degree
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (D : X →₀ ℤ)
    (heff : ∀ x, 0 ≤ D x)
    (hsupp : ∀ x ∈ D.support, Order.coheight x = 1) (x : X) :
    D x ≤ weightedDegree k f D := by
  classical
  have hnonneg (y : X) : 0 ≤ (placeDegree k f y : ℤ) * D y :=
    mul_nonneg (Int.natCast_nonneg _) (heff y)
  unfold weightedDegree Finsupp.sum
  by_cases hx : x ∈ D.support
  · have hw : (1 : ℤ) ≤ (placeDegree k f x : ℤ) := by
      have hwNat : 1 ≤ placeDegree k f x :=
        Nat.succ_le_of_lt (placeDegree_pos_of_coheight_one X k f hcurve x (hsupp x hx))
      exact_mod_cast hwNat
    calc
      D x = 1 * D x := (one_mul _).symm
      _ ≤ (placeDegree k f x : ℤ) * D x := mul_le_mul_of_nonneg_right hw (heff x)
      _ ≤ ∑ y ∈ D.support, (placeDegree k f y : ℤ) * D y :=
        Finset.single_le_sum (fun y _ => hnonneg y) hx
  · rw [Finsupp.notMem_support_iff.mp hx]
    exact Finset.sum_nonneg (fun y _ => hnonneg y)

/-- An effective divisor matching a nonzero rational function's actual orders is zero. -/
theorem effective_principal_divisor_eq_zero
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (D : X →₀ ℤ)
    (hg : g ≠ 0) (hD : MatchesPrincipalOrder X g D) (heff : ∀ x, 0 ≤ D x) :
    D = 0 := by
  have hsupp : ∀ x ∈ D.support, Order.coheight x = 1 :=
    fun x hx => coheight_eq_one_of_mem_matching_support X g D hD x hx
  have hdeg := principal_degree_zero X k f hcurve g D hg hD
  ext x
  have hbound := effective_divisor_point_le_degree X k f hcurve D heff hsupp x
  rw [hdeg] at hbound
  exact le_antisymm hbound (heff x)

end ArithmeticThetaCurveDegree

#print axioms ArithmeticThetaCurveDegree.effective_divisor_point_le_degree
#print axioms ArithmeticThetaCurveDegree.effective_principal_divisor_eq_zero
