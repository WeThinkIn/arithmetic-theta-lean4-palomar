module

public import ComputedCoefficientMatrix
public import ComputedPivotCoordinates
public import RationalMatrixScalarExtension
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

@[expose] public section

namespace ArithmeticThetaComputed

theorem computed_independent_theta_columns (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hv : ∀ i, validGram (A i)) :
    LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.length => theta (A (selectedIndex A B t))) := by
  have hli := (ArithmeticThetaElimination.computed_pivot_coordinates (B+1) h
    (coefficientMatrix A B)).1
  have hlic : LinearIndependent ℂ (fun t => fun a =>
      ((ArithmeticThetaElimination.pivotColumn (coefficientMatrix A B) t a : ℚ) : ℂ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)).mpr hli
  apply LinearIndependent.of_comp (prefixMap B)
  convert hlic using 1
  funext t a
  exact (computed_coefficient_matrix n h B A hv a (selectedIndex A B t)).symm

theorem computed_prefix_coordinates (n h B : ℕ)
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (hv : ∀ i, validGram (A i))
    (j : Fin h) (a : Fin (B+1)) :
    PowerSeries.coeff a.val (theta (A j)) =
      ∑ t : Fin (ArithmeticThetaElimination.run (coefficientMatrix A B)).pivots.length,
        ((ArithmeticThetaElimination.columnCoordinates (coefficientMatrix A B) j t : ℚ) : ℂ) *
          PowerSeries.coeff a.val (theta (A (selectedIndex A B t))) := by
  have hc := ((ArithmeticThetaElimination.computed_pivot_coordinates (B+1) h
    (coefficientMatrix A B)).2 j).1 a
  simp_rw [← computed_coefficient_matrix n h B A hv]
  exact_mod_cast hc

end ArithmeticThetaComputed
