module

public import FieldSharpKernelR0233
public import ComputedPivotCoordinates

@[expose] public section

/-! The accepted rational pivot columns give the complete theta image over every
characteristic-zero field. No embedding of that field into ℂ is used. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaFieldImageR0233
open ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaElimination

namespace FieldSeriesImageProof

variable (k : Type) [Field k] [CharZero k] {n h : ℕ} (A : Matrices n h)

def linear : (Fin h → k) →ₗ[k] PowerSeries k where
  toFun := seriesCombination k A
  map_add' := by intros; simp [seriesCombination, add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [seriesCombination, mul_smul, Finset.smul_sum]

def insert {p : ℕ} (f : Fin p → Fin h) (d : Fin p → k) : Fin h → k :=
  ∑ t, d t • Pi.single (f t) 1

lemma single (j : Fin h) : linear k A (Pi.single j 1) =
    ArithmeticThetaArithmeticFieldR0231.theta k (A j) := by
  classical
  change seriesCombination k A (Pi.single j 1) = _
  simp [seriesCombination, Pi.single_apply, apply_ite]

lemma inserted (B : ℕ) (d : Fin (pivotCount A B) → k) :
    linear k A (insert k (ArithmeticThetaComputed.selectedIndex A B) d) =
      seriesPivot k A B d := by
  simp only [insert, map_sum, map_smul, single, seriesPivot]

lemma pivot_coeff (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (B : ℕ) (d : Fin (pivotCount A B) → k) (a : Fin (B + 1)) :
    PowerSeries.coeff a.val (seriesPivot k A B d) =
      ∑ t, algebraMap ℚ k (pivotColumn (ArithmeticThetaComputed.coefficientMatrix A B) t a) * d t := by
  simp only [seriesPivot, map_sum, PowerSeries.coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [← FieldSharpKernelProof.coeff_cast k,
    ← FieldSharpKernelProof.rational_prefix A hA B]
  exact mul_comm _ _

lemma independent (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (B : ℕ) (d : Fin (pivotCount A B) → k) (hd : seriesPivot k A B d = 0) : d = 0 := by
  have hz (a : Fin (B + 1)) :
      ∑ t, algebraMap ℚ k (pivotColumn (ArithmeticThetaComputed.coefficientMatrix A B) t a) * d t = 0 := by
    rw [← pivot_coeff k A hA B, hd, map_zero]
  ext t
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (d t)).mp
  intro f
  have hr : ∑ u, f (d u) • pivotColumn (ArithmeticThetaComputed.coefficientMatrix A B) u = 0 := by
    ext a
    have he := congrArg f (hz a)
    simp only [map_sum, FieldSharpKernelProof.dual_mul, map_zero] at he
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using he
  exact Fintype.linearIndependent_iff.mp
    (computed_columns_independent (ArithmeticThetaComputed.coefficientMatrix A B)) _ hr t

lemma pivot_sub (B : ℕ) (d e : Fin (pivotCount A B) → k) :
    seriesPivot k A B (d - e) = seriesPivot k A B d - seriesPivot k A B e := by
  simp [seriesPivot, sub_smul, Finset.sum_sub_distrib]

lemma unique (hA : ∀ i, ArithmeticThetaComputed.validGram (A i)) (B : ℕ)
    (d e : Fin (pivotCount A B) → k) (he : seriesPivot k A B d = seriesPivot k A B e) : d = e := by
  apply sub_eq_zero.mp
  apply independent k A hA B
  rw [pivot_sub, he, sub_self]

lemma coordinates (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (B : ℕ) (hk : Kernel k A B) (j : Fin h) :
    ArithmeticThetaArithmeticFieldR0231.theta k (A j) =
      seriesPivot k A B (fun t => algebraMap ℚ k
        (columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t)) := by
  classical
  let M := ArithmeticThetaComputed.coefficientMatrix A B
  let d : Fin (pivotCount A B) → k := fun t => algebraMap ℚ k (columnCoordinates M j t)
  rw [← single k A j, ← inserted k A B d, ← sub_eq_zero, ← map_sub]
  apply (hk _).mpr
  rw [Matrix.mulVec_sub]
  apply sub_eq_zero.mpr
  ext a
  simp only [insert, Matrix.mulVec_sum, Matrix.mulVec_smul]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.map_apply]
  have he := congrArg (algebraMap ℚ k) (((computed_pivot_coordinates (B+1) h M).2 j).1 a)
  simpa [d, M, pivotColumn, ArithmeticThetaComputed.selectedIndex] using he

end FieldSeriesImageProof

/-- The original rational pivot metadata gives independence, unique spanning,
and exactly the original rational coordinates for the full theta series. -/
theorem field_series_image :
    ∀ (k : Type) [Field k] [CharZero k] (n h : ℕ) (A : Matrices n h),
      (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ B : ℕ,
      ArithmeticThetaSharpKernelR0195.cutoff A ≤ B → SeriesImage k A B := by
  intro k _ _ n h A hA B hB
  classical
  have hk := (field_sharp_kernel k n h A hA).1 B hB
  have hc := FieldSeriesImageProof.coordinates k A hA B hk
  refine ⟨hk, FieldSeriesImageProof.independent k A hA B, ?_, hc, ?_⟩
  · intro c
    let d : Fin (pivotCount A B) → k := fun t =>
      ∑ j, c j * algebraMap ℚ k
        (columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t)
    have hd : seriesCombination k A c = seriesPivot k A B d := by
      simp only [seriesCombination]
      simp_rw [hc]
      simp only [seriesPivot, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [d, Finset.sum_smul]
    refine ⟨d, hd, ?_⟩
    intro e he
    exact FieldSeriesImageProof.unique k A hA B e d (he.symm.trans hd)
  · intro j d hd
    have he := FieldSeriesImageProof.unique k A hA B _ _ (hd.symm.trans (hc j))
    ext t
    exact (algebraMap ℚ k).injective (congrFun he t)

#print axioms field_series_image
end ArithmeticThetaFieldImageR0233
