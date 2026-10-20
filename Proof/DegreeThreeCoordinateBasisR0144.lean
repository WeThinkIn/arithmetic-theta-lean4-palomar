module

public import CubicModelDefinitionsR0144

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! The explicit degree-three basis over the actual truncated base. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
namespace DegreeThreeCoordinateBasisR0144
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaPolygonCohomologyR0131
open CoordinateExactPolesR0143
open ArithmeticThetaGenericEvaluationR0140

variable (k : Type u) [Field k] [CharZero k]

lemma basis_compatible (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (n : ℕ) (j : Fin 3) :
    Compatible k r n hr (T.overlap n) 3 (basisNumerator k true r n j) := by
  fin_cases j
  · intro i
    simp only [basisNumerator, ↓reduceIte, degree, map_pow]
    ring
  · have hx := (tate_x_numerator_system k r hr h3 T).1 n
    intro i
    have hi := hx i
    simp only [degree, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [basisNumerator, Nat.one_ne_zero, ↓reduceIte, map_mul]
    linear_combination
      (T.overlap n) (restriction k n false (equation k r n i)) *
      restriction k n true (equation k r n (next r hr i)) * hi
  · exact (tate_y_numerator_system k r hr h3 T).1 n

lemma coefficients_zero (r n : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (c : Fin 3 → R k n)
    (hc : ∀ i, ∑ j : Fin 3, base k n (c j) * basisNumerator k true r n j i = 0) :
    c = 0 := by
  let z := zeroIndex r hr
  let h := equation k r n z
  have hreg : IsRegular h := by
    simpa [h, z, equation, zeroIndex, show ¬1 = r by omega] using
      (IdentityChartIdealR0138.right_equation k n).2
  have he : markedPoint k n 1 h = 0 := marked_equation k r n hr
  have hn (odd : Bool) : markedPoint k n 1 (numerator k odd r n z) = 1 :=
    numerator_identity k odd r n hr h3
  have hh : base k n (c 0) * h^3 +
      base k n (c 1) * (h * numerator k false r n z) +
      base k n (c 2) * numerator k true r n z = 0 := by
    simpa [Fin.sum_univ_succ, basisNumerator, degree, h, add_assoc] using hc z
  have hc2 : c 2 = 0 := by
    have hh' := congrArg (markedPoint k n 1) hh
    simpa only [map_add, map_mul, map_pow, map_zero,
      AlgebraicIdentityEvaluationR0140.marked_base, he, hn, zero_pow (by decide : (3:ℕ) ≠ 0),
      mul_zero, zero_mul, mul_one, zero_add] using hh'
  rw [hc2, map_zero, zero_mul, add_zero] at hh
  have hh1 : base k n (c 0) * h^2 + base k n (c 1) * numerator k false r n z = 0 := by
    apply hreg.1
    calc
      h * (base k n (c 0) * h^2 + base k n (c 1) * numerator k false r n z) =
        base k n (c 0) * h^3 + base k n (c 1) * (h * numerator k false r n z) := by ring
      _ = h * 0 := by simpa using hh
  have hc1 : c 1 = 0 := by
    have hh' := congrArg (markedPoint k n 1) hh1
    simpa only [map_add, map_mul, map_pow, map_zero,
      AlgebraicIdentityEvaluationR0140.marked_base, he, hn, zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero, mul_one, zero_add] using hh'
  have hb0 : base k n (c 0) = 0 := by
    apply (hreg.pow 2).2
    simpa [hc1] using hh1
  have hc0 : c 0 = 0 := by
    have hh' := congrArg (markedPoint k n 1) hb0
    simpa only [AlgebraicIdentityEvaluationR0140.marked_base, map_zero] using hh'
  funext j
  fin_cases j <;> assumption

lemma base_artinian (n : ℕ) : IsArtinianRing (R k n) := by
  have hlen := isFiniteLength_quotient_span_singleton (PowerSeries k)
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero (n+1) PowerSeries.X_ne_zero))
  have : IsArtinian (PowerSeries k)
      (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (n+1)}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  have hi : IsArtinianRing (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (n+1)}) :=
    isArtinian_of_tower (PowerSeries k)
      (S := PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (n+1)}) inferInstance
  change IsArtinianRing (PowerSeries k ⧸ (Ideal.span {PowerSeries.X}) ^ (n+1))
  rw [Ideal.span_singleton_pow]
  exact hi

set_option backward.isDefEq.respectTransparency true
section Kernel
variable {k} {n : ℕ}
open IdentityPositiveSectionsRankR0138
attribute [local instance] IdentityPositiveSectionsRankR0138.nodeAlgebra
  IdentityPositiveSectionsRankR0138.nodeModule
  IdentityPositiveSectionsRankR0138.nodeAction
  IdentityPositiveSectionsRankR0138.nodeScalar
  IdentityPositiveSectionsRankR0138.nodeFamilyScalar

variable (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (L : B k n true ≃+* LaurentPolynomial (R k n)) (hL : LaurentPresentation k n L)

/-- The displayed numerators as elements of the accepted linear kernel. -/
def vector (j : Fin 3) :
    LinearMap.ker (difference L hL (T.overlap n) (T.overlap_spec n) r hr 3) :=
  ⟨basisNumerator k true r n j,
    (compatible_iff_difference L hL (T.overlap n) (T.overlap_spec n) r hr h3 3 _).mp
      (basis_compatible k r hr h3 T n j)⟩

/-- Linear combination uses precisely the frozen structural base map. -/
def combination : (Fin 3 → R k n) →ₗ[R k n]
    LinearMap.ker (difference L hL (T.overlap n) (T.overlap_spec n) r hr 3) :=
  Fintype.linearCombination (R k n) (vector r hr h3 T L hL)

lemma combination_apply (c : Fin 3 → R k n) (i : Fin r) :
    (combination r hr h3 T L hL c).val i =
      ∑ j : Fin 3, base k n (c j) * basisNumerator k true r n j i := by
  change (Fintype.linearCombination (R k n) (vector r hr h3 T L hL) c).val i = _
  rw [Fintype.linearCombination_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply]
  rfl

lemma combination_injective : Function.Injective (combination r hr h3 T L hL) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  apply coefficients_zero k r n hr h3 c
  intro i
  rw [← combination_apply r hr h3 T L hL, hc]
  rfl

lemma combination_surjective : Function.Surjective (combination r hr h3 T L hL) := by
  let : IsArtinianRing (R k n) := base_artinian k n
  let e := (kernelCoordinates L hL (T.overlap n) (T.overlap_spec n) r hr h3 3
    (by decide)).trans (Finsupp.linearEquivFunOnFinite (R k n) (R k n) (Fin 3))
  let f := e.toLinearMap.comp (combination r hr h3 T L hL)
  have hf : Function.Injective f := e.injective.comp (combination_injective r hr h3 T L hL)
  have hs := IsArtinian.surjective_of_injective_endomorphism f hf
  intro v
  obtain ⟨c, hc⟩ := hs (e v)
  exact ⟨c, e.injective hc⟩

end Kernel
end DegreeThreeCoordinateBasisR0144

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaPolygonCohomologyR0131
open IdentityPositiveSectionsRankR0138
open DegreeThreeCoordinateBasisR0144

/-- Every degree-three section has unique coefficients in the literal 1,X,Y basis. -/
theorem degree_three_coordinate_basis :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr), ∀ n : ℕ,
      ArithmeticThetaCubicModelR0144.CoordinateBasis k true (r := r) (hr := hr) (T.overlap n) := by
  intro k _ _ r hr h3 T n
  refine ⟨basis_compatible k r hr h3 T n, ?_⟩
  intro v
  obtain ⟨L, hL, _⟩ := truncated_laurent_presentation k n
  let w := sectionsKernel L hL (T.overlap n) (T.overlap_spec n) r hr h3 3 v
  obtain ⟨c, hc⟩ := combination_surjective r hr h3 T L hL w
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hi := congrArg (fun s => s.val i) hc
    exact hi.symm.trans (combination_apply r hr h3 T L hL c i)
  · intro b hb
    apply combination_injective r hr h3 T L hL
    apply Subtype.ext
    funext i
    rw [combination_apply, hc]
    exact (hb i).symm

end ArithmeticThetaCubicModelR0144
#print axioms ArithmeticThetaCubicModelR0144.degree_three_coordinate_basis
