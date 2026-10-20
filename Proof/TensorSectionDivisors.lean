module

public import TensorDegreeDefinitions
public import GenericLineCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaTensorPower ArithmeticThetaSectionOrder

universe u v w
noncomputable section

namespace ArithmeticThetaDegreeAssembly

/-- The genuine ordered tensor section has the product of generic coefficients. -/
theorem tensorProductSection_coefficient
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (n : ℕ) (s : Fin n → Γ(H, ⊤)) :
    sectionCoefficient X (tensorPower X H n) U (tensorPowerFrame X H U e n)
      (tensorProductSection X H n ⊤ s) =
      ∏ j, sectionCoefficient X H U e (s j) := by
  have hc : sectionCoordinate X (tensorPower X H n) U (tensorPowerFrame X H U e n)
      (tensorProductSection X H n ⊤ s) =
      ∏ j, sectionCoordinate X H U e (s j) := by
    unfold sectionCoordinate
    rw [tensorProductSection_restrict]
    have hf := tensorProductSection_frame X H U e n U le_rfl
      (fun j => (e.equiv U le_rfl).symm (H.presheaf.map (homOfLE le_top).op (s j)))
    simp only [LinearEquiv.apply_symm_apply] at hf
    rw [hf, LinearEquiv.symm_apply_apply]
  unfold sectionCoefficient
  rw [hc, map_prod]

private theorem coefficient_ne_zero
    (X : Scheme.{u}) [IsIntegral X] (H : X.Modules) (hH : IsLineBundle X H)
    (U : X.Opens) [Nonempty U] (e : LocalFrame X H U)
    (s : Γ(H, ⊤)) (hs : s ≠ 0) : sectionCoefficient X H U e s ≠ 0 := by
  intro hz
  apply hs
  apply sectionCoefficient_injective X H hH U e
  rw [hz]
  simp [sectionCoefficient, sectionCoordinate]

private theorem order_product
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) {α : Type v} (a : α → X.functionField) (t : Finset α)
    (ha : ∀ j ∈ t, a j ≠ 0) :
    Scheme.ord (∏ j ∈ t, a j) x = ∑ j ∈ t, Scheme.ord (a j) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      have h := Scheme.ord_mul (x := x) (one_ne_zero : (1 : X.functionField) ≠ 0)
        (one_ne_zero : (1 : X.functionField) ≠ 0)
      simp only [one_mul] at h
      omega
  | @insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        Scheme.ord_mul (ha j (Finset.mem_insert_self j t))
          (Finset.prod_ne_zero_iff.mpr (fun k hk => ha k (Finset.mem_insert_of_mem hk))),
        ih (fun k hk => ha k (Finset.mem_insert_of_mem hk))]

/-- Genuine products of nonzero sections have the sum of their actual divisors. -/
theorem tensor_product_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (n : ℕ)
    (s : Fin n → Γ(H, ⊤)) (D : Fin n → X →₀ ℤ) :
    (∀ j, s j ≠ 0) →
    (∀ j, MatchesSectionOrder X H C (s j) (D j)) →
    tensorProductSection X H n ⊤ s ≠ 0 ∧
    MatchesSectionOrder X (tensorPower X H n) (powerCover X H C n)
      (tensorProductSection X H n ⊤ s) (∑ j, D j) := by
  classical
  intro hs hD
  have hcoeff (i : ι) (j : Fin n) :
      sectionCoefficient X H (C.opens i) (C.frame i) (s j) ≠ 0 :=
    coefficient_ne_zero X H hH (C.opens i) (C.frame i) (s j) (hs j)
  constructor
  · obtain ⟨i, _hi⟩ := Opens.mem_iSup.mp
      (C.covers (show genericPoint X ∈ (⊤ : X.Opens) by trivial))
    intro hz
    have heq := tensorProductSection_coefficient X H (C.opens i) (C.frame i) n s
    rw [hz] at heq
    have hzero : (∏ j, sectionCoefficient X H (C.opens i) (C.frame i) (s j)) = 0 := by
      rw [← heq]
      simp [sectionCoefficient, sectionCoordinate]
    exact (Finset.prod_ne_zero_iff.mpr (fun j _ => hcoeff i j)) hzero
  · intro i x hx
    change (∑ j, D j) x = Scheme.ord
      (sectionCoefficient X (tensorPower X H n) (C.opens i)
        (tensorPowerFrame X H (C.opens i) (C.frame i) n)
        (tensorProductSection X H n ⊤ s)) x
    rw [tensorProductSection_coefficient, order_product X x _ _ (fun j _ => hcoeff i j)]
    simp only [Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hD j i x hx)

/-- Diagonal tensor products give the divisor law for every natural tensor power. -/
theorem tensor_power_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (H : X.Modules) (hH : IsLineBundle X H) (ι : Type v)
    (C : NormalFrameCover X H ι) (n : ℕ)
    (s : Γ(H, ⊤)) (D : X →₀ ℤ) :
    s ≠ 0 → MatchesSectionOrder X H C s D →
    tensorPowerSection X H n ⊤ s ≠ 0 ∧
    MatchesSectionOrder X (tensorPower X H n) (powerCover X H C n)
      (tensorPowerSection X H n ⊤ s) (n • D) := by
  intro hs hD
  simpa only [tensorProductSection_diagonal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin] using
    tensor_product_divisor X H hH ι C n (fun _ => s) (fun _ => D)
      (fun _ => hs) (fun _ => hD)

end ArithmeticThetaDegreeAssembly

#print axioms ArithmeticThetaDegreeAssembly.tensor_product_divisor
#print axioms ArithmeticThetaDegreeAssembly.tensor_power_divisor
