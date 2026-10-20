module

public import ArithmeticFieldDefinitionsR0231

@[expose] public section

/-! Full coefficient-field transfer on the source valid-Gram domain.
Integer reflection preserves every coefficient. Positivity of the computed
common level supplies admissible outer substitution, including empty cases. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace ArithmeticThetaArithmeticFieldR0232
namespace ValidGramFieldFormalIdentityR0232
open ArithmeticThetaArithmeticFieldR0231
open ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaCompactUnaryR0183

lemma integralTheta_complex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (integralTheta A) =
      ArithmeticThetaComputed.theta A := by
  ext m
  simp [integralTheta, ArithmeticThetaComputed.theta]

lemma map_subst_X_pow (k : Type) [Field k] (d : ℕ) (hd : d ≠ 0)
    (f : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom k) (PowerSeries.subst (PowerSeries.X ^ d) f) =
      PowerSeries.subst (PowerSeries.X ^ d) (PowerSeries.map (Int.castRingHom k) f) := by
  ext m
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_subst_X_pow hd]
  split_ifs <;> simp

def integralCosetPolynomial {n h : ℕ} (A : Matrices n h) (U : Indexing A)
    (i : Fin h) : PowerSeries ℤ :=
  ∑ a : Cosets A i, ∏ j : Fin n,
    PowerSeries.subst (PowerSeries.X ^ ((commonN A)^2 / (U.pair (U.index i a j)).1))
      (ArithmeticThetaUnaryProduct.clearedUnaryTheta
        (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2)

lemma map_integralCosetPolynomial (k : Type) [Field k] {n h : ℕ}
    (A : Matrices n h) (U : Indexing A) (i : Fin h) :
    PowerSeries.map (Int.castRingHom k) (integralCosetPolynomial A U i) =
      ∑ a : Cosets A i, ∏ j : Fin n,
        unarySeries k (commonN A) (U.pair (U.index i a j)).1
          (U.pair (U.index i a j)).2 := by
  simp only [integralCosetPolynomial, map_sum, map_prod, unarySeries]

lemma integral_column_of_nonzero_level {n h : ℕ} (A : Matrices n h)
    (U : Indexing A) (hF : ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U)
    (hL : level (commonN A) ≠ 0) (i : Fin h) :
    PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (integralTheta (A i)) =
      integralCosetPolynomial A U i := by
  classical
  apply PowerSeries.map_injective (Int.castRingHom ℂ) (Int.cast_injective)
  rw [map_subst_X_pow ℂ _ hL, integralTheta_complex, map_integralCosetPolynomial]
  have hi := hF (Pi.single i 1)
  simpa [ArithmeticThetaLatticeSectionsR0188.expanded, ArithmeticThetaComputed.thetaMap,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
    Pi.single_apply, ite_smul] using hi

lemma field_formal_identity_of_nonzero_level (k : Type) [Field k] (n h : ℕ)
    (A : Matrices n h) (U : Indexing A)
    (hF : ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U)
    (hL : level (commonN A) ≠ 0) :
    ArithmeticThetaArithmeticFieldR0231.FormalIdentity k A U := by
  classical
  intro c
  have hi (i : Fin h) :
      PowerSeries.subst (PowerSeries.X ^ level (commonN A)) (theta k (A i)) =
        ∑ a : Cosets A i, ∏ j : Fin n,
          unarySeries k (commonN A) (U.pair (U.index i a j)).1
            (U.pair (U.index i a j)).2 := by
    rw [theta, ← map_subst_X_pow k _ hL,
      integral_column_of_nonzero_level A U hF hL i, map_integralCosetPolynomial]
  unfold ArithmeticThetaArithmeticFieldR0231.expanded
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow hL), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, PowerSeries.coe_substAlgHom, hi]

lemma commonN_zero_rank {h : ℕ} (A : Matrices 0 h) : commonN A = 1 := by
  simp [commonN]

lemma commonN_empty_family {n : ℕ} (A : Matrices n 0) : commonN A = 1 := by
  simp [commonN]

end ValidGramFieldFormalIdentityR0232

open ValidGramFieldFormalIdentityR0232 ArithmeticThetaLatticeSectionsR0188
open ArithmeticThetaCompactUnaryR0183

/-- Transfer the full formal identity to every field on the valid-Gram domain.
The empty rank and family cases have commonN = 1. -/
theorem valid_gram_field_formal_identity (k : Type) [Field k] (n h : ℕ)
    (A : Matrices n h) (U : Indexing A)
    (hA : ∀ i, ArithmeticThetaComputed.validGram (A i))
    (hF : ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U) :
    ArithmeticThetaArithmeticFieldR0231.FormalIdentity k A U := by
  apply field_formal_identity_of_nonzero_level k n h A U hF
  have hN : 0 < commonN A := by
    by_cases hn : n = 0
    · subst n
      rw [commonN_zero_rank]
      decide
    by_cases hh : h = 0
    · subst h
      rw [commonN_empty_family]
      decide
    exact (indexed_full_unary_factorization n h (Nat.pos_of_ne_zero hn)
      (Nat.pos_of_ne_zero hh) A hA).1
  exact ne_of_gt (by dsimp [level]; positivity)

end ArithmeticThetaArithmeticFieldR0232

#print axioms ArithmeticThetaArithmeticFieldR0232.valid_gram_field_formal_identity
