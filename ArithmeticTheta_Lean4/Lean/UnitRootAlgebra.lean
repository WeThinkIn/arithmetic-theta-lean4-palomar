import GeometricPrerequisiteDefinitions

/-! Finite etale unit-root algebras and their actual frame transitions. -/

open Polynomial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGeometricPrerequisites

/-- The distinguished root satisfies the defining equation, also for exponent zero. -/
lemma unitRoot_pow (R : Type u) [CommRing R] (N : ℕ) (a : Rˣ) :
    AdjoinRoot.root (X ^ N - C (a : R)) ^ N =
      algebraMap R (unitRootAlgebra R N a) (a : R) := by
  have h := AdjoinRoot.eval₂_root (X ^ N - C (a : R))
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    ← AdjoinRoot.algebraMap_eq] using h

/-- Inverting a polynomial derivative that is already a unit does not change its quotient. -/
lemma etale_adjoinRoot_of_monic_of_isUnit_derivative
    {R : Type u} [CommRing R] (f : R[X]) (hf : f.Monic)
    (hd : IsUnit (aeval (AdjoinRoot.root f) f.derivative)) :
    Algebra.Etale R (AdjoinRoot f) := by
  let P : StandardEtalePair R :=
    ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
  have hroot : P.HasMap (AdjoinRoot.root f) :=
    ⟨by simpa only [AdjoinRoot.aeval_eq] using (AdjoinRoot.mk_self (f := f)), hd⟩
  let forward : AdjoinRoot f →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  let backward : P.Ring →ₐ[R] AdjoinRoot f := P.lift _ hroot
  have hfb : forward.comp backward = AlgHom.id R P.Ring := by
    apply P.hom_ext
    simp [forward, backward]
  have hbf : backward.comp forward = AlgHom.id R (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext
    simp [forward, backward]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom backward forward hbf hfb)

/-- A positive unit exponent and a unit constant give a finite free etale algebra of rank N. -/
theorem unit_root_algebra_finite_etale :
    ∀ (R : Type u) [CommRing R] [Nontrivial R] (N : ℕ),
    0 < N → IsUnit (N : R) → ∀ a : Rˣ,
    Module.Free R (unitRootAlgebra R N a) ∧
    Module.Finite R (unitRootAlgebra R N a) ∧
    Module.finrank R (unitRootAlgebra R N a) = N ∧
    Algebra.Etale R (unitRootAlgebra R N a) := by
  intro R _ _ N hN hNunit a
  have hm : (X ^ N - C (a : R)).Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt hN)
  refine ⟨hm.free_adjoinRoot, hm.finite_adjoinRoot, ?_, ?_⟩
  · simpa using (AdjoinRoot.powerBasis' hm).finrank
  · apply etale_adjoinRoot_of_monic_of_isUnit_derivative _ hm
    have hz : IsUnit (AdjoinRoot.root (X ^ N - C (a : R))) := by
      apply (isUnit_pow_iff (Nat.ne_of_gt hN)).mp
      rw [unitRoot_pow]
      exact a.isUnit.map (algebraMap R (unitRootAlgebra R N a))
    simpa [derivative_sub, derivative_X_pow] using
      (hNunit.map (algebraMap R (unitRootAlgebra R N a))).mul (hz.pow (N - 1))

/-- A unit frame change acts by multiplication on the distinguished root. -/
theorem unit_root_frame_transition :
    ∀ (R : Type u) [CommRing R] (N : ℕ) (a b c : Rˣ),
    a = c ^ N * b → ∃ e : unitRootAlgebra R N a ≃ₐ[R] unitRootAlgebra R N b,
    e (AdjoinRoot.root (X ^ N - C (a : R))) =
      algebraMap R (unitRootAlgebra R N b) (c : R) *
        AdjoinRoot.root (X ^ N - C (b : R)) := by
  intro R _ N a b c hab
  have habR : (a : R) = (c : R) ^ N * (b : R) := by
    exact congrArg (fun x : Rˣ => (x : R)) hab
  have hbaR : (b : R) = (↑(c⁻¹) : R) ^ N * (a : R) := by
    rw [habR, ← mul_assoc, ← mul_pow]
    simp
  let F : unitRootAlgebra R N a →ₐ[R] unitRootAlgebra R N b :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
      (algebraMap R _ (c : R) * AdjoinRoot.root (X ^ N - C (b : R))) (by
        simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
          mul_pow, unitRoot_pow, sub_eq_zero]
        rw [habR, map_mul, map_pow]
        rfl)
  let G : unitRootAlgebra R N b →ₐ[R] unitRootAlgebra R N a :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
      (algebraMap R _ (↑(c⁻¹) : R) * AdjoinRoot.root (X ^ N - C (a : R))) (by
        simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
          mul_pow, unitRoot_pow, sub_eq_zero]
        rw [hbaR, map_mul, map_pow]
        rfl)
  have hF : F (AdjoinRoot.root (X ^ N - C (a : R))) =
      algebraMap R _ (c : R) * AdjoinRoot.root (X ^ N - C (b : R)) := by
    simp only [F, AdjoinRoot.liftAlgHom_root]
  have hG : G (AdjoinRoot.root (X ^ N - C (b : R))) =
      algebraMap R _ (↑(c⁻¹) : R) * AdjoinRoot.root (X ^ N - C (a : R)) := by
    simp only [G, AdjoinRoot.liftAlgHom_root]
  have hFG : F.comp G = AlgHom.id R (unitRootAlgebra R N b) := by
    apply AdjoinRoot.algHom_ext
    change F (G (AdjoinRoot.root (X ^ N - C (b : R)))) = _
    rw [hG, map_mul, F.commutes, hF, ← mul_assoc, ← map_mul]
    simp
  have hGF : G.comp F = AlgHom.id R (unitRootAlgebra R N a) := by
    apply AdjoinRoot.algHom_ext
    change G (F (AdjoinRoot.root (X ^ N - C (a : R)))) = _
    rw [hF, map_mul, G.commutes, hG, ← mul_assoc, ← map_mul]
    simp
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF⟩

end ArithmeticThetaGeometricPrerequisites
