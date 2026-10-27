import GlobalizationDefinitions

/-! Base change for the actual unit-root algebra, with its distinguished root. -/
open Polynomial
open scoped TensorProduct
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaGlobalization

/-- Unit-root charts commute with every scalar extension, including exponent zero. -/
theorem root_algebra_base_change :
    ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (N : ℕ) (a : Rˣ),
    ∃ e : TensorProduct R S
      (ArithmeticThetaGeometricPrerequisites.unitRootAlgebra R N a) ≃ₐ[S]
      ArithmeticThetaGeometricPrerequisites.unitRootAlgebra S N
        (Units.map ((algebraMap R S).toMonoidHom) a),
      e (TensorProduct.tmul R (1 : S)
        (ArithmeticThetaRootTorsor.rootElement R N a)) =
      ArithmeticThetaRootTorsor.rootElement S N
        (Units.map ((algebraMap R S).toMonoidHom) a) := by
  intro R _ S _ _ N a
  change ∃ e : S ⊗[R] AdjoinRoot (X ^ N - C (a : R)) ≃ₐ[S]
      AdjoinRoot (X ^ N - C (algebraMap R S (a : R))),
      e (1 ⊗ₜ[R] AdjoinRoot.root (X ^ N - C (a : R))) =
        AdjoinRoot.root (X ^ N - C (algebraMap R S (a : R)))
  let p : R[X] := X ^ N - C (a : R)
  let q : (S ⊗[R] R)[X] := p.map Algebra.TensorProduct.includeRight.toRingHom
  let r : S[X] := X ^ N - C (algebraMap R S (a : R))
  let e₁ : S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot q :=
    AdjoinRoot.tensorAlgEquiv p q rfl
  let e₂ : AdjoinRoot q ≃ₐ[S] AdjoinRoot r :=
    AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) q r (by
      have h : q.map (Algebra.TensorProduct.rid R S S) = r := by
        simp [q, p, r, Algebra.smul_def]
      rw [h])
  refine ⟨e₁.trans e₂, ?_⟩
  change e₂ (e₁ (1 ⊗ₜ[R] AdjoinRoot.root p)) = AdjoinRoot.root r
  rw [AdjoinRoot.tensorAlgEquiv_root]
  simp [e₂, AdjoinRoot.mapAlgEquiv, AdjoinRoot.mapAlgHom]

end ArithmeticThetaGlobalization
