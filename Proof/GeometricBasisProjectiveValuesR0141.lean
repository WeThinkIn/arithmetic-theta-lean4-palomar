module

public import GeometricIntertwinerRigidityR0141
public import GenericProjectiveEvaluationR0140

@[expose] public section

/-! Exact projective values for every actual geometric intertwining basis. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141
namespace GeometricBasisProjectiveValuesR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open GenericThetaBasisR0140

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
variable (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) (d : ℕ)

lemma point_scalar (c : LaurentSeries k) :
    (genericPoint k M s hs).appTop (scalarAt k M ⊤ c) =
      (Scheme.ΓSpecIso (.of (LaurentSeries k))).inv c := by
  have hp : genericPoint k M s hs ≫ genericStructure k M = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hh := congrArg (fun f => Scheme.Hom.appTop f
    ((Scheme.ΓSpecIso (.of (LaurentSeries k))).inv c)) hp
  simp only [Scheme.Hom.comp_appTop] at hh
  dsimp only [scalarAt]
  erw [CategoryTheory.Functor.map_id]
  exact hh

/-- Evaluation respects scalars from the actual generic structure morphism. -/
lemma value_scaled (e : GenericFrame k M s hs d) (c : LaurentSeries k)
    (φ ψ : GenericDual k M s d) (h : ScaledEq k M s d c φ ψ) :
    genericValue k M s hs d e ψ = c * genericValue k M s hs d e φ := by
  rw [← (GeometricIntertwinerRigidityR0141.scaled_iff k M s d c φ ψ).mp h]
  unfold GeometricIntertwinerRigidityR0141.mulSection genericValue
  change (Scheme.ΓSpecIso (.of (LaurentSeries k))).hom
    ((e.inv ≫ pulledInclusion (genericPoint k M s hs) (scale (scalarAt k M ⊤ c) φ)).app ⊤ _) = _
  rw [pull_scale, point_scalar, scale_precomp]
  erw [scale_app]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]
  rw [map_mul]
  erw [CommRingCat.hom_inv_apply]
  rfl

end GeometricBasisProjectiveValuesR0141
open ArithmeticThetaGenericEvaluationR0140

/-- The common intertwiner scalar cancels in every identity-fiber frame. -/
theorem geometric_basis_projective_values :
∀ (k : Type u) [Field k] [CharZero k], ∀ (m : ℕ) (hm : 0 < m) (he : Even m), ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k (2*m) (Nat.mul_pos (by decide) hm)) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s) (rot : CategoryTheory.Iso M.X M.X) (scal : kˣ → CategoryTheory.Iso M.X M.X) (inv : CategoryTheory.Iso M.X M.X) (ha : ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv), ∀ (ζ : kˣ), IsPrimitiveRoot (ζ : k) m → ∀ (eA : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ)) (eB : ArithmeticThetaGeometricLiftsR0141.Lift k M s m (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha)), ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (ArithmeticThetaGenericEvaluationR0140.genericTheta k m hm he M hM s hs) → ∀ β : Fin m → ArithmeticThetaGenericEvaluationR0140.GenericDual k M s m, ArithmeticThetaGeometricLiftsR0141.HasBasis k M s m m β → ArithmeticThetaGeometricLiftsR0141.Eigen k M s m m ζ (ArithmeticThetaGeometricLiftsR0141.scalarMap k M rot scal inv ha ζ) eA (β) → ArithmeticThetaGeometricLiftsR0141.Cyclic k M s m m hm (ArithmeticThetaGeometricLiftsR0141.shiftMap k M rot scal inv ha) eB (β) → Nonempty (ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.GenericFrame k M s hs.1 m, ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e ((β) (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm)) ≠ 0 ∧ ∀ ν : Fin m, ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e ((β) ν) / ArithmeticThetaGenericEvaluationR0140.genericValue k M s hs.1 m e ((β) (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm)) = (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m ν)) / (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaSchrodingerR0119.unary k m (ArithmeticThetaIdentitySectionsR0138.zeroIndex m hm))) := by
  intro k _ _ m hm he T M hM s hs rot scal inv ha ζ hζ eA eB hA hB β hβ hAβ hBβ
  obtain ⟨c, hc, _⟩ := geometric_intertwiner_rigidity k m hm he T M hM s hs
    rot scal inv ha ζ hζ eA eB hA hB β hβ hAβ hBβ
  obtain ⟨_, hframe, hvalues⟩ := generic_projective_evaluation k m hm he T M hM s hs
  refine ⟨hframe, ?_⟩
  intro e
  have hv (ν : Fin m) := GeometricBasisProjectiveValuesR0141.value_scaled
    k M s hs.1 m e c _ _ (hc.2 ν)
  constructor
  · rw [hv]
    exact mul_ne_zero hc.1 (hvalues e).1
  · intro ν
    rw [hv, hv, mul_div_mul_left _ _ hc.1]
    exact (hvalues e).2 ν

end ArithmeticThetaGeometricLiftsR0141
#print axioms ArithmeticThetaGeometricLiftsR0141.geometric_basis_projective_values
