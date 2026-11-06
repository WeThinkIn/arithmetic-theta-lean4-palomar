import ConstantExtensionDefinitionsR0225
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaConstantExtensionR0225.PointedCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base)
variable {k : Type} [Field k]

local instance : Algebra.IsAlgebraic k (Omega k) := AlgebraicClosure.isAlgebraic k
local instance (K : (FieldStage k)) : Algebra.IsAlgebraic K (Omega k) :=
  Algebra.IsAlgebraic.tower_top (K := k) K

/-- A finitely generated algebra of algebraic constants is finite over the
prescribed intermediate field, and hence over the actual k-scalar action. -/
theorem finite_subalgebra (K0 : (FieldStage k)) [FiniteDimensional k K0]
    (T : Subalgebra K0 (Omega k)) (hT : T.FG) : FiniteDimensional k T := by
  letI : Algebra.FiniteType K0 T := T.fg_iff_finiteType.mp hT
  letI : Algebra.IsIntegral K0 T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (R := K0) (x : (Omega k))).isIntegral⟩
  letI : Module.Finite K0 T := Algebra.IsIntegral.finite
  exact Module.Finite.trans K0 T

/-- The algebraic subalgebra already is a field, with precisely its given
embedding into the fixed algebraic closure. -/
def fieldOfSubalgebra (K0 : (FieldStage k)) (T : Subalgebra K0 (Omega k)) : (FieldStage k) :=
  Subalgebra.IsAlgebraic.toIntermediateField
    (S := T.restrictScalars k) (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)

theorem le_fieldOfSubalgebra (K0 : (FieldStage k)) (T : Subalgebra K0 (Omega k)) :
    K0 ≤ fieldOfSubalgebra K0 T := by
  intro x hx
  exact T.algebraMap_mem ⟨x, hx⟩

/-- Finite-presentation descent constructs an actual Cartesian scheme model.
The geometric-property and point bridges are separate subsequent steps. -/
theorem scheme_model (X : Curve (Omega k)) (K0 : (FieldStage k)) [FiniteDimensional k K0] :
    ∃ (K : (FieldStage k)), FiniteDimensional k K ∧ K0 ≤ K ∧
      ∃ (Y : Scheme) (f : Y ⟶ Base K) (p : X.space ⟶ Y),
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
          IsPullback p X.map f (constantMap K) := by
  letI := X.proper
  letI := X.smooth
  obtain ⟨T, hT, _, Y, f, p, hf, hqc, hqs, hp⟩ :=
    exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := K0) X.map ∅
  refine ⟨fieldOfSubalgebra K0 T, ?_, le_fieldOfSubalgebra K0 T, Y, f, p,
    hf, hqc, hqs, hp⟩
  exact finite_subalgebra K0 T hT

/-- Curve properties descend along the specified extension of fields. -/
def modelOfCartesian (X : Curve (Omega k)) (K : (FieldStage k))
    (Y : Scheme) (f : Y ⟶ Base K) (p : X.space ⟶ Y)
    (hp : IsPullback p X.map f (constantMap K)) : Model X K := by
  haveI : Surjective (constantMap K) :=
    ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Flat (constantMap K) := inferInstance
  haveI : QuasiCompact (constantMap K) := by
    unfold constantMap
    infer_instance
  haveI := X.proper
  haveI := X.smooth
  haveI := X.geometricallyIntegral
  haveI : MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact
  exact ⟨⟨Y, f,
    MorphismProperty.of_isPullback_of_descendsAlong hp.flip
      (show (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
        (constantMap K) from ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩) X.proper,
    SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective 1 hp.flip,
    GeometricallyIntegral.of_isPullback_of_geometricallyIntegral f X.map p hp⟩, p, hp⟩

theorem curve_model (X : Curve (Omega k)) (K0 : (FieldStage k)) [FiniteDimensional k K0] :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧ Nonempty (Model X K) := by
  obtain ⟨K, hK, hle, Y, f, p, _, _, _, hp⟩ := scheme_model X K0
  exact ⟨K, hK, hle, ⟨modelOfCartesian X K Y f p hp⟩⟩

/-- Descend a whole finite family of sections, keeping their actual comparison
maps. No distinctness or nonemptiness assumption is used. -/
theorem points_over_model (X : Curve (Omega k)) (K : (FieldStage k)) [FiniteDimensional k K]
    (M : Model X K) (s : ℕ) (x : Fin s → (Base (Omega k) ⟶ X.space))
    (hx : ∀ i, x i ≫ X.map = 𝟙 _) :
    ∃ K' : (FieldStage k), FiniteDimensional k K' ∧ K ≤ K' ∧
      ∃ (N : Model X K') (x0 : Fin s → (Base K' ⟶ N.curve.space)),
        ∀ i, x0 i ≫ N.curve.map = 𝟙 _ ∧ constantMap K' ≫ x0 i = x i ≫ N.projection := by
  let f := M.curve.map
  let c := constantMap K
  let e := M.cartesian.isoPullback
  haveI := M.curve.smooth
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 M.curve.map
  haveI : LocallyOfFinitePresentation f := inferInstance
  let g : Fin s → (pullback (𝟙 (Base K)) c ⟶ pullback f c) :=
    fun i => pullback.snd _ _ ≫ x i ≫ e.hom
  have hg (i) : g i ≫ pullback.snd f c = pullback.snd (𝟙 (Base K)) c := by
    simp [g, e, f, c, Category.assoc, hx]
  obtain ⟨T, hT, _, g0, hg0, hcomp⟩ :=
    exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := K) (A := (Omega k)) (fun _ : Fin s => 𝟙 (Base K))
      (fun _ : Fin s => f) g hg ∅
  let K' := fieldOfSubalgebra K T
  let b : Base K' ⟶ Base K := Spec.map (CommRingCat.ofHom (algebraMap K T))
  let c' : Base (Omega k) ⟶ Base K' := constantMap K'
  have hbc : c' ≫ b = c := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let q1 : pullback (𝟙 (Base K)) c ⟶ pullback (𝟙 (Base K)) b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c') (by
      rw [Category.assoc, hbc, pullback.condition])
  let q2 : pullback f c ⟶ pullback f b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c') (by
      rw [Category.assoc, hbc, pullback.condition])
  have hc (i) : q1 ≫ g0 i = g i ≫ q2 :=
    hcomp i q1 q2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  let j : Base K' ⟶ pullback (𝟙 (Base K)) b :=
    pullback.lift b (𝟙 _) (by simp)
  let jΩ : Base (Omega k) ⟶ pullback (𝟙 (Base K)) c :=
    pullback.lift c (𝟙 _) (by simp)
  have hj : c' ≫ j = jΩ ≫ q1 := by
    apply pullback.hom_ext <;> simp [j, jΩ, q1, hbc, Category.id_comp]
    exact (Category.id_comp c').symm
  let p : X.space ⟶ pullback f b := e.hom ≫ q2
  have hp1 : p ≫ pullback.fst f b = M.projection := by simp [p, q2, e, f, c, Category.assoc]
  have hp2 : p ≫ pullback.snd f b = X.map ≫ c' := by simp [p, q2, e, f, c, Category.assoc]
  have hp : IsPullback p X.map (pullback.snd f b) c' := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f b) _ hp2 (IsPullback.of_hasPullback f b)
    rw [hp1, hbc]
    exact M.cartesian
  let N := modelOfCartesian X K' (pullback f b) (pullback.snd f b) p hp
  refine ⟨K', finite_subalgebra K T hT, le_fieldOfSubalgebra K T, N,
    fun i => j ≫ g0 i, ?_⟩
  intro i
  constructor
  · change (j ≫ g0 i) ≫ pullback.snd f b = 𝟙 _
    rw [Category.assoc, hg0]
    exact pullback.lift_snd _ _ _
  · change c' ≫ (j ≫ g0 i) = x i ≫ p
    rw [← Category.assoc, hj, Category.assoc, hc]
    simp [g, jΩ, p, Category.assoc, Category.id_comp]
    exact Category.id_comp (x i ≫ e.hom ≫ q2)

end ArithmeticThetaConstantExtensionR0225.PointedCurve

namespace ArithmeticThetaConstantExtensionR0225
open CategoryTheory
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Base)

/-- Every prescribed finite family of points on the given curve descends to
one finite intermediate extension of k containing the prescribed stage. -/
theorem pointed_curve_constant_extension
    (k : Type) [Field k] [CharZero k]
    (X : Curve (Omega k)) (K0 : (FieldStage k)) (hK0 : FiniteDimensional k K0)
    (s : ℕ) (x : Fin s → (Base (Omega k) ⟶ X.space))
    (hx : ∀ i, x i ≫ X.map = 𝟙 _) :
    ∃ K : (FieldStage k), FiniteDimensional k K ∧ K0 ≤ K ∧
      ∃ (M : Model X K) (x0 : Fin s → (Base K ⟶ M.curve.space)),
        ∀ i, x0 i ≫ M.curve.map = 𝟙 _ ∧ constantMap K ≫ x0 i = x i ≫ M.projection := by
  letI := hK0
  obtain ⟨K, hK, hle, ⟨M⟩⟩ := PointedCurve.curve_model X K0
  letI := hK
  obtain ⟨K', hK', hle', N, x0, hx0⟩ := PointedCurve.points_over_model X K M s x hx
  exact ⟨K', hK', hle.trans hle', N, x0, hx0⟩

end ArithmeticThetaConstantExtensionR0225

#print axioms ArithmeticThetaConstantExtensionR0225.pointed_curve_constant_extension
