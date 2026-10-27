import FiniteFieldModelsDefinitionsR0221
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic

/-! Finite affine frame data for the line-model construction.
The finite-field descent theorem remains to be constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections

namespace ArithmeticThetaFiniteFieldModelsR0221.LineFiniteModel

universe u

/-- Restrict a natural frame to a smaller open. -/
def restrictFrame {X : Scheme.{u}} {J : X.Modules} {U V : X.Opens}
    (e : LocalFrame X J U) (hVU : V ≤ U) : LocalFrame X J V where
  equiv W hWV := e.equiv W (hWV.trans hVU)
  naturality W Z hZW hWV a := e.naturality W Z hZW (hWV.trans hVU) a

/-- Finite actual affine frames, including the covering and nonemptiness proofs. -/
structure FiniteAffineFrames (X : Scheme.{u}) (J : X.Modules) where
  indices : Finset X
  opens : indices → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  nonempty : ∀ i, Nonempty (opens i)
  frame : ∀ i, LocalFrame X J (opens i)
  covers : ∀ x : X, ∃ i, x ∈ opens i

/-- Compactness makes the affine local trivialization data finite. -/
theorem exists_finiteAffineFrames (X : Scheme.{u}) [CompactSpace X]
    (J : X.Modules) (hJ : IsLineBundle X J) : Nonempty (FiniteAffineFrames X J) := by
  classical
  have hlocal (x : X) : ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (LocalFrame X J V) := by
    obtain ⟨U, hxU, ⟨e⟩⟩ := hJ x
    obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
    exact ⟨V, hxV, hV, ⟨restrictFrame (localFrameOfIso X J U e) hVU⟩⟩
  choose U hmem haff hframe using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  refine ⟨{
    indices := S
    opens := fun i ↦ U i.val
    affine := fun i ↦ haff i.val
    nonempty := fun i ↦ ⟨⟨i.val, hmem i.val⟩⟩
    frame := fun i ↦ (hframe i.val).some
    covers := ?_ }⟩
  intro x
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

/-- Apply compactness using the given proper structure map of the curve. -/
theorem curve_finiteAffineFrames (X : Curve Omega) (J : X.space.Modules)
    (hJ : IsLineBundle X.space J) : Nonempty (FiniteAffineFrames X.space J) := by
  let := X.proper
  let : CompactSpace X.space := QuasiCompact.compactSpace_of_compactSpace X.map
  exact exists_finiteAffineFrames X.space J hJ

/-- Properness over the affine field spectrum gives separatedness of the curve. -/
theorem curve_separated (X : Curve Omega) : X.space.IsSeparated := by
  let := X.proper
  exact HasAffineProperty.iff_of_isAffine.mp (inferInstance : IsSeparated X.map)

namespace FiniteAffineFrames

variable {X : Scheme.{u}} {J : X.Modules} (C : FiniteAffineFrames X J)

/-- Transition functions are actual units in the overlap section rings. -/
def overlap (i j : C.indices) : Γ(X, C.opens i ⊓ C.opens j)ˣ :=
  transitionUnit ((C.frame i).equiv _ inf_le_left) ((C.frame j).equiv _ inf_le_right)

/-- The accepted transition restriction and cocycle laws on any triple subopen. -/
theorem overlap_cocycle (i j k : C.indices) (W : X.Opens)
    (hi : W ≤ C.opens i) (hj : W ≤ C.opens j) (hk : W ≤ C.opens k) :
    X.presheaf.map (homOfLE (le_inf hi hk)).op (C.overlap i k) =
      X.presheaf.map (homOfLE (le_inf hi hj)).op (C.overlap i j) *
        X.presheaf.map (homOfLE (le_inf hj hk)).op (C.overlap j k) := by
  change X.presheaf.map (homOfLE (le_inf hi hk)).op
      (transition ((C.frame i).equiv _ inf_le_left) ((C.frame k).equiv _ inf_le_right)) =
    X.presheaf.map (homOfLE (le_inf hi hj)).op
      (transition ((C.frame i).equiv _ inf_le_left) ((C.frame j).equiv _ inf_le_right)) *
    X.presheaf.map (homOfLE (le_inf hj hk)).op
      (transition ((C.frame j).equiv _ inf_le_left) ((C.frame k).equiv _ inf_le_right))
  rw [transition_restrict, transition_restrict, transition_restrict]
  exact transition_cocycle _ _ _

/-- Affine intersections are available on separated schemes. -/
theorem overlap_affine [X.IsSeparated] (i j : C.indices) :
    IsAffineOpen (C.opens i ⊓ C.opens j) := (C.affine i).inf (C.affine j)

/-- The actual local basis change, on every subopen of the intersection. -/
theorem frame_change (i j : C.indices) (W : X.Opens)
    (hi : W ≤ C.opens i) (hj : W ≤ C.opens j) (a : Γ(X, W)) :
    (C.frame j).equiv W hj a = (C.frame i).equiv W hi
      (X.presheaf.map (homOfLE (le_inf hi hj)).op (C.overlap i j) * a) := by
  change (C.frame j).equiv W hj a = (C.frame i).equiv W hi
    (X.presheaf.map (homOfLE (le_inf hi hj)).op
      (transition ((C.frame i).equiv _ inf_le_left)
        ((C.frame j).equiv _ inf_le_right)) * a)
  rw [transition_restrict]
  exact transition_apply _ _ a

end FiniteAffineFrames

/-- A finite list of algebraic coefficients fits in a finite extension containing
the prescribed field, with its actual intermediate-field rational action. -/
theorem finite_coefficient_stage (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (s : Finset Omega) : ∃ K : FieldStage,
      FiniteDimensional ℚ K ∧ K0 ≤ K ∧ ∀ a ∈ s, a ∈ K := by
  have : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  let E := IntermediateField.adjoin ℚ (s : Set Omega)
  have : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin
    (fun a _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).isIntegral)
  refine ⟨K0 ⊔ E, inferInstance, le_sup_left, ?_⟩
  intro a ha
  exact (show E ≤ K0 ⊔ E from le_sup_right)
    (IntermediateField.subset_adjoin ℚ (s : Set Omega) ha)

/-- All polynomials in a finite family are defined over a common finite stage.
The comparison uses the inclusion of that intermediate field into `Omega`. -/
theorem finite_polynomial_stage {σ ι : Type} [Fintype ι]
    (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (p : ι → MvPolynomial σ Omega) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ K0 ≤ K ∧
      ∃ q : ι → MvPolynomial σ K,
        ∀ i, MvPolynomial.map K.subtype (q i) = p i := by
  classical
  let s := Finset.univ.biUnion (fun i ↦ (p i).coeffs)
  obtain ⟨K, hK, hK0, hs⟩ := finite_coefficient_stage K0 s
  have hp (i : ι) : p i ∈ Set.range (MvPolynomial.map K.subtype) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro a ha
    exact ⟨⟨a, hs a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩)⟩, rfl⟩
  choose q hq using hp
  exact ⟨K, hK, hK0, q, hq⟩

/-- Scalar-extension maps compose using the given intermediate-field inclusion. -/
theorem constantMap_extensionMap {K0 K : FieldStage} (h : K0 ≤ K) :
    constantMap K ≫ extensionMap h = constantMap K0 := by
  unfold constantMap extensionMap
  rw [← Spec.map_comp]
  rfl

/-- Enlarge the given curve model by its actual scheme fiber product. -/
def enlargedCurve {X : Curve Omega} {K0 K : FieldStage}
    (M : Model X K0) (h : K0 ≤ K) : Curve K where
  space := pullback M.curve.map (extensionMap h)
  map := pullback.snd M.curve.map (extensionMap h)
  proper := MorphismProperty.pullback_snd _ _ M.curve.proper
  smooth := by
    let := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd _ _ M.curve.smooth
  geometricallyIntegral := MorphismProperty.pullback_snd _ _ M.curve.geometricallyIntegral

/-- The original `Omega`-curve is the scalar extension of the enlarged model. -/
def enlargedModel {X : Curve Omega} {K0 K : FieldStage}
    (M : Model X K0) (h : K0 ≤ K) : Model X K := by
  let t := IsPullback.of_hasPullback M.curve.map (extensionMap h)
  have s : IsPullback M.projection X.map M.curve.map
      (constantMap K ≫ extensionMap h) := by
    rw [constantMap_extensionMap h]
    exact M.cartesian
  exact {
    curve := enlargedCurve M h
    projection := t.lift M.projection (X.map ≫ constantMap K)
      (by rw [s.w, Category.assoc])
    cartesian := s.of_right' t }

/-- The enlargement satisfies every comparison field of the frozen refinement record. -/
def modelRefinement {X : Curve Omega} {K0 K : FieldStage}
    (M : Model X K0) (h : K0 ≤ K) : Refinement M (enlargedModel M h) where
  inclusion := h
  map := pullback.fst M.curve.map (extensionMap h)
  cartesian := IsPullback.of_hasPullback M.curve.map (extensionMap h)
  comparison := (IsPullback.of_hasPullback M.curve.map (extensionMap h)).lift_fst _ _ _

/-- Coefficient enlargement and geometric enlargement use the same finite field. -/
theorem model_with_polynomial_coefficients {σ ι : Type} [Fintype ι]
    {X : Curve Omega} {K0 : FieldStage} [FiniteDimensional ℚ K0]
    (M : Model X K0) (p : ι → MvPolynomial σ Omega) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧
      ∃ N : Model X K, Nonempty (Refinement M N) ∧
        ∃ q : ι → MvPolynomial σ K, ∀ i, MvPolynomial.map K.subtype (q i) = p i := by
  obtain ⟨K, hK, hK0, q, hq⟩ := finite_polynomial_stage K0 p
  exact ⟨K, hK, enlargedModel M hK0, ⟨modelRefinement M hK0⟩, q, hq⟩

section TensorStages

open TensorProduct

/-- The scalar extension map uses precisely the supplied field inclusion. -/
def tensorStageMap {K0 K : FieldStage} (h : K0 ≤ K)
    (A : Type) [CommRing A] [Algebra K0 A] :
    letI := (IntermediateField.inclusion h).toAlgebra
    K ⊗[K0] A →ₐ[K0] Omega ⊗[K0] A := by
  letI := (IntermediateField.inclusion h).toAlgebra
  let f : K →ₐ[K0] Omega := { K.subtype with commutes' := fun _ ↦ rfl }
  exact Algebra.TensorProduct.map f (AlgHom.id K0 A)

/-- Every finite family of elements of a scalar-extended chart ring comes from
a common finite field enlargement. This does not assume a finite presentation. -/
theorem finite_dependent_tensor_stage {ι : Type} [Fintype ι]
    (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K0 (A i)]
    (t : ∀ i, Omega ⊗[K0] A i) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      letI := (IntermediateField.inclusion h).toAlgebra
      ∃ q : ∀ i, K ⊗[K0] A i, ∀ i, tensorStageMap h (A i) (q i) = t i := by
  classical
  choose n c a ht using fun i ↦ TensorProduct.exists_sum_tmul_eq (t i)
  let s := Finset.univ.biUnion (fun i ↦ Finset.univ.image (c i))
  obtain ⟨K, hK, hK0, hs⟩ := finite_coefficient_stage K0 s
  let := (IntermediateField.inclusion hK0).toAlgebra
  have hc (i : ι) (j : Fin (n i)) : c i j ∈ K :=
    hs _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
  refine ⟨K, hK, hK0, fun i ↦ ∑ j, (⟨c i j, hc i j⟩ : K) ⊗ₜ[K0] a i j, ?_⟩
  intro i
  rw [map_sum]
  change (∑ j, c i j ⊗ₜ[K0] a i j) = t i
  exact (ht i).symm

/-- The single-chart specialization of simultaneous tensor descent. -/
theorem finite_tensor_stage {ι : Type} [Fintype ι]
    (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (A : Type) [CommRing A] [Algebra K0 A]
    (t : ι → Omega ⊗[K0] A) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      letI := (IntermediateField.inclusion h).toAlgebra
      ∃ q : ι → K ⊗[K0] A, ∀ i, tensorStageMap h A (q i) = t i :=
  finite_dependent_tensor_stage K0 (fun _ ↦ A) t

/-- Scalar extension of a chart along a field inclusion is injective. -/
theorem tensorStageMap_injective {K0 K : FieldStage} (h : K0 ≤ K)
    (A : Type) [CommRing A] [Algebra K0 A] :
    Function.Injective (tensorStageMap h A) := by
  let := (IntermediateField.inclusion h).toAlgebra
  let f : K →ₐ[K0] Omega := { K.subtype with commutes' := fun _ ↦ rfl }
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    f.toLinearMap Subtype.val_injective

/-- A finite family of units, including their inverses, descends simultaneously
to a chart ring over a finite field. Inverse relations hold already at that stage. -/
theorem finite_tensor_unit_stage {ι : Type} [Fintype ι]
    (K0 : FieldStage) [FiniteDimensional ℚ K0]
    (A : Type) [CommRing A] [Algebra K0 A]
    (t : ι → (Omega ⊗[K0] A)ˣ) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      letI := (IntermediateField.inclusion h).toAlgebra
      ∃ q : ι → (K ⊗[K0] A)ˣ,
        ∀ i, Units.map (tensorStageMap h A).toMonoidHom (q i) = t i := by
  classical
  let values : ι × Bool → Omega ⊗[K0] A := fun (i, b) ↦
    if b then ↑(t i)⁻¹ else ↑(t i)
  obtain ⟨K, hK, hK0, q, hq⟩ := finite_tensor_stage K0 A values
  let := (IntermediateField.inclusion hK0).toAlgebra
  have hv (i : ι) : tensorStageMap hK0 A (q (i, false)) = t i := hq (i, false)
  have hi (i : ι) : tensorStageMap hK0 A (q (i, true)) = ↑(t i)⁻¹ := hq (i, true)
  let u (i : ι) : (K ⊗[K0] A)ˣ := {
    val := q (i, false)
    inv := q (i, true)
    val_inv := (tensorStageMap_injective hK0 A) (by simp [map_mul, hv, hi])
    inv_val := (tensorStageMap_injective hK0 A) (by simp [map_mul, hv, hi]) }
  refine ⟨K, hK, hK0, u, ?_⟩
  intro i
  exact Units.ext (hv i)

end TensorStages

/-- The projection of any field model is affine, by its specified Cartesian square. -/
theorem model_projection_affine {X : Curve Omega} {K0 : FieldStage}
    (M : Model X K0) : IsAffineHom M.projection :=
  MorphismProperty.of_isPullback M.cartesian.flip (inferInstance : IsAffineHom (constantMap K0))

/-- A finite frame cover by principal opens inside scalar extensions of actual
affine opens of the given model. The principal equations remain section-ring
elements over `Omega` until the scalar-extension comparison is constructed. -/
structure RelativePrincipalFrames {X : Curve Omega} {K0 : FieldStage}
    (M : Model X K0) (J : X.space.Modules) where
  indices : Finset X.space
  baseOpens : indices → M.curve.space.Opens
  baseAffine : ∀ i, IsAffineOpen (baseOpens i)
  equation : ∀ i, Γ(X.space, M.projection ⁻¹ᵁ baseOpens i)
  frame : ∀ i, LocalFrame X.space J (X.space.basicOpen (equation i))
  nonempty : ∀ i, Nonempty (X.space.basicOpen (equation i))
  covers : ∀ x : X.space, ∃ i, x ∈ X.space.basicOpen (equation i)

/-- Choose finitely many principal trivializations adapted to the supplied model. -/
theorem exists_relativePrincipalFrames {X : Curve Omega} {K0 : FieldStage}
    (M : Model X K0) (J : X.space.Modules) (hJ : IsLineBundle X.space J) :
    Nonempty (RelativePrincipalFrames M J) := by
  classical
  let := X.proper
  let : CompactSpace X.space := QuasiCompact.compactSpace_of_compactSpace X.map
  let := model_projection_affine M
  have hx (x : X.space) : ∃ U : M.curve.space.Opens, IsAffineOpen U ∧
      ∃ f : Γ(X.space, M.projection ⁻¹ᵁ U), x ∈ X.space.basicOpen f ∧
        Nonempty (LocalFrame X.space J (X.space.basicOpen f)) := by
    obtain ⟨V, hxV, ⟨e⟩⟩ := hJ x
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp
      M.curve.space.isBasis_affineOpens (show M.projection x ∈ (⊤ : M.curve.space.Opens) from trivial)
    obtain ⟨f, hf, hxf⟩ := (hU.preimage M.projection).exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact ⟨U, hU, f, hxf, ⟨restrictFrame (localFrameOfIso X.space J V e) hf⟩⟩
  choose U hU f hxf hf using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (X.space.basicOpen (f x) : Set X.space))
    (fun x ↦ (X.space.basicOpen (f x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hxf x⟩)
  refine ⟨{
    indices := S
    baseOpens := fun i ↦ U i.val
    baseAffine := fun i ↦ hU i.val
    equation := fun i ↦ f i.val
    frame := fun i ↦ (hf i.val).some
    nonempty := fun i ↦ ⟨⟨i.val, hxf i.val⟩⟩
    covers := ?_ }⟩
  intro x
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

section AffineBaseChange

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {Y Z : Scheme} (p : Z ⟶ Y) (y : Y ⟶ Base R) (z : Z ⟶ Base S)

/-- Scalars on an affine chart are induced by its actual structure morphism. -/
def chartScalarMap : CommRingCat.of R ⟶ Γ(Y, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ y.appTop

/-- The chart algebra retains the structure morphism, not an arbitrary action. -/
@[instance_reducible] def chartAlgebra : Algebra R Γ(Y, ⊤) := (chartScalarMap y).hom.toAlgebra

/-- An affine Cartesian geometric square gives the actual scalar pushout of rings. -/
theorem affineBaseChange_pushout [IsAffine Y]
    (h : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    IsPushout (CommRingCat.ofHom (algebraMap R S)) (chartScalarMap y)
      (chartScalarMap z) p.appTop := by
  have ht := (isPushout_appTop_of_isPullback h).flip
  exact ht.of_iso (Scheme.ΓSpecIso (CommRingCat.of R))
    (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _) (Iso.refl _)
    (Scheme.ΓSpecIso_naturality _)
    (by simp [chartScalarMap])
    (by simp [chartScalarMap])
    (by simp)

/-- The chart scalar-extension ring isomorphism obtained from the specified
Cartesian square and the tensor-product universal property. -/
def affineBaseChangeRingIso [IsAffine Y]
    (h : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI := chartAlgebra y
    CommRingCat.of (TensorProduct R S Γ(Y, ⊤)) ≅ Γ(Z, ⊤) := by
  letI := chartAlgebra y
  exact (CommRingCat.isPushout_tensorProduct R S Γ(Y, ⊤)).isoIsPushout _ _
    (affineBaseChange_pushout p y z h)

/-- On each tensor factor the comparison is exactly the prescribed geometric map. -/
theorem affineBaseChangeRingIso_left [IsAffine Y]
    (h : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI := chartAlgebra y
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
      (affineBaseChangeRingIso p y z h).hom = chartScalarMap z := by
  let := chartAlgebra y
  exact (CommRingCat.isPushout_tensorProduct R S Γ(Y, ⊤)).inl_isoIsPushout_hom _ _ _

theorem affineBaseChangeRingIso_right [IsAffine Y]
    (h : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI := chartAlgebra y
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
      (affineBaseChangeRingIso p y z h).hom = p.appTop := by
  let := chartAlgebra y
  exact (CommRingCat.isPushout_tensorProduct R S Γ(Y, ⊤)).inr_isoIsPushout_hom _ _ _

/-- Restrict the actual Cartesian square to an affine chart of its lower model. -/
theorem restrictedCartesian
    (h : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (U : Y.Opens) :
    IsPullback (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ z) (U.ι ≫ y)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_morphismRestrict p U).paste_vert h

end AffineBaseChange

section AffineBaseChangeNaturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]
  {Y Z W : Scheme} [IsAffine Y]
  (p : Z ⟶ Y) (q : W ⟶ Y) (y : Y ⟶ Base R)
  (z : Z ⟶ Base S) (w : W ⟶ Base T)
  (hp : IsPullback p z y (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hq : IsPullback q w y (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  (a : S →ₐ[R] T) (g : W ⟶ Z)
  (hg : g ≫ p = q) (ha : g ≫ z = w ≫ Spec.map (CommRingCat.ofHom a.toRingHom))

include ha in
/-- Scalar maps commute because the scheme morphism lies over the given ring map. -/
theorem chartScalarMap_naturality :
    chartScalarMap z ≫ g.appTop = CommRingCat.ofHom a.toRingHom ≫ chartScalarMap w := by
  unfold chartScalarMap
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, ha, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

include hg ha in
/-- Tensor chart comparisons are natural under the actual scalar-extension map. -/
theorem affineBaseChangeRingIso_naturality :
    letI := chartAlgebra y
    CommRingCat.ofHom (Algebra.TensorProduct.map a
      (AlgHom.id R Γ(Y, ⊤))).toRingHom ≫ (affineBaseChangeRingIso q y w hq).hom =
      (affineBaseChangeRingIso p y z hp).hom ≫ g.appTop := by
  let := chartAlgebra y
  let m := CommRingCat.ofHom (Algebra.TensorProduct.map a
    (AlgHom.id R Γ(Y, ⊤))).toRingHom
  have hleft : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ m =
      CommRingCat.ofHom a.toRingHom ≫
        CommRingCat.ofHom (R := T) (S := TensorProduct R T Γ(Y, ⊤))
          Algebra.TensorProduct.includeLeftRingHom := by ext; rfl
  have hright : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ m =
      CommRingCat.ofHom (R := Γ(Y, ⊤)) (S := TensorProduct R T Γ(Y, ⊤))
        Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change a 1 ⊗ₜ[R] x = (1 : T) ⊗ₜ[R] x
    rw [map_one]
  apply (CommRingCat.isPushout_tensorProduct R S Γ(Y, ⊤)).hom_ext
  · change _ ≫ (m ≫ _) = _
    rw [← Category.assoc, hleft, Category.assoc, affineBaseChangeRingIso_left,
      ← Category.assoc, affineBaseChangeRingIso_left]
    exact (chartScalarMap_naturality z w a g ha).symm
  · change _ ≫ (m ≫ _) = _
    rw [← Category.assoc, hright, affineBaseChangeRingIso_right,
      ← Category.assoc, affineBaseChangeRingIso_right, ← Scheme.Hom.comp_appTop, hg]

end AffineBaseChangeNaturality

/-- The actual ring comparison on each model affine chart. -/
def modelChartIso {X : Curve Omega} {K0 : FieldStage} (M : Model X K0)
    (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra (U.ι ≫ M.curve.map)
    CommRingCat.of (TensorProduct K0 Omega Γ(U.toScheme, ⊤)) ≅
      Γ(X.space, M.projection ⁻¹ᵁ U) := by
  letI := chartAlgebra (U.ι ≫ M.curve.map)
  letI : IsAffine U.toScheme := hU
  exact affineBaseChangeRingIso (M.projection ∣_ U) (U.ι ≫ M.curve.map)
    ((M.projection ⁻¹ᵁ U).ι ≫ X.map)
    (restrictedCartesian M.projection M.curve.map X.map M.cartesian U) ≪≫
      (M.projection ⁻¹ᵁ U).topIso

/-- The analogous chart comparison for the chosen finite enlargement. -/
def refinementChartIso {X : Curve Omega} {K0 K : FieldStage} (M : Model X K0)
    (h : K0 ≤ K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := (IntermediateField.inclusion h).toAlgebra
    letI := chartAlgebra (U.ι ≫ M.curve.map)
    CommRingCat.of (TensorProduct K0 K Γ(U.toScheme, ⊤)) ≅
      Γ((enlargedModel M h).curve.space, (modelRefinement M h).map ⁻¹ᵁ U) := by
  letI := (IntermediateField.inclusion h).toAlgebra
  letI := chartAlgebra (U.ι ≫ M.curve.map)
  letI : IsAffine U.toScheme := hU
  exact affineBaseChangeRingIso ((modelRefinement M h).map ∣_ U) (U.ι ≫ M.curve.map)
    (((modelRefinement M h).map ⁻¹ᵁ U).ι ≫ (enlargedModel M h).curve.map)
    (restrictedCartesian (modelRefinement M h).map M.curve.map
      (enlargedModel M h).curve.map (modelRefinement M h).cartesian U) ≪≫
      ((modelRefinement M h).map ⁻¹ᵁ U).topIso

section RefinementCharts

variable {X : Curve Omega} {K0 K : FieldStage} {M : Model X K0} {N : Model X K}
  (E : Refinement M N) (U : M.curve.space.Opens)

/-- The equality of chart preimages is forced by the refinement triangle. -/
theorem refinement_preimage_eq :
    M.projection ⁻¹ᵁ U = N.projection ⁻¹ᵁ (E.map ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, E.comparison]

/-- Restrict the original model projection to the corresponding refinement chart. -/
def refinementChartMap : (M.projection ⁻¹ᵁ U).toScheme ⟶ (E.map ⁻¹ᵁ U).toScheme :=
  N.projection.resLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
    (refinement_preimage_eq E U).le

theorem refinementChartMap_base :
    refinementChartMap E U ≫ (E.map ∣_ U) = M.projection ∣_ U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι]
  change N.projection.resLE _ _ _ ≫ _ ≫ _ = _
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, E.comparison,
    morphismRestrict_ι]

theorem refinementChartMap_scalar :
    refinementChartMap E U ≫ ((E.map ⁻¹ᵁ U).ι ≫ N.curve.map) =
      ((M.projection ⁻¹ᵁ U).ι ≫ X.map) ≫ constantMap K := by
  change N.projection.resLE _ _ _ ≫ _ ≫ _ = _
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, N.cartesian.w,
    Category.assoc]

theorem refinementChartMap_sections :
    (refinementChartMap E U).appTop ≫ (M.projection ⁻¹ᵁ U).topIso.hom =
      (E.map ⁻¹ᵁ U).topIso.hom ≫
        N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
          (refinement_preimage_eq E U).le :=
  (arrowResLEAppIso N.projection (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
    (refinement_preimage_eq E U).le).hom.w.symm

end RefinementCharts

/-- The two chart-ring isomorphisms intertwine the actual projection on sections
with the map induced by the field inclusion on tensor products. -/
theorem modelChartIso_naturality {X : Curve Omega} {K0 K : FieldStage}
    (M : Model X K0) (h : K0 ≤ K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := (IntermediateField.inclusion h).toAlgebra
    letI := chartAlgebra (U.ι ≫ M.curve.map)
    CommRingCat.ofHom (tensorStageMap h Γ(U.toScheme, ⊤)).toRingHom ≫
      (modelChartIso M U hU).hom =
    (refinementChartIso M h U hU).hom ≫
      (enlargedModel M h).projection.appLE ((modelRefinement M h).map ⁻¹ᵁ U)
        (M.projection ⁻¹ᵁ U) (refinement_preimage_eq (modelRefinement M h) U).le := by
  let := (IntermediateField.inclusion h).toAlgebra
  let := chartAlgebra (U.ι ≫ M.curve.map)
  let : IsAffine U.toScheme := hU
  let E := modelRefinement M h
  let a : K →ₐ[K0] Omega := { K.subtype with commutes' := fun _ ↦ rfl }
  have hn := affineBaseChangeRingIso_naturality
    (E.map ∣_ U) (M.projection ∣_ U) (U.ι ≫ M.curve.map)
    ((E.map ⁻¹ᵁ U).ι ≫ (enlargedModel M h).curve.map)
    ((M.projection ⁻¹ᵁ U).ι ≫ X.map)
    (restrictedCartesian E.map M.curve.map (enlargedModel M h).curve.map E.cartesian U)
    (restrictedCartesian M.projection M.curve.map X.map M.cartesian U)
    a (refinementChartMap E U) (refinementChartMap_base E U)
    (refinementChartMap_scalar E U)
  dsimp only [modelChartIso, refinementChartIso, Iso.trans_hom]
  rw [← Category.assoc]
  change (CommRingCat.ofHom (Algebra.TensorProduct.map a
    (AlgHom.id K0 Γ(U.toScheme, ⊤))).toRingHom ≫ _) ≫ _ = _
  rw [hn, Category.assoc, refinementChartMap_sections]
  rfl

/-- Finite sections on scalar-extended affine charts descend along the actual
projection of a common finite enlargement of the given curve model. -/
theorem finite_chart_section_stage {ι : Type} [Fintype ι]
    {X : Curve Omega} {K0 : FieldStage} [FiniteDimensional ℚ K0]
    (M : Model X K0) (U : ι → M.curve.space.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : ∀ i, Γ(X.space, M.projection ⁻¹ᵁ U i)) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      ∃ q : ∀ i, Γ((enlargedModel M h).curve.space, (modelRefinement M h).map ⁻¹ᵁ U i),
        ∀ i, (enlargedModel M h).projection.appLE
          ((modelRefinement M h).map ⁻¹ᵁ U i) (M.projection ⁻¹ᵁ U i)
          (refinement_preimage_eq (modelRefinement M h) (U i)).le (q i) = s i := by
  let A (i : ι) : Type := Γ((U i).toScheme, ⊤)
  let : ∀ i, Algebra K0 (A i) := fun i ↦ chartAlgebra ((U i).ι ≫ M.curve.map)
  let t (i : ι) : TensorProduct K0 Omega (A i) := (modelChartIso M (U i) (hU i)).inv (s i)
  obtain ⟨K, hK, h, q, hq⟩ := finite_dependent_tensor_stage K0 A t
  let := (IntermediateField.inclusion h).toAlgebra
  refine ⟨K, hK, h, fun i ↦ (refinementChartIso M h (U i) (hU i)).hom (q i), ?_⟩
  intro i
  have hn := congrArg (fun f ↦ f.hom (q i)) (modelChartIso_naturality M h (U i) (hU i))
  change (modelChartIso M (U i) (hU i)).hom (tensorStageMap h (A i) (q i)) = _ at hn
  rw [hq i] at hn
  exact hn.symm.trans (by exact
    ConcreteCategory.congr_hom (modelChartIso M (U i) (hU i)).inv_hom_id (s i))

/-- A field-model projection is surjective, including every point of the model. -/
theorem model_projection_surjective {X : Curve Omega} {K : FieldStage} (M : Model X K) :
    Surjective M.projection :=
  MorphismProperty.of_isPullback M.cartesian.flip (inferInstance : Surjective (constantMap K))

theorem refinement_map_affine {X : Curve Omega} {K0 K : FieldStage}
    {M : Model X K0} {N : Model X K} (E : Refinement M N) : IsAffineHom E.map :=
  MorphismProperty.of_isPullback E.cartesian.flip
    (inferInstance : IsAffineHom (extensionMap E.inclusion))

/-- Lifting a principal equation gives exactly the original principal open. -/
theorem lifted_basicOpen_preimage {X : Curve Omega} {K0 K : FieldStage}
    {M : Model X K0} {N : Model X K} (E : Refinement M N) (U : M.curve.space.Opens)
    (q : Γ(N.curve.space, E.map ⁻¹ᵁ U)) :
    N.projection ⁻¹ᵁ N.curve.space.basicOpen q =
      X.space.basicOpen (N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
        (refinement_preimage_eq E U).le q) := by
  rw [Scheme.basicOpen_appLE, refinement_preimage_eq E U]
  exact (inf_eq_right.mpr (N.projection.preimage_mono (N.curve.space.basicOpen_le q))).symm

/-- The finite principal frame cover descends as actual affine opens of a model,
with both the covering property and exact scalar-extension preimages proved. -/
theorem finite_principal_cover_stage {X : Curve Omega} {K0 : FieldStage}
    [FiniteDimensional ℚ K0] (M : Model X K0) (J : X.space.Modules)
    (C : RelativePrincipalFrames M J) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ (N : Model X K) (_ : Refinement M N),
      ∃ V : C.indices → N.curve.space.Opens,
        (∀ i, IsAffineOpen (V i)) ∧
        (∀ i, N.projection ⁻¹ᵁ V i = X.space.basicOpen (C.equation i)) ∧
        (∀ x : N.curve.space, ∃ i, x ∈ V i) := by
  classical
  obtain ⟨K, hK, h, q, hq⟩ :=
    finite_chart_section_stage M C.baseOpens C.baseAffine C.equation
  let N := enlargedModel M h
  let E := modelRefinement M h
  let V (i : C.indices) := N.curve.space.basicOpen (q i)
  let := refinement_map_affine E
  let := model_projection_surjective N
  have hV (i : C.indices) : N.projection ⁻¹ᵁ V i =
      X.space.basicOpen (C.equation i) := by
    change N.projection ⁻¹ᵁ N.curve.space.basicOpen (q i) = _
    rw [lifted_basicOpen_preimage E (C.baseOpens i), hq i]
  refine ⟨K, hK, N, E, V, fun i ↦ ((C.baseAffine i).preimage E.map).basicOpen (q i), hV, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := N.projection.surjective x
  obtain ⟨i, hi⟩ := C.covers y
  refine ⟨i, ?_⟩
  change y ∈ N.projection ⁻¹ᵁ V i
  rw [hV i]
  exact hi

/-- The chart-ring comparison identifies the original chart factor with the
actual map on its section ring. -/
theorem modelChartIso_right {X : Curve Omega} {K : FieldStage} (M : Model X K)
    (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra (U.ι ≫ M.curve.map)
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
      (modelChartIso M U hU).hom =
        U.topIso.hom ≫ M.projection.appLE U (M.projection ⁻¹ᵁ U) le_rfl := by
  let := chartAlgebra (U.ι ≫ M.curve.map)
  let : IsAffine U.toScheme := hU
  dsimp only [modelChartIso, Iso.trans_hom]
  rw [← Category.assoc, affineBaseChangeRingIso_right]
  have hh : (M.projection.resLE U (M.projection ⁻¹ᵁ U) le_rfl).appTop ≫
      (M.projection ⁻¹ᵁ U).topIso.hom =
      U.topIso.hom ≫ M.projection.appLE U (M.projection ⁻¹ᵁ U) le_rfl :=
    (arrowResLEAppIso M.projection U (M.projection ⁻¹ᵁ U) le_rfl).hom.w.symm
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hh

/-- Equality of sections of a model affine chart can be checked after extension
to `Omega`, using injectivity of the actual map on sections. -/
theorem model_chart_section_injective {X : Curve Omega} {K : FieldStage}
    (M : Model X K) (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    Function.Injective (M.projection.appLE U (M.projection ⁻¹ᵁ U) le_rfl) := by
  let := chartAlgebra (U.ι ≫ M.curve.map)
  let e := modelChartIso M U hU
  let j := (Algebra.TensorProduct.includeRight : Γ(U.toScheme, ⊤) →ₐ[K]
    TensorProduct K Omega Γ(U.toScheme, ⊤))
  have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective
    (algebraMap K Omega).injective
  have he (a : Γ(U.toScheme, ⊤)) : e.hom (j a) =
      M.projection.appLE U (M.projection ⁻¹ᵁ U) le_rfl (U.topIso.hom a) :=
    ConcreteCategory.congr_hom (modelChartIso_right M U hU) a
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).1
  apply hj
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [he, he]
  simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] using hab

/-- The same detection statement in the exact chart presentation used by a refinement. -/
theorem refinement_chart_section_injective {X : Curve Omega} {K0 K : FieldStage}
    {M : Model X K0} {N : Model X K} (E : Refinement M N)
    (U : M.curve.space.Opens) (hU : IsAffineOpen U) :
    Function.Injective (N.projection.appLE (E.map ⁻¹ᵁ U) (M.projection ⁻¹ᵁ U)
      (refinement_preimage_eq E U).le) := by
  let := refinement_map_affine E
  have hi (V : X.space.Opens) (he : V = N.projection ⁻¹ᵁ (E.map ⁻¹ᵁ U)) :
      Function.Injective (N.projection.appLE (E.map ⁻¹ᵁ U) V he.le) := by
    subst V
    exact model_chart_section_injective N _ (hU.preimage E.map)
  exact hi _ (refinement_preimage_eq E U)

/-- Simultaneously descend units on finitely many affine charts, including their
inverse equations and their comparisons under the actual geometric projection. -/
theorem finite_chart_unit_stage {ι : Type} [Fintype ι]
    {X : Curve Omega} {K0 : FieldStage} [FiniteDimensional ℚ K0]
    (M : Model X K0) (U : ι → M.curve.space.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s : ∀ i, Γ(X.space, M.projection ⁻¹ᵁ U i)ˣ) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧ ∃ h : K0 ≤ K,
      ∃ q : ∀ i, Γ((enlargedModel M h).curve.space, (modelRefinement M h).map ⁻¹ᵁ U i)ˣ,
        ∀ i, Units.map ((enlargedModel M h).projection.appLE
          ((modelRefinement M h).map ⁻¹ᵁ U i) (M.projection ⁻¹ᵁ U i)
          (refinement_preimage_eq (modelRefinement M h) (U i)).le).hom.toMonoidHom
          (q i) = s i := by
  classical
  let values : ∀ i : ι × Bool, Γ(X.space, M.projection ⁻¹ᵁ U i.1) := fun (i, b) ↦
    if b then ↑(s i)⁻¹ else ↑(s i)
  obtain ⟨K, hK, h, q, hq⟩ := finite_chart_section_stage M
    (fun i : ι × Bool ↦ U i.1) (fun i ↦ hU i.1) values
  let N := enlargedModel M h
  let E := modelRefinement M h
  let f (i : ι) := N.projection.appLE (E.map ⁻¹ᵁ U i) (M.projection ⁻¹ᵁ U i)
    (refinement_preimage_eq E (U i)).le
  have hv (i : ι) : f i (q (i, false)) = s i := hq (i, false)
  have hi (i : ι) : f i (q (i, true)) = ↑(s i)⁻¹ := hq (i, true)
  have hf (i : ι) : Function.Injective (f i) := refinement_chart_section_injective E (U i) (hU i)
  let u (i : ι) : Γ(N.curve.space, E.map ⁻¹ᵁ U i)ˣ := {
    val := q (i, false)
    inv := q (i, true)
    val_inv := hf i (by simp [map_mul, hv, hi])
    inv_val := hf i (by simp [map_mul, hv, hi]) }
  refine ⟨K, hK, h, u, ?_⟩
  intro i
  exact Units.ext (hv i)

section LibraryBridge

/-- The two notions of restriction are canonically isomorphic. -/
def overPullbackIso {Y : Scheme.{u}} (U : Y.Opens) (J : Y.Modules) :
    (Scheme.Modules.overEquiv U).functor.obj (SheafOfModules.over J U) ≅
      (Scheme.Modules.pullback U.ι).obj J :=
  (Scheme.Modules.overFunctorEquiv U).app J ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app J

/-- The frozen local-line condition agrees with the library's genuine invertible
sheaf predicate, through the canonical restriction equivalence. -/
theorem isLineBundle_iff_isInvertible (Y : Scheme.{u}) (J : Y.Modules) :
    IsLineBundle Y J ↔ Scheme.Modules.IsInvertible J := by
  constructor
  · intro h
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨U, hx, ⟨e⟩⟩ := h x
    exact ⟨U, hx, ⟨(overPullbackIso U J).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e.symm ≪≫
        U.sheafOfModulesEquivOverUnit Y.ringCatSheaf⟩⟩
  · intro h x
    obtain ⟨U, hx, ⟨e⟩⟩ := h.exists_trivialization x
    let e' := overPullbackIso U J ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm
    exact ⟨U, hx, ⟨((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso e').symm⟩⟩

end LibraryBridge

end ArithmeticThetaFiniteFieldModelsR0221.LineFiniteModel

namespace ArithmeticThetaFiniteFieldModelsR0221
open LineFiniteModel

/-- A line on a prescribed finite model descends after a finite enlargement. -/
theorem line_finite_model (X : Curve Omega) (K0 : FieldStage)
    (hK0 : FiniteDimensional ℚ K0) (M : Model X K0) (J : X.space.Modules)
    (hJ : IsLineBundle X.space J) :
    ∃ K : FieldStage, FiniteDimensional ℚ K ∧
      ∃ (M1 : Model X K) (_ : Refinement M M1) (J0 : M1.curve.space.Modules),
        IsLineBundle M1.curve.space J0 ∧
        Nonempty ((Scheme.Modules.pullback M1.projection).obj J0 ≅ J) := by
  letI := hK0
  letI := M.curve.proper
  let e := M.cartesian.isoPullback
  let L := (Scheme.Modules.pullback e.inv).obj J
  have hL : Scheme.Modules.IsInvertible L :=
    ((isLineBundle_iff_isInvertible X.space J).mp hJ).pullback e.inv
  obtain ⟨F, hF, J0, hJ0, hc⟩ :=
    Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
      K0 Omega M.curve.map L hL
  let K : FieldStage := F.restrictScalars ℚ
  have h : K0 ≤ K := by
    intro x hx
    exact F.algebraMap_mem (⟨x, hx⟩ : K0)
  letI := hF
  have hK : FiniteDimensional ℚ K := FiniteDimensional.trans ℚ K0 F
  let N := enlargedModel M h
  let E := modelRefinement M h
  let c := e.inv ≫ N.projection
  have hc₁ : c ≫ pullback.fst M.curve.map
      (Spec.map (CommRingCat.ofHom (algebraMap K0 F))) =
      pullback.fst M.curve.map (constantMap K0) := by
    change e.inv ≫ N.projection ≫ E.map = _
    rw [E.comparison]
    exact M.cartesian.isoPullback_inv_fst
  have hc₂ : c ≫ pullback.snd M.curve.map
      (Spec.map (CommRingCat.ofHom (algebraMap K0 F))) =
      pullback.snd M.curve.map (constantMap K0) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F Omega)) := by
    change e.inv ≫ N.projection ≫ N.curve.map = _
    rw [N.cartesian.w, ← Category.assoc]
    rw [M.cartesian.isoPullback_inv_snd]
    rfl
  obtain ⟨d⟩ := hc c hc₁ hc₂
  refine ⟨K, hK, N, E, J0, (isLineBundle_iff_isInvertible _ _).mpr hJ0, ⟨?_⟩⟩
  have hec : e.hom ≫ c = N.projection := by simp [c]
  exact ((Scheme.Modules.pullbackCongr hec).app J0).symm ≪≫
    ((Scheme.Modules.pullbackComp e.hom c).app J0).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso d ≪≫
    (Scheme.Modules.pullbackComp e.hom e.inv).app J ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app J ≪≫
    (Scheme.Modules.pullbackId X.space).app J

end ArithmeticThetaFiniteFieldModelsR0221
