module

public import CurveDegreeDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
export AlgebraicGeometry (Scheme Spec IsIntegral IsLocallyNoetherian LocallyOfFiniteType IsProper)

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

/-- The scalar map in the degree definition is the actual point morphism over the base. -/
lemma specMap_baseToResidue (X : Scheme.{u}) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Spec.map (CommRingCat.ofHom (baseToResidue k f x)) = X.fromSpecResidueField x ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
    X.Γevaluation x) = _
  apply (cancel_mono (Spec (CommRingCat.of k)).toSpecΓ).mp
  simp only [Spec.map_comp, Category.assoc]
  rw [SpecMap_ΓSpecIso_inv_toSpecΓ, Category.comp_id,
    Scheme.toSpecΓ_naturality f]
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc]
  simp only [Scheme.Γevaluation, Scheme.evaluation, Spec.map_comp, Category.assoc]

/-- Closed points have finite residue extensions for the structure morphism. -/
theorem baseToResidue_finite_of_closed
    (X : Scheme.{u}) (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    RingHom.Finite (baseToResidue k f x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (baseToResidue k f x))).mp
  rw [specMap_baseToResidue]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The transparent affine dimension premise bounds every point's coheight. -/
lemma coheight_le_one_of_charts (X : Scheme.{u}) [IsIntegral X]
    (hcurve : OneDimensionalCharts X) (x : X) : Order.coheight x ≤ 1 := by
  obtain ⟨U, hU, hx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial)
    (show IsOpen ((⊤ : X.Opens) : Set X) from isOpen_univ)
  obtain ⟨U, hU, rfl⟩ := hU
  let : Nonempty U := ⟨⟨x, hx.1⟩⟩
  let := hcurve U hU
  change IsAffineOpen U at hU
  have heq : Order.coheight x = (hU.primeIdealOf ⟨x, hx.1⟩).asIdeal.height := by
    have H := hU.fromSpec_primeIdealOf ⟨x, hx.1⟩
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx.1⟩) = x at H
    conv_lhs => rw [← H, coheight_eq_of_isOpenImmersion]
    exact (idealHeight_eq_coheight _ _).symm
  rw [heq]
  exact WithBot.coe_le_coe.mp ((Ideal.height_le_ringKrullDim_of_isPrime).trans
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 Γ(X,U))))

lemma isClosed_of_coheight_one (X : Scheme.{u}) [IsIntegral X]
    (hcurve : OneDimensionalCharts X) (x : X) (hx : Order.coheight x = 1) :
    IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  have heq : y = x := by
    by_contra hne
    have hstrict : y < x := ⟨hyx, fun hxy => hne (Specializes.antisymm hxy hyx).eq⟩
    have hlt := Order.coheight_strictAnti hstrict (show Order.coheight x < ⊤ by rw [hx]; exact ENat.one_lt_top)
    have hbound := coheight_le_one_of_charts X hcurve y
    rw [hx] at hlt
    exact (not_lt_of_ge hbound) hlt
  exact Set.mem_singleton_iff.mpr heq

/-- Codimension-one points carry positive residue weights. -/
theorem placeDegree_pos_of_coheight_one
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (x : X) (hx : Order.coheight x = 1) :
    0 < placeDegree k f x := by
  let : Algebra k (X.residueField x) := (baseToResidue k f x).toAlgebra
  have : Module.Finite k (X.residueField x) :=
    baseToResidue_finite_of_closed X k f x (isClosed_of_coheight_one X hcurve x hx)
  exact Module.finrank_pos

end ArithmeticThetaCurveDegree
