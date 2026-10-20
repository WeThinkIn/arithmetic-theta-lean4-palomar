module

public import Mathlib

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ArithmeticThetaNormalization

universe u

noncomputable section

variable (X : Scheme.{u}) [IsIntegral X] (E : Type u) [Field E]
  [Algebra X.functionField E]

/-- The actual generic extension map, defined through the stalk at the generic point. -/
def genericExtensionMap : Spec (CommRingCat.of E) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField E)) ≫
    X.fromSpecStalk (genericPoint X)

instance genericExtensionMap_quasiCompact : QuasiCompact (genericExtensionMap X E) :=
  inferInstance

instance genericExtensionMap_quasiSeparated : QuasiSeparated (genericExtensionMap X E) :=
  inferInstance

theorem genericExtensionMap_apply (z : Spec (CommRingCat.of E)) :
    genericExtensionMap X E z = genericPoint X := by
  change X.fromSpecStalk (genericPoint X)
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField E)) z) = _
  have hz : Spec.map (CommRingCat.ofHom (algebraMap X.functionField E)) z =
      IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  rw [hz, Scheme.fromSpecStalk_closedPoint]

instance genericExtensionMap_dominant : IsDominant (genericExtensionMap X E) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hr : Set.range (genericExtensionMap X E) = {genericPoint X} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact genericExtensionMap_apply X E z
    · intro h
      subst x
      exact ⟨IsLocalRing.closedPoint E, genericExtensionMap_apply X E _⟩
  rw [hr]
  exact (genericPoint_spec X).def

/-- The actual relative normalization, using Mathlib's glued integral-closure scheme. -/
def extensionNormalization : Scheme.{u} := (genericExtensionMap X E).normalization

abbrev extensionToNormalization : Spec (CommRingCat.of E) ⟶ extensionNormalization X E :=
  (genericExtensionMap X E).toNormalization

abbrev extensionFromNormalization : extensionNormalization X E ⟶ X :=
  (genericExtensionMap X E).fromNormalization

theorem extensionNormalization_factorization :
    extensionToNormalization X E ≫ extensionFromNormalization X E = genericExtensionMap X E :=
  (genericExtensionMap X E).toNormalization_fromNormalization

instance extensionNormalization_integral : IsIntegral (extensionNormalization X E) :=
  inferInstanceAs (IsIntegral (genericExtensionMap X E).normalization)

instance extensionFromNormalization_integral : IsIntegralHom (extensionFromNormalization X E) :=
  inferInstanceAs (IsIntegralHom (genericExtensionMap X E).fromNormalization)

instance extensionToNormalization_dominant : IsDominant (extensionToNormalization X E) :=
  inferInstanceAs (IsDominant (genericExtensionMap X E).toNormalization)

instance extensionFromNormalization_dominant : IsDominant (extensionFromNormalization X E) := by
  have : IsDominant (extensionToNormalization X E ≫ extensionFromNormalization X E) := by
    rw [extensionNormalization_factorization]
    infer_instance
  exact IsDominant.of_comp (extensionToNormalization X E) (extensionFromNormalization X E)

theorem extensionFromNormalization_surjective : Surjective (extensionFromNormalization X E) :=
  inferInstance

theorem genericExtensionMap_preimage (U : X.Opens) [Nonempty U] :
    genericExtensionMap X E ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro z _
  change genericExtensionMap X E z ∈ U
  rw [genericExtensionMap_apply]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The ambient sections in every nonempty affine chart are the given extension field. -/
def genericSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U) ≅ CommRingCat.of E :=
  (Spec (CommRingCat.of E)).presheaf.mapIso
    (eqToIso (genericExtensionMap_preimage X E U).symm).op ≪≫ Scheme.ΓSpecIso _

/-- The actual affine coordinate ring of the relative normalization. -/
def extensionNormalizationObjIso (U : X.Opens) (hU : IsAffineOpen U) :
    let := ((genericExtensionMap X E).app U).hom.toAlgebra
    Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U)
        Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U)) :=
  (genericExtensionMap X E).normalizationObjIso hU

/-- Every nonempty affine base chart gives an integrally closed normalization chart ring. -/
theorem extensionNormalization_chart_integrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed
      Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) := by
  let R := Γ(X, U)
  let S := Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U)
  let : Algebra R S := ((genericExtensionMap X E).app U).hom.toAlgebra
  let e : S ≃+* E := (genericSectionsIso X E U).commRingCatIsoToRingEquiv
  let : IsDomain S := Function.Injective.isDomain e.toRingHom e.injective
  let : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e.symm
  let : IsIntegrallyClosed (integralClosure R S) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (R := integralClosure R S) (S := S)
  exact IsIntegrallyClosed.of_equiv (extensionNormalizationObjIso X E U hU).commRingCatIsoToRingEquiv.symm

/-- Stalks of the actual normalization are integrally closed. -/
theorem extensionNormalization_stalk_integrallyClosed (y : extensionNormalization X E) :
    IsIntegrallyClosed ((extensionNormalization X E).presheaf.stalk y) := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := extensionFromNormalization X E y) (U := ⊤) (by trivial)
  let : Nonempty U := ⟨⟨_, hyU⟩⟩
  let V := extensionFromNormalization X E ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage (extensionFromNormalization X E)
  have hyV : y ∈ V := hyU
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  let : IsIntegrallyClosed Γ(extensionNormalization X E, V) :=
    extensionNormalization_chart_integrallyClosed X E U hU
  let := TopCat.Presheaf.algebra_section_stalk (extensionNormalization X E).presheaf (⟨y, hyV⟩ : V)
  let := hV.isLocalization_stalk ⟨y, hyV⟩
  exact isIntegrallyClosed_of_isLocalization _
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- The actual normalization needs no additional integrally-closed-stalk assumption for roots. -/
theorem extensionNormalization_stalk_root_regular (y : extensionNormalization X E)
    (f : (extensionNormalization X E).functionField) (n : ℕ) (hn : 0 < n)
    (hpow : ∃ g : (extensionNormalization X E).presheaf.stalk y,
      algebraMap ((extensionNormalization X E).presheaf.stalk y)
        (extensionNormalization X E).functionField g = f ^ n) :
    ∃ g : (extensionNormalization X E).presheaf.stalk y,
      algebraMap ((extensionNormalization X E).presheaf.stalk y)
        (extensionNormalization X E).functionField g = f := by
  let := extensionNormalization_stalk_integrallyClosed X E y
  exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (IsIntegrallyClosed.isIntegral_iff.mpr hpow)

/-- The generic extension map satisfies all hypotheses used by relative normalization. -/
theorem genericExtensionMap_geometry :
    QuasiCompact (genericExtensionMap X E) ∧
    QuasiSeparated (genericExtensionMap X E) ∧
    IsDominant (genericExtensionMap X E) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Geometric properties proved for the actual normalization and its actual maps. -/
theorem extensionNormalization_geometry :
    IsIntegral (extensionNormalization X E) ∧
    IsIntegralHom (extensionFromNormalization X E) ∧
    IsDominant (extensionToNormalization X E) ∧
    IsDominant (extensionFromNormalization X E) ∧
    Surjective (extensionFromNormalization X E) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    extensionFromNormalization_surjective X E⟩

/-- Both actual chart identifications, without an assumed cover or coordinate-ring model. -/
theorem extensionNormalization_affine_coordinates (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((genericExtensionMap X E).app U).hom.toAlgebra
    Nonempty (Γ(extensionNormalization X E, extensionFromNormalization X E ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U)
        Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U))) ∧
    Nonempty (Γ(Spec (CommRingCat.of E), genericExtensionMap X E ⁻¹ᵁ U) ≅
      CommRingCat.of E) :=
  ⟨⟨extensionNormalizationObjIso X E U hU⟩, ⟨genericSectionsIso X E U⟩⟩

end

end ArithmeticThetaNormalization
