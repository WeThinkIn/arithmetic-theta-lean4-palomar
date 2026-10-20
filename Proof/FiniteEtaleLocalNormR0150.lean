module

public import GeometricNormDefinitionsR0150
public import Mathlib.RingTheory.Localization.NormTrace

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaGeometricNormR0150
namespace LocalNorm
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem section_field_square (f : X ⟶ Y) [IsFinite f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    (X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
      φ.comp (Y.germToFunctionField U).hom := by
  have hV := hU.preimage f
  have hY : Spec.map (Y.germToFunctionField U) ≫ hU.fromSpec =
      Y.fromSpecStalk (genericPoint Y) :=
    hU.fromSpecStalk_eq_fromSpecStalk _
  have hX : Spec.map (X.germToFunctionField (f ⁻¹ᵁ U)) ≫ hV.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
    hV.fromSpecStalk_eq_fromSpecStalk _
  have hnat : Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
    simpa only [← Scheme.Hom.app_eq_appLE] using hU.SpecMap_appLE_fromSpec f hV le_rfl
  have he : (f.app U) ≫ X.germToFunctionField (f ⁻¹ᵁ U) =
      Y.germToFunctionField U ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    apply (cancel_mono hU.fromSpec).mp
    simp only [Spec.map_comp, Category.assoc]
    rw [hnat, ← Category.assoc, hX, hY]
    exact hφ
  exact congrArg CommRingCat.Hom.hom he

/-- The geometric square gives exactly the scalar tower needed for localization. -/
theorem affine_field_data (f : X ⟶ Y) [IsFinite f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    FiniteFieldMap φ ∧
      (letI := (f.app U).hom.toAlgebra
       fieldDegree φ = Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) ∧
      (AffineFree f U → NormOnOpen f φ U) := by
  letI := (f.app U).hom.toAlgebra
  letI := φ.toAlgebra
  letI : Algebra Γ(Y, U) X.functionField :=
    (φ.comp (Y.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField :=
    .of_algebraMap_eq' (section_field_square f φ hφ U hU).symm
  letI : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI : IsFractionRing Γ(X, f ⁻¹ᵁ U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ (hU.preimage f)
  letI : FaithfulSMul Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro a b hab
      apply (Y.germToFunctionField_injective U)
      apply φ.injective
      have he := DFunLike.congr_fun (section_field_square f φ hφ U hU)
      exact (he a).symm.trans ((congrArg (X.germToFunctionField _) hab).trans (he b)))
  letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have hfinite : FiniteDimensional Y.functionField X.functionField :=
    Module.Finite.of_isLocalization Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(Y, U)⁰
  refine ⟨hfinite, IsFractionRing.finrank_eq Γ(Y, U) Y.functionField
    Γ(X, f ⁻¹ᵁ U) X.functionField, ?_⟩
  intro hfree
  letI : Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hfree
  intro _ _ a
  exact (Algebra.norm_localization Γ(Y, U) Γ(Y, U)⁰ a).symm

/-- Freeness of the standard localized module transfers to any localization model. -/
theorem free_localization_model {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (M : Submonoid R) [IsLocalization M R']
    [IsLocalization (Algebra.algebraMapSubmonoid S M) S']
    [Module.Free (Localization M) (LocalizedModule M S)] : Module.Free R' S' := by
  let f := (IsScalarTower.toAlgHom R S S').toLinearMap
  let e := (IsLocalization.algEquiv M (Localization M) R').toRingEquiv
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  apply Module.Free.of_equiv (σ := e.toRingHom)
    (show LocalizedModule M S ≃ₛₗ[e.toRingHom] S' from
      { __ := IsLocalizedModule.iso M f, map_smul' := ?_ })
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq M r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

/-- A free algebraic localization is the actual direct image on a basic open. -/
theorem affineFree_basicOpen (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U))
    (hr : letI := (f.app U).hom.toAlgebra
      Module.Free (Localization.Away r) (LocalizedModule.Away r Γ(X, f ⁻¹ᵁ U))) :
    AffineFree f (Y.basicOpen r) := by
  let V := f ⁻¹ᵁ U
  let V' := f ⁻¹ᵁ Y.basicOpen r
  let i : V' ⟶ V := homOfLE (f.preimage_mono (Y.basicOpen_le r))
  letI := (f.app U).hom.toAlgebra
  letI := (f.app (Y.basicOpen r)).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X, V') := (X.presheaf.map i.op).hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, V') :=
    ((X.presheaf.map i.op).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower Γ(Y, U) Γ(X, V) Γ(X, V') := .of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen r) Γ(X, V') :=
    .of_algebraMap_eq' (by
      have h := f.naturality (homOfLE (Y.basicOpen_le r)).op
      exact congrArg CommRingCat.Hom.hom h.symm)
  letI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hU.isLocalization_basicOpen r
  letI : IsLocalization.Away (f.app U r) Γ(X, V') :=
    (hU.preimage f).isLocalization_of_eq_basicOpen (f.app U r) i (f.preimage_basicOpen r)
  letI : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, V) (Submonoid.powers r))
      Γ(X, V') := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
      RingHom.algebraMap_toAlgebra] using
      (inferInstance : IsLocalization.Away (f.app U r) Γ(X, V'))
  letI := hr
  exact free_localization_model (S := Γ(X, V)) (Submonoid.powers r)

/-- Finite etale direct images become free after shrinking around any point. -/
theorem exists_affineFree (f : X ⟶ Y) [IsFinite f] [Etale f] (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ AffineFree f U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (⊤ : Y.Opens) from trivial) isOpen_univ
  have hV := hU.preimage f
  letI := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  letI : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    have hf : (f.app U).hom.Flat := by
      simpa only [Scheme.Hom.appLE_eq_app] using f.flat_appLE hU hV le_rfl
    exact hf
  letI : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    have hf : (f.app U).hom.FinitePresentation := by
      simpa only [Scheme.Hom.appLE_eq_app] using f.finitePresentation_appLE hU hV le_rfl
    exact hf
  letI : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  let p := hU.primeIdealOf ⟨y, hy⟩
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U)) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U))
    (Localization.AtPrime p.asIdeal)
  refine ⟨Y.basicOpen r, ?_, hU.basicOpen r, affineFree_basicOpen f U hU r hfree⟩
  have hp : p ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen r := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  change hU.fromSpec p ∈ Y.basicOpen r at hp
  simpa only [p, hU.fromSpec_primeIdealOf] using hp

end LocalNorm
open CategoryTheory AlgebraicGeometry

/-- Finite etale maps admit free affine norm charts, with the degree and scalar
structure prescribed by their actual generic-point square. -/
theorem finite_etale_local_norm
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Surjective f]
    (φ : Y.functionField →+* X.functionField) (hφ : IsFieldMap f φ) :
    FiniteFieldMap φ ∧
      (∀ y : Y, f.finrank y = fieldDegree φ) ∧
      (∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ AffineFree f U ∧
        NormOnOpen f φ U) := by
  have hlocal (y : Y) : FiniteFieldMap φ ∧ f.finrank y = fieldDegree φ ∧
      (∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ AffineFree f U ∧ NormOnOpen f φ U) := by
    obtain ⟨U, hy, hU, hfree⟩ := LocalNorm.exists_affineFree f y
    letI : Nonempty U := ⟨⟨y, hy⟩⟩
    obtain ⟨x, hx⟩ := f.surjective y
    letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by change f x ∈ U; rwa [hx]⟩⟩
    obtain ⟨hfin, hdeg, hnorm⟩ := LocalNorm.affine_field_data f φ hφ U hU
    refine ⟨hfin, ?_, U, hy, hU, hfree, hnorm hfree⟩
    exact (ArithmeticThetaDegreeAssembly.finrank_eq_affine_module f U hU ⟨y, hy⟩).trans hdeg.symm
  exact ⟨(hlocal (genericPoint Y)).1, fun y => (hlocal y).2.1, fun y => (hlocal y).2.2⟩

end ArithmeticThetaGeometricNormR0150
