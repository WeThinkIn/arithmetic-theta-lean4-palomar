module

public import FiniteEtaleLocalNormR0150

@[expose] public section

/-! Free affine neighborhoods for arbitrary finite étale scheme morphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150
namespace FreeCover
variable {X Y : Scheme.{u}}

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
  exact ArithmeticThetaGeometricNormR0150.LocalNorm.free_localization_model (S := Γ(X, V)) (Submonoid.powers r)

end FreeCover

/-- Every target open has a basis of affine opens on which the actual finite
étale section algebra is free, with no integrality or constant-rank hypothesis. -/
theorem finite_etale_free_cover
    (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f]
    (W : Y.Opens) (y : Y) (hyW : y ∈ W) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ W ∧ AffineFree f V.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyW W.isOpen
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
  refine ⟨⟨Y.basicOpen r, hU.basicOpen r⟩, ?_, (Y.basicOpen_le r).trans hsub,
    FreeCover.affineFree_basicOpen f U hU r hfree⟩
  have hp : p ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen r := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  change hU.fromSpec p ∈ Y.basicOpen r at hp
  simpa only [p, hU.fromSpec_primeIdealOf] using hp

end ArithmeticThetaSchemeKatoNormR0251
