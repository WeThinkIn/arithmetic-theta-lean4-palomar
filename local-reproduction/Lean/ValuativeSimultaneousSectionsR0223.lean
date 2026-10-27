import ValuativeRootSectionsDefinitionsR0223

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
namespace ArithmeticThetaValuativeRootsR0223
namespace ValuativeSimultaneousSectionsR0223
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField
open ArithmeticThetaNormalizedSections ArithmeticThetaKummerCover ArithmeticThetaGeometricDegree
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLineRoot
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaCommonHalfHodgeR0185
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open ArithmeticThetaCommonHalfHodgeR0185.CuspHalfDivisorLineR0185
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

/-- The field embedding comes from the specified generic map. -/
lemma valuation_field_map (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} [IsIntegral Z]
    (f : ValuationPoint Ω A ⟶ Z) [IsDominant (genericInclusion Ω A ≫ f)] :
    ∃ φ : Z.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (genericPoint Z) =
        genericInclusion Ω A ≫ f := by
  have hgeneral {X : Scheme.{0}} (E : Type) [Field E]
      (q : Spec (CommRingCat.of E) ⟶ X) (x : X)
      (hx : q (IsLocalRing.closedPoint E) = x) :
      ∃ φ : X.presheaf.stalk x →+* E,
        Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x = q := by
    subst x
    exact ⟨(Scheme.stalkClosedPointTo q).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk q⟩
  exact hgeneral Ω (genericInclusion Ω A ≫ f) _ (field_point_generic _ _)

lemma valuationScalar_generic (Ω : Type) [Field Ω] (A : ValuationSubring Ω) {Z : Scheme.{0}} [IsIntegral Z]
    [Algebra Z.functionField Ω] (f : ValuationPoint Ω A ⟶ Z)
    (hf : genericInclusion Ω A ≫ f = genericExtensionMap Z Ω)
    (U : Z.Opens) [Nonempty U]
    (hU : (⊤ : (ValuationPoint Ω A).Opens) ≤ f ⁻¹ᵁ U) (a : Γ(Z,U)) :
    algebraMap A Ω (specScalar f U hU a) =
      algebraMap Z.functionField Ω (Z.germToFunctionField U a) := by
  have hV : (⊤ : (FieldPoint Ω).Opens) ≤ (genericInclusion Ω A ≫ f) ⁻¹ᵁ U := by
    rw [hf, genericExtensionMap_preimage]
  have hc := specScalar_comp (algebraMap A Ω) f U hU hV a
  change specScalar (genericInclusion Ω A ≫ f) U hV a = _ at hc
  simp only [hf] at hc
  exact hc.symm.trans (specScalar_generic Ω U _ a)

/-- Express the prescribed valuation frame in the pulled-back chart frame.
The resulting roots all lie in the same valuation ring. -/
lemma prescribed_valuation_roots (Ω : Type) [Field Ω] (A : ValuationSubring Ω) {Z : Scheme.{0}} [IsIntegral Z]
    [Algebra Z.functionField Ω]
    (f : ValuationPoint Ω A ⟶ Z)
    (hf : genericInclusion Ω A ≫ f = genericExtensionMap Z Ω)
    (J : Z.Modules) (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (hU : (⊤ : (ValuationPoint Ω A).Opens) ≤ f ⁻¹ᵁ U)
    (K s : ℕ) (F : Fin s → Sections Z (tensorPower Z J K))
    (h : Sections (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J))
    (a : Fin s → A)
    (ha : ∀ j, pullbackPowerSection f J K (F j) =
      scalar A ((a j)^K) • tensorPowerSection (ValuationPoint Ω A)
        ((Scheme.Modules.pullback f).obj J) K ⊤ h) :
    ∃ c : A,
      h = scalar A c •
        res ((Scheme.Modules.pullback f).obj J) hU
          (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) ∧
      ∀ j, (algebraMap A Ω (a j * c)) ^ K =
        algebraMap Z.functionField Ω (powerCoefficient Z J U e K (F j)) := by
  let w := res ((Scheme.Modules.pullback f).obj J) hU
    (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1))
  have hw : IsFrame ((Scheme.Modules.pullback f).obj J) ⊤ w :=
    ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.frame_restrict _ hU _
      (pullback_frame f J _ (frame_generator Z J U e))
  obtain ⟨C, hC⟩ := (hw ⊤ le_rfl).surjective h
  rw [InitialHodgeSection.res_self] at hC
  change C • w = h at hC
  let c : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom C
  have hc : scalar A c = C :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm_apply_apply C
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    exact hC.symm
  · intro j
    let d := sectionCoordinate Z (tensorPower Z J K) U (tensorPowerFrame Z J U e K) (F j)
    have ht := pullback_power_coordinate f J U e hU K (F j)
    have he : scalar A (specScalar f U hU d) =
        scalar A ((a j)^K) * C^K := by
      apply (InitialHodgeSection.tensor_frame _ w hw K ⊤ le_rfl).injective
      simp only [InitialHodgeSection.res_self]
      rw [mul_smul]
      change _ = scalar A ((a j)^K) • (C^K •
        tensorPowerSection (ValuationPoint Ω A) ((Scheme.Modules.pullback f).obj J) K ⊤ w)
      rw [← InitialHodgeSection.tensor_smul, hC]
      exact ht.symm.trans (ha j)
    have hd : specScalar f U hU d = (a j * c)^K := by
      have he' := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom he
      simpa only [scalar, map_mul, map_pow, Iso.inv_hom_id_apply,
        CommRingCat.hom_comp, RingHom.comp_apply, mul_pow] using he'
    rw [← map_pow, ← hd]
    exact valuationScalar_generic Ω A f hf U hU d

/-- The prescribed generic scalar determines the entire regular valuation section,
using the canonical pullback triangle and the accepted compatible frame. -/
lemma valuation_section_value (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} [IsIntegral Z] [Algebra Z.functionField Ω]
    (E : IntermediateField Z.functionField Ω)
    (J : Z.Modules) (U : Z.Opens) [Nonempty U] (e : LocalFrame Z J U)
    (eY : LocalFrame (extensionNormalization Z E)
      ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J)
      (extensionFromNormalization Z E ⁻¹ᵁ U))
    (heY : FramePullbackCompatible (extensionFromNormalization Z E) J U e eY)
    (f : ValuationPoint Ω A ⟶ Z) (hU : (⊤ : (ValuationPoint Ω A).Opens) ≤ f ⁻¹ᵁ U)
    (g : ValuationPoint Ω A ⟶ extensionNormalization Z E)
    (hg : g ≫ extensionFromNormalization Z E = f)
    (hbranch : genericInclusion Ω A ≫ g =
      Spec.map (CommRingCat.ofHom E.subtype) ≫ extensionToNormalization Z E)
    (t : Sections (extensionNormalization Z E)
      ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J))
    (v : A)
    (hv : (normalizationFunctionFieldMap Z E
      (sectionCoefficient (extensionNormalization Z E)
        ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J)
        (extensionFromNormalization Z E ⁻¹ᵁ U) eY t) : Ω) =
      algebraMap A Ω v) :
    (along g (extensionFromNormalization Z E) f hg J).hom.app ⊤
      (pullbackGlobalSection g ((Scheme.Modules.pullback (extensionFromNormalization Z E)).obj J) t) =
      scalar A v • res ((Scheme.Modules.pullback f).obj J) hU
        (Scheme.Modules.pullbackLocalSection f (e.equiv U le_rfl 1)) := by
  let p := extensionFromNormalization Z E
  let V := p ⁻¹ᵁ U
  let d := sectionCoordinate (extensionNormalization Z E) ((Scheme.Modules.pullback p).obj J) V eY t
  have hV : (⊤ : (ValuationPoint Ω A).Opens) ≤ g ⁻¹ᵁ V := by
    change ⊤ ≤ (g ≫ p) ⁻¹ᵁ U
    simpa only [p, hg] using hU
  have hs := normalization_scalar_triangle A Ω E
    (algebraMap A Ω) E.subtype g hbranch V hV d
  have hd : specScalar g V hV d = v := by
    apply IsFractionRing.injective A Ω
    exact hs.trans hv
  have hlocal := coordinate_spec ((Scheme.Modules.pullback p).obj J) V eY t
  have he := heY U le_rfl 1
  simp only [map_one] at he
  change Scheme.Modules.pullbackLocalSection p (e.equiv U le_rfl 1) = eY.equiv V le_rfl 1 at he
  rw [← he] at hlocal
  have ht := along_local_scalar p g f hg J t U (e.equiv U le_rfl 1) d hlocal hU hV
  rw [← scalar_specScalar, hd, transport_as_app] at ht
  exact ht

lemma valuation_branch_dominant (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    {Z : Scheme.{0}} [IsIntegral Z] [Algebra Z.functionField Ω]
    (E : IntermediateField Z.functionField Ω)
    (g : ValuationPoint Ω A ⟶ extensionNormalization Z E)
    (hg : genericInclusion Ω A ≫ g =
      Spec.map (CommRingCat.ofHom E.subtype) ≫ extensionToNormalization Z E) :
    IsDominant (genericInclusion Ω A ≫ g) := by
  have hpt (x : FieldPoint Ω) : (genericInclusion Ω A ≫ g) x =
      genericPoint (extensionNormalization Z E) := by
    rw [hg, Scheme.Hom.comp_apply]
    exact (congrArg (extensionToNormalization Z E) (Subsingleton.elim _ _)).trans
      (toNormalization_genericPoint Z E)
  have hr : Set.range (genericInclusion Ω A ≫ g) =
      {genericPoint (extensionNormalization Z E)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hpt x
    · intro hy
      exact ⟨IsLocalRing.closedPoint Ω, (hpt _).trans hy.symm⟩
  constructor
  rw [denseRange_iff_closure_range, hr]
  exact (genericPoint_spec (extensionNormalization Z E)).def

end ValuativeSimultaneousSectionsR0223
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaNormalization ArithmeticThetaNormalizationField
open ArithmeticThetaNormalizedSections ArithmeticThetaKummerCover ArithmeticThetaGeometricDegree
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLineRoot
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaSimultaneousUnaryR0187
open ArithmeticThetaSimultaneousUnaryR0187.SimultaneousDiskRootSectionsR0187
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodgeCoverR0185
open ValuativeSimultaneousSectionsR0223

/-- One smooth proper finite flat cover realizes all prescribed valuative sections. -/
theorem valuative_simultaneous_sections :
∀ (k : Type) [Field k] [CharZero k] (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (b : Quiver.Hom Z (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.IsProper b] [AlgebraicGeometry.SmoothOfRelativeDimension 1 b] (J : Z.Modules), AlgebraicGeometry.Scheme.Modules.IsInvertible J → ∀ (K s : ℕ), 0 < K → ∀ (F : Fin s → ArithmeticThetaSimultaneousUnaryR0187.Sections Z (ArithmeticThetaTensorPower.tensorPower Z J K)), (∀ j, F j ≠ 0) → ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (f : Quiver.Hom (ArithmeticThetaValuativeRootsR0223.ValuationPoint Ω A) Z), AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp (ArithmeticThetaValuativeRootsR0223.genericInclusion Ω A) f) → ∀ (h : ArithmeticThetaSimultaneousUnaryR0187.Sections (ArithmeticThetaValuativeRootsR0223.ValuationPoint Ω A) ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J)), ArithmeticThetaRelativeDiscriminantR0171.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj J) ⊤ h → ∀ (a : Fin s → A), (∀ j, ArithmeticThetaValuativeRootsR0223.IntegralEquation Ω A f J K (F j) h (a j)) → ∃ R : ArithmeticThetaSimultaneousUnaryR0187.RootCover k Z b (K^s), ArithmeticThetaValuativeRootsR0223.Realizes k R Ω A J K s F f h a := by
  intro k _ _ Z _ b _ _ J hJ K s hK F hF Ω _ A f hdom h hh a ha
  letI := hdom
  obtain ⟨φ, hφ⟩ := valuation_field_map Ω A f
  letI : Algebra Z.functionField Ω := φ.toAlgebra
  have hf : genericInclusion Ω A ≫ f = genericExtensionMap Z Ω := hφ.symm
  obtain ⟨U, u, hz, hu⟩ := local_frame_exists hJ (f (IsLocalRing.closedPoint A))
  let e := InitialHodgeSection.frame J u hu
  letI : Nonempty U := ⟨⟨_, hz⟩⟩
  have hU : (⊤ : (ValuationPoint Ω A).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hz).ge
  obtain ⟨c, hc, hr⟩ := prescribed_valuation_roots Ω A f hf J U e hU K s F h a ha
  let r : Fin s → Ω := fun j => algebraMap A Ω (a j * c)
  let coeff : Fin s → Z.functionField := fun j => powerCoefficient Z J U e K (F j)
  obtain ⟨hnoeth, hchar, hnormal⟩ :=
    ArithmeticThetaSmoothNormality.smooth_normalization_prerequisites Z k b
  letI := hnoeth
  letI := hchar
  obtain ⟨hgeom, eY, heY, t, ht, _⟩ := smooth_proper_root_sections Z k b
    (smooth_relative_curve_dimension Z k b) J (line_of_invertible J hJ)
    U e Ω K s hK F r hr
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  let p := rootCoverMap Z Ω s r
  let Y := rootCover Z Ω s r
  let R : RootCover k Z b (K^s) :=
    { space := Y
      map := p
      integral := inferInstance
      finite := hgeom.1
      flat := rootCover_finite_flat Z k b Ω K s hK r coeff hr
      surjective := hgeom.2.1
      proper := hgeom.2.2.2.1
      smooth := finite_smooth_curve_dimension k b p
      degree := fun x => ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one (rootCover_geometric_degree_positive
          Z k b Ω K s hK r coeff hr x),
        rootCover_geometric_degree_bound Z k b Ω K s hK r coeff hr x⟩ }
  obtain ⟨g, ⟨hg, hbranch⟩, _⟩ :=
    ArithmeticThetaCoverComparison.normalization_prescribed_valuative_branch
      Z hnormal Ω K s hK r coeff hr A f hf
  refine ⟨R, g, hg, valuation_branch_dominant Ω A _ g hbranch, t, ?_⟩
  intro j
  have hvalue := coverRoot_prescribed Z Ω K s hK r coeff hr j
  have htv : (normalizationFunctionFieldMap Z (generatedRootField Z Ω s r)
      (sectionCoefficient Y ((Scheme.Modules.pullback p).obj J) (p ⁻¹ᵁ U) eY (t j)) :
        Ω) = r j := by
    rw [(ht j).1]
    exact hvalue
  refine ⟨?_, (ht j).2, ?_⟩
  · intro hz
    have rz : r j = 0 := by
      rw [hz] at htv
      simpa only [sectionCoefficient, sectionCoordinate, map_zero, ZeroMemClass.coe_zero] using htv.symm
    apply powerCoefficient_ne_zero J hJ U e K (F j) (hF j)
    apply (algebraMap Z.functionField Ω).injective
    have hp : algebraMap Z.functionField Ω
        (powerCoefficient Z J U e K (F j)) = r j ^ K := (hr j).symm
    simpa only [rz, zero_pow (Nat.ne_of_gt hK), map_zero] using hp
  · have htDisk := valuation_section_value Ω A (generatedRootField Z Ω s r)
      J U e eY heY f hU g hg hbranch (t j) (a j * c) htv
    change _ = scalar A (a j) • h
    rw [htDisk, hc, ← mul_smul]
    congr 1
    exact map_mul (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom _ _


#print axioms valuative_simultaneous_sections
end ArithmeticThetaValuativeRootsR0223
