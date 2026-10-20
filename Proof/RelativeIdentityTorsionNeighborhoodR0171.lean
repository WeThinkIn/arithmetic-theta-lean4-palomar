module

public import RelativeDiscriminantDefinitionsR0171

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeDiscriminantR0171
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170

namespace IdentityTorsionNeighborhood

/-- A section of an étale morphism is open, by the open diagonal criterion. -/
lemma section_open {S T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (s : S ⟶ T) (hs : s ≫ p = 𝟙 S) : IsOpenImmersion s := by
  letI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y f ⟨hft, hfu⟩
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  apply MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) s p ⟨inferInstance, inferInstance⟩
  rw [hs]
  infer_instance

/-- Radical ideals with the same support on an affine chart are equal. -/
lemma radical_ideal_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (U : X.affineOpens) (hI : (I.ideal U).IsRadical) (hJ : (J.ideal U).IsRadical)
    (h : ∀ x ∈ U.1, x ∈ I.support ↔ x ∈ J.support) : I.ideal U = J.ideal U := by
  rw [← hI.radical, ← hJ.radical]
  change I.radical.ideal U = J.radical.ideal U
  rw [← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' I.support) =
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' J.support)
  congr 1
  ext z
  exact h _ (by
    have hz : U.2.fromSpec z ∈ Set.range U.2.fromSpec := Set.mem_range_self z
    rw [U.2.range_fromSpec] at hz
    exact hz)

/-- Isolate an étale section inside a closed ambient embedding. -/
lemma isolate_section {S T X : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (s : S ⟶ T) (hs : s ≫ p = 𝟙 S) (i : T ⟶ X) [IsClosedImmersion i] :
    ∃ V : X.Opens, (∀ x : S, (s ≫ i) x ∈ V) ∧
      ∀ x ∈ V, x ∈ Set.range i ↔ x ∈ Set.range (s ≫ i) := by
  letI := section_open p s hs
  obtain ⟨v, hv, hvpre⟩ := i.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp
    s.isOpenEmbedding.isOpen_range
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · intro x
    change s x ∈ i ⁻¹' v
    rw [hvpre]
    exact Set.mem_range_self x
  · intro x hx
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y ∈ Set.range s := by rw [← hvpre]; exact hx
      obtain ⟨z, rfl⟩ := hy
      exact ⟨z, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨s y, rfl⟩

end IdentityTorsionNeighborhood

/-- Every point of the identity admits a regular chart where the actual torsion
ideal equals the identity ideal. Positive multiplication includes c = 1. -/
theorem relative_identity_torsion_neighborhood :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (c : ℕ) (hc : 0 < c) (x : ArithmeticThetaRelativeDiscriminantR0171.Base R), ∃ (U : (ArithmeticThetaRelativeKatoR0169.Curve R W).affineOpens) (a : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj (Opposite.op U.1)), ArithmeticThetaRelativeKatoR0169.origin R W x ∈ U.1 ∧ ArithmeticThetaRelativeDiscriminantR0171.IdentityChart R W G c U a := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG c hc x
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  letI : Etale (G.schemeNsmul c) :=
    (relative_multiplication_degree R W G hG c hc).2.1
  let T := pullback (G.schemeNsmul c) (origin R W)
  let i : T ⟶ Curve R W := pullback.fst _ _
  let p : T ⟶ Base R := pullback.snd _ _
  let s : Base R ⟶ T := pullback.lift (origin R W) (𝟙 _)
    (by simpa using RelativeExistence.origin_fixed R W G hG c)
  have hsi : s ≫ i = origin R W := pullback.lift_fst _ _ _
  have hsp : s ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨V, hV, hVr⟩ := IdentityTorsionNeighborhood.isolate_section p s hsp i
  rw [hsi] at hV hVr
  obtain ⟨U, hxU, a, ha, hIa⟩ := (relative_torsion_cartier R W G hG).1 (origin R W x)
  obtain ⟨_, ⟨v, hv, rfl⟩, hxv, hvsub⟩ := (Curve R W).isBasis_affineOpens.exists_subset_of_mem_open
    (show origin R W x ∈ (U.1 ⊓ V : (Curve R W).Opens) from ⟨hxU, hV x⟩)
    (U.1 ⊓ V).isOpen
  let U' : (Curve R W).affineOpens := ⟨v, hv⟩
  have hle : U'.1 ≤ U.1 := fun y hy => (hvsub hy).1
  let F := (Curve R W).presheaf.map (homOfLE hle).op
  letI : Nonempty U.1 := ⟨⟨origin R W x, hxU⟩⟩
  letI : Nonempty U'.1 := ⟨⟨origin R W x, hxv⟩⟩
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha)
  have hFa : F a ≠ 0 := (map_ne_zero_iff F.hom
    (map_injective_of_isIntegral (Curve R W) (homOfLE hle))).mpr ha0
  refine ⟨U', F a, hxv, ?_, ?_, ?_⟩
  · exact isRegular_iff_ne_zero.mpr hFa
  · rw [← (identityIdeal R W).map_ideal hle, hIa, Ideal.map_span, Set.image_singleton]
    rfl
  · apply IdentityTorsionNeighborhood.radical_ideal_eq
      (torsionIdeal R W G c) (identityIdeal R W) U'
      (RelativeKatoCartierRatio.torsion_radical R W G hG c hc U')
      (RelativeKatoCartierRatio.ker_radical (origin R W) U')
    intro y hy
    have hi : torsionIdeal R W G c = i.ker := by
      exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (origin R W) (G.schemeNsmul c)).symm
    rw [hi]
    change y ∈ (i.ker.support : Set (Curve R W)) ↔
      y ∈ ((origin R W).ker.support : Set (Curve R W))
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq,
      (origin R W).isClosedEmbedding.isClosed_range.closure_eq]
    exact hVr y (hvsub hy).2

#print axioms relative_identity_torsion_neighborhood

/-- Cancel the common regular generator in the accepted Cartier equation,
then retain the exact scalar c as a unit in the actual section ring. -/
theorem relative_initial_unit :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (U : (ArithmeticThetaRelativeKatoR0169.Curve R W).affineOpens) [Nonempty U.1] (a : (ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj (Opposite.op U.1)) (ha : ArithmeticThetaRelativeDiscriminantR0171.IdentityChart R W G c U a), ∃! ε : ((ArithmeticThetaRelativeKatoR0169.Curve R W).presheaf.obj (Opposite.op U.1))ˣ, (c : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) * g = (ArithmeticThetaRelativeKatoR0169.Curve R W).germToFunctionField U.1 ((ε : _) * a^(c^2-1)) := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG c hc hc6 g hg U _ a ha
  obtain ⟨e, he⟩ := relative_kato_cartier_ratio R W G hG c hc hc6 g hg
    U a a ha.1 ha.1 ha.2.1 (ha.2.2.trans ha.2.1)
  let F := (Curve R W).germToFunctionField U.1
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha.1)
  have hA : F a ≠ 0 := (map_ne_zero_iff _ ((Curve R W).germToFunctionField_injective U.1)).mpr ha0
  have hpow : c^2 = (c^2-1)+1 := by have := Nat.one_le_pow 2 c (by omega); omega
  have he' : g = F ((e : _) * a^(c^2-1)) := by
    apply mul_right_cancel₀ hA
    rw [hpow, pow_succ] at he
    simpa only [F, map_mul, map_pow, mul_assoc] using he
  letI : Algebra ℚ Γ(Curve R W, U.1) :=
    ((Curve R W).presheaf.map (homOfLE le_top).op).hom.comp
      ((structureMap R W).appTop.hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℚ R))) |>.toAlgebra
  have hcunit : IsUnit (c : Γ(Curve R W, U.1)) := by
    have hq : IsUnit (c : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa only [map_natCast] using hq.map (algebraMap ℚ Γ(Curve R W, U.1))
  refine ⟨hcunit.unit * e, ?_, ?_⟩
  · simp only [Units.val_mul, hcunit.unit_spec, map_mul, map_pow, map_natCast, he', F]
    ring
  · intro e' heq
    apply Units.ext
    apply mul_right_cancel₀ (pow_ne_zero (c^2-1) ha0)
    apply (Curve R W).germToFunctionField_injective U.1
    rw [← heq]
    simp only [Units.val_mul, hcunit.unit_spec, map_mul, map_pow, map_natCast, he', F]
    ring

#print axioms relative_initial_unit
end ArithmeticThetaRelativeDiscriminantR0171
