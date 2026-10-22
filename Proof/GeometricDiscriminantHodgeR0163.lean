module

public import OriginHodgeComparisonR0163
public import HodgeTensorSectionsR0163
public import OriginLogarithmicTaylorR0163
public import ActualDiscriminantCotangentTensorR0162

@[expose] public section

-- Preserve the original elaborated instance path after import reduction.
attribute [local instance 1001] IsRegularLocalRing.toIsLocalRing

/-! The intrinsic discriminant section of the actual generic Hodge line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ArithmeticThetaHodgeInitialR0163
namespace GeometricDiscriminantHodgeR0163
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaConormalInitialR0162 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaCompactifiedDifferentialR0145
open OriginHodgeComparisonR0163
attribute [local instance] sectionModule
variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
variable (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
variable [IsIntegral (genericScheme k M)]

lemma actual_constant (ε : OriginStalk k M s hs →+* LaurentSeries k)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k))
    (ha : ActualTaylor k M s hs ε κ) (a : OriginStalk k M s hs) :
    PowerSeries.constantCoeff (κ a) = ε a := by
  obtain ⟨hε, χ, φ, σ, Ψ, hχ, hφ, hσ, hΨ, hκ⟩ := ha
  rw [hε]
  exact hκ.2.1 a

/-- The prescribed geometric comparison evaluates a differential by the
coefficient of its germ in the actual pulled-back frame. -/
lemma comparison_frame
    [Algebra (LaurentSeries k) (OriginStalk k M s hs)]
    (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (hε : ε.toRingHom = (Scheme.stalkClosedPointTo (Origin k M s hs)).hom)
    (e : DifferentialFiber ε ≃ₗ[LaurentSeries k] Γ(Hodge k M s hs, ⊤))
    (he : ∀ (U : (genericScheme k M).Opens)
      (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
      (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
      (Hodge k M s hs).presheaf.map (homOfLE (show (genericPoint k M s hs) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (e (differentialClass ε ((genericScheme k M).presheaf.germ U _ hx a))) =
        Scheme.Modules.pullbackLocalSection (genericPoint k M s hs) (differentialAt k M U a))
    (δ : Frame k M) (U : (genericScheme k M).Opens)
    (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    e (differentialClass ε ((genericScheme k M).presheaf.germ U _ hx a)) =
      hodgeSection k M s hs δ
        (ε ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a))) := by
  apply restrict_injective _ (Scheme.preimage_eq_top_of_closedPoint_mem (genericPoint k M s hs) hx)
  rw [he]
  have hf := frameSections_differential (genericStructure k M) δ
    (genericPoint k M s hs) U hx a
  change hodgeSection k M s hs δ
    ((Scheme.stalkClosedPointTo (Origin k M s hs))
      ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a))) = _ at hf
  have hv : ε ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) =
      (Scheme.stalkClosedPointTo (Origin k M s hs))
        ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) :=
    RingHom.congr_fun hε _
  rw [hv, hf, restrict_topSection]
  rfl

/-- The full logarithmic chain rule sends every Taylor-normalized parameter
to the actual Hodge frame, without selecting a preferred representative. -/
lemma normalized_parameter
    [Algebra (LaurentSeries k) (OriginStalk k M s hs)]
    (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (κ : OriginStalk k M s hs →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k))
    (ha : ActualTaylor k M s hs ε.toRingHom κ.toRingHom)
    (e : DifferentialFiber ε ≃ₗ[LaurentSeries k] Γ(Hodge k M s hs, ⊤))
    (he : ∀ (U : (genericScheme k M).Opens)
      (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
      (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
      (Hodge k M s hs).presheaf.map (homOfLE (show (genericPoint k M s hs) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (e (differentialClass ε ((genericScheme k M).presheaf.germ U _ hx a))) =
        Scheme.Modules.pullbackLocalSection (genericPoint k M s hs) (differentialAt k M U a))
    (δ : Frame k M) (hδ : LogarithmicTaylor k M s hs δ)
    (π : OriginStalk k M s hs) (hπ : PowerSeries.coeff 1 (κ π) = 1) :
    e (differentialClass ε π) = hodgeSection k M s hs δ 1 := by
  obtain ⟨U, hx, a, rfl⟩ := (genericScheme k M).presheaf.exists_germ_eq π
  rw [comparison_frame k M s hs ε ha.1 e he δ U hx a]
  congr 1
  have hc := congrArg PowerSeries.constantCoeff (hδ ε.toRingHom κ.toRingHom ha U hx a)
  rw [actual_constant k M s hs ε.toRingHom κ.toRingHom ha] at hc
  simp only [map_mul, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, one_mul] at hc
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_derivative] at hc
  have hc' : ε ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) =
      PowerSeries.coeff 1 (κ ((genericScheme k M).presheaf.germ U _ hx a)) := by
    simpa using hc
  exact hc'.trans hπ

end GeometricDiscriminantHodgeR0163

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaConormalInitialR0162 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaKatoExistenceR0151 ArithmeticThetaTensorPower
open GeometricDiscriminantHodgeR0163
attribute [local instance] sectionModule

/-- The unique actual Hodge section representing the initial class of 5g,
with its entire discriminant coefficient in every normalized frame. -/
theorem geometric_discriminant_hodge :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (g : AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g → ∃ d : ((ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs.1 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs.1 g d ∧ (∀ d' : ((ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs.1 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs.1 g d' → d' = d) ∧ (∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ArithmeticThetaHodgeInitialR0163.ExactHodgeExpansion k M s hs.1 δ d) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ X Y hX hY g hg
  classical
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs.1) :=
    (originScalar k M s hs.1).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs.1) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs.1).toAlgebra
  obtain ⟨g₀, hg₀, _⟩ := actual_discriminant_cotangent_tensor k r hr h3 he T M hM s hs G hG
  have hgg : g = g₀ := by
    obtain ⟨g₁, hg₁, hu⟩ := actual_kato_function_existence
      k r hr h3 T he M hM s hs G hG 5 (by decide) (by decide)
    exact (hu g hg).trans (hu g₀ hg₀.1).symm
  subst g₀
  obtain ⟨ε, κ, c, b, π, ha, hc, hb, hπ, ht, hn⟩ := hg₀.2
  obtain ⟨e, he', heu⟩ := origin_hodge_comparison k r hr h3 he T M hM s hs G hG ε ha.1
  obtain ⟨v, hv, hvu⟩ := hodge_tensor_sections (LaurentSeries k)
    (ArithmeticThetaHodgeFourTorsionR0147.Hodge k M s hs.1) 24
  let d := v (PiTensorProduct.map (fun _ : Fin 24 => e.toLinearMap) (c.symm (gradeClass ε 24 b)))
  refine ⟨d, ⟨ε, κ, c, e, v, b, ha, hc, he', hv, hb, rfl⟩, ?_, ?_⟩
  · intro d' hd'
    obtain ⟨ε', κ', c', e', v', b', ha', hc', he'', hv', hb', hd'⟩ := hd'
    have hε : ε' = ε := by
      apply AlgHom.ext
      intro a
      exact RingHom.congr_fun (ha'.1.trans ha.1.symm) a
    subst ε'
    have heq : e' = e := heu e' he''
    have hvq : v' = v := hvu v' hv'
    subst e'
    subst v'
    have hbq : b' = b := by
      apply Subtype.ext
      exact IsFractionRing.injective (OriginStalk k M s hs.1)
        (genericScheme k M).functionField (hb'.trans hb.symm)
    subst b'
    obtain ⟨ε₀, κ₀, ha₀, hi₀, hp₀, hn₀, ht₀⟩ :=
      actual_origin_augmented_taylor k r hr h3 he T M hM s hs G hG
    have hε₀ : ε₀ = ε := by
      apply AlgHom.ext
      intro a
      exact RingHom.congr_fun (ha₀.1.trans ha.1.symm) a
    subst ε₀
    obtain ⟨c₀, hc₀, hu⟩ := canonical_differential_tensor (LaurentSeries k)
      (OriginStalk k M s hs.1) ε hp₀ hn₀ 24
    have hcq : c' = c := (hu c' hc').trans (hu c hc).symm
    subst c'
    exact hd'
  · intro δ hδ
    have hparam := normalized_parameter k M s hs.1 ε κ ha e he' δ
      (origin_logarithmic_taylor k r hr h3 he T M hM s hs G hG X Y hX hY δ hδ) π.1 hπ
    refine ⟨?_, ?_⟩
    · intro hz
      apply hn
      have hvzero := v.injective (hz.trans (map_zero v).symm)
      change PiTensorProduct.congr (fun _ : Fin 24 => e) (c.symm (gradeClass ε 24 b)) = 0 at hvzero
      exact (PiTensorProduct.congr (fun _ : Fin 24 => e)).injective
        (hvzero.trans (map_zero _).symm)
    · dsimp only [d]
      rw [ht, map_smul, map_smul, PiTensorProduct.map_tprod]
      change ArithmeticThetaUnaryKatoPowerR0160.discriminant k r •
        v (PiTensorProduct.tprod (LaurentSeries k) (fun _ : Fin 24 => e (differentialClass ε π.1))) = _
      rw [hparam, hv]
      rfl

end ArithmeticThetaHodgeInitialR0163
#print axioms ArithmeticThetaHodgeInitialR0163.geometric_discriminant_hodge

