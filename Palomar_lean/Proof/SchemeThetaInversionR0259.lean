module

public import SchemeThetaMarkingDefinitionsR0259

@[expose] public section

/-! Inversion of the actual conormal-rigidified theta line on any scheme base. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeThetaInversion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift

variable {S : Scheme.{u}} (E : Family S)

@[instance_reducible] def pointGroup {T : Scheme.{u}} (t : T ⟶ S) : Group (SchemeHomOver t E.p) where
  mul := E.law.mul t
  one := E.law.one t
  inv := E.law.inv t
  mul_assoc := E.law.mul_assoc t
  one_mul := E.law.one_mul t
  mul_one := E.law.mul_one t
  inv_mul_cancel := E.law.inv_mul_cancel t

lemma zero_over : E.zero ≫ E.p = 𝟙 S :=
  ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_section E

instance zero_closed : IsClosedImmersion E.zero := by
  letI := E.proper
  letI : IsClosedImmersion (E.zero ≫ E.p) := by rw [zero_over]; infer_instance
  exact IsClosedImmersion.of_comp E.zero E.p

lemma zero_cartier : E.zero.ker.IsInvertible :=
  ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E

lemma line_invertible (m : ℕ) : Scheme.Modules.IsInvertible (thetaLine E m) :=
  ((zero_cartier E).pow m).isInvertible_module.dual.1.tensor_monoidalV2
    ((((zero_cartier E).isInvertible_module.pullback E.zero).tensorPow m).pullback E.p)

lemma inverse_natural {T T' : Scheme.{u}} (t : T ⟶ S)
    (t' : T' ⟶ S) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t E.p) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (E.law.inv t a) =
      E.law.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  letI := pointGroup E t'
  have hmul : E.law.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (E.law.inv t a))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ a) = E.law.one t' := by
    rw [← E.law.mul_natural t t' ψ hψ, E.law.inv_mul_cancel, SchemeLocal.one_natural]
  exact eq_inv_of_mul_eq_one_left hmul

lemma inverse_over : inverse E ≫ E.p = E.p :=
  (E.law.inv E.p ⟨𝟙 E.curve, Category.id_comp E.p⟩).property

lemma inverse_square : inverse E ≫ inverse E = 𝟙 E.curve := by
  let a : SchemeHomOver E.p E.p := ⟨𝟙 E.curve, Category.id_comp _⟩
  let n := E.law.inv E.p a
  have hn : GoodReductionJacobian.schemeHomOverComp n.val n.property a = n := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural E E.p E.p n.val n.property a
  rw [hn] at h
  have hi : E.law.inv E.p (E.law.inv E.p a) = a := by
    letI := pointGroup E E.p
    exact inv_inv a
  exact congrArg Subtype.val (h.trans hi)

def inversionIso : E.curve ≅ E.curve where
  hom := inverse E
  inv := inverse E
  hom_inv_id := inverse_square E
  inv_hom_id := inverse_square E

lemma inverse_zero : E.zero ≫ inverse E = E.zero := by
  let a : SchemeHomOver E.p E.p := ⟨𝟙 E.curve, Category.id_comp _⟩
  let z := E.law.one (𝟙 _)
  have hz : GoodReductionJacobian.schemeHomOverComp z.val z.property a = z := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural E E.p (𝟙 _) z.val z.property a
  rw [hz] at h
  have hi : E.law.inv (𝟙 _) z = z := by
    letI := pointGroup E (𝟙 _)
    exact inv_one
  exact congrArg Subtype.val (h.trans hi)

lemma ideal_inverse : (E.zero).ker.comap (inverse E) = (E.zero).ker := by
  letI : IsIso (inverse E) := (inversionIso E).isIso_hom
  exact ker_baseChange (IsPullback.of_vert_isIso
    (show CommSq (E.zero) (𝟙 _) (inverse E) (E.zero) from
      ⟨by rw [inverse_zero, Category.id_comp]⟩))

def dualPowerInverseIso (m : ℕ) :
    (Scheme.Modules.pullback (inverse E)).obj (Scheme.Modules.dual (((E.zero).ker ^ m).module)) ≅
      Scheme.Modules.dual (((E.zero).ker ^ m).module) := by
  let e := idealPullbackIso (inverse E) ((E.zero).ker ^ m) ((E.zero).ker ^ m)
    ((zero_cartier E).pow m) ((zero_cartier E).pow m)
    (by rw [comap_power, ideal_inverse])
  letI := dualComparison_isIso (inverse E) ((E.zero).ker ^ m).module
    ((zero_cartier E).pow m).isInvertible_module
  exact asIso (dualComparison (inverse E) _) ≪≫
    ((MonoidalClosed.internalHom (C := E.curve.Modules)).mapIso e.symm.op).app
      (𝟙_ E.curve.Modules)

/-- An unnormalized lift constructed from the actual invariant ideal. -/
def initialLift (m : ℕ) : Lift E m (inverse E) :=
  Scheme.Modules.pullbackTensorObjIso (inverse E) _ _ ≪≫
    (dualPowerInverseIso E m ⊗ᵢ
      ((Scheme.Modules.pullbackComp (inverse E) E.p).app ((ArithmeticThetaSchemeHodgeR0205.Cotangent E).tensorPow m) ≪≫
        (Scheme.Modules.pullbackCongr (inverse_over E)).app ((ArithmeticThetaSchemeHodgeR0205.Cotangent E).tensorPow m)))

lemma structure_surjective : Function.Surjective E.p.appTop :=
  (ArithmeticThetaKatoCharacterizationR0254.GlobalUnitTwoThreeNormRigidity.structure_app_bijective E ⊤).surjective

lemma unique_fixed_lift (m : ℕ) :
    ∃! φ : Lift E m (inverse E),
      (Scheme.Modules.pullback E.zero).mapIso φ =
        fixedComparison E m E.zero (inverse E) (inverse_zero E) :=
  existsUnique_fibreIso E.p (structure_surjective E) E.zero (zero_over E)
    _ _ ((line_invertible E m).pullback _) _ (initialLift E m)

lemma normalized_square (m : ℕ) (φ : Lift E m (inverse E))
    (hφ : (Scheme.Modules.pullback E.zero).mapIso φ =
      fixedComparison E m E.zero (inverse E) (inverse_zero E)) :
    (Scheme.Modules.pullback (inverse E)).mapIso φ ≪≫ φ =
      squareComparison E m (inverse E) (inverse_square E) := by
  apply FixedPointPullback.square_of_rigidified E.zero (inverse E)
    (inverse_zero E) (inverse_square E) (thetaLine E m) _ (Iso.refl _) φ
  · simpa only [Iso.trans_refl, fixedComparison] using hφ
  · intro ψ hψ
    exact aut_eq_refl E.p (structure_surjective E) E.zero (zero_over E)
      (line_invertible E m) ψ (by simpa only [Iso.trans_refl] using hψ)

lemma normalized_exists_unique (m : ℕ) :
    ∃! ι : Lift E m (inverse E), NormalizedInversion E m ι := by
  obtain ⟨ι, hi, hu⟩ := unique_fixed_lift E m
  refine ⟨ι, ⟨⟨inverse_zero E, hi⟩, ⟨inverse_square E, normalized_square E m ι hi⟩⟩, ?_⟩
  intro ψ hψ
  obtain ⟨h, hh⟩ := hψ.1
  exact hu ψ hh

end SchemeThetaInversion

/-- Unique normalized inversion of the specified theta line, including degree zero. -/
theorem scheme_theta_inversion :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ m : ℕ,
      ∃! ι : Lift E m (inverse E), NormalizedInversion E m ι := by
  intro k _ _ S σ E m
  exact SchemeThetaInversion.normalized_exists_unique E m

#print axioms scheme_theta_inversion
end ArithmeticThetaSchemeThetaMarkingR0259
