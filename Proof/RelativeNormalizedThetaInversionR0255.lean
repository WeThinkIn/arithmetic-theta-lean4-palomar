module

public import RelativeThetaLiftsDefinitionsR0255

@[expose] public section

/-! Normalized inversion on the entire relative theta line. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaLiftsR0255
namespace RelativeNormalizedThetaInversion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedMarkedIdealSpecializationR0136
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open ArithmeticThetaPolygonCartierR0133

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

lemma zero_over : zero E ≫ E.projection = 𝟙 _ := (E.law.one (𝟙 _)).property

instance zero_closed : IsClosedImmersion (zero E) := by
  letI := E.proper
  letI : IsClosedImmersion (zero E ≫ E.projection) := by
    rw [zero_over]
    infer_instance
  exact IsClosedImmersion.of_comp (zero E) E.projection

lemma zero_cartier : (zero E).ker.IsInvertible := by
  letI := E.proper
  letI := E.smooth
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (zero E) (zero_over E)

abbrev hodge : (base (R := R)).Modules :=
  (Scheme.Modules.pullback (zero E)).obj E.projection.kaehler

lemma differential_invertible : Scheme.Modules.IsInvertible E.projection.kaehler := by
  letI := E.smooth
  exact (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
    (E.projection.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1

lemma hodge_invertible : Scheme.Modules.IsInvertible (hodge E) :=
  (differential_invertible E).pullback (zero E)

lemma line_invertible (m : ℕ) : Scheme.Modules.IsInvertible
    (ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m) :=
  ((zero_cartier E).pow m).isInvertible_module.dual.1.tensor_monoidalV2
    (((hodge_invertible E).tensorPow m).pullback E.projection)

/-- The derivation-defined relative conormal isomorphism. -/
def conormalIso : (Scheme.Modules.pullback (zero E)).obj (zero E).ker.module ≅ hodge E := by
  letI := E.smooth
  letI := Conormal.section_conormal_isIso E.projection (zero E) (zero_over E)
    (zero_cartier E) (differential_invertible E)
  exact asIso (Conormal.conormalMap E.projection (zero E))

/-- The zeroth ideal power is the unit module even over the zero ring. -/
def topIdealIso (X : Scheme.{u}) : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support.TopOffSupport.nonempty_module_top_iso X).some

/-- Conormal powers, with the unit comparison included at exponent zero. -/
def powerConormalIso : (m : ℕ) →
    (Scheme.Modules.pullback (zero E)).obj ((zero E).ker ^ m).module ≅
      (hodge E).tensorPow m
  | 0 => by
    rw [pow_zero]
    letI := ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133.unitPullback_isIso (zero E)
    exact (Scheme.Modules.pullback (zero E)).mapIso (topIdealIso E.curve) ≪≫
      asIso (unitPullback (zero E))
  | 1 => by
    simpa only [pow_one] using conormalIso E ≪≫ (Scheme.Modules.tensorPowOneIso (hodge E)).symm
  | m+2 => by
    rw [pow_succ]
    exact (Scheme.Modules.pullback (zero E)).mapIso
      (idealTensorIso ((zero_cartier E).pow (m+1)) (zero_cartier E)).symm ≪≫
      Scheme.Modules.pullbackTensorObjIso (zero E) _ _ ≪≫
      (powerConormalIso (m+1) ⊗ᵢ conormalIso E)

/-- The actual identity fibre of the dual origin ideal power. -/
def dualPowerConormalIso (m : ℕ) :
    (Scheme.Modules.pullback (zero E)).obj (Scheme.Modules.dual (((zero E).ker ^ m).module)) ≅
      Scheme.Modules.dual ((hodge E).tensorPow m) := by
  letI := dualComparison_isIso (zero E) ((zero E).ker ^ m).module
    ((zero_cartier E).pow m).isInvertible_module
  exact asIso (dualComparison (zero E) _) ≪≫
    ((MonoidalClosed.internalHom (C := (base (R := R)).Modules)).mapIso
      (powerConormalIso E m).symm.op).app (𝟙_ (base (R := R)).Modules)

/-- Cancel the Hodge power against its conormal dual, without a Hodge frame. -/
def rigidification (m : ℕ) :
    (Scheme.Modules.pullback (zero E)).obj (ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m) ≅
      𝟙_ (base (R := R)).Modules := by
  let W := (hodge E).tensorPow m
  let eW : (Scheme.Modules.pullback (zero E)).obj
      ((Scheme.Modules.pullback E.projection).obj W) ≅ W :=
    (Scheme.Modules.pullbackComp (zero E) E.projection).app W ≪≫
      ((Scheme.Modules.pullbackCongr (zero_over E)) ≪≫ Scheme.Modules.pullbackId _).app W
  letI := ((hodge_invertible E).tensorPow m).isIso_ihom_ev_app_monoidalV2.1
    (𝟙_ (base (R := R)).Modules)
  exact Scheme.Modules.pullbackTensorObjIso (zero E) _ _ ≪≫
    (dualPowerConormalIso E m ⊗ᵢ eW) ≪≫ (β_ (Scheme.Modules.dual W) W) ≪≫
    asIso ((ihom.ev W).app (𝟙_ (base (R := R)).Modules))

lemma inverse_natural {T T' : Scheme.{u}} (t : T ⟶ base (R := R))
    (t' : T' ⟶ base (R := R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t E.projection) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (E.law.inv t a) =
      E.law.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  letI := E.law.pointGroup t'
  have hmul : E.law.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (E.law.inv t a))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ a) = E.law.one t' := by
    rw [← E.law.mul_natural t t' ψ hψ, E.law.inv_mul_cancel, E.law.one_natural]
  exact eq_inv_of_mul_eq_one_left hmul

lemma inverse_over : inverse E ≫ E.projection = E.projection :=
  (E.law.inv E.projection ⟨𝟙 E.curve, Category.id_comp E.projection⟩).property

lemma inverse_square : inverse E ≫ inverse E = 𝟙 E.curve := by
  let a : SchemeHomOver E.projection E.projection := ⟨𝟙 E.curve, Category.id_comp _⟩
  let n := E.law.inv E.projection a
  have hn : GoodReductionJacobian.schemeHomOverComp n.val n.property a = n := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural E E.projection E.projection n.val n.property a
  rw [hn] at h
  have hi : E.law.inv E.projection (E.law.inv E.projection a) = a := by
    letI := E.law.pointGroup E.projection
    exact inv_inv a
  exact congrArg Subtype.val (h.trans hi)

def inversionIso : E.curve ≅ E.curve where
  hom := inverse E
  inv := inverse E
  hom_inv_id := inverse_square E
  inv_hom_id := inverse_square E

lemma inverse_zero : zero E ≫ inverse E = zero E := by
  let a : SchemeHomOver E.projection E.projection := ⟨𝟙 E.curve, Category.id_comp _⟩
  let z := E.law.one (𝟙 _)
  have hz : GoodReductionJacobian.schemeHomOverComp z.val z.property a = z := by
    apply Subtype.ext
    exact Category.comp_id _
  have h := inverse_natural E E.projection (𝟙 _) z.val z.property a
  rw [hz] at h
  have hi : E.law.inv (𝟙 _) z = z := by
    letI := E.law.pointGroup (𝟙 _)
    exact inv_one
  exact congrArg Subtype.val (h.trans hi)

lemma ideal_inverse : (zero E).ker.comap (inverse E) = (zero E).ker := by
  letI : IsIso (inverse E) := (inversionIso E).isIso_hom
  exact ker_baseChange (IsPullback.of_vert_isIso
    (show CommSq (zero E) (𝟙 _) (inverse E) (zero E) from
      ⟨by rw [inverse_zero, Category.id_comp]⟩))

def dualPowerInverseIso (m : ℕ) :
    (Scheme.Modules.pullback (inverse E)).obj (Scheme.Modules.dual (((zero E).ker ^ m).module)) ≅
      Scheme.Modules.dual (((zero E).ker ^ m).module) := by
  let e := idealPullbackIso (inverse E) ((zero E).ker ^ m) ((zero E).ker ^ m)
    ((zero_cartier E).pow m) ((zero_cartier E).pow m)
    (by rw [comap_power, ideal_inverse])
  letI := dualComparison_isIso (inverse E) ((zero E).ker ^ m).module
    ((zero_cartier E).pow m).isInvertible_module
  exact asIso (dualComparison (inverse E) _) ≪≫
    ((MonoidalClosed.internalHom (C := E.curve.Modules)).mapIso e.symm.op).app
      (𝟙_ E.curve.Modules)

/-- An unnormalized lift constructed from the actual invariant ideal. -/
def initialLift (m : ℕ) : Lift E m (inverse E) :=
  Scheme.Modules.pullbackTensorObjIso (inverse E) _ _ ≪≫
    (dualPowerInverseIso E m ⊗ᵢ
      ((Scheme.Modules.pullbackComp (inverse E) E.projection).app ((hodge E).tensorPow m) ≪≫
        (Scheme.Modules.pullbackCongr (inverse_over E)).app ((hodge E).tensorPow m)))

/-- Adapt the given law, with every geometric map and operation retained. -/
def relativeFamily : ArithmeticThetaLocalWeierstrassR0203.Family (base (R := R)) where
  curve := E.curve
  p := E.projection
  law := {
    mul := E.law.mul
    one := E.law.one
    inv := E.law.inv
    mul_assoc := E.law.mul_assoc
    one_mul := E.law.one_mul
    mul_one := E.law.mul_one
    inv_mul_cancel := E.law.inv_mul_cancel
    mul_comm := E.commutative
    mul_natural := E.law.mul_natural }
  proper := E.proper
  dimension := E.smooth
  connected := E.connected

lemma constants_bijective : Function.Bijective
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ E.projection.appTop).hom) := by
  exact (ArithmeticThetaKatoCharacterizationR0254.GlobalUnitTwoThreeNormRigidity.structure_app_bijective
    (relativeFamily E) ⊤).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective

lemma unique_fixed_lift (m : ℕ) :
    ∃! φ : Lift E m (inverse E),
      (Scheme.Modules.pullback (zero E)).mapIso φ =
        fixedComparison E m (zero E) (inverse E) (inverse_zero E) := by
  let M := (Scheme.Modules.pullback (inverse E)).obj (ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m)
  let N := ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m
  let β := rigidification E m
  let c := fixedComparison E m (zero E) (inverse E) (inverse_zero E)
  obtain ⟨φ, hφ⟩ := Polarisation.nonempty_rigidifiedIso_of_iso
    E.projection (constants_bijective E) (zero E) (zero_over E) M N (c ≪≫ β) β (initialLift E m)
  haveI := Polarisation.subsingleton_rigidifiedIso
    E.projection (constants_bijective E) (zero E) (zero_over E) M N
    ((line_invertible E m).pullback _) (c ≪≫ β) β
  have he : (Scheme.Modules.pullback (zero E)).mapIso φ = c := by
    apply Iso.ext
    exact (cancel_mono β.hom).mp (congrArg Iso.hom hφ)
  refine ⟨φ, he, fun ψ hψ => ?_⟩
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨ψ, by rw [hψ]⟩ : {ψ : M ≅ N // (Scheme.Modules.pullback (zero E)).mapIso ψ ≪≫ β = c ≪≫ β})
    ⟨φ, hφ⟩)

lemma rigidifiedAut_eq_refl (m : ℕ)
    (φ : ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m ≅ ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m)
    (hφ : (Scheme.Modules.pullback (zero E)).mapIso φ ≪≫ rigidification E m = rigidification E m) :
    φ = Iso.refl _ := by
  let M := ArithmeticThetaRelativeThetaLiftsR0255.thetaLine E m
  let α := rigidification E m
  haveI := Polarisation.subsingleton_rigidifiedIso
    E.projection (constants_bijective E) (zero E) (zero_over E) M M (line_invertible E m) α α
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨φ, hφ⟩ : {ψ : M ≅ M // (Scheme.Modules.pullback (zero E)).mapIso ψ ≪≫ α = α})
    ⟨Iso.refl _, by simp⟩)

lemma normalized_exists_unique (m : ℕ) :
    ∃! φ : Lift E m (inverse E), NormalizedInversion E m φ := by
  obtain ⟨φ, hφ, hu⟩ := unique_fixed_lift E m
  refine ⟨φ, ⟨⟨inverse_zero E, hφ⟩, ⟨inverse_square E, ?_⟩⟩, ?_⟩
  · exact FixedPointPullback.square_of_rigidified (zero E) (inverse E)
      (inverse_zero E) (inverse_square E) _ _ (rigidification E m) φ
      (by rw [hφ]; rfl) (rigidifiedAut_eq_refl E m)
  · intro ψ hψ
    obtain ⟨h, hh⟩ := hψ.1
    exact hu ψ hh

end RelativeNormalizedThetaInversion

/-- Unique identity-normalized inversion on the full relative theta line,
including exponent zero and arbitrary Noetherian rational bases. -/
theorem relative_normalized_theta_inversion :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R), ∀ m : ℕ,
      AlgebraicGeometry.Scheme.Modules.IsInvertible (thetaLine E m) ∧
        ∃! ι : Lift E m (inverse E), NormalizedInversion E m ι := by
  intro R _ _ _ E m
  exact ⟨RelativeNormalizedThetaInversion.line_invertible E m,
    RelativeNormalizedThetaInversion.normalized_exists_unique E m⟩

#print axioms relative_normalized_theta_inversion
end ArithmeticThetaRelativeThetaLiftsR0255
