import GeometricDiscriminantHodgeR0163

/-! The integral discriminant tensor on the completed Tate base. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaHodgeInitialR0163
namespace IntegralDiscriminantHodgeR0163
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaIntegralHodgeR0149
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

lemma frame_one {S : Scheme.{u}} {F : S.Modules}
    (e : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ F) (n : ℕ) :
    Scheme.Modules.Hom.app (powerFrame e n).hom ⊤ (1 : Γ(S, ⊤)) =
      tensorPowerSection S F n ⊤ (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(S, ⊤))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hu : (tensorLeftUnitIso S (SheafOfModules.unit S.ringCatSheaf)).inv.app ⊤
        (1 : Γ(S, ⊤)) = tensorSection S (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit S.ringCatSheaf) ⊤ (1 : Γ(S, ⊤)) (1 : Γ(S, ⊤)) := by
      apply (ConcreteCategory.bijective_of_isIso
        ((tensorLeftUnitIso S (SheafOfModules.unit S.ringCatSheaf)).hom.app ⊤)).1
      rw [tensorLeftUnitIso_section]
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
      rfl
    change (sheafTensorCongr S (powerFrame e n) e).hom.app ⊤
      ((tensorLeftUnitIso S _).inv.app ⊤ (1 : Γ(S, ⊤))) = _
    rw [hu, sheafTensorCongr_section, ih]
    rfl

lemma frame_apply {S : Scheme.{u}} {F : S.Modules}
    (e : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ F)
    (n : ℕ) (a : Γ(S, ⊤)) :
    Scheme.Modules.Hom.app (powerFrame e n).hom ⊤ a = a •
      tensorPowerSection S F n ⊤ (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(S, ⊤))) := by
  rw [← frame_one, ← Scheme.Modules.Hom.app_smul]
  congr 1
  exact (mul_one a).symm

lemma congr_section {S : Scheme.{u}} {F H : S.Modules} (e : F ≅ H)
    (n : ℕ) (z : Γ(F, ⊤)) :
    (powerCongr e n).hom.app ⊤ (tensorPowerSection S F n ⊤ z) =
      tensorPowerSection S H n ⊤ (Scheme.Modules.Hom.app e.hom ⊤ z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sheafTensorCongr S (powerCongr e n) e).hom.app ⊤
      (tensorSection S _ _ ⊤ (tensorPowerSection S F n ⊤ z) z) = _
    rw [sheafTensorCongr_section, ih]
    rfl

variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
variable (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
variable (b : GenericComparison k M) (E : IntegralFrame k M s) (δ : Frame k M)

lemma extends_one (hE : ExtendsFrame k M s hs b E δ) :
    (fiberComparison k M s hs b).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericBase k) (Scheme.Modules.Hom.app E.hom ⊤ (1 : Γ(baseScheme k, ⊤)))) =
      hodgeSection k M s hs δ 1 := by
  have h := congrArg (fun f => Scheme.Modules.Hom.app f ⊤
    (Scheme.Modules.pullbackLocalSection (genericBase k)
      (L := (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules))
      (1 : Γ(baseScheme k, ⊤)))) hE
  change (fiberComparison k M s hs b).hom.app ⊤
      (((Scheme.Modules.pullback (genericBase k)).map E.hom).app ⊤ _) =
    Scheme.Modules.Hom.app (hodgeFrame k M s hs δ).hom ⊤ ((unitPullback (genericBase k)).app ⊤ _) at h
  have hn := Scheme.Modules.pullbackLocalSection_app (genericBase k) E.hom
    (U := ⊤) (1 : Γ(baseScheme k, ⊤))
  have hu := GenericDualLocalizationR0140.unitPullback_app (genericBase k) ⊤
    (1 : Γ(baseScheme k, ⊤))
  have hleft := congrArg (fun z => (fiberComparison k M s hs b).hom.app ⊤ z) hn
  have hright := congrArg (fun z : Γ(Spec (CommRingCat.of (LaurentSeries k)), ⊤) =>
    Scheme.Modules.Hom.app (hodgeFrame k M s hs δ).hom ⊤ z)
    (hu.trans (map_one ((genericBase k).app ⊤).hom))
  simpa only [hodgeSection, map_one] using hleft.trans (h.trans hright)

lemma restriction_frame (hE : ExtendsFrame k M s hs b E δ) (n : ℕ)
    (a : Γ(baseScheme k, ⊤)) :
    powerRestriction k M s hs b n (Scheme.Modules.Hom.app (powerFrame E n).hom ⊤ a) =
      (genericBase k).appTop a • tensorPowerSection _ (Hodge k M s hs) n ⊤
        (hodgeSection k M s hs δ 1) := by
  rw [frame_apply]
  unfold powerRestriction
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_smul]
  congr 1
  rw [show Scheme.Modules.pullbackLocalSection (genericBase k)
      (tensorPowerSection (baseScheme k) (IntegralHodge k M s) n ⊤ (Scheme.Modules.Hom.app E.hom ⊤ (1 : Γ(baseScheme k, ⊤)))) =
    pullbackGlobalSection (genericBase k) _
      (tensorPowerSection (baseScheme k) (IntegralHodge k M s) n ⊤ (Scheme.Modules.Hom.app E.hom ⊤ (1 : Γ(baseScheme k, ⊤)))) from rfl]
  erw [pullback_tensorPower_section]
  erw [congr_section, extends_one k M s hs b E δ hE]

lemma restriction_injective (hE : ExtendsFrame k M s hs b E δ) (n : ℕ) :
    Function.Injective (powerRestriction k M s hs b n) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app (powerFrame E n).hom ⊤)).2 q
  obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app (powerFrame E n).hom ⊤)).2 q'
  rw [restriction_frame k M s hs b E δ hE, restriction_frame k M s hs b E δ hE] at h
  have h' : Scheme.Modules.Hom.app (powerFrame (hodgeFrame k M s hs δ) n).hom ⊤ ((genericBase k).appTop a) =
      Scheme.Modules.Hom.app (powerFrame (hodgeFrame k M s hs δ) n).hom ⊤ ((genericBase k).appTop a') := by
    simpa only [frame_apply, hodgeSection, map_one] using h
  have hh := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (powerFrame (hodgeFrame k M s hs δ) n).hom ⊤)).1 h'
  letI := GenericDualLocalizationR0140.genericBase_schematic k
  exact congrArg _ ((genericBase k).app_injective ⊤ hh)

lemma scalar_restriction (a : PowerSeries k) :
    (genericBase k).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
        (algebraMap (PowerSeries k) (LaurentSeries k) a) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) a).symm

lemma series_order (r : ℕ) (hr : 0 < r) :
    (discriminantSeries k r).order = ((2*r : ℕ) : ENat) := by
  have hp : PowerSeries.HasSubst (PowerSeries.X^r : PowerSeries k) :=
    PowerSeries.HasSubst.X_pow (Nat.ne_of_gt hr)
  have hu : PowerSeries.order (PowerSeries.subst (PowerSeries.X^r : PowerSeries k)
      (PowerSeries.map (algebraMap ℚ k) ArithmeticThetaDiscriminant.P)) = 0 := by
    apply (PowerSeries.order_eq_nat (n := 0)).2
    constructor
    · rw [PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.constantCoeff_subst_X_pow (Nat.ne_of_gt hr),
        ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, ArithmeticThetaDiscriminant.P_constant, map_one]
      exact one_ne_zero
    · intro i hi
      omega
  unfold discriminantSeries
  rw [map_mul, map_pow, PowerSeries.map_X, map_pow,
    PowerSeries.subst_mul hp, PowerSeries.subst_pow hp, PowerSeries.subst_X hp,
    PowerSeries.subst_pow hp, PowerSeries.order_mul, PowerSeries.order_pow,
    PowerSeries.order_X_pow, PowerSeries.order_pow, hu]
  simp [nsmul_eq_mul, Nat.cast_mul]

end IntegralDiscriminantHodgeR0163
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaTensorPower ArithmeticThetaIntegralHodgeR0149
open IntegralDiscriminantHodgeR0163

/-- The unique integral extension, with full coefficient and exact nonzero order. -/
theorem integral_discriminant_hodge :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (b : ArithmeticThetaIntegralHodgeR0149.GenericComparison k M), ArithmeticThetaIntegralHodgeR0149.IsGenericComparison k M b → ∀ (E : ArithmeticThetaIntegralHodgeR0149.IntegralFrame k M s), ArithmeticThetaIntegralHodgeR0149.ExtendsFrame k M s hs.1 b E δ → ∀ (g : AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G 5 g → ∃ q : ((ArithmeticThetaHodgeInitialR0163.IntegralPower k M s 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs.1 g (ArithmeticThetaHodgeInitialR0163.powerRestriction k M s hs.1 b 24 q) ∧ (∀ q' : ((ArithmeticThetaHodgeInitialR0163.IntegralPower k M s 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs.1 g (ArithmeticThetaHodgeInitialR0163.powerRestriction k M s hs.1 b 24 q') → q' = q) ∧ ArithmeticThetaHodgeInitialR0163.powerCoefficient k M s E 24 q = ArithmeticThetaHodgeInitialR0163.discriminantSeries k r ∧ ArithmeticThetaHodgeInitialR0163.powerCoefficient k M s E 24 q ≠ 0 ∧ (ArithmeticThetaHodgeInitialR0163.powerCoefficient k M s E 24 q).order = ((2*r : ℕ) : ENat) := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ X Y hX hY δ hδ b hb E hE g hg
  obtain ⟨d, hd, hdu, hexp⟩ := geometric_discriminant_hodge
    k r hr h3 he T M hM s hs G hG X Y hX hY g hg
  let a : Γ(baseScheme k, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (discriminantSeries k r)
  let q : Γ(IntegralPower k M s 24, ⊤) := Scheme.Modules.Hom.app (powerFrame E 24).hom ⊤ a
  have hq : powerRestriction k M s hs.1 b 24 q = d := by
    dsimp only [q]
    rw [restriction_frame k M s hs.1 b E δ hE]
    rw [(hexp δ hδ).2]
    congr 1
    exact scalar_restriction k (discriminantSeries k r)
  have hc : powerCoefficient k M s E 24 q = discriminantSeries k r := by
    unfold powerCoefficient
    dsimp only [q]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    change (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (discriminantSeries k r)) = _
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv_hom_id _
  have ho := series_order k r hr
  have hn : discriminantSeries k r ≠ 0 := by
    intro hz
    rw [hz, PowerSeries.order_zero] at ho
    exact ENat.top_ne_natCast _ ho
  refine ⟨q, ?_, ?_, hc, hc ▸ hn, hc ▸ ho⟩
  · rw [hq]
    exact hd
  · intro q' hq'
    apply restriction_injective k M s hs.1 b E δ hE 24
    exact (hdu _ hq').trans hq.symm

end ArithmeticThetaHodgeInitialR0163
#print axioms ArithmeticThetaHodgeInitialR0163.integral_discriminant_hodge
