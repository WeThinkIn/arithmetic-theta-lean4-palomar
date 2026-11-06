module

public import CompletedRingModuleComparison
public import CompletedRingRestrictions
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

@[expose] public section

open AlgebraicGeometry CategoryTheory
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ArithmeticThetaFormalConstants

section LocalizationComparison
variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  (t : R)

/-- The ring localization is a localization of the structural base module. -/
instance structuralIsLocalizedModule :
    IsLocalizedModule (Submonoid.powers t)
      (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B t))).toLinearMap := by
  apply isLocalizedModule_iff_isLocalization.mpr
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
    (inferInstance : IsLocalization (Submonoid.powers (algebraMap R B t))
      (Localization.Away (algebraMap R B t)))

variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Localize a linear equivalence using the actual structural scalar map. -/
def structuralLocalizedEquiv (e : B ≃ₗ[R] M) :
    Localization.Away (algebraMap R B t) ≃ₗ[R] LocalizedModule (Submonoid.powers t) M :=
  LinearEquiv.ofBijective
    (IsLocalizedModule.map (Submonoid.powers t)
      (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B t))).toLinearMap
      (LocalizedModule.mkLinearMap _ M) e.toLinearMap)
    ⟨IsLocalizedModule.map_injective _ _ _ _ e.injective,
      IsLocalizedModule.map_surjective _ _ _ _ e.surjective⟩

lemma structuralLocalizedEquiv_apply (e : B ≃ₗ[R] M) (b : B) :
    structuralLocalizedEquiv R B t e (algebraMap B _ b) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) M (e b) :=
  IsLocalizedModule.map_apply _ _ _ _ _
end LocalizationComparison

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)) (t : R)

lemma ringParameter_eq (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    ringParameter R X f t U = algebraMap R (RingCompleted R X f t U) t := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact (IsScalarTower.algebraMap_apply R Γ(X, U) (RingCompleted R X f t U) t).symm

def canonicalLocalizedEquivalences (e : CompletionEquivalences R X f t) :
    LocalizedEquivalences R X f t := fun U => by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact structuralLocalizedEquiv R (RingCompleted R X f t U) t (e U)

lemma canonicalLocalizedEquivalences_matches (e : CompletionEquivalences R X f t) :
    MatchesLocalization R X f t e (canonicalLocalizedEquivalences R X f t e) := by
  intro U a
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  exact structuralLocalizedEquiv_apply R (RingCompleted R X f t U) t (e U) a

/-- Extension of a sheaf restriction preserves all structural scalars. -/
lemma completedRestriction_scalar {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi) (r : R) :
    phi (ringOf R X f t U (structuralMap R X f U r)) =
      ringOf R X f t V (structuralMap R X f V r) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  rw [hphi]
  congr 1
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom f h).commutes r

/-- The completed extension has the structural R-linearity forced by its values. -/
def completedRestrictionAlgHom {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
    RingCompleted R X f t U →ₐ[R] RingCompleted R X f t V := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  exact { phi with commutes' := completedRestriction_scalar R X f t h phi hphi }

lemma completion_naturality (e : CompletionEquivalences R X f t)
    (he : MatchesCompletion R X f t e) {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi) (a : RingCompleted R X f t U) :
    e V (phi a) = ArithmeticThetaCompletedCharts.completedRestriction R X f t h (e U a) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  let p := completedRestrictionAlgHom R X f t h phi hphi
  have hh : (e V).toLinearMap.comp (p.toLinearMap.comp (e U).symm.toLinearMap) =
      ArithmeticThetaCompletedCharts.completedRestriction R X f t h := by
    apply Comparison.linearMap_ext_of (Ideal.span {t}) (Submodule.fg_span_singleton t)
    intro b
    change e V (phi ((e U).symm (AdicCompletion.of _ _ b))) = _
    rw [← he U b, LinearEquiv.symm_apply_apply]
    change e V (phi (ringOf R X f t U (show Γ(X, U) from b))) = _
    rw [hphi, he, he]
    symm
    exact AdicCompletion.map_of _ _ _
  have hh' := LinearMap.congr_fun hh (e U a)
  change e V (phi ((e U).symm (e U a))) = _ at hh'
  simpa only [LinearEquiv.symm_apply_apply] using hh'

/-- The actual completed restriction inverts the actual target parameter. -/
def localizedRingRestriction {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi) :
    LocalizedRing R X f t U →+* LocalizedRing R X f t V :=
  IsLocalization.Away.lift (ringParameter R X f t U)
    (show IsUnit ((localizedOf R X f t V).comp phi (ringParameter R X f t U)) from by
      change IsUnit (localizedOf R X f t V (phi (ringParameter R X f t U)))
      rw [show phi (ringParameter R X f t U) = ringParameter R X f t V from
        completedRestriction_scalar R X f t h phi hphi t]
      exact IsLocalization.Away.algebraMap_isUnit (ringParameter R X f t V))

lemma localizedRingRestriction_extends {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi) :
    ExtendsLocalization R X f t phi (localizedRingRestriction R X f t h phi hphi) :=
  fun a => IsLocalization.Away.lift_eq _ _ a

lemma localizedRingRestriction_unique {U V : X.Opens}
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (p q : LocalizedRing R X f t U →+* LocalizedRing R X f t V)
    (hp : ExtendsLocalization R X f t phi p) (hq : ExtendsLocalization R X f t phi q) :
    p = q := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ringParameter R X f t U))
  exact RingHom.ext (fun a => (hp a).trans (hq a).symm)

/-- Scalar compatibility of the ring extension after localization. -/
def localizedRestrictionAlgHom {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi)
    (psi : LocalizedRing R X f t U →+* LocalizedRing R X f t V)
    (hpsi : ExtendsLocalization R X f t phi psi) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
    LocalizedRing R X f t U →ₐ[R] LocalizedRing R X f t V := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  refine { psi with commutes' := fun r => ?_ }
  rw [IsScalarTower.algebraMap_apply R (RingCompleted R X f t U) (LocalizedRing R X f t U),
    IsScalarTower.algebraMap_apply R (RingCompleted R X f t V) (LocalizedRing R X f t V)]
  exact (hpsi _).trans (congrArg (localizedOf R X f t V)
    (completedRestriction_scalar R X f t h phi hphi r))

lemma localization_naturality (e : CompletionEquivalences R X f t)
    (he : MatchesCompletion R X f t e) (ell : LocalizedEquivalences R X f t)
    (hell : MatchesLocalization R X f t e ell) {U V : X.Opens} (h : V ≤ U)
    (phi : RingCompleted R X f t U →+* RingCompleted R X f t V)
    (hphi : ExtendsRestriction R X f t h phi)
    (psi : LocalizedRing R X f t U →+* LocalizedRing R X f t V)
    (hpsi : ExtendsLocalization R X f t phi psi) (z : LocalizedRing R X f t U) :
    ell V (psi z) = ArithmeticThetaCompletedCharts.localizedRestriction R X f t h (ell U z) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI : IsLocalizedModule (Submonoid.powers t)
      (IsScalarTower.toAlgHom R (RingCompleted R X f t U) (LocalizedRing R X f t U)).toLinearMap :=
    structuralIsLocalizedModule R (RingCompleted R X f t U) t
  let p := localizedRestrictionAlgHom R X f t h phi hphi psi hpsi
  have hh : (ell V).toLinearMap.comp p.toLinearMap =
      (ArithmeticThetaCompletedCharts.localizedRestriction R X f t h).comp
        (ell U).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers t)
      (IsScalarTower.toAlgHom R (RingCompleted R X f t U) (LocalizedRing R X f t U)).toLinearMap
      (ArithmeticThetaCompletedCharts.toLocalized R X f t V)
    apply LinearMap.ext
    intro a
    change ell V (psi (localizedOf R X f t U a)) =
      ArithmeticThetaCompletedCharts.localizedRestriction R X f t h
        (ell U (localizedOf R X f t U a))
    rw [hpsi, hell, hell, completion_naturality R X f t e he h phi hphi]
    symm
    exact IsLocalizedModule.map_apply _ _ _ _ _
  exact LinearMap.congr_fun hh z

lemma localizedEquivalences_unique (e : CompletionEquivalences R X f t)
    (p q : LocalizedEquivalences R X f t)
    (hp : MatchesLocalization R X f t e p) (hq : MatchesLocalization R X f t e q) : p = q := by
  funext U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI : IsLocalizedModule (Submonoid.powers t)
      (IsScalarTower.toAlgHom R (RingCompleted R X f t U) (LocalizedRing R X f t U)).toLinearMap :=
    structuralIsLocalizedModule R (RingCompleted R X f t U) t
  apply LinearEquiv.toLinearMap_injective
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers t)
    (IsScalarTower.toAlgHom R (RingCompleted R X f t U) (LocalizedRing R X f t U)).toLinearMap
    (ArithmeticThetaCompletedCharts.toLocalized R X f t U)
  exact LinearMap.ext (fun a => (hp U a).trans (hq U a).symm)

/-- The localization comparison and all actual restriction squares, uniquely. -/
theorem localized_ring_module_naturality
    (e : CompletionEquivalences R X f t) (he : MatchesCompletion R X f t e) :
    ∃! ell : LocalizedEquivalences R X f t,
      MatchesLocalization R X f t e ell ∧
      ∀ (U V : X.Opens) (h : V ≤ U),
      ∃! phi : RingCompleted R X f t U →+* RingCompleted R X f t V,
        ExtendsRestriction R X f t h phi ∧
        ∃! psi : LocalizedRing R X f t U →+* LocalizedRing R X f t V,
          ExtendsLocalization R X f t phi psi ∧
          ∀ z : LocalizedRing R X f t U,
            ell V (psi z) = ArithmeticThetaCompletedCharts.localizedRestriction R X f t h (ell U z) := by
  let ell := canonicalLocalizedEquivalences R X f t e
  have hell : MatchesLocalization R X f t e ell := canonicalLocalizedEquivalences_matches R X f t e
  refine ⟨ell, ⟨hell, ?_⟩, fun q hq => localizedEquivalences_unique R X f t e q ell hq.1 hell⟩
  intro U V h
  obtain ⟨phi, hphi, uphi⟩ := completed_ring_restrictions R X f t U V h
  refine ⟨phi, ⟨hphi, ?_⟩, fun q hq => uphi q hq.1⟩
  let psi := localizedRingRestriction R X f t h phi hphi
  have hpsi : ExtendsLocalization R X f t phi psi := localizedRingRestriction_extends R X f t h phi hphi
  refine ⟨psi, ⟨hpsi, localization_naturality R X f t e he ell hell h phi hphi psi hpsi⟩, ?_⟩
  intro q hq
  exact localizedRingRestriction_unique R X f t phi q psi hq.1 hpsi

end ArithmeticThetaFormalConstants
