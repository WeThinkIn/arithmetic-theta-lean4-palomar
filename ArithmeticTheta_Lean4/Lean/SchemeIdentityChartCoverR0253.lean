import KatoInitialDefinitionsR0253

/-! Actual ideal generators on arbitrarily small identity neighborhoods. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaKatoInitialR0253
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeKatoUnitR0250
open ArithmeticThetaSchemeHodgeR0205

namespace SchemeIdentityChartCover

/-- Restricting to the image of an open immersion preserves the full kernel,
including its nilpotent information. -/
lemma ker_comp_on_open {S T X : Scheme.{u}} (s : S ⟶ T) (i : T ⟶ X)
    [IsOpenImmersion s] [QuasiCompact i] [QuasiCompact (s ≫ i)]
    (U : X.affineOpens) (hU : i ⁻¹ᵁ U.1 ≤ s.opensRange) :
    (s ≫ i).ker.ideal U = i.ker.ideal U := by
  letI : IsIso (s.app (i ⁻¹ᵁ U.1)) := s.isIso_app _ hU
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  ext a
  simp only [RingHom.mem_ker, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  exact map_eq_zero_iff (s.app (i ⁻¹ᵁ U.1)).hom
    (ConcreteCategory.bijective_of_isIso (s.app (i ⁻¹ᵁ U.1))).1

/-- An invertible ideal has regular generators on arbitrarily small basic opens. -/
lemma small_generator {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible)
    (x : X) (V : X.Opens) (hx : x ∈ V) :
    ∃ (U : X.affineOpens) (a : Γ(X, U.1)),
      x ∈ U.1 ∧ U.1 ≤ V ∧ IsRegular a ∧ I.ideal U = Ideal.span {a} := by
  obtain ⟨U, f, hxf, a, ha, hIa⟩ := hI x
  let W := X.affineBasicOpen f
  obtain ⟨g, hgV, hxg⟩ := W.2.exists_basicOpen_le ⟨x, hx⟩ hxf
  let U' := X.affineBasicOpen g
  let hle : U'.1 ≤ W.1 := X.basicOpen_le g
  let F := X.presheaf.map (homOfLE hle).op
  refine ⟨U', F a, hxg, hgV, ?_, ?_⟩
  · letI := W.2.isLocalization_basicOpen g
    exact isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.nonZeroDivisors_le_comap (M := .powers g)
        (S := Γ(X, X.basicOpen g)) ha)
  · rw [← I.map_ideal hle, hIa, Ideal.map_span, Set.image_singleton]
    rfl

lemma multiplication_zero {S : Scheme.{u}} (E : Family S) (c : ℕ) :
    E.zero ≫ multiplication E c = E.zero := by
  have hn := congrArg Subtype.val
    (SchemeTorsionCartesian.multiple_natural E E.p (𝟙 S) E.zero
      (CartesianIdentityIdeal.zero_section E) c ⟨𝟙 E.curve, Category.id_comp E.p⟩)
  have he : GoodReductionJacobian.schemeHomOverComp E.zero
      (CartesianIdentityIdeal.zero_section E) ⟨𝟙 E.curve, Category.id_comp E.p⟩ =
      E.law.one (𝟙 S) := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp, Category.comp_id]
    rfl
  have hm : ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) c
      (E.law.one (𝟙 S)) = E.law.one (𝟙 S) := by
    clear hn
    induction c with
    | zero => rfl
    | succ n ih =>
      change E.law.mul _ (ArithmeticThetaSchemeLevelR0204.multiple E _ n _) _ = _
      rw [ih, E.law.one_mul]
  rw [he, hm] at hn
  exact hn

end SchemeIdentityChartCover

/-- Every identity point has arbitrarily small affine charts carrying an actual
regular ideal section, on which the entire positive torsion ideal is the identity ideal. -/
theorem scheme_identity_chart_cover :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ c : ℕ, 0 < c →
      ArithmeticThetaKatoInitialR0253.IdentityChartCover E c := by
  intro k _ _ S σ E c hc
  letI : IsProper E.p := E.proper
  letI : IsClosedImmersion (E.zero ≫ E.p) := by
    rw [CartesianIdentityIdeal.zero_section]
    infer_instance
  letI : IsClosedImmersion E.zero := IsClosedImmersion.of_comp E.zero E.p
  letI : Etale (multiplication E c) :=
    (scheme_multiplication_degree k S σ E c hc).2.1
  let T := pullback (multiplication E c) E.zero
  let i : T ⟶ E.curve := pullback.fst _ _
  let p : T ⟶ S := pullback.snd _ _
  let s : S ⟶ T := pullback.lift E.zero (𝟙 S)
    (by simpa using SchemeIdentityChartCover.multiplication_zero E c)
  have hsi : s ≫ i = E.zero := pullback.lift_fst _ _ _
  have hsp : s ≫ p = 𝟙 S := pullback.lift_snd _ _ _
  letI : IsOpenImmersion s :=
    ArithmeticThetaRelativeDiscriminantR0171.IdentityTorsionNeighborhood.section_open p s hsp
  letI : IsClosedImmersion (s ≫ i) := by rw [hsi]; infer_instance
  obtain ⟨V, hV, hVr⟩ :=
    ArithmeticThetaRelativeDiscriminantR0171.IdentityTorsionNeighborhood.isolate_section p s hsp i
  rw [hsi] at hV hVr
  intro z W hz
  obtain ⟨U, a, hzU, hUW, ha, hIa⟩ := SchemeIdentityChartCover.small_generator
    E.zero.ker (CartesianIdentityIdeal.zero_ideal_invertible E)
    (E.zero z) (W ⊓ V) ⟨hz, hV z⟩
  have haI : a ∈ E.zero.ker.ideal U := by
    rw [hIa]
    exact Ideal.subset_span (Set.mem_singleton a)
  have har : a ∈ Set.range (E.zero.ker.moduleι.app U.1) := by
    rw [(E.zero.ker.range_moduleIota_app_and_injective U).1]
    exact haI
  obtain ⟨x, hx⟩ := har
  refine ⟨U, x, hzU, fun y hy => (hUW hy).1, ?_⟩
  change IsRegular (equation E U.1 x) ∧ _ ∧ _
  have heq : equation E U.1 x = a := hx
  refine ⟨heq ▸ ha, ?_, ?_⟩
  · simpa only [identityIdeal, heq] using hIa
  · have hpre : i ⁻¹ᵁ U.1 ≤ s.opensRange := by
      intro y hy
      obtain ⟨w, hw⟩ := (hVr (i y) (hUW hy).2).mp (Set.mem_range_self y)
      refine ⟨w, i.isClosedEmbedding.injective ?_⟩
      change i (s w) = i y
      simpa only [← hsi, Scheme.Hom.comp_apply] using hw
    have hi : torsionIdeal E c = i.ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion E.zero (multiplication E c)).symm
    rw [hi, identityIdeal, ← hsi]
    exact (SchemeIdentityChartCover.ker_comp_on_open s i U hpre).symm

#print axioms scheme_identity_chart_cover
end ArithmeticThetaKatoInitialR0253
