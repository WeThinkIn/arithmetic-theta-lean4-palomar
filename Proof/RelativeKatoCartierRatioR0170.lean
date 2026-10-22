module

public import RelativeTorsionCartierR0170
public import RelativeKatoNaturalityDefinitionsR0170
public import RelativeKatoExistenceR0169

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
namespace RelativeKatoCartierRatio
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

/-- A reduced closed subscheme has radical ideals on affine opens. -/
lemma ker_radical {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    [IsReduced Y] (U : X.affineOpens) : (f.ker.ideal U).IsRadical := by
  rw [Scheme.Hom.ker_apply]
  exact Ideal.isRadical_bot.comap (f.app U).hom

/-- A regular generator of a reduced divisor has multiplicity one on its support. -/
lemma generator_order {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (I : X.IdealSheafData) (U : X.affineOpens) [Nonempty U.1]
    (a : Γ(X, U.1)) (ha : IsRegular a) (hIa : I.ideal U = Ideal.span {a})
    (hr : (I.ideal U).IsRadical) (x : X) (hxU : x ∈ U.1)
    (hx : Order.coheight x = 1) :
    Scheme.ord (X.germToFunctionField U.1 a) x =
      @ite ℤ (x ∈ I.support) (Classical.propDecidable _) 1 0 := by
  classical
  let y : U.1 := ⟨x, hxU⟩
  letI := hnormal x
  letI : IsPrincipalIdealRing (X.presheaf.stalk x) :=
    VerticalOrders.normal_stalk_pid x hx
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk y
  letI := U.2.isLocalization_stalk y
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha)
  have hn : X.presheaf.germ U.1 x hxU a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr ha0
  have hrad : (Ideal.span {X.presheaf.germ U.1 x hxU a}).IsRadical := by
    change (Ideal.span {algebraMap Γ(X, U.1) (X.presheaf.stalk x) a}).IsRadical
    rw [← Set.image_singleton, ← Ideal.map_span]
    apply Ideal.radical_eq_iff.mp
    rw [← IsLocalization.map_radical (U.2.primeIdealOf y).asIdeal.primeCompl
      (X.presheaf.stalk x), ← hIa, hr.radical]
  have hs : x ∈ I.support ↔ ¬ IsUnit (X.presheaf.germ U.1 x hxU a) := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, hIa,
      X.zeroLocus_span, X.zeroLocus_singleton]
    exact not_congr (X.mem_basicOpen a x hxU)
  rw [ArithmeticThetaGeometricNormR0150.NormOrders.section_order U.1 x hxU hx a ha0]
  split_ifs with h
  · rw [ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.local_order_of_radical
      _ hn (hs.mp h) hrad]
    rfl
  · have hu := not_not.mp (fun hn => h (hs.mpr hn))
    rw [Ring.ord_of_isUnit hu]
    rfl

/-- The actual torsion ideal defines a reduced subscheme because multiplication is étale. -/
lemma torsion_radical (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (n : ℕ) (hn : 0 < n)
    (U : (Curve R W).affineOpens) : (torsionIdeal R W G n |>.ideal U).IsRadical := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  letI : Etale (G.schemeNsmul n) :=
    (relative_multiplication_degree R W G hG n hn).2.1
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) := MulEquiv.isDomain R e.symm.toMulEquiv
  letI : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) := IsIntegrallyClosed.of_equiv e
  let T := pullback (G.schemeNsmul n) (origin R W)
  let f : T ⟶ Spec (CommRingCat.of R) := pullback.snd _ _
  letI : ∀ x : T, _root_.IsReduced (T.presheaf.stalk x) := fun x => by
    letI := (Smooth.isDomain_and_isIntegrallyClosed_stalk f x).1
    infer_instance
  letI : IsReduced T := isReduced_of_isReduced_stalk T
  change (((origin R W).ker.comap (G.schemeNsmul n)).ideal U).IsRadical
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact ker_radical (pullback.fst (G.schemeNsmul n) (origin R W)) U

lemma order_pow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (a : X.functionField) (ha : a ≠ 0) (n : ℕ) (x : X) :
    Scheme.ord (a^n) x = (n : ℤ) * Scheme.ord a x := by
  induction n with
  | zero =>
    have H := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    simp only [one_mul] at H
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n ha) ha, ih]
    push_cast
    ring

end RelativeKatoCartierRatio

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open RelativeKatoCartierRatio

/-- The accepted height-one divisor gives the full local Cartier equation. -/
theorem relative_kato_cartier_ratio :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g), ArithmeticThetaRelativeKatoNaturalityR0170.CartierRatio R W G c g := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG c hc hc6 g hg
  classical
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  have hs (x : Curve R W) : x ∈ (identityIdeal R W).support ↔
      x ∈ Set.range (origin R W) := by
    change x ∈ ((origin R W).ker.support : Set _) ↔ _
    rw [Scheme.Hom.support_ker, (origin R W).isClosedEmbedding.isClosed_range.closure_eq]
  have ht (x : Curve R W) : x ∈ (torsionIdeal R W G c).support ↔
      G.schemeNsmul c x ∈ Set.range (origin R W) := by
    change x ∈ ((identityIdeal R W).comap (G.schemeNsmul c)).support ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    exact hs _
  intro U _ a b ha hb hIa hIb
  let A := (Curve R W).germToFunctionField U.1 a
  let B := (Curve R W).germToFunctionField U.1 b
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp hb)
  have hA : A ≠ 0 := (map_ne_zero_iff _ ((Curve R W).germToFunctionField_injective U.1)).mpr ha0
  have hB : B ≠ 0 := (map_ne_zero_iff _ ((Curve R W).germToFunctionField_injective U.1)).mpr hb0
  let q := g * B / A^(c^2)
  have hq : q ≠ 0 := div_ne_zero (mul_ne_zero hg.1.1 hB) (pow_ne_zero _ hA)
  have heq : q * A^(c^2) = g * B := div_mul_cancel₀ _ (pow_ne_zero _ hA)
  have hord : ∀ x ∈ U.1, Order.coheight x = 1 → Scheme.ord q x = 0 := by
    intro x hxU hx
    have hnormal := (relative_curve_geometry R W).2.2.1
    have hoa := generator_order hnormal (identityIdeal R W) U a ha hIa
      (ker_radical (origin R W) U) x hxU hx
    have hob := generator_order hnormal (torsionIdeal R W G c) U b hb hIb
      (torsion_radical R W G hG c (by omega) U) x hxU hx
    rw [hs] at hoa
    rw [ht] at hob
    have H := congrArg (fun f => Scheme.ord f x) heq
    rw [Scheme.ord_mul hq (pow_ne_zero _ hA), Scheme.ord_mul hg.1.1 hB,
      order_pow A hA, hg.1.2.1 x hx] at H
    change Scheme.ord q x + (c^2 : ℕ) * Scheme.ord
      ((Curve R W).germToFunctionField U.1 a) x =
      katoOrder R W G c x + Scheme.ord ((Curve R W).germToFunctionField U.1 b) x at H
    rw [hoa, hob] at H
    simp only [katoOrder] at H
    push_cast at H
    split_ifs at H <;> simp_all
  obtain ⟨e, ⟨he, hue⟩, _⟩ := RelativeExistence.unit_of_orders
    (relative_curve_geometry R W).2.2.1 U.1 q hq hord
  refine ⟨hue.unit, ?_⟩
  rw [hue.unit_spec]
  change g * B = (Curve R W).germToFunctionField U.1 (e * a^(c^2))
  rw [map_mul, map_pow, he]
  exact heq.symm

#print axioms relative_kato_cartier_ratio
end ArithmeticThetaRelativeKatoNaturalityR0170
