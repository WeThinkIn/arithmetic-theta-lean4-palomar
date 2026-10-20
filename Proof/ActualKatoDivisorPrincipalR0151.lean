module

public import KatoExistenceDefinitionsR0151
public import FinitePullbackSectionDegree
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
public import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
public import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
public import Theorems.Thm_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

/-! Principality of the actual Kato divisor. The inverse odd division polynomial
is constructed over the original field. Reducedness gives simple affine zeros,
residue-field evaluation identifies the actual multiplication fiber, and weighted
principal degree zero determines the order at the specified origin. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u v

namespace ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal

open Polynomial
open scoped nonZeroDivisors

variable {F : Type u} [Field F]

/-- The affine division polynomial, before passing to rational functions. -/
def divisionElement (W : WeierstrassCurve F) (c : ℕ) : W.toAffine.CoordinateRing :=
  algebraMap F[X] W.toAffine.CoordinateRing (W.preΨ' c)

/-- The inverse odd division polynomial is the candidate rational function.
This definition uses the actual Weierstrass coordinate ring and fraction field. -/
def divisionCandidate (W : WeierstrassCurve F) (c : ℕ) : W.toAffine.FunctionField :=
  (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (divisionElement W c))⁻¹

lemma divisionElement_ne_zero [CharZero F] (W : WeierstrassCurve F)
    {c : ℕ} (hc : 0 < c) : divisionElement W c ≠ 0 := by
  intro h
  apply W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
  apply FaithfulSMul.algebraMap_injective F[X] W.toAffine.CoordinateRing
  simpa only [divisionElement, map_zero] using h

lemma divisionCandidate_ne_zero [CharZero F] (W : WeierstrassCurve F)
    {c : ℕ} (hc : 0 < c) : divisionCandidate W c ≠ 0 := by
  apply inv_ne_zero
  intro h
  apply divisionElement_ne_zero W hc
  apply IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField
  simpa only [map_zero] using h

lemma odd_of_coprime_six {c : ℕ} (hc : Nat.Coprime c 6) : Odd c := by
  have h2 : Nat.Coprime c 2 := hc.of_dvd_right (by decide)
  exact Nat.coprime_two_right.mp h2

/-- The coefficient and degree are calculated in the original field. -/
lemma divisionPolynomial_degree [CharZero F] (W : WeierstrassCurve F)
    {c : ℕ} (hc : 0 < c) (ho : Odd c) :
    (W.preΨ' c).natDegree = (c ^ 2 - 1) / 2 ∧
      (W.preΨ' c).leadingCoeff = (c : F) := by
  have hn : (c : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  simp only [W.natDegree_preΨ' hn, W.leadingCoeff_preΨ' hn, (Nat.not_even_iff_odd.mpr ho), if_false,
    and_self]

/-- The polynomial detects the full multiplication kernel over any field.
In particular, the field may be the residue field of a nonsplit closed point. -/
lemma divisionPolynomial_vanishes_iff [DecidableEq F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (ho : Odd c) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (W.preΨ' c).eval x = 0 ↔ c • WeierstrassCurve.Affine.Point.some x y h = 0 :=
  (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ho h).symm

/-- The denominator in the multiplication formula is exactly the square of
the odd division polynomial. -/
lemma divisionPolynomial_sq (W : WeierstrassCurve F) {c : ℕ} (ho : Odd c) :
    W.ΨSq (c : ℤ) = W.preΨ' c ^ 2 := by
  simp only [W.ΨSq_ofNat, (Nat.not_even_iff_odd.mpr ho), if_false, mul_one]

/-- Coprimality excludes cancellation in the actual multiplication formula. -/
lemma divisionPolynomial_coprime (W : WeierstrassCurve F) [W.IsElliptic]
    {c : ℕ} (ho : Odd c) : IsCoprime (W.Φ (c : ℤ)) (W.preΨ' c ^ 2) := by
  rw [← divisionPolynomial_sq W ho]
  exact W.isCoprime_Phi_PsiSq c

/-- Separability is proved over the original field, without a splitting
assumption on the torsion points. -/
lemma divisionPolynomial_separable [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c) :
    (W.preΨ' c).Separable := by
  exact W.separable_prePsi_of_isUnit ho
    ((isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))).mul
      (WeierstrassCurve.IsElliptic.isUnit (W := W)))

/-- The derivative is nonzero at a torsion abscissa in an arbitrary extension
field, including the residue field of a closed point. -/
lemma divisionPolynomial_derivative_ne_zero [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    {L : Type v} [Field L] (σ : F →+* L) (x : L)
    (hx : (W.preΨ' c).eval₂ σ x = 0) :
    (W.preΨ' c).derivative.eval₂ σ x ≠ 0 := by
  exact (divisionPolynomial_separable W hc ho).eval₂_derivative_ne_zero σ hx

/-- The construction uses a polynomial defined over the coefficient field;
its value commutes with every specified field homomorphism. -/
lemma divisionPolynomial_eval_map (W : WeierstrassCurve F) (c : ℕ)
    {L : Type v} [Field L] (σ : F →+* L) (x : F) :
    ((W.map σ).preΨ' c).eval (σ x) = σ ((W.preΨ' c).eval x) := by
  rw [W.map_preΨ']
  exact Polynomial.eval_map_apply σ x

/-- A separable equation forces its derivative to be a unit in any algebra
where the equation vanishes, including nonreduced test algebras. -/
lemma derivative_unit_of_aeval_zero {B : Type v} [CommRing B] [Algebra F B]
    (p : F[X]) (hp : p.Separable) (x : B) (hx : aeval x p = 0) :
    IsUnit (aeval x p.derivative) := by
  obtain ⟨a, b, hab⟩ := hp
  have h := congrArg (aeval x) hab
  simp only [map_add, map_mul, map_one, hx, mul_zero, zero_add] at h
  exact isUnit_iff_exists_inv.mpr ⟨aeval x b, by simpa only [mul_comm] using h⟩

/-- A separable polynomial relation kills every relative derivative of its
root. This will be applied to the actual division-polynomial quotient. -/
lemma derivation_root_eq_zero {B : Type v} [CommRing B] [Algebra F B]
    {N : Type*} [AddCommGroup N] [Module B N] [Module F N] [IsScalarTower F B N]
    (D : Derivation F B N) (p : F[X]) (hp : p.Separable)
    (x : B) (hx : aeval x p = 0) : D x = 0 := by
  apply (derivative_unit_of_aeval_zero p hp x hx).smul_eq_zero.mp
  rw [← D.map_aeval, hx, map_zero]

/-- The second coordinate is unramified on the odd torsion locus. Both
coordinate derivatives vanish over the original scalar algebra. -/
lemma division_locus_derivations_zero [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    {B : Type v} [CommRing B] [Algebra F B]
    (x y : B) (heq : (W.map (algebraMap F B)).toAffine.Equation x y)
    (hψ : aeval x (W.preΨ' c) = 0)
    {N : Type*} [AddCommGroup N] [Module B N] [Module F N] [IsScalarTower F B N]
    (D : Derivation F B N) : D x = 0 ∧ D y = 0 := by
  have hx := derivation_root_eq_zero D _ (divisionPolynomial_separable W hc ho) x hψ
  refine ⟨hx, ?_⟩
  have hψ' : ((W.map (algebraMap F B)).preΨ (c : ℤ)).eval x = 0 := by
    rw [WeierstrassCurve.preΨ_ofNat, W.map_preΨ', Polynomial.eval_map]
    exact hψ
  have hu := (W.map (algebraMap F B)).isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
    (by simpa only [WeierstrassCurve.map_Δ] using
      (WeierstrassCurve.IsElliptic.isUnit (W := W)).map (algebraMap F B)) ho heq hψ'
  apply hu.smul_eq_zero.mp
  have h := congrArg D ((WeierstrassCurve.Affine.equation_iff x y).mp heq)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    map_add, D.leibniz, D.leibniz_pow, D.map_algebraMap, hx, smul_zero,
    add_zero] at h ⊢
  simpa only [add_smul, mul_smul, two_smul, one_smul, Nat.reduceSub, pow_one, pow_zero] using h

/-- The odd division locus is unramified whenever the displayed coordinates
generate the algebra. The hypothesis records generators, not reducedness. -/
lemma division_locus_formallyUnramified [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    {B : Type v} [CommRing B] [Algebra F B]
    (x y : B) (heq : (W.map (algebraMap F B)).toAffine.Equation x y)
    (hψ : aeval x (W.preΨ' c) = 0) (hgen : Algebra.adjoin F {x, y} = ⊤) :
    Algebra.FormallyUnramified F B := by
  have hD : KaehlerDifferential.D F B = 0 := by
    obtain ⟨hx, hy⟩ := division_locus_derivations_zero W hc ho x y heq hψ
      (KaehlerDifferential.D F B)
    apply Derivation.ext_of_adjoin_eq_top {x, y} hgen
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · have hz' : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact hy
  constructor
  apply (subsingleton_iff_forall_eq 0).mpr
  intro z
  have hz : z ∈ (⊥ : Submodule B (KaehlerDifferential F B)) := by
    have htop : (⊤ : Submodule B (KaehlerDifferential F B)) ≤ ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      simp only [hD, Derivation.zero_apply]
      exact (⊥ : Submodule B (KaehlerDifferential F B)).zero_mem
    exact htop trivial
  exact hz

lemma division_locus_reduced [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    {B : Type v} [CommRing B] [Algebra F B]
    (x y : B) (heq : (W.map (algebraMap F B)).toAffine.Equation x y)
    (hψ : aeval x (W.preΨ' c) = 0) (hgen : Algebra.adjoin F {x, y} = ⊤) :
    IsReduced B := by
  letI := division_locus_formallyUnramified W hc ho x y heq hψ hgen
  classical
  letI : Algebra.FiniteType F B := ⟨⟨{x, y}, by simpa using hgen⟩⟩
  exact Algebra.FormallyUnramified.isReduced_of_field F B

def affineX (W : WeierstrassCurve F) : W.toAffine.CoordinateRing :=
  algebraMap F[X] W.toAffine.CoordinateRing X

def affineY (W : WeierstrassCurve F) : W.toAffine.CoordinateRing :=
  AdjoinRoot.root W.toAffine.polynomial

lemma affineX_aeval (W : WeierstrassCurve F) (p : F[X]) :
    aeval (affineX W) p = algebraMap F[X] W.toAffine.CoordinateRing p := by
  have h : (aeval (affineX W)).toRingHom = algebraMap F[X] W.toAffine.CoordinateRing := by
    apply Polynomial.ringHom_ext
    · intro a
      change aeval (affineX W) (C a) = _
      rw [aeval_C]
      exact (IsScalarTower.algebraMap_apply F F[X] W.toAffine.CoordinateRing a).symm
    · change aeval (affineX W) X = affineX W
      exact aeval_X _
  exact RingHom.congr_fun h p

/-- Polynomial evaluation along any actual coordinate-ring homomorphism. -/
lemma divisionElement_eval (W : WeierstrassCurve F) (c : ℕ)
    {L : Type v} [CommRing L] (σ : W.toAffine.CoordinateRing →+* L) :
    σ (divisionElement W c) = (W.preΨ' c).eval₂
      (σ.comp (algebraMap F W.toAffine.CoordinateRing)) (σ (affineX W)) := by
  have h : σ.comp (algebraMap F[X] W.toAffine.CoordinateRing) =
      Polynomial.eval₂RingHom (σ.comp (algebraMap F W.toAffine.CoordinateRing))
        (σ (affineX W)) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_C]
      exact congrArg σ (IsScalarTower.algebraMap_apply F F[X] W.toAffine.CoordinateRing z).symm
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X, affineX]
  exact RingHom.congr_fun h (W.preΨ' c)

lemma affine_coordinates_generate (W : WeierstrassCurve F) :
    Algebra.adjoin F {affineX W, affineY W} = ⊤ := by
  classical
  apply top_unique
  intro z _
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have hp (f : F[X]) : algebraMap F[X] W.toAffine.CoordinateRing f ∈
      Algebra.adjoin F {affineX W, affineY W} := by
    rw [← affineX_aeval]
    apply Algebra.adjoin_mono (s := {affineX W}) (t := {affineX W, affineY W}) _
      (Polynomial.aeval_mem_adjoin_singleton F (x := affineX W) (p := f))
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    simp [hz]
  rw [← hpq, Algebra.smul_def, Algebra.smul_def, mul_one]
  exact add_mem (hp p) (mul_mem (hp q) (Algebra.subset_adjoin (by
    change affineY W ∈ ({affineX W, affineY W} : Set W.toAffine.CoordinateRing)
    simp)))

lemma affine_coordinates_equation (W : WeierstrassCurve F) :
    (W.map (algebraMap F W.toAffine.CoordinateRing)).toAffine.Equation
      (affineX W) (affineY W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  have h := AdjoinRoot.eval₂_root W.toAffine.polynomial
  change Polynomial.eval₂ (algebraMap F[X] W.toAffine.CoordinateRing) (affineY W)
    (X ^ 2 + C (C W.a₁ * X + C W.a₃) * X -
      C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) = 0 at h
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    map_add, map_mul, map_pow] at h
  change affineY W ^ 2 +
    (algebraMap F W.toAffine.CoordinateRing W.a₁ * affineX W +
      algebraMap F W.toAffine.CoordinateRing W.a₃) * affineY W -
    (affineX W ^ 3 + algebraMap F W.toAffine.CoordinateRing W.a₂ * affineX W ^ 2 +
      algebraMap F W.toAffine.CoordinateRing W.a₄ * affineX W +
      algebraMap F W.toAffine.CoordinateRing W.a₆) = 0 at h
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination h

lemma affine_coordinates_map_equation (W : WeierstrassCurve F)
    {L : Type v} [CommRing L] (σ : W.toAffine.CoordinateRing →+* L) :
    (W.map (σ.comp (algebraMap F W.toAffine.CoordinateRing))).toAffine.Equation
      (σ (affineX W)) (σ (affineY W)) := by
  have h := (affine_coordinates_equation W).map σ
  simpa only [WeierstrassCurve.map_map] using h

/-- Division-function vanishing and torsion for an arbitrary residue-field
coordinate map, with its induced scalar homomorphism kept explicit. -/
lemma divisionElement_torsion (W : WeierstrassCurve F) [W.IsElliptic]
    {L : Type v} [Field L] [DecidableEq L] (σ : W.toAffine.CoordinateRing →+* L)
    {c : ℕ} (ho : Odd c) :
    ∃ h : (W.map (σ.comp (algebraMap F W.toAffine.CoordinateRing))).toAffine.Nonsingular
        (σ (affineX W)) (σ (affineY W)),
      σ (divisionElement W c) = 0 ↔
        c • WeierstrassCurve.Affine.Point.some _ _ h = 0 := by
  let V := W.map (σ.comp (algebraMap F W.toAffine.CoordinateRing))
  have he : V.toAffine.Equation (σ (affineX W)) (σ (affineY W)) :=
    affine_coordinates_map_equation W σ
  have hn := V.toAffine.equation_iff_nonsingular.mp he
  refine ⟨hn, ?_⟩
  rw [divisionElement_eval, ← Polynomial.eval_map, ← W.map_preΨ']
  exact divisionPolynomial_vanishes_iff V ho hn

/-- The actual affine zero scheme of the division polynomial, over the
original field. No torsion splitting field is part of this definition. -/
abbrev DivisionQuotient (W : WeierstrassCurve F) (c : ℕ) :=
  W.toAffine.CoordinateRing ⧸ Ideal.span {divisionElement W c}

lemma division_quotient_reduced [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c) :
    IsReduced (DivisionQuotient W c) := by
  let π : W.toAffine.CoordinateRing →ₐ[F] DivisionQuotient W c :=
    Ideal.Quotient.mkₐ F (Ideal.span {divisionElement W c})
  apply division_locus_reduced W hc ho (π (affineX W)) (π (affineY W))
  · exact (affine_coordinates_equation W).baseChange π
  · rw [Polynomial.aeval_algHom_apply, affineX_aeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  · have h := congrArg (Subalgebra.map π) (affine_coordinates_generate W)
    rw [AlgHom.map_adjoin, Set.image_insert_eq, Set.image_singleton,
      Algebra.map_top, (AlgHom.range_eq_top π).mpr (Ideal.Quotient.mk_surjective)] at h
    exact h

lemma division_ideal_radical [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c) :
    (Ideal.span {divisionElement W c}).IsRadical :=
  (Ideal.isRadical_iff_quotient_reduced _).mpr (division_quotient_reduced W hc ho)

/-- In a local Dedekind domain a nonzero radical principal ideal is either
the unit ideal or the maximal ideal. This turns reducedness into multiplicity one. -/
lemma radical_span_eq_maximal {R : Type*} [CommRing R]
    [IsLocalRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0)
    (hu : ¬ IsUnit a) (hr : (Ideal.span {a}).IsRadical) :
    Ideal.span {a} = IsLocalRing.maximalIdeal R := by
  rw [← hr.radical, Ideal.radical_eq_sInf]
  apply le_antisymm
  · apply sInf_le
    exact ⟨Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      ((IsLocalRing.mem_maximalIdeal a).mpr hu)), inferInstance⟩
  · apply le_sInf
    intro I hI
    have hne : I ≠ ⊥ := by
      intro hbot
      apply ha
      have hm := hI.1 (Ideal.mem_span_singleton_self a)
      simpa only [hbot, Ideal.mem_bot] using hm
    exact (IsLocalRing.eq_maximalIdeal (hI.2.isMaximal hne)).ge

lemma local_order_of_radical {R : Type*} [CommRing R]
    [IsLocalRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0)
    (hu : ¬ IsUnit a) (hr : (Ideal.span {a}).IsRadical) :
    Ring.ord R a = 1 := by
  rw [Ring.ord, radical_span_eq_maximal a ha hu hr]
  letI : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one R (R ⧸ IsLocalRing.maximalIdeal R)

/-- Radicality survives the actual localization map. -/
lemma localized_division_ideal_radical [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    (S : Submonoid W.toAffine.CoordinateRing)
    (B : Type*) [CommRing B] [Algebra W.toAffine.CoordinateRing B] [IsLocalization S B] :
    (Ideal.span {algebraMap W.toAffine.CoordinateRing B (divisionElement W c)}).IsRadical := by
  rw [← Set.image_singleton, ← Ideal.map_span]
  apply Ideal.radical_eq_iff.mp
  rw [← IsLocalization.map_radical S B,
    (division_ideal_radical W hc ho).radical]

/-- The local multiplicity is exactly one at every prime containing the
odd division polynomial, with no rationality assumption on the prime. -/
lemma localized_division_order [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {c : ℕ} (hc : 0 < c) (ho : Odd c)
    (P : Ideal W.toAffine.CoordinateRing) [P.IsPrime]
    (B : Type*) [CommRing B] [Algebra W.toAffine.CoordinateRing B]
    [IsLocalization.AtPrime B P] [IsLocalRing B] [IsDedekindDomain B] :
    Ring.ord B (algebraMap W.toAffine.CoordinateRing B (divisionElement W c)) =
      @ite _ (divisionElement W c ∈ P) (Classical.propDecidable _) 1 0 := by
  classical
  letI := IsLocalization.AtPrime.faithfulSMul B W.toAffine.CoordinateRing P
  have hn : algebraMap W.toAffine.CoordinateRing B (divisionElement W c) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr
      (divisionElement_ne_zero W hc)
  have hu := IsLocalization.AtPrime.isUnit_to_map_iff B P (divisionElement W c)
  split_ifs with h
  · apply local_order_of_radical _ hn
    · intro hh
      exact (hu.mp hh) h
    · exact localized_division_ideal_radical W hc ho P.primeCompl B
  · exact Ring.ord_of_isUnit (hu.mpr h)

open CategoryTheory AlgebraicGeometry

lemma smooth_oneDimensionalCharts {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p] :
    ArithmeticThetaCurveDegree.OneDimensionalCharts X := by
  intro U hU hnon
  constructor
  intro P hP hp
  letI := hp
  let z : PrimeSpectrum Γ(X, U) := ⟨P, hp⟩
  have hz : hU.fromSpec z ∈ U := (hU.isoSpec.inv z).property
  have hn : hU.fromSpec z ≠ genericPoint X := by
    intro he
    have he' : hU.fromSpec z = hU.fromSpec (genericPoint (Spec Γ(X, U))) :=
      he.trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm
    have hz' := hU.fromSpec.isOpenEmbedding.injective he'
    rw [genericPoint_eq_bot_of_affine] at hz'
    exact hP (congrArg PrimeSpectrum.asIdeal hz')
  have hcl := ArithmeticThetaGeometricNormR0150.NormOrders.smooth_closed_of_ne_generic F p _ hn
  have hi : hU.primeIdealOf ⟨hU.fromSpec z, hz⟩ = z :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hm := hU.primeIdealOf_isMaximal_of_isClosed ⟨hU.fromSpec z, hz⟩ hcl
  rw [hi] at hm
  exact hm

/-- A rational section has residue degree one for the structural scalar map. -/
lemma placeDegree_section {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of F)) (e : Spec (CommRingCat.of F) ⟶ X)
    (he : e ≫ p = 𝟙 _) :
    ArithmeticThetaCurveDegree.placeDegree F p (e (IsLocalRing.closedPoint F)) = 1 := by
  let x := e (IsLocalRing.closedPoint F)
  let b : X.residueField x ⟶ CommRingCat.of F :=
    @Scheme.descResidueField F _ X x (Scheme.stalkClosedPointTo e)
      (Scheme.isLocalHom_stalkClosedPointTo e)
  have hb : Spec.map b ≫ X.fromSpecResidueField x = e :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ e
  let σ := ArithmeticThetaCurveDegree.baseToResidue F p x
  have hcomp : CommRingCat.ofHom σ ≫ b = 𝟙 (CommRingCat.of F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ArithmeticThetaCurveDegree.specMap_baseToResidue,
      ← Category.assoc, hb, he, Spec.map_id]
  have hs : Function.Surjective σ := by
    intro z
    refine ⟨b z, b.hom.injective ?_⟩
    exact ConcreteCategory.congr_hom hcomp (b z)
  letI := σ.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨σ.injective, hs⟩

/-- Every stalk fiber of an étale map has length one. -/
lemma etale_stalkFiberLength {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] (y : Y) :
    ArithmeticThetaDegreeAssembly.stalkFiberLength f y = 1 := by
  letI := (f.stalkMap y).hom.toAlgebra
  letI : IsLocalHom (algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  letI : Algebra.EssFiniteType (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f y
  letI : Algebra.FormallyUnramified (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f y
  have he : (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y))).map
      (f.stalkMap y).hom = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  unfold ArithmeticThetaDegreeAssembly.stalkFiberLength
  rw [he]
  letI : IsSimpleModule (Y.presheaf.stalk y)
      ((Y.presheaf.stalk y) ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [Module.length_eq_one]
  rfl

/-- Degree of an étale fiber counts nonsplit points with their actual residue degrees. -/
lemma etale_fiber_residue_sum {Y X : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (hX : ArithmeticThetaCurveDegree.OneDimensionalCharts X)
    (x : X) (hx : Order.coheight x = 1) :
    (∑ᶠ y : {y : Y // f y = x}, f.residueDegree y.val) = f.finrank (genericPoint X) := by
  simpa only [etale_stalkFiberLength, one_mul] using
    ArithmeticThetaDegreeAssembly.fiber_length_residue_sum f hX x hx

lemma weighted_etale_fiber {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (f : X ⟶ X) [IsFinite f] [Etale f] (hf : f ≫ p = p)
    (e : X) (he : Order.coheight e = 1)
    (hw : ArithmeticThetaCurveDegree.placeDegree F p e = 1) :
    (∑ᶠ x, @ite ℤ (f x = e) (Classical.propDecidable _)
      (ArithmeticThetaCurveDegree.placeDegree F p x : ℤ) 0) =
      (f.finrank (genericPoint X) : ℤ) := by
  classical
  letI : Finite {x : X // f x = e} := (f.finite_preimage_singleton e).to_subtype
  letI : Fintype {x : X // f x = e} := Fintype.ofFinite _
  have hweight (x : {x : X // f x = e}) :
      ArithmeticThetaCurveDegree.placeDegree F p x.val = f.residueDegree x.val := by
    have h := ArithmeticThetaDegreeAssembly.placeDegree_comp F p f x.val
    rwa [hf, x.property, hw, one_mul] at h
  have hsum := etale_fiber_residue_sum f (smooth_oneDimensionalCharts p) e he
  have hsum' : (∑ᶠ x : {x : X // f x = e},
      (ArithmeticThetaCurveDegree.placeDegree F p x.val : ℤ)) =
      (f.finrank (genericPoint X) : ℤ) := by
    simp_rw [hweight]
    rw [finsum_eq_sum_of_fintype] at hsum ⊢
    exact_mod_cast hsum
  rw [finsum_subtype_eq_finsum_cond (f := fun x : X =>
    (ArithmeticThetaCurveDegree.placeDegree F p x : ℤ)) (fun x => f x = e)] at hsum'
  have hh (x : X) : (∑ᶠ (_ : f x = e),
      (ArithmeticThetaCurveDegree.placeDegree F p x : ℤ)) =
      if f x = e then (ArithmeticThetaCurveDegree.placeDegree F p x : ℤ) else 0 := by
    by_cases h : f x = e <;> simp [h]
  simpa only [hh] using hsum' 

/-- A weighted degree-zero identity determines the remaining coefficient
once all other coefficients of a finite divisor are known. -/
lemma recover_origin_coefficient {A : Type*} (e : A) (S : Set A) (hS : S.Finite)
    (he : e ∈ S) (w f : A → ℤ) (hw : w e = 1)
    (hf : ∀ x, x ≠ e → f x = -(@ite ℤ (x ∈ S) (Classical.propDecidable _) 1 0))
    (hz : (∑ᶠ x, w x * f x) = 0) (n : ℤ)
    (hn : (∑ᶠ x, @ite ℤ (x ∈ S) (Classical.propDecidable _) (w x) 0) = n) :
    f e = n - 1 := by
  classical
  have h1 : (Function.support (fun x => if x = e then f e + 1 else (0 : ℤ))).Finite := by
    apply (Set.finite_singleton e).subset
    intro x hx
    by_contra h
    exact hx (if_neg h)
  have h2 : (Function.support (fun x => if x ∈ S then w x else (0 : ℤ))).Finite := by
    apply hS.subset
    intro x hx
    by_contra h
    exact hx (if_neg h)
  have hsplit : (fun x => w x * f x) =
      (fun x => (if x = e then f e + 1 else 0) - (if x ∈ S then w x else 0)) := by
    funext x
    by_cases hxe : x = e
    · subst x
      simp [he, hw]
    · rw [hf x hxe, if_neg hxe]
      split_ifs <;> ring
  rw [hsplit, finsum_sub_distrib h1 h2, hn] at hz
  have hsingle : (∑ᶠ x, if x = e then f e + 1 else (0 : ℤ)) = f e + 1 := by
    rw [finsum_eq_single _ e (fun x hx => if_neg hx), if_pos rfl]
  rw [hsingle] at hz
  omega

lemma section_coheight_one {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (e : Spec (CommRingCat.of F) ⟶ X) (he : e ≫ p = 𝟙 _) :
    Order.coheight (e (IsLocalRing.closedPoint F)) = 1 := by
  letI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id p e he
  have hcl : IsClosed ({e (IsLocalRing.closedPoint F)} : Set X) := by
    rw [← Set.image_singleton]
    exact e.isClosedEmbedding.isClosedMap _ isClosed_singleton
  letI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed p _ hcl
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one
    (X.presheaf.stalk (e (IsLocalRing.closedPoint F)))
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- On a proper smooth curve, the finite étale fiber degree determines the
order at the rational origin from the already established orders off it. -/
lemma divisor_from_off_origin {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p] [IsProper p]
    (e : Spec (CommRingCat.of F) ⟶ X) (he : e ≫ p = 𝟙 _)
    (f : X ⟶ X) [IsFinite f] [Etale f] (hf : f ≫ p = p)
    (hfe : f (e (IsLocalRing.closedPoint F)) = e (IsLocalRing.closedPoint F))
    (g : X.functionField) (hg : g ≠ 0)
    (hoff : ∀ x, x ≠ e (IsLocalRing.closedPoint F) →
      Scheme.ord g x = -(@ite ℤ (f x = e (IsLocalRing.closedPoint F))
        (Classical.propDecidable _) 1 0)) :
    ∀ x, Scheme.ord g x =
      (@ite ℤ (x = e (IsLocalRing.closedPoint F)) (Classical.propDecidable _)
        (f.finrank (genericPoint X) : ℤ) 0) -
      (@ite ℤ (f x = e (IsLocalRing.closedPoint F)) (Classical.propDecidable _) 1 0) := by
  classical
  let o := e (IsLocalRing.closedPoint F)
  have hw := placeDegree_section p e he
  have hco := section_coheight_one p e he
  have hz := ArithmeticThetaCurveDegree.DegreeCohomology.weighted_order_sum_eq_zero
    X F p (smooth_oneDimensionalCharts p) g hg
  have horigin := recover_origin_coefficient o {x | f x = o}
    (f.finite_preimage_singleton o) hfe
    (fun x => (ArithmeticThetaCurveDegree.placeDegree F p x : ℤ)) (Scheme.ord g)
    (by exact_mod_cast hw) hoff hz (f.finrank (genericPoint X))
    (weighted_etale_fiber p f hf o hco hw)
  intro x
  by_cases hx : x = o
  · subst x
    simpa [o, hfe] using horigin
  · change x ≠ e (IsLocalRing.closedPoint F) at hx
    simpa only [if_neg hx, zero_sub] using hoff x hx

/-- Reduced principal divisors have multiplicity one after restriction to
any affine stalk on a smooth curve. -/
lemma radical_section_order {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (a : Γ(X, U)) (ha : a ≠ 0) (hr : (Ideal.span {a}).IsRadical)
    (x : U) (hx : Order.coheight x.val = 1) :
    Scheme.ord (X.germToFunctionField U a) x.val =
      @ite ℤ (a ∈ (hU.primeIdealOf x).asIdeal) (Classical.propDecidable _) 1 0 := by
  classical
  letI := ArithmeticThetaGeometricNormR0150.NormOrders.smooth_stalk_pid F p x.val hx
  letI := hU.isLocalization_stalk x
  have hn : X.presheaf.germ U x.val x.property a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x.val x.property)).mpr ha
  have hrad : (Ideal.span {X.presheaf.germ U x.val x.property a}).IsRadical := by
    change (Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk x.val) a}).IsRadical
    rw [← Set.image_singleton, ← Ideal.map_span]
    apply Ideal.radical_eq_iff.mp
    rw [← IsLocalization.map_radical (hU.primeIdealOf x).asIdeal.primeCompl
      (X.presheaf.stalk x.val), hr.radical]
  have hu := IsLocalization.AtPrime.isUnit_to_map_iff
    (X.presheaf.stalk x.val) (hU.primeIdealOf x).asIdeal a
  rw [ArithmeticThetaGeometricNormR0150.NormOrders.section_order U x.val x.property hx a ha]
  split_ifs with h
  · have hnu : ¬ IsUnit (X.presheaf.germ U x.val x.property a) := fun hh => hu.mp hh h
    rw [local_order_of_radical _ hn hnu hrad]
    rfl
  · have hu' : IsUnit (X.presheaf.germ U x.val x.property a) := hu.mpr h
    rw [Ring.ord_of_isUnit hu']
    rfl

/-- The ring of the specified affine chart, identified with sections on
its image by the actual open immersion. -/
def chartSectionEquiv {A : Type u} [CommRing A] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] :
    A ≃+* Γ(X, j ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.trans
    (j.appIso ⊤).commRingCatIsoToRingEquiv.symm

lemma radical_span_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) (h : (Ideal.span {a}).IsRadical) :
    (Ideal.span {e a}).IsRadical := by
  rw [← Set.image_singleton, ← Ideal.map_span]
  change ((Ideal.span {a}).map (e : A →+* B)).IsRadical
  rw [Ideal.map_comap_of_equiv e]
  exact h.comap _

lemma open_evaluation {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (z : Y) (hz : j z ∈ j ''ᵁ (⊤ : Y.Opens)) :
    X.evaluation (j ''ᵁ ⊤) (j z) hz ≫ j.residueFieldMap z =
      (j.appIso ⊤).hom ≫ Y.Γevaluation z := by
  rw [Scheme.evaluation_naturality]
  simp only [Scheme.Hom.appIso_hom, Scheme.Γevaluation, Scheme.evaluation,
    Category.assoc, TopCat.Presheaf.germ_res_assoc]

/-- The coordinate-ring map defined by the actual residue-field point. -/
def affineResidueMap {A : Type u} [CommRing A] (z : Spec (CommRingCat.of A)) :
    A →+* (Spec (CommRingCat.of A)).residueField z :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (Spec (CommRingCat.of A)).Γevaluation z).hom

lemma affineResidueMap_spec {A : Type u} [CommRing A] (z : Spec (CommRingCat.of A)) :
    Spec.map (CommRingCat.ofHom (affineResidueMap z)) =
      (Spec (CommRingCat.of A)).fromSpecResidueField z := by
  let Y := Spec (CommRingCat.of A)
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.Γevaluation z) = _
  apply (cancel_mono Y.toSpecΓ).mp
  simp only [Spec.map_comp, Category.assoc]
  rw [SpecMap_ΓSpecIso_inv_toSpecΓ, Category.comp_id]
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
  simp only [Scheme.Γevaluation, Scheme.evaluation, Spec.map_comp]
  rfl

lemma chartSection_evaluation_zero_iff {A : Type u} [CommRing A] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (z : Spec (CommRingCat.of A)) (hz : j z ∈ j ''ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens))
    (a : A) :
    X.evaluation (j ''ᵁ ⊤) (j z) hz (chartSectionEquiv j a) = 0 ↔
      affineResidueMap z a = 0 := by
  have h := ConcreteCategory.congr_hom (open_evaluation j z hz) (chartSectionEquiv j a)
  change (j.residueFieldMap z) (X.evaluation (j ''ᵁ ⊤) (j z) hz (chartSectionEquiv j a)) =
    (Spec (CommRingCat.of A)).Γevaluation z
      ((j.appIso ⊤).hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) at h
  rw [Iso.inv_hom_id_apply] at h
  rw [← map_eq_zero_iff (j.residueFieldMap z).hom (j.residueFieldMap z).hom.injective, h]
  rfl

/-- The actual division section on the image of the chosen chart. -/
def chartDivisionSection (W : WeierstrassCurve F) {X : Scheme.{u}}
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] (c : ℕ) : Γ(X, j ''ᵁ ⊤) :=
  chartSectionEquiv j (divisionElement W c)

lemma chartDivisionSection_radical [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] {c : ℕ} (hc : 0 < c) (ho : Odd c) :
    (Ideal.span {chartDivisionSection W j c}).IsRadical :=
  radical_span_ringEquiv (chartSectionEquiv j) _ (division_ideal_radical W hc ho)

lemma section_mem_prime_iff {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (x : U) (a : Γ(X, U)) :
    a ∈ (hU.primeIdealOf x).asIdeal ↔ X.evaluation U x.val x.property a = 0 := by
  rw [hU.primeIdealOf_eq_map_closedPoint]
  change X.presheaf.germ U x.val x.property a ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.val) ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem.symm

/-- Scheme order of the actual division section at any point of the chart.
Evaluation uses the residue field of that point, so nonsplit points are included. -/
lemma chartDivisionSection_order [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] [Nonempty (j ''ᵁ ⊤ : X.Opens)]
    {c : ℕ} (hc : 0 < c) (ho : Odd c)
    (x : (j ''ᵁ ⊤ : X.Opens)) (hx : Order.coheight x.val = 1) :
    Scheme.ord (X.germToFunctionField (j ''ᵁ ⊤) (chartDivisionSection W j c)) x.val =
      @ite ℤ (X.evaluation (j ''ᵁ ⊤) x.val x.property (chartDivisionSection W j c) = 0)
        (Classical.propDecidable _) 1 0 := by
  have hU : IsAffineOpen (j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  have hn : chartDivisionSection W j c ≠ 0 := by
    exact (map_ne_zero_iff _ (chartSectionEquiv j).injective).mpr (divisionElement_ne_zero W hc)
  rw [radical_section_order p _ hU _ hn (chartDivisionSection_radical W j hc ho) x hx,
    section_mem_prime_iff]

/-- The function-field identification induced by a dense open immersion.
The generic points and stalk maps, rather than abstract field choices,
determine this identification. -/
def openFieldIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] : X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint Y))

local instance nonempty_top (Y : Scheme.{u}) [IsIntegral Y] : Nonempty (⊤ : Y.Opens) :=
  ⟨⟨genericPoint Y, trivial⟩⟩

lemma openFieldIso_germ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [Nonempty (j ''ᵁ ⊤ : X.Opens)] :
    X.germToFunctionField (j ''ᵁ ⊤) ≫ (openFieldIso j).hom =
      (j.appIso ⊤).hom ≫ Y.germToFunctionField ⊤ := by
  simp only [openFieldIso, Iso.trans_hom, asIso_hom,
    Scheme.germToFunctionField, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.Hom.germ_stalkMap, Scheme.Hom.appIso_hom,
    Category.assoc, TopCat.Presheaf.germ_res]

/-- Functions on a specified affine open, as rational functions on its
ambient integral scheme. -/
def affineOpenToField {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] : A →+* X.functionField :=
  (openFieldIso j).inv.hom.comp
    (((Spec (CommRingCat.of A)).germToFunctionField ⊤).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

lemma affineOpenToField_injective {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] :
    Function.Injective (affineOpenToField j) := by
  exact (openFieldIso j).commRingCatIsoToRingEquiv.symm.injective.comp
    (((Spec (CommRingCat.of A)).germToFunctionField_injective ⊤).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.injective)

lemma affineOpenToField_eq_section {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    [Nonempty (j ''ᵁ ⊤ : X.Opens)] (a : A) :
    affineOpenToField j a = X.germToFunctionField (j ''ᵁ ⊤) (chartSectionEquiv j a) := by
  apply (openFieldIso j).commRingCatIsoToRingEquiv.injective
  change (openFieldIso j).hom ((openFieldIso j).inv
      ((Spec (CommRingCat.of A)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
    (openFieldIso j).hom (X.germToFunctionField (j ''ᵁ ⊤)
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
  rw [Iso.inv_hom_id_apply]
  have h := ConcreteCategory.congr_hom (openFieldIso_germ j)
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using h.symm

/-- A nonzero rational candidate on any integral compactification with its
specified Weierstrass affine chart. -/
def chartCandidate (W : WeierstrassCurve F) {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] (c : ℕ) : X.functionField :=
  (affineOpenToField j (divisionElement W c))⁻¹

lemma chartCandidate_ne_zero [CharZero F] (W : WeierstrassCurve F)
    {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] {c : ℕ} (hc : 0 < c) : chartCandidate W j c ≠ 0 := by
  apply inv_ne_zero
  intro h
  apply divisionElement_ne_zero W hc
  apply affineOpenToField_injective j
  simpa only [map_zero] using h

lemma rational_order_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (hg : g ≠ 0) (x : X) :
    Scheme.ord g⁻¹ x = -Scheme.ord g x := by
  have h1 : Scheme.ord (1 : X.functionField) x = 0 := by
    simpa only [map_one] using (Scheme.ord_of_isUnit
      (X := X) (U := ⊤) (f := (1 : Γ(X, ⊤))) isUnit_one (x := x) trivial)
  have h := Scheme.ord_mul (x := x) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, h1] at h
  omega

lemma chartCandidate_order [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of F)) [SmoothOfRelativeDimension 1 p]
    (j : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ X)
    [IsOpenImmersion j] [Nonempty (j ''ᵁ ⊤ : X.Opens)]
    {c : ℕ} (hc : 0 < c) (ho : Odd c)
    (x : (j ''ᵁ ⊤ : X.Opens)) (hx : Order.coheight x.val = 1) :
    Scheme.ord (chartCandidate W j c) x.val =
      -(@ite ℤ (X.evaluation (j ''ᵁ ⊤) x.val x.property (chartDivisionSection W j c) = 0)
        (Classical.propDecidable _) 1 0) := by
  have hn : affineOpenToField j (divisionElement W c) ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenToField_injective j)).mpr (divisionElement_ne_zero W hc)
  rw [chartCandidate, rational_order_inv _ hn,
    affineOpenToField_eq_section j]
  exact congrArg Neg.neg (chartDivisionSection_order W p j hc ho x hx)

open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCompactifiedDifferentialR0145

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The actual accepted coordinate chart, rewritten using the Weierstrass
coordinate ring. Its composite retains the specified inclusion in the model. -/
def actualAffineChart (M : Model k T) (s : baseScheme k ⟶ M.X)
    (a : complementScheme k M s ≅ cubicScheme k r) :
    Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing) ⟶ genericScheme k M :=
  (ProjectiveCubicChart.specIso (ProjectiveCubicChart.affineEquiv k r).symm).hom ≫
    a.inv ≫ (complement k M s).ι

instance actualAffineChart_open (M : Model k T) (s : baseScheme k ⟶ M.X)
    (a : complementScheme k M s ≅ cubicScheme k r) :
    IsOpenImmersion (actualAffineChart k M s a) := by
  unfold actualAffineChart
  infer_instance

lemma actualAffineChart_range (M : Model k T) (s : baseScheme k ⟶ M.X)
    (a : complementScheme k M s ≅ cubicScheme k r) :
    Set.range (actualAffineChart k M s a) = (complement k M s : Set (genericScheme k M)) := by
  let t : Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing) ⟶ complementScheme k M s :=
    (ProjectiveCubicChart.specIso (ProjectiveCubicChart.affineEquiv k r).symm).hom ≫ a.inv
  change Set.range (fun z => (complement k M s).ι (t z)) = _
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (t z).property
  · intro hx
    obtain ⟨z, hz⟩ := t.surjective ⟨x, hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩

lemma actualAffineChart_covers (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (x : genericScheme k M) (hx : x ≠ ArithmeticThetaGeometricNormR0150.identityPoint k M s hs) :
    ∃ z, actualAffineChart k M s a z = x := by
  change x ∈ Set.range (actualAffineChart k M s a)
  rw [actualAffineChart_range,
    GenericAffineCubicIsomorphismR0144.complement_eq_genericPoint_compl k M hM s hs]
  rintro ⟨b, hb⟩
  apply hx
  rw [Subsingleton.elim b (IsLocalRing.closedPoint (LaurentSeries k))] at hb
  exact hb.symm

/-- The original-field candidate on the actual generic Tate curve. -/
def actualCandidate (M : Model k T) (s : baseScheme k ⟶ M.X)
    (a : complementScheme k M s ≅ cubicScheme k r)
    [IsIntegral (genericScheme k M)] (c : ℕ) : (genericScheme k M).functionField :=
  chartCandidate (curve k r) (actualAffineChart k M s a) c

lemma actualCandidate_ne_zero (M : Model k T) (s : baseScheme k ⟶ M.X)
    (a : complementScheme k M s ≅ cubicScheme k r)
    [IsIntegral (genericScheme k M)] {c : ℕ} (hc : 0 < c) :
    actualCandidate k M s a c ≠ 0 := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  exact chartCandidate_ne_zero (curve k r) (actualAffineChart k M s a) hc

open NeronModelInfra ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- Field-valued torsion is equivalent to lying over the identity as a
scheme point. The field need not be algebraically closed. -/
lemma field_point_torsion_iff {F : Type u} [Field F] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of F)}
    (G : WeierstrassProjModel.RelativeGroupLaw F p)
    {L : Type u} [Field L] (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of F))
    (P : SchemeHomOver t p) (c : ℕ) :
    G.nsmul t c P = G.one t ↔
      G.schemeNsmul c (P.val (IsLocalRing.closedPoint L)) =
        (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) := by
  let e := (G.one (𝟙 _)).val
  have he : e ≫ p = 𝟙 _ := (G.one (𝟙 _)).property
  letI : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id p e he
  have hone : (G.one t).val = t ≫ e :=
    (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id _))).symm
  constructor
  · intro h
    have hm := congrArg (fun z : SchemeHomOver t p => z.val (IsLocalRing.closedPoint L)) h
    rw [← comp_schemeNsmul, hone, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hm
    exact hm.trans (congrArg e (Subsingleton.elim _ _))
  · intro h
    apply Subtype.ext
    rw [← comp_schemeNsmul, hone]
    exact field_point_eq_section (p := p) (P.val ≫ G.schemeNsmul c) t e
      (by rw [Category.assoc, G.schemeNsmul_over]; exact P.property) he
      (IsLocalRing.closedPoint L) (IsLocalRing.closedPoint F) h

lemma affineEquiv_X (r : ℕ) : ProjectiveCubicChart.affineEquiv k r (affineX (curve k r)) =
    cubicCoordinate k r false := by
  change ProjectiveCubicChart.affineEquiv k r (Ideal.Quotient.mk _ (C X)) =
    Ideal.Quotient.mk _ (MvPolynomial.X 0)
  simp [ProjectiveCubicChart.affineEquiv, ProjectiveCubicChart.polynomialEquiv,
    ProjectiveCubicChart.toMv]

lemma affineEquiv_Y (r : ℕ) : ProjectiveCubicChart.affineEquiv k r (affineY (curve k r)) =
    cubicCoordinate k r true := by
  change ProjectiveCubicChart.affineEquiv k r (Ideal.Quotient.mk _ X) =
    Ideal.Quotient.mk _ (MvPolynomial.X 1)
  simp [ProjectiveCubicChart.affineEquiv, ProjectiveCubicChart.polynomialEquiv,
    ProjectiveCubicChart.toMv]

lemma affineEquiv_scalar (r : ℕ) (z : LaurentSeries k) :
    ProjectiveCubicChart.affineEquiv k r
      (algebraMap (LaurentSeries k) (curve k r).toAffine.CoordinateRing z) =
      algebraMap (LaurentSeries k) (CubicRing k r) z := by
  change ProjectiveCubicChart.affineEquiv k r (Ideal.Quotient.mk _ (C (C z))) =
    Ideal.Quotient.mk _ (MvPolynomial.C z)
  simp [ProjectiveCubicChart.affineEquiv, ProjectiveCubicChart.polynomialEquiv,
    ProjectiveCubicChart.toMv]

lemma chartIso_of_equiv (r : ℕ) (e : ChartRing k r ≃+* CubicRing k r)
    (hscalar : ∀ a, e (ProjectiveCubicChart.chartScalar k r a) =
      algebraMap (LaurentSeries k) (CubicRing k r) a)
    (hx : e (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
      cubicCoordinate k r false)
    (hy : e (WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective) =
      cubicCoordinate k r true) :
    IsChartIso k r (ProjectiveCubicChart.specIso e) := by
  constructor
  · rw [ProjectiveCubicChart.specIso_hom, ProjectiveCubicChart.chart_structure,
      ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext hscalar
  · intro odd
    dsimp only [cubicScheme]
    rw [ProjectiveCubicChart.specIso_hom, ProjectiveCubicChart.spec_map_section]
    cases odd
    · exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv hx
    · exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv hy

lemma actualAffineChart_projective (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (a : complementScheme k M s ≅ cubicScheme k r)
    (e : ChartRing k r ≃+* CubicRing k r)
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : IsCompactificationIso k M s hs a (ProjectiveCubicChart.specIso e) E) :
    actualAffineChart k M s a ≫ E.hom =
      Spec.map (CommRingCat.ofHom
        (e.trans (ProjectiveCubicChart.affineEquiv k r).symm).toRingHom) ≫ chartInclusion k r := by
  simp only [actualAffineChart, Category.assoc, hE.2.1, Iso.inv_hom_id_assoc,
    ProjectiveCubicChart.specIso_hom]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- On the accepted projective chart, polynomial vanishing detects the
specified multiplication kernel on every extension-field point. -/
lemma chart_torsion_iff_divisionPolynomial (r : ℕ) (h3 : 3 ≤ r) (he : Even r)
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (L : Type u) [Field L] [DecidableEq L] [Algebra (LaurentSeries k) L]
    (P : SchemeHomOver (extensionBase k L) (projectiveStructure k r))
    (χ : ChartRing k r →+* L)
    (hP : P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r)
    {c : ℕ} (hc : Odd c) :
    G.nsmul (extensionBase k L) c P = G.one (extensionBase k L) ↔
      (((curve k r).toProjective.baseChange L).toAffine.preΨ' c).eval
        (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)) = 0 := by
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  letI : ((curve k r).toProjective.baseChange L).toAffine.IsElliptic :=
    WeierstrassCurve.instIsEllipticBaseChange (curve k r)
  obtain ⟨hxy, hpoint⟩ := hev.2 L P χ hP
  rw [← (ev L).injective.eq_iff,
    evaluation_nsmul k r G ev hev L P c, evaluation_one k r G ev hev L, hpoint]
  exact WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi _ hc hxy

/-- The division polynomial cuts out the actual projective multiplication
fiber on the coordinate chart, at every scheme point of that chart. -/
lemma projective_chart_support (r : ℕ) (h3 : 3 ≤ r) (he : Even r)
    (G : WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (projectiveStructure k r))
    (ev : PointEvaluation k r) (hev : IsCoordinateEvaluation k r G ev)
    (e : ChartRing k r ≃+* (curve k r).toAffine.CoordinateRing)
    (hscalar : ∀ a, e (ProjectiveCubicChart.chartScalar k r a) =
      algebraMap (LaurentSeries k) (curve k r).toAffine.CoordinateRing a)
    (hx : e (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
      affineX (curve k r))
    (z : Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing))
    {c : ℕ} (ho : Odd c) :
    affineResidueMap z (divisionElement (curve k r) c) = 0 ↔
      G.schemeNsmul c ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartInclusion k r) z) =
        (G.one (𝟙 _)).val (IsLocalRing.closedPoint (LaurentSeries k)) := by
  classical
  let L := (Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing)).residueField z
  let σ : (curve k r).toAffine.CoordinateRing →+* L := affineResidueMap z
  let τ := σ.comp (algebraMap (LaurentSeries k) (curve k r).toAffine.CoordinateRing)
  letI : Algebra (LaurentSeries k) L := τ.toAlgebra
  let χ := σ.comp e.toRingHom
  have hχ : χ.comp (ProjectiveCubicChart.chartScalar k r) = τ := by
    ext a
    exact congrArg σ (hscalar a)
  let P : SchemeHomOver (extensionBase k L) (projectiveStructure k r) :=
    ⟨Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r, by
      rw [Category.assoc, ProjectiveCubicChart.chart_structure, ← Spec.map_comp]
      exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hχ⟩
  have hz : Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint L) = z := by
    rw [show σ = affineResidueMap z from rfl, affineResidueMap_spec]
    exact Scheme.fromSpecResidueField_apply _ _
  have hP : P.val (IsLocalRing.closedPoint L) =
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ chartInclusion k r) z := by
    change (Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r) _ = _
    rw [show CommRingCat.ofHom χ = CommRingCat.ofHom e.toRingHom ≫
      CommRingCat.ofHom σ from rfl, Spec.map_comp]
    simp only [Scheme.Hom.comp_apply, hz]
  have hpol : (((curve k r).toProjective.baseChange L).toAffine.preΨ' c).eval
      (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective)) =
      σ (divisionElement (curve k r) c) := by
    change (((curve k r).map τ).preΨ' c).eval
      (σ (e (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective))) = _
    rw [hx, WeierstrassCurve.map_preΨ', Polynomial.eval_map]
    exact (divisionElement_eval (curve k r) c σ).symm
  have hpoly := chart_torsion_iff_divisionPolynomial k r h3 he G ev hev L P χ rfl ho
  rw [hpol] at hpoly
  have hpoint := field_point_torsion_iff G (extensionBase k L) P c
  rw [hP] at hpoint
  exact hpoly.symm.trans hpoint

end ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionCandidate_ne_zero
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionPolynomial_vanishes_iff
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionPolynomial_coprime
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.actualCandidate_ne_zero
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionPolynomial_separable
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chart_torsion_iff_divisionPolynomial

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionPolynomial_derivative_ne_zero
#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionPolynomial_eval_map

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.division_quotient_reduced

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.division_ideal_radical

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.local_order_of_radical

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.localized_division_ideal_radical

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.localized_division_order

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.radical_section_order

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chartDivisionSection_radical

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.section_mem_prime_iff

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chartDivisionSection_order

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionElement_eval

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisionElement_torsion

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.etale_stalkFiberLength

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.etale_fiber_residue_sum

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.recover_origin_coefficient

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.smooth_oneDimensionalCharts

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.openFieldIso_germ

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.affineOpenToField_eq_section

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.rational_order_inv

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chartCandidate_order

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.field_point_torsion_iff

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.affineEquiv_X

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.affineEquiv_Y

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.affineEquiv_scalar

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.placeDegree_section

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.weighted_etale_fiber

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.open_evaluation

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.affineResidueMap_spec

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chartSection_evaluation_zero_iff

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.section_coheight_one

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.divisor_from_off_origin

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.projective_chart_support

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.actualAffineChart_range

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.actualAffineChart_covers

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.chartIso_of_equiv

#print axioms ArithmeticThetaKatoExistenceR0151.ActualKatoDivisorPrincipal.actualAffineChart_projective

namespace ArithmeticThetaKatoExistenceR0151
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ActualKatoDivisorPrincipal
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaCompactifiedDifferentialR0145 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

/-- The inverse odd division polynomial is an actual nonzero rational function
with the prescribed nonsplit torsion divisor on the algebraized generic Tate curve. -/
theorem actual_kato_divisor_principal :
∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∃ g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.HasKatoDivisor k M s hs.1 G c g := by
  intro k _ _ r hr h3 T he M hM s hs G hG _ _ c hc hcop
  classical
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI := generic_relative_one k h3 M hM s hs
  letI := AlgebraizedGenericSmoothnessR0135.generic_proper k M hM
  letI := CompactifiedCoordinateIsomorphism.curve_elliptic k h3 he
  have hcpos : 0 < c := lt_trans Nat.zero_lt_one hc
  have ho := odd_of_coprime_six hcop
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k r hr h3 T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨e, hscalar, hx, hy⟩ := ProjectiveCubicChart.exists_chartEquiv k r
  let ci : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)) :=
    ProjectiveCubicChart.specIso e
  have hci : IsChartIso k r ci := chartIso_of_equiv k r e hscalar hx hy
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs
    X Y hX hY a ha ci hci
  have hi : E.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hE.1, E.inv_hom_id_assoc]
  let H := transport E.symm hi G
  have hHo : (H.one (𝟙 _)).val = origin k r := by
    change (G.one (𝟙 _)).val ≫ E.hom = _
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hE.2.2
  obtain ⟨ev, hev⟩ := projective_points_evaluation k r h3 he H hHo
  let ρ : ChartRing k r ≃+* (curve k r).toAffine.CoordinateRing :=
    e.trans (ProjectiveCubicChart.affineEquiv k r).symm
  have hρscalar (b : LaurentSeries k) : ρ (ProjectiveCubicChart.chartScalar k r b) =
      algebraMap (LaurentSeries k) (curve k r).toAffine.CoordinateRing b := by
    apply (ProjectiveCubicChart.affineEquiv k r).injective
    change (ProjectiveCubicChart.affineEquiv k r)
      ((ProjectiveCubicChart.affineEquiv k r).symm (e _)) = _
    rw [RingEquiv.apply_symm_apply, hscalar, affineEquiv_scalar]
  have hρx : ρ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
      affineX (curve k r) := by
    apply (ProjectiveCubicChart.affineEquiv k r).injective
    change (ProjectiveCubicChart.affineEquiv k r)
      ((ProjectiveCubicChart.affineEquiv k r).symm (e _)) = _
    rw [RingEquiv.apply_symm_apply, hx, affineEquiv_X]
  let j : Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing) ⟶ genericScheme k M :=
    actualAffineChart k M s a
  let g : (genericScheme k M).functionField := actualCandidate k M s a c
  have hg : g ≠ 0 := actualCandidate_ne_zero k M s a hcpos
  obtain ⟨hfinite, hetale, hsurj, hrank⟩ :=
    multiplication_finite_etale_degree k r hr h3 T he M hM s hs G hG c hcpos
  letI := hfinite
  letI := hetale
  letI := hsurj
  have hone : (G.one (𝟙 _)).val = genericPoint k M s hs.1 := by
    simpa only [pointOver, Category.id_comp] using congrArg Subtype.val (hG.1 (𝟙 _))
  have hfix : multiplication k M G c (identityPoint k M s hs.1) = identityPoint k M s hs.1 := by
    have h := congrArg (fun f : Spec (CommRingCat.of (LaurentSeries k)) ⟶ genericScheme k M =>
      f (IsLocalRing.closedPoint (LaurentSeries k))) (CoprimeTorsion.one_mul_map G c)
    rw [hone] at h
    exact h
  have hconj : multiplication k M G c ≫ E.hom = E.hom ≫ H.schemeNsmul c :=
    transport_multiplication E hE.1 hi G c
  have hdiag : j ≫ E.hom = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ chartInclusion k r :=
    actualAffineChart_projective k M s hs.1 a e E hE
  have hident : E.hom (identityPoint k M s hs.1) =
      (H.one (𝟙 _)).val (IsLocalRing.closedPoint (LaurentSeries k)) := by
    rw [hHo]
    exact congrArg (fun f => f (IsLocalRing.closedPoint (LaurentSeries k))) hE.2.2
  have hoff : ∀ x, x ≠ identityPoint k M s hs.1 →
      Scheme.ord g x = -(if multiplication k M G c x = identityPoint k M s hs.1 then 1 else 0) := by
    intro x hxo
    by_cases hgen : x = _root_.genericPoint (genericScheme k M)
    · subst x
      have hn : _root_.genericPoint (genericScheme k M) ≠ identityPoint k M s hs.1 := hxo
      rw [NormOrders.ord_generic (X := genericScheme k M),
        NormOrders.map_generic (X := genericScheme k M) (Y := genericScheme k M), if_neg hn, neg_zero]
    · obtain ⟨z, hz⟩ := actualAffineChart_covers k M hM s hs.1 a x hxo
      have hzU : j z ∈ j ''ᵁ (⊤ : (Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing)).Opens) :=
        ⟨z, trivial, rfl⟩
      letI : Nonempty (j ''ᵁ ⊤ : (genericScheme k M).Opens) := ⟨⟨j z, hzU⟩⟩
      have hco : Order.coheight (j z) = 1 := by
        rw [show j z = x from hz]
        exact NormOrders.smooth_coheight_one_of_ne_generic (X := genericScheme k M) (LaurentSeries k)
          (genericStructure k M) x hgen
      have hord := chartCandidate_order (X := genericScheme k M) (curve k r) (genericStructure k M) j hcpos ho ⟨j z, hzU⟩ hco
      have hsupport := (chartSection_evaluation_zero_iff j z hzU (divisionElement (curve k r) c)).trans
        (projective_chart_support k r h3 he H ev hev ρ hρscalar hρx z ho)
      have hm := congrArg (fun f : genericScheme k M ⟶ projectiveCurve k r => f (j z)) hconj
      have hd := congrArg (fun f : Spec (CommRingCat.of (curve k r).toAffine.CoordinateRing) ⟶
        projectiveCurve k r => f z) hdiag
      simp only [Scheme.Hom.comp_apply] at hm hd
      have hkernel : H.schemeNsmul c
          ((Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ chartInclusion k r) z) =
          (H.one (𝟙 _)).val (IsLocalRing.closedPoint (LaurentSeries k)) ↔
          multiplication k M G c (j z) = identityPoint k M s hs.1 := by
        rw [← E.hom.isOpenEmbedding.injective.eq_iff, hm, hd, hident]
        rfl
      have hsupp := hsupport.trans hkernel
      change Scheme.ord (chartCandidate (curve k r) j c) x = _
      rw [← show j z = x from hz]
      rw [← hsupp]
      exact hord
  have hall := divisor_from_off_origin (X := genericScheme k M) (genericStructure k M) (genericPoint k M s hs.1)
    (genericPoint_structure k M s hs.1) (multiplication k M G c)
    (G.schemeNsmul_over c) hfix g hg hoff
  refine ⟨g, hg, ?_⟩
  intro x
  simpa only [katoOrder, identityPoint, hrank, Nat.cast_pow] using hall x

end ArithmeticThetaKatoExistenceR0151
#print axioms ArithmeticThetaKatoExistenceR0151.actual_kato_divisor_principal
