module

public import GeneralKatoPrincipalityR0168
public import GeneralCoprimeDivisorNormR0168
public import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
public import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
public import ActualKatoFunctionExistenceR0151

@[expose] public section

/-! Normalization and uniqueness on an arbitrary characteristic-zero elliptic curve. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaGeometricNormR0150
open ArithmeticThetaGeometricNormR0150.ActualNormalizedKatoUniqueness
open ArithmeticThetaKatoExistenceR0151.SimultaneousKatoNormalization
open ArithmeticThetaKatoExistenceR0151.ActualKatoFunctionExistence

namespace GeneralKatoExistence

lemma norms_commute (F : Type u) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] (G : Law F W)
    (hG : IsOriginLaw F W G) [IsIntegral (Curve F W)]
    [IsLocallyNoetherian (Curve F W)] (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (φ ψ : (Curve F W).functionField →+* (Curve F W).functionField)
    (hφ : IsFieldMap (G.schemeNsmul m) φ) (hψ : IsFieldMap (G.schemeNsmul n) ψ)
    (g : (Curve F W).functionField) :
    fieldNorm ψ (fieldNorm φ g) = fieldNorm φ (fieldNorm ψ g) := by
  obtain ⟨hfm, hem, hsm, _⟩ := general_multiplication_degree F W G hG m hm
  obtain ⟨hfn, hen, hsn, _⟩ := general_multiplication_degree F W G hG n hn
  letI := hfm
  letI := hem
  letI := hsm
  letI := hfn
  letI := hen
  letI := hsn
  apply commuting_norms (G.schemeNsmul m) (G.schemeNsmul n) ?_ φ ψ hφ hψ g
  rw [schemeNsmul_comp, schemeNsmul_comp, Nat.mul_comm m n]

lemma normalized_unique {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (F : Type u) [Field F] (p : X ⟶ Spec (.of F))
    [SmoothOfRelativeDimension 1 p] [IsProper p]
    [GeometricallyReduced p] [GeometricallyConnected p]
    (φ₂ φ₃ : X.functionField →+* X.functionField)
    (hs₂ : ∀ a, fieldNorm φ₂ (baseScalar F p a) = baseScalar F p (a^4))
    (hs₃ : ∀ a, fieldNorm φ₃ (baseScalar F p a) = baseScalar F p (a^9))
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (hord : ∀ x, Scheme.ord f x = Scheme.ord g x)
    (hf₂ : fieldNorm φ₂ f = f) (hg₂ : fieldNorm φ₂ g = g)
    (hf₃ : fieldNorm φ₃ f = f) (hg₃ : fieldNorm φ₃ g = g) : f = g := by
  obtain ⟨a, ha⟩ := exists_baseScalar_of_ord_zero F p (f/g)
    (div_ne_zero hf hg) (ord_div_eq_zero f g hf hg hord)
  have hn₂ := norm_quotient_fixed φ₂ f g hg hf₂ hg₂
  have hn₃ := norm_quotient_fixed φ₃ f g hg hf₃ hg₃
  rw [← ha, hs₂] at hn₂
  rw [← ha, hs₃] at hn₃
  have hp4 : (f/g)^4 = f/g := by
    rw [← ha]
    simpa only [baseScalar, map_pow] using hn₂
  have hp9 : (f/g)^9 = f/g := by
    rw [← ha]
    simpa only [baseScalar, map_pow] using hn₃
  exact (div_eq_one_iff_eq hg).mp
    (eq_one_of_four_nine (f/g) (div_ne_zero hf hg) hp4 hp9)

end GeneralKatoExistence
open GeneralKatoExistence

/-- The unique function with the actual Kato divisor and every positive
coprime multiplication norm, over the original coefficient field. -/
theorem general_kato_existence :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (G : ArithmeticThetaGeneralEllipticKatoR0168.Law F W) (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)], ∀ (c : ℕ), 1 < c → Nat.Coprime c 6 → ∃! g : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField, ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F W G c g := by
  intro F _ _ W _ G hG _ _ c hc hc6
  letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : GeometricallyIntegral (structureMap F W) :=
    WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso W
      (WeierstrassProjModel.projModel_pullback_iso_baseChange W.toProjective)
  letI : GeometricallyConnected (structureMap F W) := by
    constructor
    intro K _ y Z fst snd h
    letI : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    infer_instance
  obtain ⟨g, hg⟩ := general_kato_principality F W G hG c hc hc6
  obtain ⟨_, _, _, _, φ₂, hφ₂, _, hs₂⟩ :=
    general_multiplication_degree F W G hG 2 (by decide)
  obtain ⟨_, _, _, _, φ₃, hφ₃, _, hs₃⟩ :=
    general_multiplication_degree F W G hG 3 (by decide)
  have hc2 : Nat.Coprime c 2 := hc6.of_dvd_right (by decide)
  have hc3 : Nat.Coprime c 3 := hc6.of_dvd_right (by decide)
  have hn₂ := general_coprime_divisor_norm F W G hG c 2 hc (by decide) hc2 φ₂ hφ₂ g hg
  have hn₃ := general_coprime_divisor_norm F W G hG c 3 hc (by decide) hc3 φ₃ hφ₃ g hg
  obtain ⟨A, hA, hAg⟩ := exists_defect F (structureMap F W)
    (fieldNorm φ₂ g) g hn₂.1 hg.1 (fun x => (hn₂.2 x).trans (hg.2 x).symm)
  obtain ⟨B, hB, hBg⟩ := exists_defect F (structureMap F W)
    (fieldNorm φ₃ g) g hn₃.1 hg.1 (fun x => (hn₃.2 x).trans (hg.2 x).symm)
  obtain ⟨a, ha, ha₂, ha₃⟩ := explicit_normalization
    (scalarHom F (structureMap F W)) (normHom φ₂) (normHom φ₃)
    hs₂ hs₃ g hg.1 A B hA hB hAg hBg
    (norms_commute F W G hG 2 3 (by decide) (by decide) φ₂ φ₃ hφ₂ hφ₃ g)
  let ι := scalarHom F (structureMap F W)
  let f := ι a * g
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  have hf : HasKatoDivisor F W G c f := by
    refine ⟨mul_ne_zero hιa hg.1, ?_⟩
    intro x
    change Scheme.ord (ι a * g) x = _
    rw [Scheme.ord_mul hιa hg.1, scalar_order F (structureMap F W) a ha, zero_add]
    exact hg.2 x
  have hf₂ : fieldNorm φ₂ f = f := ha₂
  have hf₃ : fieldNorm φ₃ f = f := ha₃
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · intro d hd hcd φ hφ
    have hN := general_coprime_divisor_norm F W G hG c d hc hd hcd φ hφ f hf
    apply normalized_unique F (structureMap F W) φ₂ φ₃ hs₂ hs₃
      (fieldNorm φ f) f hN.1 hf.1 (fun x => (hN.2 x).trans (hf.2 x).symm)
    · rw [norms_commute F W G hG d 2 hd (by decide) φ φ₂ hφ hφ₂ f, hf₂]
    · exact hf₂
    · rw [norms_commute F W G hG d 3 hd (by decide) φ φ₃ hφ hφ₃ f, hf₃]
    · exact hf₃
  · intro f' hf'
    exact normalized_unique F (structureMap F W) φ₂ φ₃ hs₂ hs₃
      f' f hf'.1.1 hf.1 (fun x => (hf'.1.2 x).trans (hf.2 x).symm)
      (hf'.2 2 (by decide) hc2 φ₂ hφ₂) hf₂
      (hf'.2 3 (by decide) hc3 φ₃ hφ₃) hf₃

#print axioms general_kato_existence
end ArithmeticThetaGeneralEllipticKatoR0168
