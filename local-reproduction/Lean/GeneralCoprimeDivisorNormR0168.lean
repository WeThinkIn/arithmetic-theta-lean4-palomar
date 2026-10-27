import GeneralMultiplicationDegreeR0168
import CoprimeTorsionDivisorNormR0150

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaGeneralEllipticKatoR0168
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaGeometricNormR0150

/-- Every positive coprime multiplication norm preserves the full Kato divisor
on the specified arbitrary characteristic-zero elliptic curve. -/
theorem general_coprime_divisor_norm :
∀ (F : Type u) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (G : ArithmeticThetaGeneralEllipticKatoR0168.Law F W) (hG : ArithmeticThetaGeneralEllipticKatoR0168.IsOriginLaw F W G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W)], ∀ (c d : ℕ), 1 < c → 0 < d → Nat.Coprime c d → ∀ (φ : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField →+* (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField), ArithmeticThetaGeometricNormR0150.IsFieldMap (G.schemeNsmul d) φ → ∀ (g : (ArithmeticThetaGeneralEllipticKatoR0168.Curve F W).functionField), ArithmeticThetaGeneralEllipticKatoR0168.HasKatoDivisor F W G c g → ArithmeticThetaGeneralEllipticKatoR0168.HasKatoDivisor F W G c (ArithmeticThetaGeometricNormR0150.fieldNorm φ g) := by
  intro F _ _ W _ G hG _ _ c d hc hd hcd φ hφ g hg
  classical
  obtain ⟨hfinite, hetale, hsurj, _⟩ :=
    general_multiplication_degree F W G hG d hd
  letI := hfinite
  letI := hetale
  letI := hsurj
  letI : SmoothOfRelativeDimension 1 (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap F W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  refine ⟨NormOrders.fieldNorm_ne_zero (G.schemeNsmul d) φ hφ hg.1, ?_⟩
  obtain ⟨a, _, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcd.symm hc
  have he : (G.one (𝟙 _)).val (IsLocalRing.closedPoint F) = originPoint F W := by
    rw [hG.1]
    rfl
  intro x
  rw [geometric_norm_orders F (Curve F W) (Curve F W)
    (structureMap F W) (structureMap F W) (G.schemeNsmul d)
    (G.schemeNsmul_over d) φ hφ g hg.1 x]
  unfold pushOrder
  simp_rw [hg.2, ArithmeticThetaGeneralEllipticKatoR0168.katoOrder]
  have h := CoprimeTorsion.push_kato G c d a ha x
  rw [he] at h
  exact h

#print axioms general_coprime_divisor_norm
end ArithmeticThetaGeneralEllipticKatoR0168
