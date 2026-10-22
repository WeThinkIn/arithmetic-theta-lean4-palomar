module

public import CartierUnitRatioExtensionR0254
public import GlobalUnitTwoThreeNormRigidityR0254
public import SchemeKatoNormR0251

@[expose] public section

/-! Intrinsic characterization by the actual Cartier divisor and two determinant norms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaKatoCharacterizationR0254
namespace SchemeKatoIntrinsicCharacterization
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaSchemeKatoNormR0251

/-- Multiplicativity of the unique determinant norm transfers fixedness to a
factor after cancellation of a unit in the actual section ring. -/
lemma normInvariant_factor {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [Etale f]
    (U : X.Opens) (a v : Sections X U) (w : (Sections X U)ˣ)
    (hv : NormInvariant f U v) (hw : NormInvariant f U (w : _))
    (heq : v = a * (w : _)) : NormInvariant f U a := by
  obtain ⟨N, hN, e, hNv⟩ := hv
  obtain ⟨M, hM, e', hMw⟩ := hw
  have hNM : N = M := (finite_etale_norm_family X X f).unique hN hM
  subst M
  have hmul : restrict U (f ⁻¹ᵁ U) e v =
      restrict U (f ⁻¹ᵁ U) e a * restrict U (f ⁻¹ᵁ U) e (w : _) := by
    rw [heq]
    exact map_mul (X.presheaf.map (homOfLE e).op).hom a (w : _)
  refine ⟨N, hN, e, ?_⟩
  apply w.isUnit.isRegular.right
  calc
    N U (restrict U (f ⁻¹ᵁ U) e a) * (w : _) =
        N U (restrict U (f ⁻¹ᵁ U) e a) *
          N U (restrict U (f ⁻¹ᵁ U) e (w : _)) := by rw [hMw]
    _ = N U (restrict U (f ⁻¹ᵁ U) e v) := by rw [hmul, map_mul]
    _ = v := hNv
    _ = a * (w : _) := heq

end SchemeKatoIntrinsicCharacterization
open AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeKatoUnitR0250 ArithmeticThetaSchemeKatoNormR0251

/-- The canonical affine-test normalization is equivalent to the exact Cartier
divisor and multiplication-by-two and multiplication-by-three norm identities. -/
theorem scheme_kato_intrinsic_characterization :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : Quiver.Hom S (Base k)) (E : Family S),
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : UnitSection E c,
      IsKatoUnit E k σ c v ↔ HasCartierDivisor E c v ∧
        NormInvariant (multiplication E 2) (complement E c) (v : _) ∧
        NormInvariant (multiplication E 3) (complement E c) (v : _) := by
  intro k _ _ S σ E c hc hc6 v
  have hc2 : Nat.Coprime c 2 := hc6.of_dvd_right (by decide)
  have hc3 : Nat.Coprime c 3 := hc6.of_dvd_right (by decide)
  constructor
  · intro hv
    exact ⟨scheme_kato_cartier_divisor k S σ E c hc hc6 v hv,
      scheme_kato_norm k S σ E c hc hc6 v hv 2 (by decide) hc2,
      scheme_kato_norm k S σ E c hc hc6 v hv 3 (by decide) hc3⟩
  · rintro ⟨hv, hv2, hv3⟩
    obtain ⟨w, hw⟩ := scheme_kato_unit_existence k S σ E c hc hc6
    have hwD := scheme_kato_cartier_divisor k S σ E c hc hc6 w hw
    obtain ⟨a, ha, _⟩ := cartier_unit_ratio_extension k S σ E c hc hc6 v w hv hwD
    have hn (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d)
        (hvd : NormInvariant (multiplication E d) (complement E c) (v : _)) :
        NormInvariant (multiplication E d) (complement E c) (restrictGlobal E c a) := by
      letI := (scheme_multiplication_degree k S σ E d hd).1
      letI := (scheme_multiplication_degree k S σ E d hd).2.1
      exact SchemeKatoIntrinsicCharacterization.normInvariant_factor
        (multiplication E d) (complement E c) (restrictGlobal E c a) (v : _) w
        hvd (scheme_kato_norm k S σ E c hc hc6 w hw d hd hcd) ha
    have ha1 : a = 1 := global_unit_two_three_norm_rigidity k S σ E c hc hc6 a
      (hn 2 (by decide) hc2 hv2) (hn 3 (by decide) hc3 hv3)
    have hvw : v = w := by
      apply Units.ext
      simpa only [ha1, restrictGlobal, Units.val_one,
        ArithmeticThetaArbitraryKatoUnitR0249.restrict, map_one, one_mul] using ha
    exact hvw ▸ hw

#print axioms scheme_kato_intrinsic_characterization
end ArithmeticThetaKatoCharacterizationR0254
