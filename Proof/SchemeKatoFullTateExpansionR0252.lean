module

public import CanonicalPeriodOneExpansionR0252
public import SchemeKatoNormR0251
public import SchemeKatoCartierDivisorR0250
public import SchemeKatoUnitUniquenessR0250

@[expose] public section

/-! The canonical scheme unit, its Cartier divisor and determinant norms,
and the full Tate expansion of its actual pullback are properties of one unit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaSchemeKatoExpansionR0252
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeKatoUnitR0250
open ArithmeticThetaPeriodOneNormR0248

/-- Affine-test normalization identifies the literal pulled-back section. -/
private lemma canonical_tate_expansion
    (k : Type) [Field k] [CharZero k] (B : Scheme.{0})
    (σ : B ⟶ Base k) (E : Family B) (c : ℕ)
    (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (v : UnitSection E c) (hv : IsKatoUnit E k σ c v) :
    TateExpansion k σ E c v := by
  intro l _ _ _
  letI : CharZero (LaurentSeries l) := LaurentSeries.XAdic.charZero l
  letI : (periodCurve l).IsElliptic :=
    (ArithmeticThetaPeriodOneR0246.period_one_geometric_comparison l).1
  have hgeom := ArithmeticThetaRelativeKatoR0169.relative_curve_geometry
    (LaurentSeries l) (periodCurve l)
  letI : IsIntegral (Curve l (periodCurve l)) := hgeom.1
  letI : IsLocallyNoetherian (Curve l (periodCurve l)) := hgeom.2.1
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨ev, ⟨hev, hi⟩, _⟩ := period_one_function_field_evaluation l
  refine ⟨ev, hev, hi, ?_⟩
  intro G hG b hb C
  letI : Algebra k (LaurentSeries l) :=
    ((algebraMap l (LaurentSeries l)).comp (algebraMap k l)).toAlgebra
  obtain ⟨w, hw, e, he⟩ := hv (LaurentSeries l) (periodCurve l) G hG b hb C
  obtain ⟨hU, hexp⟩ := canonical_period_one_expansion l G hG c hc hc6 w (by
    exact (congrArg (fun a : Algebra ℚ (LaurentSeries l) =>
      @ArithmeticThetaArbitraryKatoUnitR0249.IsKatoUnit
        (LaurentSeries l) _ (periodCurve l) G a c w)
      (Subsingleton.elim _ _)).mp hw)
  refine ⟨e, hU, ?_⟩
  have H := hexp ev hev
  rw [he] at H
  exact H

/-- Unique canonical scheme unit with divisor, every coprime positive norm,
and full period-one expansion in every actual pointed Cartesian test. -/
theorem scheme_kato_full_tate_expansion :
∀ (k : Type) [Field k] [CharZero k] (B : AlgebraicGeometry.Scheme.{0}) (σ : Quiver.Hom B (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family B), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∃! v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ∧ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ (∀ d : ℕ, 0 < d → Nat.Coprime c d → ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E d) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _)) ∧ ArithmeticThetaSchemeKatoExpansionR0252.TateExpansion k σ E c v := by
  intro k _ _ B σ E c hc hc6
  obtain ⟨v, hv⟩ := scheme_kato_unit_existence k B σ E c hc hc6
  refine ⟨v, ⟨hv, scheme_kato_cartier_divisor k B σ E c hc hc6 v hv,
    ?_, canonical_tate_expansion k B σ E c hc hc6 v hv⟩, ?_⟩
  · exact ArithmeticThetaSchemeKatoNormR0251.scheme_kato_norm k B σ E c hc hc6 v hv
  · intro w hw
    exact scheme_kato_unit_uniqueness k B σ E c hc hc6 w v hw.1 hv

end ArithmeticThetaSchemeKatoExpansionR0252

#print axioms ArithmeticThetaSchemeKatoExpansionR0252.scheme_kato_full_tate_expansion
