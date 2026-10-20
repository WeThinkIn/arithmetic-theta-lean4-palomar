module

public import ArbitraryKatoNormR0251
public import FiniteEtaleNormFamilyR0251

@[expose] public section

/-! Descent of the determinant norm identity for the canonical scheme Kato unit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoNormR0251
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence
open ArithmeticThetaSchemeKatoUnitR0250

namespace SchemeKatoNorm

attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic

variable {k : Type u} [Field k] [CharZero k] {B : Scheme.{u}}
  (σ : B ⟶ Base k) (E : Family B) (c : ℕ) (hc : 1 < c)
  (hc6 : Nat.Coprime c 6) (v : UnitSection E c) (hv : IsKatoUnit E k σ c v)
  (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d)

include hc hc6 hv hd hcd

lemma chart_fixed (P : LocalPresentation k B σ E) :
    LocallyNormFixed (P.law.schemeNsmul d)
      (ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c)
      (P.comparison.appLE (complement E c) _
        (SchemeKatoUnitExistence.test_complement σ E P.ring P.equation P.law
          P.originLaw (chartComparison P) c).le (v : _)) := by
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨w, hw, e, he⟩ := hv P.ring P.equation P.law P.originLaw
    P.base P.base_eq (chartComparison P)
  have H := arbitrary_kato_norm P.ring P.equation P.law P.originLaw c hc hc6
    w hw d hd hcd
  rw [he] at H
  dsimp only [chartComparison] at H
  convert H using 1
  rfl

lemma preimage_le : multiplication E d ⁻¹ᵁ complement E c ≤ complement E c := by
  intro x hx
  obtain ⟨P, y, hy⟩ := SchemeMultiplicationDegree.chart_covers σ E x
  have hD := SchemeKatoUnitExistence.test_complement σ E P.ring P.equation
    P.law P.originLaw (chartComparison P) c
  obtain ⟨e, _⟩ := chart_fixed σ E c hc hc6 v hv d hd hcd P
  have hs := SchemeMultiplicationDegree.chart_square σ E P d
  have he : P.comparison (P.law.schemeNsmul d y) = multiplication E d x := by
    have hh := congrArg (fun f => f y) hs.w
    simpa only [Scheme.Hom.comp_apply, hy] using hh.symm
  have hm : P.law.schemeNsmul d y ∈
      ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c := by
    rw [hD]
    change P.comparison (P.law.schemeNsmul d y) ∈ complement E c
    rwa [he]
  have hyD := e hm
  rw [hD] at hyD
  change P.comparison y ∈ complement E c at hyD
  rwa [hy] at hyD

lemma fixed (N : NormFamily (multiplication E d))
    (hN : IsNormFamily (multiplication E d) N)
    (e : multiplication E d ⁻¹ᵁ complement E c ≤ complement E c) :
    N (complement E c) (restrict _ _ e (v : _)) = (v : _) := by
  letI := (scheme_multiplication_degree k B σ E d hd).1
  letI := (scheme_multiplication_degree k B σ E d hd).2.1
  apply NormSection.sections_eq_local
  intro x hx
  obtain ⟨P, y, hy⟩ := SchemeMultiplicationDegree.chart_covers σ E x
  letI : IsOpenImmersion P.comparison := SchemeMultiplicationDegree.chart_open σ E P
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  letI := (SchemeMultiplicationDegree.affine_degree P.ring P.equation P.law
    P.originLaw d hd).1
  letI := (SchemeMultiplicationDegree.affine_degree P.ring P.equation P.law
    P.originLaw d hd).2.1
  let D := ArithmeticThetaArbitraryKatoUnitR0249.complement P.ring P.equation P.law c
  have hD : D = P.comparison ⁻¹ᵁ complement E c :=
    SchemeKatoUnitExistence.test_complement σ E P.ring P.equation
      P.law P.originLaw (chartComparison P) c
  obtain ⟨ep, hp⟩ := finite_etale_norm_base_change _ _ _ _
    (multiplication E d) (P.law.schemeNsmul d) P.comparison P.comparison
    (SchemeMultiplicationDegree.chart_square σ E P d) (complement E c)
    (restrict _ _ e (v : _)) (N _ (restrict _ _ e (v : _)))
    (hN.1 _ _) D hD.le
  obtain ⟨eb, hb⟩ := chart_fixed σ E c hc hc6 v hv d hd hcd P
  rw [NormBaseChange.appLE_restrict] at hp
  rw [NormBaseChange.restrict_appLE] at hb
  have heq := (finite_etale_norm_section _ _ (P.law.schemeNsmul d) D _).unique hp hb
  have ei : P.comparison ''ᵁ D ≤ complement E c := by
    rintro _ ⟨z, hz, rfl⟩
    exact hD.le hz
  refine ⟨P.comparison ''ᵁ D, ⟨y, ?_, hy⟩, ei, ?_⟩
  · rw [hD]
    change P.comparison y ∈ complement E c
    rwa [hy]
  · exact SchemeKatoUnitExistence.restriction_eq_of_appLE_eq P.comparison
      (complement E c) D hD.le ei _ _ heq

end SchemeKatoNorm

/-- The actual multiplicative sheaf norm fixes the accepted canonical Kato unit
on its entire torsion complement over every characteristic-zero scheme base. -/
theorem scheme_kato_norm :
    ∀ (k : Type u) [Field k] [CharZero k] (B : Scheme.{u})
      (σ : B ⟶ Base k) (E : Family B),
    ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
    ∀ v : UnitSection E c, IsKatoUnit E k σ c v →
    ∀ d : ℕ, 0 < d → Nat.Coprime c d →
      NormInvariant (multiplication E d) (complement E c) (v : _) := by
  intro k _ _ B σ E c hc hc6 v hv d hd hcd
  letI := (scheme_multiplication_degree k B σ E d hd).1
  letI := (scheme_multiplication_degree k B σ E d hd).2.1
  obtain ⟨N, hN, _⟩ := finite_etale_norm_family E.curve E.curve (multiplication E d)
  have e := SchemeKatoNorm.preimage_le σ E c hc hc6 v hv d hd hcd
  exact ⟨N, hN, e, SchemeKatoNorm.fixed σ E c hc hc6 v hv d hd hcd N hN e⟩

#print axioms scheme_kato_norm
end ArithmeticThetaSchemeKatoNormR0251
