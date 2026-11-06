import SchemeKatoUnitExistenceR0250
import SchemeMultiplicationDegreeR0250

/-! The exact Cartier divisor of the complete scheme-family Kato unit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaSchemeKatoUnitR0250
namespace SchemeKatoCartierDivisor
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeDiscriminantR0244
open ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence
open ArithmeticThetaArbitraryKatoUnitR0249 (restrict)
open ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor

lemma identity_effective {S : Scheme.{u}} (E : Family S) :
    ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (identityIdeal E) := by
  intro x
  obtain ⟨U, f, hx, a, ha, hIa⟩ :=
    ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E x
  exact ⟨E.curve.affineBasicOpen f, hx, a,
    isRegular_iff_mem_nonZeroDivisors.mpr ha, hIa⟩

lemma torsion_effective {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}} (σ : S ⟶ Base k) (E : Family S) (c : ℕ) (hc : 0 < c) :
    ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (torsionIdeal E c) := by
  letI := (scheme_multiplication_degree k S σ E c hc).2.1
  exact effective_comap_flat (multiplication E c) (identityIdeal E) (identity_effective E)

lemma appLE_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : f ''ᵁ V = U) :
    Function.Injective (f.appLE U V e) := by
  subst U
  intro s t he
  have H := SchemeKatoUnitExistence.restriction_eq_of_appLE_eq f (f ''ᵁ V) V e le_rfl s t he
  simpa using H

/-- Transport an equation and its correcting unit through an open chart. -/
lemma equation_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (C : Y.Opens) (D : X.Opens) (hD : D = f ⁻¹ᵁ C)
    (v : Γ(Y, C)) (w : Γ(X, D)) (eD : D ≤ f ⁻¹ᵁ C)
    (hw : w = f.appLE C D eD v)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (a b : Γ(Y, U)) (n : ℕ) (ε : (Γ(X, V))ˣ)
    (he : restrict D (V ⊓ D) inf_le_right w *
      restrict V (V ⊓ D) inf_le_left (f.appLE U V e b) =
      restrict V (V ⊓ D) inf_le_left ((ε : _) * (f.appLE U V e a)^n)) :
    ∃ (ei : f ''ᵁ V ≤ U) (η : (Γ(Y, f ''ᵁ V))ˣ),
      Equation C U v a b n (f ''ᵁ V) ei (η : _) := by
  have ei : f ''ᵁ V ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact e hx
  let η := Units.map (f.appIso V).inv.hom.toMonoidHom ε
  refine ⟨ei, η, ?_⟩
  have et : V ⊓ D ≤ f ⁻¹ᵁ (f ''ᵁ V ⊓ C) := by
    intro x hx
    exact ⟨⟨x, hx.1, rfl⟩, hD.le hx.2⟩
  have hi : f ''ᵁ (V ⊓ D) = f ''ᵁ V ⊓ C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, hD.le hx.2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hD.ge hy⟩, rfl⟩
  apply appLE_injective f _ _ et hi
  dsimp only [Equation]
  rw [hw] at he
  simp only [restrict, map_mul, map_pow, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] at he ⊢
  change _ = f.appLE (f ''ᵁ V) (V ⊓ D) _ ((f.appIso V).inv (ε : _)) * _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  simpa only [Category.assoc, Scheme.Hom.map_appLE] using he


attribute [local instance] LocalPresentation.commRing LocalPresentation.algebra
  LocalPresentation.elliptic

/-- Every point of an affine curve open admits the transported affine equation. -/
lemma local_equation {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    (σ : S ⟶ Base k) (E : Family S) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (v : UnitSection E c) (hv : IsKatoUnit E k σ c v)
    (U : E.curve.affineOpens) (a b : Γ(E.curve, U.1))
    (ha : IsRegular a) (hb : IsRegular b)
    (hIa : (identityIdeal E).ideal U = Ideal.span {a})
    (hIb : (torsionIdeal E c).ideal U = Ideal.span {b}) (x : U.1) :
    ∃ (V : E.curve.affineOpens) (e : V.1 ≤ U.1), x.1 ∈ V.1 ∧
      ∃ ε : (Γ(E.curve, V.1))ˣ,
        Equation (complement E c) U.1 (v : _) a b (c^2) V.1 e (ε : _) := by
  obtain ⟨P, y, hy⟩ := SchemeMultiplicationDegree.chart_covers σ E x.1
  letI : IsOpenImmersion P.comparison := SchemeMultiplicationDegree.chart_open σ E P
  letI : Algebra ℚ P.ring := ((algebraMap k P.ring).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨w, hw, eD, hvw⟩ := hv P.ring P.equation P.law P.originLaw
    P.base P.base_eq (chartComparison P)
  have hD := SchemeKatoUnitExistence.test_complement σ E P.ring P.equation
    P.law P.originLaw (chartComparison P) c
  have hcart := ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_cartier_divisor
    P.ring P.equation P.law P.originLaw c hc hc6 w hw
  obtain ⟨V, hV, hyV, e⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ P.comparison ⁻¹ᵁ U.1 from (show P.comparison y ∈ U.1 by rw [hy]; exact x.2))
  let V' : (ArithmeticThetaRelativeKatoR0169.Curve P.ring P.equation).affineOpens := ⟨V, hV⟩
  have hcomp := scheme_torsion_cartesian k S σ E (Base P.ring)
    (Spec.map (CommRingCat.ofHom (algebraMap k P.ring))) (chartFamily P)
    P.base P.base_eq (chartComparison P) c
  have hI : (identityIdeal E).comap P.comparison =
      ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal P.ring P.equation := by
    simpa only [chartComparison, chartFamily, identityIdeal, weierstrass_zero, ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal] using hcomp.2.1
  have hJ : (torsionIdeal E c).comap P.comparison =
      ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal P.ring P.equation P.law c := by
    simpa only [chartComparison, chartFamily, torsionIdeal, identityIdeal, weierstrass_zero,
      SchemeKatoUnitExistence.weierstrass_multiplication,
      ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal,
      ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal] using hcomp.2.2.1
  have hA : (ArithmeticThetaArbitraryKatoUnitR0249.identityIdeal P.ring P.equation).ideal V' =
      Ideal.span {P.comparison.appLE U.1 V e a} := by
    rw [← hI, Scheme.IdealSheafData.ideal_comap_of_le _ _ U V' e,
      hIa, Ideal.map_span, Set.image_singleton]
  have hB : (ArithmeticThetaArbitraryKatoUnitR0249.torsionIdeal P.ring P.equation P.law c).ideal V' =
      Ideal.span {P.comparison.appLE U.1 V e b} := by
    rw [← hJ, Scheme.IdealSheafData.ideal_comap_of_le _ _ U V' e,
      hIb, Ideal.map_span, Set.image_singleton]
  obtain ⟨ε, hε⟩ := hcart.2.2 V' _ _
    (regular_appLE P.comparison U V' e a ha)
    (regular_appLE P.comparison U V' e b hb) hA hB
  obtain ⟨ei, η, hη⟩ := equation_image P.comparison (complement E c) _ hD
    (v : _) (w : _) eD hvw U.1 V e a b (c^2) ε hε
  exact ⟨⟨P.comparison ''ᵁ V, hV.image_of_isOpenImmersion P.comparison⟩,
    ei, ⟨y, hyV, hy⟩, η, hη⟩

end SchemeKatoCartierDivisor

open ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory AlgebraicGeometry

/-- The full scheme-family unit has divisor c²[0] − [E[c]], with the correcting
unit defined on the entire arbitrary affine open, including empty opens. -/
theorem scheme_kato_cartier_divisor :
    ∀ (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
      (σ : S ⟶ Base k) (E : Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 →
      ∀ v : UnitSection E c, IsKatoUnit E k σ c v → HasCartierDivisor E c v := by
  intro k _ _ S σ E c hc hc6 v hv
  refine ⟨SchemeKatoCartierDivisor.identity_effective E,
    SchemeKatoCartierDivisor.torsion_effective σ E c (by omega), ?_⟩
  intro U a b ha hb hIa hIb
  apply ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor.glue_equation
    (torsionIdeal E c) U v.val a b ha hb hIb (c^2)
  exact SchemeKatoCartierDivisor.local_equation σ E c hc hc6 v hv U a b ha hb hIa hIb

#print axioms scheme_kato_cartier_divisor
end ArithmeticThetaSchemeKatoUnitR0250
