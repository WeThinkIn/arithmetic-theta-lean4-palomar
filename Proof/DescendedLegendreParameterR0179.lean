module

public import LevelCompactificationDefinitionsR0179
public import Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective
public import Theorems.Thm_AlgebraicGeometry_IsFinite_of_comp_of_surjective
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

@[expose] public section

/-! Descent of the actual Legendre projection through the compatible sign quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLevelCompactificationR0179
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaCompatibleLevelR0178

namespace DescendedLegendreParameterR0179

/-- Étaleness descends through a finite étale surjection on the source. -/
lemma etale_of_comp {X Y Z : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ Z)
    [IsFinite q] [Etale q] [Surjective q] [Etale (q ≫ p)] : Etale p := by
  letI : Smooth p := Smooth.of_comp_of_smooth_of_surjective q p
  apply (Etale.iff_smoothOfRelativeDimension_zero p).mpr
  cases isEmpty_or_nonempty X with
  | inl hx =>
    letI := hx
    haveI : IsEmpty Y := ⟨fun y => by
      obtain ⟨x, _⟩ := q.surjective y
      exact isEmptyElim x⟩
    exact ⟨fun y => isEmptyElim y⟩
  | inr hx =>
    letI := hx
    exact (SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
      q p 0 0).1

end DescendedLegendreParameterR0179

/-- The unique parameter on the same quotient is finite étale and surjective,
with the full-GL degree divided by twelve. -/
theorem descended_legendre_parameter :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (D : LevelData k L),
      ∃! p : Quiver.Hom (OpenBase k L D) (Base (LegendreRing k)),
        IsParameter k L D p ∧ IsFinite p ∧ Etale p ∧ Surjective p ∧
        ∀ y, p.finrank y = levelDegree L / 12 := by
  intro k _ _ L _ _ D
  let q := D.quotient.quotient.q
  let a := D.cover.inclusion ≫ D.atlas.level.projection
  have hinv : D.quotient.sign ≫ a = a := by
    dsimp only [a]
    rw [← Category.assoc, D.quotient.sign_eq, Category.assoc, D.atlas.sign.over_eq]
  obtain ⟨p, hp, hu⟩ := D.quotient.quotient.universal _ a hinv
  letI : IsFinite q := D.quotient.quotient.finite
  letI : Etale q := D.quotient.quotient.etale
  letI : Surjective q := D.quotient.quotient.surjective
  have hqp : q ≫ p = a := hp
  letI : IsFinite (q ≫ p) := hqp ▸ D.cover.finite
  letI : Etale (q ≫ p) := hqp ▸ D.cover.etale
  letI : Surjective (q ≫ p) := hqp ▸ D.cover.surjective
  letI : Etale p := DescendedLegendreParameterR0179.etale_of_comp q p
  letI : IsFinite p := IsFinite.of_comp_of_surjective q p
  letI : Surjective p := Surjective.of_comp q p
  refine ⟨p, ⟨⟨hp, ?_⟩, inferInstance, inferInstance, inferInstance, ?_⟩, ?_⟩
  · apply (cancel_epi q).mp
    rw [← Category.assoc, hqp]
    exact D.quotient.quotient.over_eq.symm
  · intro y
    have h := Scheme.Hom.finrank_comp_of_finrank_eq_const q p 2
      D.quotient.quotient.degree y
    rw [hqp, D.cover.degree] at h
    calc
      p.finrank y = (2 * p.finrank y) / 2 := by omega
      _ = (levelDegree L / 6) / 2 := by rw [h]
      _ = levelDegree L / 12 := by rw [Nat.div_div_eq_div_mul]
  · intro p' hp'
    exact hu p' hp'.1.1

#print axioms descended_legendre_parameter
end ArithmeticThetaLevelCompactificationR0179
