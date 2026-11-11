import Mathlib.Algebra.Group.Hom.Basic

/-!
# Relations determine equalities and coordinates

These results use only additive maps on the same coefficient group. In
particular, they apply to linear combinations of sections and to linear
combinations of formal series. Their statements contain no geometric
construction or task-specific definition.
-/

set_option autoImplicit false

namespace ArithmeticThetaReview.Relations

/-- Identical zero relations determine all equalities between combinations. -/
theorem equality_of_same_relations :
    ∀ (V W Z : Type) [AddGroup V] [AddGroup W] [AddGroup Z]
      (f : V →+ W) (g : V →+ Z),
      (∀ v, f v = 0 ↔ g v = 0) →
      ∀ x y, f x = f y ↔ g x = g y := by
  intro V W Z _ _ _ f g hzero x y
  calc
    f x = f y ↔ f (x - y) = 0 := by rw [map_sub, sub_eq_zero]
    _ ↔ g (x - y) = 0 := hzero (x - y)
    _ ↔ g x = g y := by rw [map_sub, sub_eq_zero]

/-- The same coefficient parametrization preserves independence and unique
coordinates. The coordinates themselves are unchanged in both directions. -/
theorem coordinates_of_same_relations :
    ∀ (V W Z D : Type) [AddGroup V] [AddGroup W] [AddGroup Z]
      (f : V →+ W) (g : V →+ Z),
      (∀ v, f v = 0 ↔ g v = 0) →
      ∀ p : D → V,
        (Function.Injective (g ∘ p) ∧ ∀ v, ∃! d, g v = g (p d)) ↔
        (Function.Injective (f ∘ p) ∧ ∀ v, ∃! d, f v = f (p d)) := by
  intro V W Z D _ _ _ f g hzero p
  have heq := equality_of_same_relations V W Z f g hzero
  constructor
  · rintro ⟨hi, hc⟩
    refine ⟨fun d e hde => hi ((heq (p d) (p e)).mp hde), ?_⟩
    intro v
    obtain ⟨d, hd, hu⟩ := hc v
    exact ⟨d, (heq v (p d)).mpr hd,
      fun e he => hu e ((heq v (p e)).mp he)⟩
  · rintro ⟨hi, hc⟩
    refine ⟨fun d e hde => hi ((heq (p d) (p e)).mpr hde), ?_⟩
    intro v
    obtain ⟨d, hd, hu⟩ := hc v
    exact ⟨d, (heq v (p d)).mp hd,
      fun e he => hu e ((heq v (p e)).mpr he)⟩

end ArithmeticThetaReview.Relations
