module

public import ActualScalarTranslationR0146
public import ActualRotationTranslationR0146
public import AlgebraizedAnnularActionsR0137

@[expose] public section

/-! Addition of the actual generic marked points, including modular carry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaMarkedGroupLawR0146
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaModelSymmetriesR0137
open ArithmeticThetaGeometricLiftsR0141

namespace MarkedPointAddition
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
variable (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)

/-- A chosen actual section, whose uniqueness removes dependence on the choice. -/
def sectionAt (i : Fin r) (a : kˣ) : baseScheme k ⟶ M.X :=
  (marked_section_algebraization k r hr h3 T M hM i a).exists.choose

lemma sectionAt_spec (i : Fin r) (a : kˣ) :
    MarkedLift k M i a (sectionAt k h3 M hM i a) :=
  (marked_section_algebraization k r hr h3 T M hM i a).exists.choose_spec

def point (i : Fin r) (a : kˣ) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of (LaurentSeries k)))) (genericStructure k M) :=
  pointOver k M (𝟙 _) (sectionAt k h3 M hM i a) (sectionAt_spec k h3 M hM i a).1

lemma point_eq (i : Fin r) (a : kˣ) (p : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) :
    point k h3 M hM i a = pointOver k M (𝟙 _) p hp.1 := by
  have he := ActualRotationTranslation.markedLift_unique k M i a
    (sectionAt k h3 M hM i a) p (sectionAt_spec k h3 M hM i a) hp
  subst p
  rfl

lemma point_map (i j : Fin r) (a b : kˣ) (f : M.X ⟶ M.X)
    (hf : f ≫ M.p = M.p)
    (ht : MarkedLift k M j b (sectionAt k h3 M hM i a ≫ f)) :
    (point k h3 M hM i a).val ≫ genericMap k M f hf =
      (point k h3 M hM j b).val := by
  have he := ActualRotationTranslation.markedLift_unique k M j b
    _ _ ht (sectionAt_spec k h3 M hM j b)
  simpa only [point, pointOver, Category.id_comp] using
    ActualScalarTranslation.genericPoint_map k M
      (sectionAt k h3 M hM i a) (sectionAt k h3 M hM j b)
      (sectionAt_spec k h3 M hM i a).1 (sectionAt_spec k h3 M hM j b).1 f hf he

variable (he : Even r) (s : baseScheme k ⟶ M.X)
variable (hs : MarkedLift k M (zeroIndex r hr) 1 s)
variable (G : Law k M) (hG : IsOriginLaw k M s hs.1 G)
variable (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
variable (ha : Actions k M rot scal inv)
include he s hs hG rot scal inv ha

lemma mul_scalar (i : Fin r) (a b : kˣ) :
    G.mul (𝟙 _) (point k h3 M hM i a) (point k h3 M hM (zeroIndex r hr) b) =
      point k h3 M hM i (a*b) := by
  apply Subtype.ext
  have ht := actual_scalar_translation k r hr h3 T he M hM s hs G hG
    rot scal inv ha b (sectionAt k h3 M hM (zeroIndex r hr) b)
    (sectionAt_spec k h3 M hM (zeroIndex r hr) b) (𝟙 _) (point k h3 M hM i a)
  change (G.mul (𝟙 _) (point k h3 M hM i a) (point k h3 M hM (zeroIndex r hr) b)).val = _ at ht
  rw [ht]
  apply point_map k h3 M hM
  have hh := (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha
    i a _ (sectionAt_spec k h3 M hM i a)).2.1 b
  simpa only [mul_comm b a] using hh

lemma mul_rotation (i : Fin r) (a : kˣ) :
    G.mul (𝟙 _) (point k h3 M hM i a)
      (point k h3 M hM (next r hr (zeroIndex r hr)) 1) =
      point k h3 M hM (next r hr i) a := by
  apply Subtype.ext
  have ht := actual_rotation_translation k r hr h3 T he M hM s hs G hG
    rot scal inv ha (sectionAt k h3 M hM (next r hr (zeroIndex r hr)) 1)
    (sectionAt_spec k h3 M hM (next r hr (zeroIndex r hr)) 1)
    (𝟙 _) (point k h3 M hM i a)
  change (G.mul (𝟙 _) (point k h3 M hM i a)
    (point k h3 M hM (next r hr (zeroIndex r hr)) 1)).val = _ at ht
  rw [ht]
  apply point_map k h3 M hM
  exact (algebraized_marked_transport k r hr h3 T M hM rot scal inv ha
    i a _ (sectionAt_spec k h3 M hM i a)).1

lemma mul_iterate (n : ℕ) (i : Fin r) (a b : kˣ) :
    G.mul (𝟙 _) (point k h3 M hM i a)
      (point k h3 M hM ((next r hr)^[n] (zeroIndex r hr)) b) =
      point k h3 M hM ((next r hr)^[n] i) (a*b) := by
  induction n with
  | zero => exact mul_scalar k h3 M hM he s hs G hG rot scal inv ha i a b
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [← mul_rotation k h3 M hM he s hs G hG rot scal inv ha,
      ← G.mul_assoc, ih,
      mul_rotation k h3 M hM he s hs G hG rot scal inv ha]

end MarkedPointAddition
open MarkedPointAddition

/-- Addition in the actual generic group law is the marked modular addition. -/
theorem marked_point_addition :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
    ∀ (G : Law k M), IsOriginLaw k M s hs.1 G →
    ∀ (i j : Fin r) (a b : kˣ) (p q z : baseScheme k ⟶ M.X)
    (hp : MarkedLift k M i a p) (hq : MarkedLift k M j b q)
    (hz : MarkedLift k M (sumIndex (hr := hr) i j) (a*b) z),
    G.mul (𝟙 (Spec (CommRingCat.of (LaurentSeries k))))
      (pointOver k M (𝟙 _) p hp.1) (pointOver k M (𝟙 _) q hq.1) =
      pointOver k M (𝟙 _) z hz.1 := by
  intro k _ _ r hr h3 T he M hM s hs G hG i j a b p q z hp hq hz
  obtain ⟨rot, scal, inv, ha⟩ := algebraized_annular_actions k r hr h3 T M hM
  have hj : (next r hr)^[j.val] (zeroIndex r hr) = j := by
    apply Fin.ext
    rw [AlgebraizedActionLawsR0137.next_iterate_val]
    simp only [zeroIndex, zero_add, Nat.mod_eq_of_lt j.isLt]
  have hij : (next r hr)^[j.val] i = sumIndex (hr := hr) i j := by
    apply Fin.ext
    exact AlgebraizedActionLawsR0137.next_iterate_val j.val i
  have hh := mul_iterate k h3 M hM he s hs G hG rot scal inv ha j.val i a b
  rw [hj, hij, point_eq k h3 M hM i a p hp, point_eq k h3 M hM j b q hq,
    point_eq k h3 M hM _ _ z hz] at hh
  exact hh

#print axioms marked_point_addition
end ArithmeticThetaMarkedGroupLawR0146
