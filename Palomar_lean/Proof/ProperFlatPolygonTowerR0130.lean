module

public import FiniteStageCompletionComparisonR0129
public import FiniteStageAdjacentR0129
public import InfinitesimalPolygonAtlasR0129
public import InfinitesimalPolygonProperR0129
public import InfinitesimalPolygonFlatR0129
public import PolygonProvidersRecoveryR0130
public import PolygonThickeningRecoveryR0130

@[expose] public section

/-! Assembly of the actual infinitesimal polygon tower from its geometric providers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaInfinitesimalPolygonR0129
namespace TowerAssemblyR0130
open CategoryTheory AlgebraicGeometry

variable (k : Type u) [Field k] [CharZero k]

omit [CharZero k] in
@[simp] lemma tower_chartReduction_id (n : ℕ) :
    chartReduction k n n (le_refl n) = 𝟙 (specA k n) := by
  unfold chartReduction specA
  rw [← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

omit [CharZero k] in
lemma tower_chartReduction_comp (n N P : ℕ) (h : n ≤ N) (h' : N ≤ P) :
    chartReduction k n N h ≫ chartReduction k N P h' =
      chartReduction k n P (le_trans h h') := by
  simp only [chartReduction, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- Choices of actual finite atlases acquire canonical transition laws because
the prescribed chart reductions determine every global morphism. -/
def assembledTower (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) : Tower k r hr := by
  let E := fun n => (finite_stage_adjacent k n).exists.choose
  have hE : ∀ n, IsAdjacent k n (E n) :=
    fun n => (finite_stage_adjacent k n).exists.choose_spec
  let D := fun n => Classical.choice (infinitesimal_polygon_atlas k r hr h3 n (E n) (hE n))
  let f := fun n N h =>
    (polygon_thickening_transition k r hr h3 n N h (E n) (E N) (hE n) (hE N)
      (D n) (D N)).exists.choose
  have hf : ∀ n N h, IsReduction k r n N hr h (D n) (D N) (f n N h) :=
    fun n N h =>
      (polygon_thickening_transition k r hr h3 n N h (E n) (E N) (hE n) (hE N)
        (D n) (D N)).exists.choose_spec.1
  refine {
    overlap := E
    overlap_spec := hE
    atlas := D
    transition := f
    transition_spec := hf
    identity := ?_
    composition := ?_ }
  · intro n
    apply (D n).hom_ext
    intro j
    rw [(hf n n (le_refl n)).2 j, tower_chartReduction_id, Category.id_comp,
      Category.comp_id]
  · intro n N P h h'
    apply (D n).hom_ext
    intro j
    rw [← Category.assoc, (hf n N h).2 j, Category.assoc, (hf N P h').2 j,
      ← Category.assoc, tower_chartReduction_comp, (hf n P (le_trans h h')).2 j]

/-- All transitions in the assembled tower are the actual base-change closed immersions. -/
theorem assembledTower_transition_geometry (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (n N : ℕ) (h : n ≤ N) :
    IsClosedImmersion ((assembledTower k r hr h3).transition n N h) ∧
      IsPullback ((assembledTower k r hr h3).transition n N h)
        ((assembledTower k r hr h3).atlas n).p ((assembledTower k r hr h3).atlas N).p
        (baseReduction k n N h) := by
  exact (polygon_thickening_transition k r hr h3 n N h _ _
    ((assembledTower k r hr h3).overlap_spec n)
    ((assembledTower k r hr h3).overlap_spec N)
    ((assembledTower k r hr h3).atlas n)
    ((assembledTower k r hr h3).atlas N)).exists.choose_spec.2

theorem assembledTower_flat (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (n : ℕ) :
    Flat ((assembledTower k r hr h3).atlas n).p :=
  infinitesimal_polygon_flat k r hr h3 n _
    ((assembledTower k r hr h3).overlap_spec n) ((assembledTower k r hr h3).atlas n)


/-- Properness applies to the actual structural map at every stage. -/
theorem assembledTower_proper (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (n : ℕ) :
    IsProper ((assembledTower k r hr h3).atlas n).p :=
  infinitesimal_polygon_proper k r hr h3 n _
    ((assembledTower k r hr h3).overlap_spec n) ((assembledTower k r hr h3).atlas n)

end TowerAssemblyR0130

/-- One compatible tower of proper flat polygons, with all base changes and
completion comparisons. No stage or coefficient field is bounded. -/
theorem proper_flat_polygon_tower :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r → ∃ T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr, (∀ n : ℕ, AlgebraicGeometry.IsProper (T.atlas n).p ∧ AlgebraicGeometry.Flat (T.atlas n).p) ∧ (∀ (n N : ℕ) (h : n ≤ N), AlgebraicGeometry.IsClosedImmersion (T.transition n N h) ∧ CategoryTheory.IsPullback (T.transition n N h) (T.atlas n).p (T.atlas N).p (ArithmeticThetaInfinitesimalPolygonR0129.baseReduction k n N h)) ∧ (∀ n : ℕ, ∃ (e : ArithmeticThetaInfinitesimalPolygonR0129.HatA k n ≃+* ArithmeticThetaInfinitesimalPolygonR0129.A k n) (o : ∀ side : Bool, ArithmeticThetaInfinitesimalPolygonR0129.HatB k n side ≃+* ArithmeticThetaInfinitesimalPolygonR0129.B k n side), ArithmeticThetaInfinitesimalPolygonR0129.CompletionComparison k n e o) := by
  intro k _ _ r hr h3
  refine ⟨TowerAssemblyR0130.assembledTower k r hr h3, ?_, ?_, ?_⟩
  · intro n
    exact ⟨TowerAssemblyR0130.assembledTower_proper k r hr h3 n,
      TowerAssemblyR0130.assembledTower_flat k r hr h3 n⟩
  · exact TowerAssemblyR0130.assembledTower_transition_geometry k r hr h3
  · exact finite_stage_completion_comparison k

end ArithmeticThetaInfinitesimalPolygonR0129
