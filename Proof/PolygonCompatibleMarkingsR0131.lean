module

public import MarkedCartierEquationR0131
public import PolygonSmoothMarkedSectionsR0131
public import PolygonCohomologyDefinitionsR0131

@[expose] public section

/-! Disjoint component markings and their compatibility with every tower reduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

namespace CompatibleMarkingsR0131
variable (k : Type u) [Field k] [CharZero k]

lemma point_in_right (n : ℕ) (a : kˣ) (p : specR k n) :
    Spec.map (CommRingCat.ofHom (markedPoint k n a)) p ∈ Set.range (rightLeg k n) := by
  have hu : IsUnit (markedPoint k n a (if true then coordX k n else coordY k n)) := by
    simp [markedPoint]
  let s : specR k n ⟶ specB k n true :=
    Spec.map (CommRingCat.ofHom (openPoint (markedPoint k n a) true hu))
  have hs : s ≫ rightLeg k n = Spec.map (CommRingCat.ofHom (markedPoint k n a)) := by
    dsimp only [s, rightLeg, specR, specA, specB]
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (openPoint_restriction (markedPoint k n a) true hu)
  exact ⟨s p, congrArg (fun f : specR k n ⟶ specA k n => f p) hs⟩

lemma disjoint_markings (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E)
    (i j : Fin r) (hij : i ≠ j) (a b : kˣ) :
    Disjoint (Set.range (markedSection k r n hr D i a))
      (Set.range (markedSection k r n hr D j b)) := by
  have hadj (i j : Fin r) (hij : next r hr i = j) (a b : kˣ)
      (p q : specR k n)
      (heq : markedSection k r n hr D i a p = markedSection k r n hr D j b q) : False := by
    subst j
    change D.chart i (Spec.map (CommRingCat.ofHom (markedPoint k n a)) p) =
      D.chart (next r hr i) (Spec.map (CommRingCat.ofHom (markedPoint k n b)) q) at heq
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (D.adjacent i) _ _ heq
    exact Set.disjoint_left.mp (legs_disjoint k n E) ⟨z, hz⟩ (point_in_right k n a p)
  rw [Set.disjoint_left]
  rintro x ⟨p, rfl⟩ ⟨q, hq⟩
  by_cases hn : next r hr i = j
  · exact hadj i j hn a b p q hq.symm
  by_cases hp : next r hr j = i
  · exact hadj j i hp b a q p hq
  · exact Set.disjoint_left.mp (D.disjoint i j hij hn hp)
      ⟨_, rfl⟩ ⟨_, hq⟩

lemma point_reduction (n N : ℕ) (h : n ≤ N) (a : kˣ) :
    (markedPoint k n a).comp
        (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h) =
      (truncReduce (PowerSeries k) PowerSeries.X n N h).comp (markedPoint k N a) := by
  apply Ideal.Quotient.ringHom_ext
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, markedPoint, mkPoint, truncReduce, trunc]
  · intro j
    fin_cases j <;>
      simp [RingHom.comp_apply, markedPoint, mkPoint, truncReduce, trunc,
        markedUnit, parameter]

lemma section_reduction (r : ℕ) (hr : 0 < r) (T : Tower k r hr)
    (n N : ℕ) (h : n ≤ N) (i : Fin r) (a : kˣ) :
    markedSection k r n hr (T.atlas n) i a ≫ T.transition n N h =
      baseReduction k n N h ≫ markedSection k r N hr (T.atlas N) i a := by
  rw [markedSection, Category.assoc, (T.transition_spec n N h).2 i,
    ← Category.assoc, markedSection, ← Category.assoc]
  congr 1
  simp only [chartReduction, baseReduction, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (point_reduction k n N h a)

end CompatibleMarkingsR0131

/-- Markings in distinct cyclic positions are disjoint and commute with all reductions. -/
theorem polygon_compatible_disjoint_markings :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ T : Tower k r hr,
      (∀ (n : ℕ) (i j : Fin r), i ≠ j → ∀ (a b : kˣ),
        Disjoint (Set.range (markedSection k r n hr (T.atlas n) i a))
          (Set.range (markedSection k r n hr (T.atlas n) j b))) ∧
      (∀ (n N : ℕ) (h : n ≤ N) (i : Fin r) (a : kˣ),
        markedSection k r n hr (T.atlas n) i a ≫ T.transition n N h =
          baseReduction k n N h ≫ markedSection k r N hr (T.atlas N) i a) := by
  intro k _ _ r hr _ T
  exact ⟨fun n i j hij a b => CompatibleMarkingsR0131.disjoint_markings k r n hr
      (T.atlas n) i j hij a b,
    CompatibleMarkingsR0131.section_reduction k r hr T⟩

end ArithmeticThetaPolygonCohomologyR0131
