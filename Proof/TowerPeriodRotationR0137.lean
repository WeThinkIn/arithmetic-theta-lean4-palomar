module

public import ModelSymmetriesDefinitionsR0137

@[expose] public section

/-! Rotation of the entire infinitesimal polygon, constructed by gluing its charts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
namespace TowerPeriodRotationR0137
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]

omit [CharZero k] in
lemma scalar_one (n : ℕ) : scalar k n 1 = 1 := by
  simp [scalar]

omit [CharZero k] in
lemma coordinate_id (n : ℕ) : CoordinateMap k n 1 false (RingHom.id _) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> simp [scalar_one]

omit [CharZero k] in
/-- The base coefficients and the two node coordinates generate each quotient ring. -/
lemma coordinate_unique (n : ℕ) (f : A k n →+* A k n)
    (hf : CoordinateMap k n 1 false f) : f = RingHom.id _ := by
  have hx : f (chartX k n) = chartX k n := by simpa [scalar_one] using hf.2.1
  have hy : f (chartY k n) = chartY k n := by simpa [scalar_one] using hf.2.2
  let q := (trunc (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n).comp
    (ArithmeticThetaNodeCharts.quotientMap k)
  have hq : f.comp q = q := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact hf.1 (trunc (PowerSeries k) PowerSeries.X n a)
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg (fun g : ArithmeticThetaNodeCharts.PolynomialChart k →+* A k n => g a) hq

lemma next_eq_rotate (r : ℕ) (hr : 0 < r) (i : Fin r) :
    next r hr i = finRotate r i := by
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  apply Fin.ext
  simp [next, finRotate_apply, Fin.val_add, Nat.add_mod]

variable {k} {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}

/-- Every permutation commuting with successor acts by unchanged chart coordinates. -/
def permHom (D : Atlas k r n hr E) (e : Equiv.Perm (Fin r))
    (he : ∀ i, e (next r hr i) = next r hr (e i)) : D.X ⟶ D.X :=
  D.desc (fun i => D.chart (e i)) (by
    intro i
    rw [he]
    exact (D.adjacent (e i)).w)

@[reassoc (attr := simp)]
lemma chart_permHom (D : Atlas k r n hr E) (e : Equiv.Perm (Fin r))
    (he : ∀ i, e (next r hr i) = next r hr (e i)) (i : Fin r) :
    D.chart i ≫ permHom D e he = D.chart (e i) := D.chart_desc _ _ i

lemma symm_commutes (e : Equiv.Perm (Fin r))
    (he : ∀ i, e (next r hr i) = next r hr (e i)) (i : Fin r) :
    e.symm (next r hr i) = next r hr (e.symm i) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply, he]

/-- Gluing the inverse permutation gives the actual inverse scheme morphism. -/
def permIso (D : Atlas k r n hr E) (e : Equiv.Perm (Fin r))
    (he : ∀ i, e (next r hr i) = next r hr (e i)) : D.X ≅ D.X where
  hom := permHom D e he
  inv := permHom D e.symm (symm_commutes e he)
  hom_inv_id := by
    apply D.hom_ext
    intro i
    simp
  inv_hom_id := by
    apply D.hom_ext
    intro i
    simp

def rotation (D : Atlas k r n hr E) : D.X ≅ D.X :=
  permIso D (finRotate r) (by intro i; simp only [next_eq_rotate])

@[reassoc (attr := simp)]
lemma chart_rotation (D : Atlas k r n hr E) (i : Fin r) :
    D.chart i ≫ (rotation D).hom = D.chart (next r hr i) := by
  dsimp only [rotation, permIso]
  rw [chart_permHom, next_eq_rotate]

lemma rotation_over (D : Atlas k r n hr E) : (rotation D).hom ≫ D.p = D.p := by
  apply D.hom_ext
  intro i
  rw [chart_rotation_assoc, D.chart_over, D.chart_over]

lemma rotation_stage (D : Atlas k r n hr E) :
    StageAction k D (next r hr) 1 false (rotation D) := by
  refine ⟨rotation_over D, RingHom.id _, coordinate_id k n, ?_⟩
  intro i
  simp [chart_rotation]

lemma stage_unique (D : Atlas k r n hr E) (g : D.X ≅ D.X)
    (hg : StageAction k D (next r hr) 1 false g) : g = rotation D := by
  obtain ⟨_, f, hf, hc⟩ := hg
  have hfid := coordinate_unique k n f hf
  subst f
  apply CategoryTheory.Iso.ext
  apply D.hom_ext
  intro i
  simpa using (hc i).trans (by simp)

lemma rotation_compatible (T : Tower k r hr) :
    CompatibleAutos k T (fun n => rotation (T.atlas n)) := by
  refine ⟨fun n => rotation_over (T.atlas n), ?_⟩
  intro n N h
  apply (T.atlas n).hom_ext
  intro i
  rw [← Category.assoc, (T.transition_spec n N h).2 i, Category.assoc,
    chart_rotation, chart_rotation_assoc, (T.transition_spec n N h).2]

end TowerPeriodRotationR0137
open CategoryTheory ArithmeticThetaInfinitesimalPolygonR0129

/-- The unique compatible geometric period rotation, at every nilpotent thickness. -/
theorem tower_period_rotation :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
      ∃! g : ∀ n : ℕ, (T.atlas n).X ≅ (T.atlas n).X,
        ArithmeticThetaModelSymmetriesR0137.TowerAction k T
          (ArithmeticThetaInfinitesimalPolygonR0129.next r hr) 1 false g := by
  intro k _ _ r hr _ T
  refine ⟨fun n => TowerPeriodRotationR0137.rotation (T.atlas n),
    ⟨TowerPeriodRotationR0137.rotation_compatible T,
      fun n => TowerPeriodRotationR0137.rotation_stage (T.atlas n)⟩, ?_⟩
  intro g hg
  funext n
  exact TowerPeriodRotationR0137.stage_unique (T.atlas n) (g n) (hg.2 n)

end ArithmeticThetaModelSymmetriesR0137
