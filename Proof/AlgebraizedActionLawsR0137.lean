module

public import AlgebraizedAnnularActionsR0137
public import ProperTowerAutomorphismEffectivityR0137
public import TowerInversionR0137
public import TowerScalarTranslationR0137
public import TowerPeriodRotationR0137

@[expose] public section

/-! The eight unlifted action relations on the whole proper model.
Annular restrictions determine the morphisms by proper adic faithfulness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
namespace AlgebraizedActionLawsR0137
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open TowerScalarTranslation TowerInversionR0137
variable (k : Type u) [Field k] [CharZero k]

lemma ringMap_one (n : ℕ) : ringMap k n 1 = RingHom.id _ := by
  apply point_ext
  · ext b; simp
  · simp
  · simp

lemma ringMap_mul (n : ℕ) (a b : kˣ) :
    (ringMap k n a).comp (ringMap k n b) = ringMap k n (a*b) := by
  apply point_ext
  · ext z; simp
  · simp [RingHom.comp_apply, scalar_mul, mul_left_comm, mul_assoc]
  · simp [RingHom.comp_apply, scalar_mul, mul_left_comm, mul_assoc]

lemma chartMap_one (n : ℕ) : chartMap k n 1 = 𝟙 _ := by
  rw [chartMap, ringMap_one]
  exact Spec.map_id _

lemma chartMap_mul (n : ℕ) (a b : kˣ) :
    chartMap k n a ≫ chartMap k n b = chartMap k n (a*b) := by
  rw [chartMap, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ringMap_mul]
  rfl

lemma swap_scalar (n : ℕ) (b : k) : swap k n (scalar k n b) = scalar k n b :=
  swap_base_apply ..

lemma ringMap_conjugate (n : ℕ) (a : kˣ) :
    (swap k n).comp ((ringMap k n a).comp (swap k n)) = ringMap k n a⁻¹ := by
  apply point_ext
  · ext z; simp
  · simp [RingHom.comp_apply, swap_scalar]
  · simp [RingHom.comp_apply, swap_scalar]

lemma chartMap_conjugate (n : ℕ) (a : kˣ) :
    chartSwap k n ≫ chartMap k n a ≫ chartSwap k n = chartMap k n a⁻¹ := by
  simp only [chartSwap, chartMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [ringMap_conjugate]

variable {k} {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def modelChart (M : Model k T) (n : ℕ) (i : Fin r) : specA k n ⟶ M.X :=
  (T.atlas n).chart i ≫ M.inclusion n

/-- Testing on every chart at every thickness determines a map on the model. -/
lemma chart_ext (M : Model k T) (hM : IsModel k T M)
    {f g : M.X ⟶ M.X} (hf : f ≫ M.p = M.p) (hg : g ≫ M.p = M.p)
    (h : ∀ n i, modelChart M n i ≫ f = modelChart M n i ≫ g) : f = g := by
  let : IsProper M.p := hM.1
  apply ProperTowerAutomorphismEffectivityR0137.hom_ext k M hM M.p hf hg
  intro n
  apply (T.atlas n).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans ((h n i).trans (Category.assoc _ _ _))

lemma modelAction_over (M : Model k T) {p : Fin r → Fin r} {a : kˣ}
    {b : Bool} {f : M.X ≅ M.X} (h : ModelAction k M p a b f) : f.hom ≫ M.p = M.p := by
  obtain ⟨g, hg, hf⟩ := h
  exact hf.1

lemma chart_rotation (M : Model k T) {f : M.X ≅ M.X}
    (h : ModelAction k M (next r hr) 1 false f) (n : ℕ) (i : Fin r) :
    modelChart M n i ≫ f.hom = modelChart M n (next r hr i) := by
  obtain ⟨g, hg, hf⟩ := h
  obtain ⟨_, q, hq, hc⟩ := hg.2 n
  rw [TowerPeriodRotationR0137.coordinate_unique k n q hq] at hc
  simpa [modelChart, Category.assoc, hf.2 n] using congrArg (fun z => z ≫ M.inclusion n) (hc i)

lemma chart_scalar (M : Model k T) {a : kˣ} {f : M.X ≅ M.X}
    (h : ModelAction k M id a false f) (n : ℕ) (i : Fin r) :
    modelChart M n i ≫ f.hom = chartMap k n a ≫ modelChart M n i := by
  obtain ⟨g, hg, hf⟩ := h
  obtain ⟨_, q, hq, hc⟩ := hg.2 n
  rw [coordinates_unique k n a q hq] at hc
  simpa [modelChart, Category.assoc, hf.2 n, chartMap] using
    congrArg (fun z => z ≫ M.inclusion n) (hc i)

lemma chart_inversion (M : Model k T) {f : M.X ≅ M.X}
    (h : ModelAction k M Fin.rev 1 true f) (n : ℕ) (i : Fin r) :
    modelChart M n i ≫ f.hom = chartSwap k n ≫ modelChart M n (Fin.rev i) := by
  obtain ⟨g, hg, hf⟩ := h
  obtain ⟨_, q, hq, hc⟩ := hg.2 n
  rw [swap_unique k n q hq] at hc
  simpa [modelChart, Category.assoc, hf.2 n, chartSwap] using
    congrArg (fun z => z ≫ M.inclusion n) (hc i)

lemma iterate_over {X S : Scheme.{u}} (p : X ⟶ S) (f : X ⟶ X)
    (hf : f ≫ p = p) (m : ℕ) : iterateHom f m ≫ p = p := by
  induction m with
  | zero => simp [iterateHom]
  | succ m ih => simp [iterateHom, Category.assoc, hf, ih]

lemma chart_iterate_rotation (M : Model k T) {f : M.X ≅ M.X}
    (h : ModelAction k M (next r hr) 1 false f) (n m : ℕ) (i : Fin r) :
    modelChart M n i ≫ iterateHom f.hom m = modelChart M n ((next r hr)^[m] i) := by
  induction m with
  | zero => simp [iterateHom]
  | succ m ih =>
    rw [iterateHom, ← Category.assoc, ih, chart_rotation M h]
    rw [Function.iterate_succ_apply']

lemma next_iterate_val (m : ℕ) (i : Fin r) :
    ((next r hr)^[m] i).val = (i.val + m) % r := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    simp only [next, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

lemma next_period (i : Fin r) : (next r hr)^[r] i = i := by
  apply Fin.ext
  rw [next_iterate_val]
  simp [Nat.mod_eq_of_lt i.isLt]

/-- The action laws hold for any actions satisfying the frozen annular predicates. -/
lemma laws (M : Model k T) (hM : IsModel k T M)
    (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X)
    (h : Actions k M rot scal inv) : ActionLaws k M rot scal inv := by
  obtain ⟨hR, hS, hI⟩ := h
  have hRp := modelAction_over M hR
  have hSp := fun a => modelAction_over M (hS a)
  have hIp := modelAction_over M hI
  have hcR := chart_rotation M hR
  have hcS := fun a => chart_scalar M (hS a)
  have hcI := chart_inversion M hI
  have h1 : (scal 1).hom = 𝟙 M.X := by
    apply chart_ext M hM (hSp 1) (Category.id_comp _)
    intro n i
    rw [hcS, chartMap_one, Category.id_comp, Category.comp_id]
  have hmul : ∀ a b : kˣ, (scal (a*b)).hom = (scal a).hom ≫ (scal b).hom := by
    intro a b
    apply chart_ext M hM (hSp (a*b)) (by rw [Category.assoc, hSp, hSp])
    intro n i
    rw [hcS, ← Category.assoc, hcS, Category.assoc, hcS,
      ← Category.assoc, chartMap_mul]
  refine ⟨?_, h1, hmul, ?_, ?_, ?_, ?_, ?_⟩
  · apply chart_ext M hM (iterate_over M.p rot.hom hRp r) (Category.id_comp _)
    intro n i
    rw [chart_iterate_rotation M hR, next_period, Category.comp_id]
  · apply chart_ext M hM (by rw [Category.assoc, hIp, hIp]) (Category.id_comp _)
    intro n i
    rw [← Category.assoc, hcI, Category.assoc, hcI, Fin.rev_rev,
      ← Category.assoc, chartSwap_sq, Category.id_comp, Category.comp_id]
  · intro a
    apply chart_ext M hM (by rw [Category.assoc, hSp, hRp])
      (by rw [Category.assoc, hRp, hSp])
    intro n i
    rw [← Category.assoc, hcR, hcS, ← Category.assoc, hcS, Category.assoc, hcR]
  · apply (cancel_mono rot.hom).mp
    rw [rot.inv_hom_id]
    apply chart_ext M hM
      (by simp only [Category.assoc, hRp, hIp]) (Category.id_comp _)
    intro n i
    simp only [Category.assoc]
    rw [← Category.assoc, hcI, Category.assoc, ← Category.assoc (modelChart _ _ _), hcR,
      ← Category.assoc (modelChart _ _ _), hcI, Category.assoc, hcR]
    rw [TowerInversionR0137.rev_next, Fin.rev_rev, ← Category.assoc, chartSwap_sq]
    simp
  · intro a
    apply chart_ext M hM (by simp only [Category.assoc, hIp, hSp]) (hSp a⁻¹)
    intro n i
    rw [← Category.assoc, hcI, Category.assoc,
      ← Category.assoc (modelChart _ _ _), hcS, Category.assoc, hcI, Fin.rev_rev, hcS]
    simp only [← Category.assoc]
    rw [Category.assoc (chartSwap k n) (chartMap k n a), chartMap_conjugate]
  · intro c a ha
    have hp : ∀ m, iterateHom (scal a).hom m = (scal (a^m)).hom := by
      intro m
      induction m with
      | zero => simpa [iterateHom] using h1.symm
      | succ m ih => rw [iterateHom, ih, pow_succ, hmul]
    rw [hp, ha, h1]

end AlgebraizedActionLawsR0137
open CategoryTheory

theorem algebraized_action_laws :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∀ (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X),
    ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv →
      ArithmeticThetaModelSymmetriesR0137.ActionLaws k M rot scal inv := by
  intro k _ _ r hr _ T M hM rot scal inv h
  exact AlgebraizedActionLawsR0137.laws M hM rot scal inv h

end ArithmeticThetaModelSymmetriesR0137

#print axioms ArithmeticThetaModelSymmetriesR0137.algebraized_action_laws
