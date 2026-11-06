module

public import RatioRegularityDefinitionsR0067

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Constancy on the concrete completed cyclic node charts. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w
namespace ArithmeticThetaCyclicConstantsR0088

/-- Algebraic lifting from the reduced equalizer. The section selects the scalar;
separatedness replaces any choice of a limiting sequence of scalars. -/
private theorem lift_constants
    {B : Type u} {A : Type v} {ι : Type w}
    [CommRing B] [CommRing A] (base : B →+* A) (σ : A →+* B)
    (hσ : ∀ b, σ (base b) = b) (t : B) (i₀ : ι)
    (P : (ι → A) → Prop)
    (hsub : ∀ a, P a → ∀ b, P (fun i => a i - base b))
    (hdiv : ∀ a, P (fun i => base t * a i) → P a)
    (hred : ∀ a, P a → ∃ b, ∀ i, base t ∣ a i - base b)
    (hsep : ∀ z : A, (∀ n : ℕ, (base t)^n ∣ z) → z = 0) :
    ∀ a, P a → ∃! b, ∀ i, base b = a i := by
  have step : ∀ n (a : ι → A), P a → ∀ i,
      (base t)^n ∣ a i - base (σ (a i₀)) := by
    intro n
    induction n with
    | zero => intros; simp
    | succ n ih =>
      intro a ha i
      obtain ⟨b, hb⟩ := hred a ha
      choose d hd using hb
      have had : ∀ i, a i = base b + base t * d i := by
        intro i
        linear_combination hd i
      have hdP : P d := by
        apply hdiv
        have he : (fun i => base t * d i) = (fun i => a i - base b) := by
          funext i
          exact (hd i).symm
        rw [he]
        exact hsub a ha b
      obtain ⟨z, hz⟩ := ih d hdP i
      refine ⟨z, ?_⟩
      rw [had i, had i₀, map_add, map_mul, hσ, hσ, map_add, map_mul]
      rw [pow_succ]
      linear_combination base t * hz
  intro a ha
  have he : ∀ i, base (σ (a i₀)) = a i := by
    intro i
    exact (sub_eq_zero.mp (hsep _ (fun n => step n a ha i))).symm
  refine ⟨σ (a i₀), he, ?_⟩
  intro b hb
  rw [← hb i₀, hσ]

namespace Reduced
open ArithmeticThetaNodeCharts
variable (k : Type u) [Field k] [CharZero k]

private def branch (side : Bool) : Node k →+* LaurentPolynomial k :=
  Ideal.Quotient.lift (relationIdeal k)
    (MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp PowerSeries.constantCoeff)
      (fun i => if side then (if i = 0 then LaurentPolynomial.T 1 else 0)
        else (if i = 0 then 0 else LaurentPolynomial.T (-1)))) (by
    change relationIdeal k ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    cases side <;> simp [relation, parameter])

private lemma branch_base (side : Bool) (c : PowerSeries k) :
    branch k side (algebraMap (PowerSeries k) (Node k) c) =
      LaurentPolynomial.C (PowerSeries.constantCoeff c) := by
  change (MvPolynomial.eval₂Hom _ _) (MvPolynomial.C c) = _
  simp

private lemma branch_x (side : Bool) :
    branch k side (x k) = if side then LaurentPolynomial.T 1 else 0 := by
  cases side <;> simp [branch, x, quotientMap]

private lemma branch_y (side : Bool) :
    branch k side (y k) = if side then 0 else LaurentPolynomial.T (-1) := by
  cases side <;> simp [branch, y, quotientMap]

private abbrev allowed (side : Bool) (i : ℤ) : Prop :=
  if side then 0 ≤ i else i ≤ 0

private lemma branch_normal (side : Bool) (i : ℤ) :
    branch k side (normalMonomial k i) =
      if allowed side i then LaurentPolynomial.T i else 0 := by
  by_cases hi : 0 ≤ i
  · rw [normalMonomial, if_pos hi, map_pow, branch_x]
    cases side
    · by_cases hz : i = 0
      · subst i; simp [allowed]
      · have hn : i.toNat ≠ 0 := by omega
        simp [allowed, show ¬i ≤ 0 by omega, hn]
    · simp [allowed, hi, LaurentPolynomial.T_pow, Int.toNat_of_nonneg hi]
  · rw [normalMonomial, if_neg hi, map_pow, branch_y]
    have hn : (-i).toNat ≠ 0 := by omega
    cases side
    · simp [allowed, show i ≤ 0 by omega, LaurentPolynomial.T_pow,
        Int.toNat_of_nonneg (show 0 ≤ -i by omega)]
    · simp [allowed, hi, hn]

private def basis : Module.Basis ℤ (PowerSeries k) (Node k) :=
  Classical.choose (node_free_basis k)

private lemma basis_apply (i : ℤ) : basis k i = normalMonomial k i :=
  Classical.choose_spec (node_free_basis k) i

private lemma branch_coeff (side : Bool) (z : Node k) (j : ℤ) :
    (branch k side z).coeff j =
      if allowed side j then PowerSeries.constantCoeff (basis k |>.repr z j) else 0 := by
  classical
  conv_lhs => rw [← (basis k).linearCombination_repr z]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, Algebra.smul_def, map_mul, branch_base, basis_apply,
    branch_normal, mul_ite, mul_zero, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hcoeff (h : Prop) [Decidable h] (p q : LaurentPolynomial k) :
      (if h then p else q).coeff j = (if h then p.coeff j else q.coeff j) := by
    split_ifs <;> rfl
  simp only [hcoeff, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_zero, Finsupp.single_apply, Finsupp.zero_apply]
  rw [Finset.sum_congr rfl (fun i hi => show
    (if allowed side i then (if i = j then
      PowerSeries.constantCoeff ((basis k).repr z i) else 0) else 0) =
    (if i = j then (if allowed side j then
      PowerSeries.constantCoeff ((basis k).repr z j) else 0) else 0) by
        by_cases h : i = j <;> simp [h])]
  simp only [Finset.sum_ite_eq']
  split_ifs with hj hs hs
  · rfl
  · rfl
  · have hz := Finsupp.notMem_support_iff.mp hj
    simp [hz]
  · rfl


private lemma parameter_dvd_of_coeff_zero (z : Node k)
    (hz : ∀ i, PowerSeries.constantCoeff ((basis k).repr z i) = 0) : t k ∣ z := by
  classical
  rw [← (basis k).linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.dvd_sum
  intro i hi
  obtain ⟨c, hc⟩ := (PowerSeries.X_dvd_iff.mpr (hz i))
  refine ⟨c • basis k i, ?_⟩
  rw [hc]
  simp [Algebra.smul_def, t, parameter, mul_assoc]

private lemma repr_base (c : PowerSeries k) :
    (basis k).repr (algebraMap (PowerSeries k) (Node k) c) = Finsupp.single 0 c := by
  have h0 : basis k 0 = 1 := by simp [basis_apply, normalMonomial]
  have he : algebraMap (PowerSeries k) (Node k) c = c • basis k 0 := by
    rw [h0, Algebra.smul_def, mul_one]
  rw [he, map_smul, Module.Basis.repr_self]
  simp

private lemma parameter_dvd_sub (z : Node k)
    (hz : ∀ i, i ≠ 0 → PowerSeries.constantCoeff ((basis k).repr z i) = 0) :
    t k ∣ z - algebraMap (PowerSeries k) (Node k)
      (PowerSeries.C (PowerSeries.constantCoeff ((basis k).repr z 0))) := by
  apply parameter_dvd_of_coeff_zero
  intro i
  simp only [map_sub, repr_base, Finsupp.sub_apply]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [Finsupp.single_apply, hi, Ne.symm hi, hz i hi]

private lemma reduced_edge (z w : Node k) (h : branch k false z = branch k true w) :
    (∀ i : ℤ, i < 0 → PowerSeries.constantCoeff ((basis k).repr z i) = 0) ∧
    (∀ i : ℤ, 0 < i → PowerSeries.constantCoeff ((basis k).repr w i) = 0) ∧
    PowerSeries.constantCoeff ((basis k).repr z 0) =
      PowerSeries.constantCoeff ((basis k).repr w 0) := by
  have hc (i : ℤ) := congrArg (fun p : LaurentPolynomial k => p.coeff i) h
  simp only [branch_coeff, allowed, Bool.false_eq_true, if_false, if_true] at hc
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simpa [le_of_lt hi, not_le.mpr hi] using hc i
  · intro i hi
    have he : 0 = PowerSeries.constantCoeff ((basis k).repr w i) := by
      simpa [le_of_lt hi, not_le.mpr hi] using hc i
    exact he.symm
  · simpa using hc 0


private lemma next_surjective (r : ℕ) (hr : 0 < r) :
    Function.Surjective (ArithmeticThetaRatioRegularityR0067.nextIndex r hr) := by
  intro j
  by_cases hj : j.val = 0
  · refine ⟨⟨r - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [ArithmeticThetaRatioRegularityR0067.nextIndex,
      ArithmeticThetaIndexedOverlapsR0058.next, show r - 1 + 1 = r by omega, hj]
  · refine ⟨⟨j.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [ArithmeticThetaRatioRegularityR0067.nextIndex,
      ArithmeticThetaIndexedOverlapsR0058.next, show j.val - 1 + 1 = j.val by omega,
      Nat.mod_eq_of_lt j.isLt]

private lemma cycle_invariant {α : Type*} (r : ℕ) (hr : 0 < r)
    (f : Fin r → α)
    (hf : ∀ j, f j = f (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j)) :
    ∀ j, f j = f ⟨0, hr⟩ := by
  intro ⟨j, hj⟩
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j < r := by omega
    have he : ArithmeticThetaRatioRegularityR0067.nextIndex r hr ⟨j, hj'⟩ =
        ⟨j+1, hj⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hj
    rw [← he, ← hf]
    exact ih hj'

private lemma reduced_cycle (r : ℕ) (hr : 0 < r) (z : Fin r → Node k)
    (hz : ∀ j, branch k false (z j) =
      branch k true (z (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j))) :
    ∃ c : PowerSeries k, ∀ j, t k ∣ z j - algebraMap (PowerSeries k) (Node k) c := by
  let c := fun j => PowerSeries.constantCoeff ((basis k).repr (z j) 0)
  have hc : ∀ j, c j = c ⟨0, hr⟩ :=
    cycle_invariant r hr c (fun j => (reduced_edge k _ _ (hz j)).2.2)
  refine ⟨PowerSeries.C (c ⟨0, hr⟩), fun j => ?_⟩
  rw [← hc j]
  apply parameter_dvd_sub
  intro i hi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · exact (reduced_edge k _ _ (hz j)).1 i hneg
  · obtain ⟨p, hp⟩ := next_surjective r hr j
    simpa [hp] using (reduced_edge k _ _ (hz p)).2.1 i hpos


open ArithmeticThetaIndexedOverlapsR0058
open ArithmeticThetaAnnularGeometry.CompletedNodeSupport

private def openResidue (j : ℕ) :
    ArithmeticThetaIndexedOverlapsR0058.Open k j true →+* LaurentPolynomial k :=
  IsLocalization.Away.lift (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k true)
    (g := branch k true) (by
      simpa [ArithmeticThetaIndexedOverlapsR0058.nodeCoord, branch_x] using
        (LaurentPolynomial.isUnit_T (R := k) 1))

private lemma openResidue_node (j : ℕ) (z : ArithmeticThetaNodeCharts.Node k) :
    openResidue k j (algebraMap (ArithmeticThetaNodeCharts.Node k)
      (ArithmeticThetaIndexedOverlapsR0058.Open k j true) z) = branch k true z := by
  unfold openResidue
  exact RingHom.congr_fun (IsLocalization.Away.lift_comp
    (ArithmeticThetaIndexedOverlapsR0058.nodeCoord k true)
    (g := branch k true) (by
      simpa [ArithmeticThetaIndexedOverlapsR0058.nodeCoord, branch_x] using
        (LaurentPolynomial.isUnit_T (R := k) 1))) z

private lemma nodeEquiv_base (c : PowerSeries k) :
    nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c) =
      algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) c := by
  exact (Ideal.quotientEquivAlgOfEq (PowerSeries k) (show
    ArithmeticThetaScaledTateBridgeR0046.relationIdeal k 1 =
      ArithmeticThetaNodeCharts.relationIdeal k by
    simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
      ArithmeticThetaScaledTateBridgeR0046.relation,
      ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
      ArithmeticThetaNodeCharts.parameter])).commutes c

private lemma nodeEquiv_x :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1) =
      ArithmeticThetaNodeCharts.x k := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.x ArithmeticThetaNodeCharts.x
    ArithmeticThetaScaledTateBridgeR0046.quotientMap ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma nodeEquiv_y :
    nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1) =
      ArithmeticThetaNodeCharts.y k := by
  unfold nodeEquiv ArithmeticThetaScaledTateBridgeR0046.y ArithmeticThetaNodeCharts.y
    ArithmeticThetaScaledTateBridgeR0046.quotientMap ArithmeticThetaNodeCharts.quotientMap
  apply Ideal.quotientEquivAlgOfEq_mk
  simp [ArithmeticThetaScaledTateBridgeR0046.relationIdeal,
    ArithmeticThetaScaledTateBridgeR0046.relation,
    ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaNodeCharts.relationIdeal, ArithmeticThetaNodeCharts.relation,
    ArithmeticThetaNodeCharts.parameter]

private lemma openResidue_base (j : ℕ) (c : PowerSeries k) :
    openResidue k j (openBase k j true c) =
      LaurentPolynomial.C (PowerSeries.constantCoeff c) := by
  change openResidue k j (algebraMap _ _ (nodeEquiv k
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c))) = _
  rw [openResidue_node, nodeEquiv_base, branch_base]

private lemma openResidue_x (j : ℕ) :
    openResidue k j (ox k j true) = LaurentPolynomial.T 1 := by
  rw [ox, openResidue_node, branch_x]
  rfl

private lemma openResidue_inv (j : ℕ) :
    openResidue k j (↑((xUnit k j)⁻¹)) = LaurentPolynomial.T (-1) := by
  have hu : (xUnit k j : ArithmeticThetaIndexedOverlapsR0058.Open k j true) =
      ox k j true := IsUnit.unit_spec _
  apply (LaurentPolynomial.isUnit_T (R := k) 1).mul_right_cancel
  calc
    _ = openResidue k j ((↑((xUnit k j)⁻¹)) * (xUnit k j :
        ArithmeticThetaIndexedOverlapsR0058.Open k j true)) := by
      rw [map_mul, hu, openResidue_x]
    _ = 1 := by simp
    _ = _ := by rw [← LaurentPolynomial.T_add]; norm_num

private lemma openResidue_kills (j : ℕ) :
    openIdeal k j true ≤ RingHom.ker (openResidue k j) := by
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  change openResidue k j (openBase k j true PowerSeries.X) = 0
  rw [openResidue_base]
  simp

private def hatResidue (j : ℕ) :
    ArithmeticThetaIndexedOverlapsR0058.OpenHat k j true →+* LaurentPolynomial k :=
  residueExtension (openIdeal k j true) (openResidue k j) (openResidue_kills k j)

private lemma hatResidue_of (j : ℕ) (z : ArithmeticThetaIndexedOverlapsR0058.Open k j true) :
    hatResidue k j (completeOpen k j true z) = openResidue k j z :=
  residueExtension_of _ _ _ z

private lemma hatResidue_parameter (j : ℕ) :
    hatResidue k j (ArithmeticThetaGenericOverlapR0065.openParameter k j true) = 0 := by
  rw [ArithmeticThetaGenericOverlapR0065.openParameter, hatResidue_of]
  change openResidue k j (openBase k j true PowerSeries.X) = 0
  simp [openResidue_base]

private lemma residue_restriction (j : ℕ)
    (z : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    hatResidue k j (ArithmeticThetaCorrectedGammaR0061.restrict k j true
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z)) =
      branch k true (nodeEquiv k z) := by
  have hs := (Classical.choose_spec
    (completed_coordinate_restrictions k j true).exists).1
  rw [show ArithmeticThetaCorrectedGammaR0061.restrict k j true
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z) =
      completeOpen k j true (openMap k j true z) from RingHom.congr_fun hs z]
  rw [hatResidue_of]
  exact openResidue_node k j _

private lemma openResidue_adjacent (r j : ℕ) (hr : 0 < r) (hj : j < r) :
    (openResidue k (next r j)).comp ((adjacent k r j).toRingHom.comp
      (openMap k j false)) = (branch k false).comp (nodeEquiv k).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change openResidue k (next r j) (adjacent k r j (openBase k j false c)) =
      branch k false (nodeEquiv k (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c))
    rw [show adjacent k r j (openBase k j false c) = openBase k (next r j) true c
      from RingHom.congr_fun (indexed_adjacent_coordinates k r j hr hj).1 c]
    rw [openResidue_base, nodeEquiv_base, branch_base]
  · intro i
    fin_cases i
    · change openResidue k (next r j) (adjacent k r j
        (algebraMap _ _ (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1)))) =
        branch k false (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.x k 1))
      rw [nodeEquiv_x]
      change openResidue k (next r j) (adjacent k r j (ox k j false)) = _
      rw [(indexed_adjacent_coordinates k r j hr hj).2.2.1, map_mul]
      simp [ot, openResidue_base, branch_x]
    · change openResidue k (next r j) (adjacent k r j
        (algebraMap _ _ (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1)))) =
        branch k false (nodeEquiv k (ArithmeticThetaScaledTateBridgeR0046.y k 1))
      rw [nodeEquiv_y]
      change openResidue k (next r j) (adjacent k r j (oy k j false)) = _
      rw [(indexed_adjacent_coordinates k r j hr hj).2.1, openResidue_inv, branch_y]
      rfl

private lemma residue_overlap (r j : ℕ) (hr : 0 < r) (hj : j < r)
    (z : ArithmeticThetaAnnularTorsionPrereqR0053.Node k) :
    hatResidue k (next r j) (ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj
      (ArithmeticThetaCorrectedGammaR0061.restrict k j false
        (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z))) =
      branch k false (nodeEquiv k z) := by
  have hR := (Classical.choose_spec (completed_coordinate_restrictions k j false).exists).1
  have hE := (Classical.choose_spec (completed_indexed_adjacent k r j hr hj).exists).1
  rw [show ArithmeticThetaCorrectedGammaR0061.restrict k j false
      (ArithmeticThetaAnnularTorsionPrereqR0053.complete k z) =
      completeOpen k j false (openMap k j false z) from RingHom.congr_fun hR z]
  rw [show ArithmeticThetaCorrectedGammaR0061.overlap k r j hr hj
      (completeOpen k j false (openMap k j false z)) =
      completeOpen k (next r j) true (adjacent k r j (openMap k j false z))
      from RingHom.congr_fun hE (openMap k j false z)]
  rw [hatResidue_of]
  exact RingHom.congr_fun (openResidue_adjacent k r j hr hj) z


private lemma complete_parameter :
    ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      (ArithmeticThetaScaledTateBridgeR0046.t k 1) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
  simp [ArithmeticThetaAnnularTorsionPrereqR0053.complete,
    ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
    ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
    ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]

private lemma complete_base (c : PowerSeries k) :
    ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k c := rfl

private lemma completion_approx (a : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :
    ∃ z : ArithmeticThetaAnnularTorsionPrereqR0053.Node k,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∣
        a - ArithmeticThetaAnnularTorsionPrereqR0053.complete k z := by
  obtain ⟨z, hz⟩ := ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.completion_approx_one
    (ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1)
    (Submodule.fg_span_singleton _) a
  refine ⟨z, ?_⟩
  change a - ArithmeticThetaAnnularTorsionPrereqR0053.complete k z ∈
    Ideal.map (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)
      (Ideal.span {ArithmeticThetaScaledTateBridgeR0046.t k 1}) at hz
  simpa only [Ideal.map_span, Set.image_singleton, complete_parameter,
    Ideal.mem_span_singleton] using hz

private lemma map_eq_of_dvd {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (t a b : A) (ht : f t = 0) (h : t ∣ a - b) : f a = f b := by
  obtain ⟨c, hc⟩ := h
  have he := congrArg f hc
  simpa [map_sub, map_mul, ht, sub_eq_zero] using he

private lemma completed_reduced (r : ℕ) (hr : 0 < r)
    (a : Fin r → ArithmeticThetaAnnularTorsionPrereqR0053.Chart k)
    (ha : ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr a) :
    ∃ c : PowerSeries k, ∀ j, ArithmeticThetaAnnularTorsionPrereqR0053.tau k ∣
      a j - ArithmeticThetaAnnularTorsionPrereqR0053.base k c := by
  choose z hz using fun j => completion_approx k (a j)
  have hedges : ∀ j, branch k false (nodeEquiv k (z j)) =
      branch k true (nodeEquiv k (z (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j))) := by
    intro j
    let l : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k →+* LaurentPolynomial k :=
      (hatResidue k (next r j.val)).comp
        ((ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt).toRingHom.comp
          (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false))
    let q : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k →+* LaurentPolynomial k :=
      (hatResidue k (next r j.val)).comp
        (ArithmeticThetaCorrectedGammaR0061.restrict k (next r j.val) true)
    have hl : l (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = 0 := by
      dsimp [l]
      rw [ArithmeticThetaGenericOverlapR0065.restriction_parameter,
        ArithmeticThetaGenericOverlapR0065.overlap_openParameter, hatResidue_parameter]
    have hq : q (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) = 0 := by
      dsimp [q]
      rw [ArithmeticThetaGenericOverlapR0065.restriction_parameter, hatResidue_parameter]
    have hlz := map_eq_of_dvd l _ _ _ hl (hz j)
    have hqz := map_eq_of_dvd q _ _ _ hq
      (hz (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j))
    have he : l (a j) = q (a (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j)) :=
      congrArg (hatResidue k (next r j.val)) (ha j)
    calc
      _ = l (ArithmeticThetaAnnularTorsionPrereqR0053.complete k (z j)) :=
        (residue_overlap k r j.val hr j.isLt _).symm
      _ = l (a j) := hlz.symm
      _ = q (a (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j)) := he
      _ = q (ArithmeticThetaAnnularTorsionPrereqR0053.complete k
          (z (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j))) := hqz
      _ = _ := residue_restriction k (next r j.val) _
  obtain ⟨c, hc⟩ := reduced_cycle k r hr (fun j => nodeEquiv k (z j)) hedges
  refine ⟨c, fun j => ?_⟩
  let F := (ArithmeticThetaAnnularTorsionPrereqR0053.complete k).comp
    (nodeEquiv k).symm.toRingHom
  have hFt : F (ArithmeticThetaNodeCharts.t k) =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
    rw [← ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.node_equiv_t k]
    change ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      ((nodeEquiv k).symm (nodeEquiv k _)) = _
    rw [RingEquiv.symm_apply_apply, complete_parameter]
  have hFc : F (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k) c) =
      ArithmeticThetaAnnularTorsionPrereqR0053.base k c := by
    rw [← nodeEquiv_base k c]
    change ArithmeticThetaAnnularTorsionPrereqR0053.complete k
      ((nodeEquiv k).symm (nodeEquiv k _)) = _
    rw [RingEquiv.symm_apply_apply, complete_base]
  have hFz : F (nodeEquiv k (z j)) = ArithmeticThetaAnnularTorsionPrereqR0053.complete k (z j) := by
    simp [F]
  have hd := map_dvd F (hc j)
  rw [hFt, map_sub, hFc, hFz] at hd
  simpa using dvd_add (hz j) hd


private lemma restriction_base (j : ℕ) (side : Bool) (c : PowerSeries k) :
    ArithmeticThetaCorrectedGammaR0061.restrict k j side
      (ArithmeticThetaAnnularTorsionPrereqR0053.base k c) =
      completeOpen k j side (openBase k j side c) := by
  exact RingHom.congr_fun (Classical.choose_spec
    (completed_coordinate_restrictions k j side).exists).1
    (ArithmeticThetaAnnularTorsionPrereqR0053.nodeBase k c)

private lemma base_compatible (r : ℕ) (hr : 0 < r) (c : PowerSeries k) :
    ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr
      (fun _ => ArithmeticThetaAnnularTorsionPrereqR0053.base k c) := by
  intro j
  rw [restriction_base, restriction_base]
  have hE := (Classical.choose_spec (completed_indexed_adjacent k r j.val hr j.isLt).exists).1
  change ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
      (completeOpen k j.val false (openBase k j.val false c)) =
      completeOpen k (next r j.val) true (openBase k (next r j.val) true c)
  rw [show ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
      (completeOpen k j.val false (openBase k j.val false c)) =
      completeOpen k (next r j.val) true (adjacent k r j.val (openBase k j.val false c))
      from RingHom.congr_fun hE (openBase k j.val false c)]
  rw [show adjacent k r j.val (openBase k j.val false c) = openBase k (next r j.val) true c
      from RingHom.congr_fun (indexed_adjacent_coordinates k r j.val hr j.isLt).1 c]

private def scalarSection : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k →+* PowerSeries k :=
  Classical.choose (ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels
    k true 1 one_ne_zero).1.exists

private lemma scalarSection_base (c : PowerSeries k) :
    scalarSection k (ArithmeticThetaAnnularTorsionPrereqR0053.base k c) = c :=
  RingHom.congr_fun (Classical.choose_spec
    (ArithmeticThetaAnnularTorsionPrereqR0053.completed_section_kernels
      k true 1 one_ne_zero).1.exists).1 c

private lemma tau_ne_zero : ArithmeticThetaAnnularTorsionPrereqR0053.tau k ≠ 0 := by
  intro h
  have he := congrArg (scalarSection k) h
  change scalarSection k (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) = _ at he
  rw [scalarSection_base, map_zero] at he
  exact PowerSeries.X_ne_zero he

private lemma compatibility_div (r : ℕ) (hr : 0 < r)
    (a : Fin r → ArithmeticThetaAnnularTorsionPrereqR0053.Chart k)
    (ha : ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr
      (fun j => ArithmeticThetaAnnularTorsionPrereqR0053.tau k * a j)) :
    ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr a := by
  intro j
  letI := ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.open_hat_domain k (next r j.val) true
  have hne : ArithmeticThetaGenericOverlapR0065.openParameter k (next r j.val) true ≠ 0 := by
    intro h
    apply tau_ne_zero k
    apply ArithmeticThetaGenericOverlapR0065.FaithfulnessSupport.open_hat_restriction_injective
      k (next r j.val) true
    simpa [ArithmeticThetaGenericOverlapR0065.restriction_parameter] using h
  have he := ha j
  simp only [map_mul, ArithmeticThetaGenericOverlapR0065.restriction_parameter,
    ArithmeticThetaGenericOverlapR0065.overlap_openParameter] at he
  change
    ArithmeticThetaGenericOverlapR0065.openParameter k (next r j.val) true *
          (ArithmeticThetaCorrectedGammaR0061.overlap k r j.val hr j.isLt
            (ArithmeticThetaCorrectedGammaR0061.restrict k j.val false (a j))) =
        ArithmeticThetaGenericOverlapR0065.openParameter k (next r j.val) true *
          (ArithmeticThetaCorrectedGammaR0061.restrict k (next r j.val) true
            (a (ArithmeticThetaRatioRegularityR0067.nextIndex r hr j))) at he
  exact mul_left_cancel₀ hne he

private lemma chart_separated (a : ArithmeticThetaAnnularTorsionPrereqR0053.Chart k)
    (ha : ∀ n : ℕ, ArithmeticThetaAnnularTorsionPrereqR0053.tau k ^ n ∣ a) : a = 0 := by
  let I := ArithmeticThetaScaledTateBridgeR0046.nodeIdeal k 1
  let J := I.map (ArithmeticThetaAnnularTorsionPrereqR0053.complete k)
  letI : IsAdicComplete J (ArithmeticThetaAnnularTorsionPrereqR0053.Chart k) :=
    AdicCompletion.isAdicComplete_self I (Submodule.fg_span_singleton _)
  apply IsHausdorff.haus' (I := J)
  intro n
  apply SModEq.zero.mpr
  simpa [J, I, ArithmeticThetaScaledTateBridgeR0046.nodeIdeal,
    Ideal.map_span, complete_parameter, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using ha n

end Reduced

/-- The equalizer on the actual completed thickness-one cyclic annular charts
is precisely the image of the power-series base, for every positive cycle length. -/
theorem cyclic_completed_family_constant :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r)
      (a : Fin r → ArithmeticThetaRatioRegularityR0067.Chart k),
      ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr a →
      ∃! c : PowerSeries k, ∀ j : Fin r,
        ArithmeticThetaAnnularTorsionPrereqR0053.base k c = a j := by
  intro k _ _ r hr a ha
  apply lift_constants (ArithmeticThetaAnnularTorsionPrereqR0053.base k)
    (Reduced.scalarSection k) (Reduced.scalarSection_base k) PowerSeries.X
    (⟨0, hr⟩ : Fin r) (ArithmeticThetaRatioRegularityR0067.CompletedCompatible k r hr)
    ?_ (Reduced.compatibility_div k r hr) (Reduced.completed_reduced k r hr)
    (Reduced.chart_separated k) a ha
  intro b hb c j
  simpa only [map_sub, hb j, Reduced.base_compatible k r hr c j]
    using sub_congr (hb j) (Reduced.base_compatible k r hr c j)

end ArithmeticThetaCyclicConstantsR0088
