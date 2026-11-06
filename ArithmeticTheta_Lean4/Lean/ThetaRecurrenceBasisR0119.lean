import FormalSchrodingerDefinitionsR0119

/-! The literal theta residue vectors form a basis of the full bilateral
recurrence space over the actual Laurent-series field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119

variable (k : Type u) [Field k]

lemma recurrence_monomial_mul (a b : ℤ) :
    monomial k a * monomial k b = monomial k (a + b) := by
  simp [monomial, HahnSeries.single_mul_single]

@[simp] lemma recurrence_monomial_zero : monomial k 0 = 1 := by
  simp [monomial]

lemma theta_mem_solutions (m : ℕ) (ν : Fin m) :
    theta k m ν ∈ Solutions k m := by
  intro r
  have hmod : Int.ModEq (m : ℤ) (r + m) (ν.val : ℤ) ↔
      Int.ModEq (m : ℤ) r (ν.val : ℤ) := by simp [Int.ModEq]
  change (if Int.ModEq (m : ℤ) (r + m) (ν.val : ℤ) then _ else _) = _
  simp only [theta, hmod]
  split_ifs with h
  · rw [recurrence_monomial_mul]
    congr 1
    ring
  · simp

lemma synth_mem_solutions (m : ℕ) (v : Fin m → K k) :
    synth k m v ∈ Solutions k m := by
  exact Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ (v ν) (theta_mem_solutions k m ν)

lemma residue_fin_unique {m : ℕ} (ν μ : Fin m) :
    Int.ModEq (m : ℤ) (ν.val : ℤ) (μ.val : ℤ) ↔ ν = μ := by
  rw [Int.ModEq, Int.emod_eq_of_lt (by omega) (by exact_mod_cast ν.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast μ.isLt)]
  simp only [Int.natCast_inj, Fin.ext_iff]

lemma synth_apply_of_modeq (m : ℕ) (v : Fin m → K k) (r : ℤ)
    (ν : Fin m) (h : Int.ModEq (m : ℤ) r (ν.val : ℤ)) :
    synth k m v r = v ν * monomial k (r^2) := by
  classical
  have hiff (μ : Fin m) : Int.ModEq (m : ℤ) r (μ.val : ℤ) ↔ μ = ν := by
    constructor
    · intro hμ
      exact (residue_fin_unique μ ν).mp (hμ.symm.trans h)
    · rintro rfl
      exact h
  simp [synth, theta, Finset.sum_apply, hiff]

lemma normalized_solution_periodic (m : ℕ) (f : Solutions k m) :
    Function.Periodic (fun r : ℤ => monomial k (-(r^2)) * f.val r) (m : ℤ) := by
  intro r
  dsimp only
  rw [f.property r, ← mul_assoc, recurrence_monomial_mul]
  congr 2
  ring

lemma normalized_solution_modeq (m : ℕ) (f : Solutions k m) (r s : ℤ)
    (h : Int.ModEq (m : ℤ) r s) :
    monomial k (-(r^2)) * f.val r = monomial k (-(s^2)) * f.val s := by
  obtain ⟨a, ha⟩ := Int.modEq_iff_add_fac.mp h
  rw [ha, mul_comm (m : ℤ) a]
  exact ((normalized_solution_periodic k m f).int_mul a r).symm

/-- Coordinates use the inverse of the literal theta coefficient at its
representative. This includes arbitrary Laurent-series scalars. -/
def recurrenceCoordinates (m : ℕ) (f : Solutions k m) : Fin m → K k :=
  fun ν => monomial k (-((ν.val : ℤ)^2)) * f.val ν.val

lemma recurrenceCoordinates_synth (m : ℕ) (v : Fin m → K k) :
    recurrenceCoordinates k m ⟨synth k m v, synth_mem_solutions k m v⟩ = v := by
  funext ν
  change monomial k (-((ν.val : ℤ)^2)) * synth k m v ν.val = v ν
  rw [synth_apply_of_modeq k m v ν.val ν (Int.ModEq.refl _)]
  rw [mul_left_comm, recurrence_monomial_mul]
  simp

lemma synth_recurrenceCoordinates (m : ℕ) [NeZero m] (f : Solutions k m) :
    synth k m (recurrenceCoordinates k m f) = f.val := by
  funext r
  have hm : (0 : ℤ) < m := by exact_mod_cast NeZero.pos m
  let ν : Fin m := ⟨(r % (m : ℤ)).toNat, by
    have := Int.emod_lt_of_pos r hm
    have := Int.emod_nonneg r (ne_of_gt hm)
    omega⟩
  have hν : (ν.val : ℤ) = r % (m : ℤ) := by
    dsimp [ν]
    exact Int.toNat_of_nonneg (Int.emod_nonneg r (ne_of_gt hm))
  have h : Int.ModEq (m : ℤ) r (ν.val : ℤ) := by
    rw [hν]
    exact (Int.mod_modEq r (m : ℤ)).symm
  rw [synth_apply_of_modeq k m _ r ν h]
  change (monomial k (-((ν.val : ℤ)^2)) * f.val ν.val) * monomial k (r^2) = _
  rw [← normalized_solution_modeq k m f r ν.val h]
  rw [mul_right_comm, recurrence_monomial_mul]
  simp

/-- The explicit linear equivalence for the full integer-indexed recurrence. -/
def recurrenceEquiv (m : ℕ) [NeZero m] :
    (Fin m → K k) ≃ₗ[K k] Solutions k m where
  toFun v := ⟨synth k m v, synth_mem_solutions k m v⟩
  invFun := recurrenceCoordinates k m
  left_inv := recurrenceCoordinates_synth k m
  right_inv f := Subtype.ext (synth_recurrenceCoordinates k m f)
  map_add' v w := by
    apply Subtype.ext
    simp [synth, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    apply Subtype.ext
    simp [synth, Finset.smul_sum, smul_smul]

/-- The frozen basis and dimension obligation, with precisely the prescribed
finite synthesis map and the Laurent-series scalar field. -/
theorem theta_recurrence_basis :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m →
    ∃ E : (Fin m → K k) ≃ₗ[K k] (Solutions k m),
      (∀ v : Fin m → K k, (E v).val = synth k m v) ∧
      Module.Finite (K k) (Solutions k m) ∧
      Module.finrank (K k) (Solutions k m) = m := by
  intro k _ _ m _ _
  let E := recurrenceEquiv k m
  refine ⟨E, fun _ => rfl, Module.Finite.equiv E, ?_⟩
  rw [← E.finrank_eq]
  exact Module.finrank_fin_fun (K k)

end ArithmeticThetaSchrodingerR0119
