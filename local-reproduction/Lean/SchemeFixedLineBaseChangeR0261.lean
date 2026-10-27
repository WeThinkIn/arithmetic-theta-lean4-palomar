import SchemeSchrodingerDefinitionsR0261

/-! Finite-order fixed kernels commute with arbitrary scheme pullback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace ArithmeticThetaSchemeSchrodingerR0261
namespace FixedKernelBaseChange

section Categorical
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {W : C} (m : ℕ) (A : End W)

/-- The categorical cyclic average; the denominator is an actual invertible map. -/
def projector [IsIso (m • 𝟙 W)] : End W :=
  (∑ j ∈ Finset.range m, A ^ j) ≫ inv (m • 𝟙 W)

lemma projector_denominator [IsIso (m • 𝟙 W)] :
    projector m A ≫ (m • 𝟙 W) = ∑ j ∈ Finset.range m, A ^ j := by
  simp only [projector, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

lemma fixed_projector [IsIso (m • 𝟙 W)] {Z : C} (f : Z ⟶ W)
    (hf : f ≫ A = f) : f ≫ projector m A = f := by
  apply (cancel_mono (m • 𝟙 W)).1
  rw [Category.assoc, projector_denominator]
  have hp (j : ℕ) : f ≫ A ^ j = f := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, End.mul_def, ← Category.assoc, hf, ih]
  rw [Preadditive.comp_sum]
  simp only [hp, Finset.sum_const, Finset.card_range,
    Preadditive.comp_nsmul, Category.comp_id]

lemma projector_condition [IsIso (m • 𝟙 W)] (hA : A ^ m = 1) :
    projector m A ≫ (A - 1) = 0 := by
  apply (cancel_mono (m • 𝟙 W)).1
  have hc : (A - 1) ≫ (m • 𝟙 W) = (m • 𝟙 W) ≫ (A - 1) := by
    simp
  rw [Category.assoc, hc, ← Category.assoc, projector_denominator]
  have hg := mul_geom_sum A m
  rw [hA, sub_self] at hg
  simpa only [End.mul_def, zero_comp] using hg

variable [HasKernels C]

def retract [IsIso (m • 𝟙 W)] (hA : A ^ m = 1) : W ⟶ kernel (A - 1) :=
  kernel.lift _ (projector m A) (projector_condition m A hA)

@[reassoc (attr := simp)]
lemma retract_ι [IsIso (m • 𝟙 W)] (hA : A ^ m = 1) :
    retract m A hA ≫ kernel.ι (A - 1) = projector m A := by
  simp [retract]

lemma ι_fixed : kernel.ι (A - 1) ≫ A = kernel.ι (A - 1) := by
  have h := kernel.condition (A - 1)
  rw [Preadditive.comp_sub, End.one_def, Category.comp_id, sub_eq_zero] at h
  exact h

@[reassoc (attr := simp)]
lemma ι_retract [IsIso (m • 𝟙 W)] (hA : A ^ m = 1) :
    kernel.ι (A - 1) ≫ retract m A hA = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (A - 1))).1
  simp only [Category.assoc, retract_ι, Category.id_comp]
  exact fixed_projector m A _ (ι_fixed A)

variable {D : Type w} [Category.{v} D] [Preadditive D] [HasKernels D]
variable (F : C ⥤ D) [F.Additive]

omit [HasKernels C] [HasKernels D] in
lemma map_projector [IsIso (m • 𝟙 W)] [IsIso (m • 𝟙 (F.obj W))] :
    F.map (projector m A) = projector m (F.map A) := by
  simp only [projector, F.map_comp, F.map_sum, F.map_inv, F.map_nsmul, F.map_id]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (F.mapEnd W).map_pow A j)

/-- The canonical kernel comparison for any additive functor. -/
theorem kernel_comparison [IsIso (m • 𝟙 W)] (hA : A ^ m = 1) :
    ∃ e : F.obj (kernel (A - 1)) ≅ kernel (F.map A - 𝟙 (F.obj W)),
      e.hom ≫ kernel.ι (F.map A - 𝟙 (F.obj W)) = F.map (kernel.ι (A - 1)) := by
  let : IsIso (m • 𝟙 (F.obj W)) := by
    have : IsIso (F.map (m • 𝟙 W)) := inferInstance
    simpa only [F.map_nsmul, F.map_id] using this
  let i := F.map (kernel.ι (A - 1))
  let r := F.map (retract m A hA)
  have hir : i ≫ r = 𝟙 _ := by
    exact (F.map_comp _ _).symm.trans
      ((congrArg (fun z => F.map z) (ι_retract m A hA)).trans (F.map_id _))
  have hi : i ≫ (F.map A - 𝟙 (F.obj W)) = 0 := by
    dsimp [i]
    rw [← F.map_id W, ← F.map_sub, ← F.map_comp, kernel.condition, F.map_zero]
  let f := kernel.lift (F.map A - 𝟙 (F.obj W)) i hi
  let g := kernel.ι (F.map A - 𝟙 (F.obj W)) ≫ r
  have hfg : f ≫ g = 𝟙 _ := by
    dsimp [g, f]
    rw [← Category.assoc, kernel.lift_ι, hir]
    rfl
  have hgf : g ≫ f = 𝟙 _ := by
    apply (cancel_mono (kernel.ι (F.map A - 𝟙 (F.obj W)))).1
    dsimp [g, f]
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    change kernel.ι (F.map A - 𝟙 (F.obj W)) ≫
      (F.map (retract m A hA) ≫ F.map (kernel.ι (A - 1))) = _
    rw [← F.map_comp, retract_ι m A hA, map_projector m A F]
    exact fixed_projector m (F.map A) _ (ι_fixed (F.map A))
  exact ⟨⟨f, g, hfg, hgf⟩, kernel.lift_ι _ _ _⟩

end Categorical

/-- Every positive integer acts invertibly on every module sheaf over a
characteristic-zero field, using the given structural morphism. -/
lemma denominator_isIso (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (W : S.Modules) (m : ℕ) (hm : 0 < m) : IsIso (m • 𝟙 W) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let := Scheme.TwoAffineOpenCover.algebraOfHom σ U
  have hn : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  let c : Γ(S, U) := algebraMap k Γ(S, U) ((m : k)⁻¹)
  have hc : c * (m : Γ(S, U)) = 1 := by
    dsimp [c]
    rw [← map_natCast (algebraMap k Γ(S, U)), ← map_mul, inv_mul_cancel₀ hn, map_one]
  have happ : ∀ (n : ℕ) (x : Γ(W, U)), (n • 𝟙 W).app U x = n • x := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih => simp [succ_nsmul, Scheme.Modules.Hom.add_app, ih]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hinv (x : Γ(W, U)) : c • (m • x) = x := by
    rw [← Nat.cast_smul_eq_nsmul Γ(S, U), smul_smul, hc, one_smul]
  constructor
  · intro x y h
    rw [happ, happ] at h
    simpa only [hinv] using congrArg (fun z : Γ(W, U) => c • z) h
  · intro x
    refine ⟨c • x, ?_⟩
    rw [happ, ← Nat.cast_smul_eq_nsmul Γ(S, U), smul_smul, mul_comm, hc, one_smul]

end FixedKernelBaseChange
/-- The actual fixed kernel commutes with arbitrary, possibly nonflat, base change. -/
theorem scheme_fixed_line_base_change
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (W : S.Modules) (m : ℕ) (hm : 0 < m) (A : End W) (hA : A ^ m = 1) :
    FixedNatural A := by
  let := FixedKernelBaseChange.denominator_isIso k S σ W m hm
  intro T b
  exact FixedKernelBaseChange.kernel_comparison m A (Scheme.Modules.pullback b) hA

end ArithmeticThetaSchemeSchrodingerR0261

#print axioms ArithmeticThetaSchemeSchrodingerR0261.scheme_fixed_line_base_change
