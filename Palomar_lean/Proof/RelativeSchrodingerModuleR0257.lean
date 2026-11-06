module

public import RelativeSchrodingerDefinitionsR0257

@[expose] public section

/-! The cyclic averaging retraction onto the actual fixed submodule. -/
set_option autoImplicit false
noncomputable section
universe u v
open scoped TensorProduct
namespace ArithmeticThetaRelativeSchrodingerR0257
namespace RelativeSchrodingerModule

variable {R : Type u} [CommRing R] [Algebra ℚ R]
variable {V : Type v} [AddCommGroup V] [Module R V]

def average (m : ℕ) (A : Module.End R V) : Module.End R V :=
  algebraMap ℚ R ((m : ℚ)⁻¹) • ∑ j ∈ Finset.range m, A ^ j

lemma average_fixed (m : ℕ) (A : Module.End R V) (hA : A ^ m = 1) (x : V) :
    A (average m A x) = average m A x := by
  have h : A * (∑ j ∈ Finset.range m, A ^ j) = ∑ j ∈ Finset.range m, A ^ j := by
    have h := mul_geom_sum A m
    rw [hA, sub_self, sub_mul, one_mul, sub_eq_zero] at h
    exact h
  change A ((algebraMap ℚ R ((m : ℚ)⁻¹)) • _) = _
  rw [map_smul]
  exact congrArg (fun f : Module.End R V => algebraMap ℚ R ((m : ℚ)⁻¹) • f x) h

omit [Algebra ℚ R] in
lemma pow_apply_fixed (A : Module.End R V) (x : V) (hx : A x = x) (j : ℕ) :
    (A ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hx]

lemma average_of_fixed (m : ℕ) (hm : 0 < m) (A : Module.End R V)
    (x : V) (hx : A x = x) : average m A x = x := by
  have hn : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hc : algebraMap ℚ R ((m : ℚ)⁻¹) * (m : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hn, map_one]
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply,
    pow_apply_fixed A x hx, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

def retract (m : ℕ) (A : Module.End R V) (hA : A ^ m = 1) :
    V →ₗ[R] Fixed R V A :=
  (average m A).codRestrict _ (fun x => by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact average_fixed m A hA x)

lemma retract_subtype (m : ℕ) (hm : 0 < m) (A : Module.End R V) (hA : A ^ m = 1) :
    (retract m A hA).comp (Fixed R V A).subtype = LinearMap.id := by
  ext x
  exact average_of_fixed m hm A x (by
    simpa only [Module.End.mem_eigenspace_iff, one_smul] using x.property)

theorem fixed_finite_projective (m : ℕ) (hm : 0 < m) (A : Module.End R V)
    (hA : A ^ m = 1) [Module.Finite R V] [Module.Projective R V] :
    Module.Finite R (Fixed R V A) ∧ Module.Projective R (Fixed R V A) := by
  have hs := retract_subtype m hm A hA
  refine ⟨Module.Finite.of_surjective (retract m A hA) ?_,
    Module.Projective.of_split (Fixed R V A).subtype (retract m A hA) hs⟩
  intro x
  exact ⟨x.val, DFunLike.congr_fun hs x⟩

lemma baseChange_average_of_fixed (m : ℕ) (hm : 0 < m) (A : Module.End R V)
    (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] V)
    (hx : A.baseChange S x = x) : (average m A).baseChange S x = x := by
  have hn : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hc : algebraMap ℚ R ((m : ℚ)⁻¹) * (m : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hb : (∑ j ∈ Finset.range m, A ^ j).baseChange S =
      ∑ j ∈ Finset.range m, (A.baseChange S) ^ j := by
    exact (map_sum (Module.End.baseChangeHom R S V) _ _).trans
      (Finset.sum_congr rfl (fun j _ => map_pow (Module.End.baseChangeHom R S V) A j))
  simp only [average, LinearMap.baseChange_smul, hb, LinearMap.smul_apply,
    LinearMap.sum_apply, pow_apply_fixed (A.baseChange S) x hx,
    Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

/-- The fixed submodule's canonical tensor inclusion, with its genuine eigenspace codomain. -/
def fixedTensorInclusion (A : Module.End R V) (S : Type u) [CommRing S] [Algebra R S] :
    S ⊗[R] Fixed R V A →ₗ[S] Fixed S (S ⊗[R] V) (A.baseChange S) :=
  ((Fixed R V A).subtype.baseChange S).codRestrict _ (by
    intro x
    rw [Module.End.mem_eigenspace_iff, one_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      have hw : A w.val = w.val := by
        simpa only [Module.End.mem_eigenspace_iff, one_smul] using w.property
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply, hw]
    | add x y hx hy => simp only [map_add, hx, hy])

theorem fixed_baseChange (m : ℕ) (hm : 0 < m) (A : Module.End R V)
    (hA : A ^ m = 1) : FixedBaseChange R V A := by
  intro S _ _
  let f := fixedTensorInclusion A S
  let g := ((retract m A hA).baseChange S).comp
    (Fixed S (S ⊗[R] V) (A.baseChange S)).subtype
  have hgf : g.comp f = LinearMap.id := by
    change ((retract m A hA).baseChange S).comp
      ((Fixed R V A).subtype.baseChange S) = LinearMap.id
    rw [← LinearMap.baseChange_comp, retract_subtype m hm A hA, LinearMap.baseChange_id]
  have hfg : f.comp g = LinearMap.id := by
    ext x
    change ((Fixed R V A).subtype.baseChange S)
      ((retract m A hA).baseChange S x.val) = x.val
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    change (average m A).baseChange S x.val = x.val
    apply baseChange_average_of_fixed m hm A S
    simpa only [Module.End.mem_eigenspace_iff, one_smul] using x.property
  let e : S ⊗[R] Fixed R V A ≃ₗ[S] Fixed S (S ⊗[R] V) (A.baseChange S) :=
    { f with
      invFun := g
      left_inv := fun x => DFunLike.congr_fun hgf x
      right_inv := fun x => DFunLike.congr_fun hfg x }
  exact ⟨e, fun _ _ => rfl⟩

omit [Algebra ℚ R] in
lemma unit_pow_sub_one (m : ℕ) (c : Rˣ)
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c)
    (i : ℕ) (hi : i < m) (hi0 : i ≠ 0) : IsUnit ((c : R) ^ i - 1) :=
  hc.2 ⟨i, hi⟩ hi0

omit [Algebra ℚ R] in
lemma primitive_inv (m : ℕ) (c : Rˣ)
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c⁻¹ := by
  refine ⟨by rw [inv_pow, hc.1, inv_one], ?_⟩
  intro i hi
  have he : ((c⁻¹ : Rˣ) : R) ^ i.val - 1 =
      -(((c⁻¹ : Rˣ) : R) ^ i.val * ((c : R) ^ i.val - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul, one_pow, mul_one, neg_sub]
  rw [he]
  exact ((c⁻¹ ^ i.val).isUnit.mul (hc.2 i hi)).neg

omit [Algebra ℚ R] in
lemma primitive_geometric_sum (m : ℕ) (c : Rˣ)
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c)
    (j : ℕ) (hj : j < m) (hj0 : j ≠ 0) :
    ∑ i ∈ Finset.range m, ((c : R) ^ j) ^ i = 0 := by
  have hp : (c : R) ^ m = 1 := by simpa using congrArg (fun z : Rˣ => (z : R)) hc.1
  have hs := geom_sum_mul ((c : R) ^ j) m
  rw [← pow_mul, Nat.mul_comm j m, pow_mul, hp, one_pow, sub_self] at hs
  exact (hc.2 ⟨j, hj⟩ hj0).mul_right_cancel (by simpa using hs)

def eigenProjector (m : ℕ) (A : Module.End R V) (c : Rˣ) (i : ℕ) : Module.End R V :=
  average m (((c⁻¹ : Rˣ) : R) ^ i • A)

lemma eigenProjector_sum (m : ℕ) (hm : 0 < m) (A : Module.End R V) (c : Rˣ)
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    (∑ i ∈ Finset.range m, eigenProjector m A c i) = 1 := by
  have hci := primitive_inv m c hc
  have hn : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hcancel : algebraMap ℚ R ((m : ℚ)⁻¹) * (m : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hn, map_one]
  simp only [eigenProjector, average, smul_pow, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  have hsum : (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
      (((c⁻¹ : Rˣ) : R) ^ i) ^ j • A ^ j) = (m : R) • (1 : Module.End R V) := by
    rw [Finset.sum_eq_single 0]
    · simp [← Nat.cast_smul_eq_nsmul R]
    · intro j hj hj0
      simp_rw [← pow_mul, Nat.mul_comm _ j, pow_mul, ← Finset.sum_smul]
      rw [primitive_geometric_sum m c⁻¹ hci j (Finset.mem_range.mp hj) hj0, zero_smul]
    · simp [hm.ne']
  rw [hsum, smul_smul, hcancel, one_smul]

lemma eigenProjector_eigen (m : ℕ) (A : Module.End R V) (hA : A ^ m = 1)
    (c : Rˣ) (hc : c ^ m = 1) (i : ℕ) (x : V) :
    A (eigenProjector m A c i x) = (c : R) ^ i • eigenProjector m A c i x := by
  have hp : (((c⁻¹ : Rˣ) : R) ^ i • A) ^ m = 1 := by
    rw [smul_pow, ← pow_mul, Nat.mul_comm i m, pow_mul]
    have hc' : ((c⁻¹ : Rˣ) : R) ^ m = 1 := by
      have h : (c⁻¹) ^ m = 1 := by rw [inv_pow, hc, inv_one]
      simpa using congrArg (fun z : Rˣ => (z : R)) h
    rw [hc', one_pow, one_smul, hA]
  have h := average_fixed m _ hp x
  have h' := congrArg (fun y : V => (c : R) ^ i • y) h
  simpa only [LinearMap.smul_apply, smul_smul, ← mul_pow,
    Units.mul_inv, one_pow, one_smul, eigenProjector] using h'

lemma eigenProjector_of_eigen (m : ℕ) (hm : 0 < m) (A : Module.End R V)
    (c : Rˣ) (i : ℕ) (x : V) (hx : A x = (c : R) ^ i • x) :
    eigenProjector m A c i x = x := by
  apply average_of_fixed m hm
  simp only [LinearMap.smul_apply, hx, smul_smul, ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

omit [Algebra ℚ R] in
lemma primitive_difference (m : ℕ) (c : Rˣ)
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c)
    (i j : Fin m) (hij : i ≠ j) : IsUnit ((c : R) ^ i.val - (c : R) ^ j.val) := by
  have hlt (a b : Fin m) (hab : a.val < b.val) :
      IsUnit ((c : R) ^ b.val - (c : R) ^ a.val) := by
    have he : (c : R) ^ b.val - (c : R) ^ a.val =
        (c : R) ^ a.val * ((c : R) ^ (b.val - a.val) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hab), mul_one]
    rw [he]
    exact (c ^ a.val).isUnit.mul (unit_pow_sub_one m c hc (b.val - a.val)
      (lt_of_le_of_lt (Nat.sub_le _ _) b.isLt) (Nat.ne_of_gt (Nat.sub_pos_of_lt hab)))
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · simpa only [neg_sub] using (hlt i j h).neg
  · exact hlt j i h

omit [Algebra ℚ R] in
lemma pow_apply_eigen (A : Module.End R V) (a : R) (x : V) (hx : A x = a • x)
    (j : ℕ) : (A ^ j) x = a ^ j • x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

lemma average_apply_eigen (m : ℕ) (A : Module.End R V) (a : R) (x : V)
    (hx : A x = a • x) :
    average m A x = (algebraMap ℚ R ((m : ℚ)⁻¹) * ∑ j ∈ Finset.range m, a ^ j) • x := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply,
    pow_apply_eigen A a x hx, Finset.sum_smul, mul_smul]

lemma eigenProjector_other (m : ℕ) (A : Module.End R V) (hA : A ^ m = 1)
    (c : Rˣ) (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c)
    (i j : Fin m) (hij : i ≠ j) (x : V) (hx : A x = (c : R) ^ j.val • x) :
    eigenProjector m A c i.val x = 0 := by
  have he := eigenProjector_eigen m A hA c hc.1 i.val x
  have he' : A (eigenProjector m A c i.val x) =
      (c : R) ^ j.val • eigenProjector m A c i.val x := by
    have hscaled : (((c⁻¹ : Rˣ) : R) ^ i.val • A) x =
        (((c⁻¹ : Rˣ) : R) ^ i.val * (c : R) ^ j.val) • x := by
      simp [hx, smul_smul]
    rw [eigenProjector, average_apply_eigen m _ _ x hscaled]
    simp only [map_smul, hx, smul_smul, mul_comm]
  apply (primitive_difference m c hc i j hij).smul_eq_zero.mp
  rw [sub_smul, ← he, ← he', sub_self]

omit [Algebra ℚ R] in
lemma orbit_relation (A B : Module.End R V) (c : Rˣ)
    (hAB : A * B = (c : R) • (B * A)) (i : ℕ) :
    A * B ^ i = (c : R) ^ i • (B ^ i * A) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      A * B ^ (i + 1) = (A * B ^ i) * B := by rw [pow_succ, mul_assoc]
      _ = (c : R) ^ i • (B ^ i * (A * B)) := by rw [ih, smul_mul_assoc, mul_assoc]
      _ = (c : R) ^ (i + 1) • (B ^ (i + 1) * A) := by
        rw [hAB, mul_smul_comm, smul_smul, pow_succ, pow_succ, mul_assoc]

omit [Algebra ℚ R] in
lemma orbit_eigen (A B : Module.End R V) (c : Rˣ)
    (hAB : A * B = (c : R) • (B * A)) (i : ℕ) (x : Fixed R V A) :
    A ((B ^ i) x.val) = (c : R) ^ i • (B ^ i) x.val := by
  have hx : A x.val = x.val := by
    simpa only [Module.End.mem_eigenspace_iff, one_smul] using x.property
  have h := DFunLike.congr_fun (orbit_relation A B c hAB i) x.val
  simpa only [Module.End.mul_apply, LinearMap.smul_apply, hx] using h

def orbitSum (m : ℕ) (A B : Module.End R V) : (Fin m → Fixed R V A) →ₗ[R] V where
  toFun w := ∑ i : Fin m, (B ^ i.val) (w i).val
  map_add' w z := by simp [Finset.sum_add_distrib]
  map_smul' r w := by simp [Finset.smul_sum]

omit [Algebra ℚ R] in
lemma power_cancel (m : ℕ) (B : Module.End R V) (hB : B ^ m = 1)
    (i : ℕ) (hi : i ≤ m) (x : V) : (B ^ i) ((B ^ (m - i)) x) = x := by
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_of_le hi, hB, Module.End.one_apply]

lemma orbitSum_projector (m : ℕ) (hm : 0 < m) (A B : Module.End R V)
    (c : Rˣ) (hA : A ^ m = 1) (hAB : A * B = (c : R) • (B * A))
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c)
    (w : Fin m → Fixed R V A) (i : Fin m) :
    eigenProjector m A c i.val (orbitSum m A B w) = (B ^ i.val) (w i).val := by
  change eigenProjector m A c i.val (∑ j : Fin m, (B ^ j.val) (w j).val) = _
  rw [map_sum, Finset.sum_eq_single i]
  · exact eigenProjector_of_eigen m hm A c i.val _ (orbit_eigen A B c hAB i.val (w i))
  · intro j _ hji
    exact eigenProjector_other m A hA c hc i j hji.symm _ (orbit_eigen A B c hAB j.val (w j))
  · simp

lemma backward_projector_fixed (m : ℕ) (A B : Module.End R V)
    (c : Rˣ) (hA : A ^ m = 1) (hAB : A * B = (c : R) • (B * A))
    (hc : c ^ m = 1) (i : Fin m) (x : V) :
    (B ^ (m - i.val)) (eigenProjector m A c i.val x) ∈ Fixed R V A := by
  rw [Module.End.mem_eigenspace_iff, one_smul]
  have h := DFunLike.congr_fun (orbit_relation A B c hAB (m - i.val))
    (eigenProjector m A c i.val x)
  simp only [Module.End.mul_apply, LinearMap.smul_apply,
    eigenProjector_eigen m A hA c hc, map_smul, smul_smul] at h
  have hp : (c : R) ^ (m - i.val) * (c : R) ^ i.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
    simpa using congrArg (fun z : Rˣ => (z : R)) hc
  simpa only [hp, one_smul] using h

theorem orbitSum_bijective (m : ℕ) (hm : 0 < m) (A B : Module.End R V)
    (c : Rˣ) (hA : A ^ m = 1) (hB : B ^ m = 1)
    (hAB : A * B = (c : R) • (B * A))
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    Function.Bijective (orbitSum m A B) := by
  constructor
  · intro w z hwz
    funext i
    apply Subtype.ext
    have h := congrArg (eigenProjector m A c i.val) hwz
    rw [orbitSum_projector m hm A B c hA hAB hc,
      orbitSum_projector m hm A B c hA hAB hc] at h
    have h' := congrArg (fun y => (B ^ (m - i.val)) y) h
    simpa only [← Module.End.mul_apply, ← pow_add,
      Nat.sub_add_cancel (Nat.le_of_lt i.isLt), hB, Module.End.one_apply] using h'
  · intro x
    let w : Fin m → Fixed R V A := fun i =>
      ⟨(B ^ (m - i.val)) (eigenProjector m A c i.val x),
        backward_projector_fixed m A B c hA hAB hc.1 i x⟩
    refine ⟨w, ?_⟩
    change (∑ i : Fin m, (B ^ i.val) ((B ^ (m - i.val))
      (eigenProjector m A c i.val x))) = x
    simp_rw [power_cancel m B hB _ (Nat.le_of_lt (Fin.isLt _))]
    rw [← LinearMap.sum_apply, Fin.sum_univ_eq_sum_range, eigenProjector_sum m hm A c hc]
    rfl

def orbitEquiv (m : ℕ) (hm : 0 < m) (A B : Module.End R V)
    (c : Rˣ) (hA : A ^ m = 1) (hB : B ^ m = 1)
    (hAB : A * B = (c : R) • (B * A))
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    (Fin m → Fixed R V A) ≃ₗ[R] V :=
  LinearEquiv.ofBijective (orbitSum m A B) (orbitSum_bijective m hm A B c hA hB hAB hc)

omit [Algebra ℚ R] in
lemma orbitSum_A (m : ℕ) (A B : Module.End R V) (c : Rˣ)
    (hAB : A * B = (c : R) • (B * A)) (w : Fin m → Fixed R V A) :
    A (orbitSum m A B w) = orbitSum m A B (fun i => (c : R) ^ i.val • w i) := by
  change A (∑ i : Fin m, (B ^ i.val) (w i).val) = _
  simp only [map_sum, orbit_eigen A B c hAB]
  simp [orbitSum]

omit [Algebra ℚ R] in
lemma orbitSum_B_single (m : ℕ) (A B : Module.End R V) (hB : B ^ m = 1)
    (i : Fin m) (w : Fixed R V A) :
    B (orbitSum m A B (Pi.single i w)) = (B ^ ((i.val + 1) % m)) w.val := by
  classical
  have hs : orbitSum m A B (Pi.single i w) = (B ^ i.val) w.val := by
    change (∑ j : Fin m, (B ^ j.val) ((Pi.single i w : Fin m → Fixed R V A) j).val) = _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [hs, ← Module.End.mul_apply, ← pow_succ', pow_eq_pow_mod _ hB]

theorem fixed_rank_one (m : ℕ) (hm : 0 < m) (hV : FiniteProjectiveRank R V m)
    (A B : Module.End R V) (c : Rˣ) (hA : A ^ m = 1) (hB : B ^ m = 1)
    (hAB : A * B = (c : R) • (B * A))
    (hc : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c) :
    FiniteProjectiveRank R (Fixed R V A) 1 := by
  letI := hV.1
  letI := hV.2.1
  obtain ⟨hfinite, hprojective⟩ := fixed_finite_projective m hm A hA
  letI := hfinite
  refine ⟨hfinite, hprojective, ?_⟩
  intro K _ _ _
  haveI : Module.Finite K (K ⊗[R] Fixed R V A) := inferInstance
  refine ⟨inferInstance, ?_⟩
  let e := orbitEquiv m hm A B c hA hB hAB hc
  let eK : (Fin m → K ⊗[R] Fixed R V A) ≃ₗ[K] K ⊗[R] V :=
    (TensorProduct.piRight R K K (fun _ : Fin m => Fixed R V A)).symm.trans
      (e.baseChange R K _ _)
  have hdim := eK.finrank_eq
  rw [Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hdim
  rw [(hV.2.2 K).2] at hdim
  exact Nat.eq_of_mul_eq_mul_left hm (hdim.trans (Nat.mul_one m).symm)

end RelativeSchrodingerModule

/-- The relative orbit decomposition uses the actual fixed eigenspace and is
compatible with arbitrary scalar extension, without a flatness hypothesis. -/
theorem relative_schrodinger_module :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R]
      (V : Type v) [AddCommGroup V] [Module R V] (m : ℕ),
      0 < m → FiniteProjectiveRank R V m →
      ∀ (A B : Module.End R V) (c : Rˣ),
      A ^ m = 1 → B ^ m = 1 → A * B = (c : R) • (B * A) →
      ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m c →
      OrbitComparison R V m A B c ∧ FixedBaseChange R V A := by
  intro R _ _ V _ _ m hm hV A B c hA hB hAB hc
  refine ⟨⟨RelativeSchrodingerModule.fixed_rank_one m hm hV A B c hA hB hAB hc, ?_⟩,
    RelativeSchrodingerModule.fixed_baseChange m hm A hA⟩
  refine ⟨RelativeSchrodingerModule.orbitEquiv m hm A B c hA hB hAB hc,
    fun _ => rfl, ?_, ?_⟩
  · exact RelativeSchrodingerModule.orbitSum_A m A B c hAB
  · exact RelativeSchrodingerModule.orbitSum_B_single m A B hB

end ArithmeticThetaRelativeSchrodingerR0257
