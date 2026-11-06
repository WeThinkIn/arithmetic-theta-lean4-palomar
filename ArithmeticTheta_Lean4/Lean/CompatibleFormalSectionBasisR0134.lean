import PositiveSectionBasisR0134
import PositiveSectionsReductionR0134
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Compatible bases for the genuine positive numerator section modules. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace CompatibleFormalSectionBasisR0134
open ArithmeticThetaInfinitesimalPolygonR0129
open PositiveSectionsReductionR0134

def linearSum {S M J : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype J] (b : J → M) : (J → S) →ₗ[S] M where
  toFun c := ∑ j, c j • b j
  map_add' c e := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c e := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- A nilpotent approximation gives surjectivity, and equal finite free
rank turns this into bijectivity. -/
lemma bijective_of_approx {S M J : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [Fintype J] (e : (J → S) ≃ₗ[S] M) (f : (J → S) →ₗ[S] M)
    (t : S) (q : ℕ) (ht : t^q = 0)
    (hf : ∀ x, ∃ c y, x = f c + t • y) : Function.Bijective f := by
  let tC : (J → S) →+ (J → S) := (t • (LinearMap.id : (J → S) →ₗ[S] (J → S))).toAddMonoidHom
  let tM : M →+ M := (t • (LinearMap.id : M →ₗ[S] M)).toAddMonoidHom
  have honto : Function.Surjective f := by
    apply surjective_of_nilpotent_approximation f.toAddMonoidHom tC tM
      (fun x => f.map_smul t x) hf q
    intro x
    have hi : ∀ m, (tM^[m]) x = t^m • x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        change t • (tM^[m]) x = _
        rw [ih, smul_smul, pow_succ']
    rw [hi, ht, zero_smul]
  have hi := Module.End.injective_of_surjective S (J → S)
    (f := e.symm.toLinearMap.comp f) (e.symm.surjective.comp honto)
  exact ⟨fun x y h => hi (congrArg e.symm h), honto⟩

variable (k : Type u) [Field k] [CharZero k]
variable (r : ℕ) (hr : 0 < r) (T : Tower k r hr) (a : Fin r → kˣ) (d : ℕ)

local instance nodeAlgebra (n : ℕ) : Algebra (R k n) (A k n) := (base k n).toAlgebra
local instance nodeModule (n : ℕ) : Module (R k n) (A k n) := (nodeAlgebra k n).toModule
local instance nodeAction (n : ℕ) : DistribMulAction (R k n) (A k n) :=
  (nodeModule k n).toDistribMulAction
local instance nodeMulAction (n : ℕ) : MulAction (R k n) (A k n) :=
  (nodeAction k n).toMulAction
local instance nodeScalar (n : ℕ) : SMul (R k n) (A k n) := ⟨fun c x => base k n c * x⟩
local instance nodeFamilyScalar (n : ℕ) : SMul (R k n) (Fin r → A k n) :=
  ⟨fun c x i => base k n c * x i⟩

def sectionModule (n : ℕ) : Submodule (R k n) (Fin r → A k n) where
  carrier := Compatible k r n hr (T.overlap n) a d
  zero_mem' := compatible_zero k r n hr (T.overlap n) a d
  add_mem' := fun hs hv => compatible_add k r n hr (T.overlap n) a d _ _ hs hv
  smul_mem' := fun c _ hs => compatible_base_mul k r n hr (T.overlap n)
    (T.overlap_spec n) a d c _ hs

abbrev V (n : ℕ) := ↥(sectionModule k r hr T a d n)

/-- Synthesis uses the fixed structural map, with no scalar extension choice. -/
def synth (n : ℕ) (b : Fin (d*r) → V k r hr T a d n) :
    (Fin (d*r) → R k n) →ₗ[R k n] V k r hr T a d n :=
  linearSum b

lemma synth_val (n : ℕ) (b : Fin (d*r) → V k r hr T a d n)
    (c : Fin (d*r) → R k n) (i : Fin r) :
    (synth k r hr T a d n b c).val i = ∑ j, base k n (c j) * (b j).val i := by
  change (∑ j, c j • b j : V k r hr T a d n).val i = _
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul]
  rfl

lemma isBasis_iff (n : ℕ) (b : Fin (d*r) → V k r hr T a d n) :
    IsBasis k r n hr (T.overlap n) a d b ↔ Function.Bijective (synth k r hr T a d n b) := by
  change (∀ s : V k r hr T a d n, ∃! c : Fin (d*r) → R k n, ∀ i,
    s.val i = ∑ j, base k n (c j) * (b j).val i) ↔ _
  have he (s : V k r hr T a d n) (c : Fin (d*r) → R k n) :
      (∀ i, s.val i = ∑ j, base k n (c j) * (b j).val i) ↔
        synth k r hr T a d n b c = s := by
    simp only [← synth_val]
    constructor
    · intro h; exact Subtype.ext (funext fun i => (h i).symm)
    · intro h; intro i; rw [h]
  simp only [he]
  exact (Function.bijective_iff_existsUnique _).symm

/-- The genuine coefficient reduction on sections. -/
def red (n N : ℕ) (h : n ≤ N) (s : V k r hr T a d N) : V k r hr T a d n :=
  ⟨fun i => truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
    n N h (s.val i), compatible_reduction k r hr T a d n N h s⟩

lemma red_synth (n N : ℕ) (h : n ≤ N) (b : Fin (d*r) → V k r hr T a d N)
    (c : Fin (d*r) → R k N) :
    red k r hr T a d n N h (synth k r hr T a d N b c) =
      synth k r hr T a d n (fun j => red k r hr T a d n N h (b j))
        (fun j => truncReduce (PowerSeries k) PowerSeries.X n N h (c j)) := by
  apply Subtype.ext
  funext i
  change truncReduce _ _ n N h ((synth k r hr T a d N b c).val i) = _
  simp only [synth_val, map_sum, map_mul, reduce_base]
  rfl

lemma red_comp (n N P : ℕ) (h : n ≤ N) (h' : N ≤ P) (s : V k r hr T a d P) :
    red k r hr T a d n N h (red k r hr T a d N P h' s) =
      red k r hr T a d n P (h.trans h') s := by
  apply Subtype.ext
  funext i
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (s.val i)
  change truncReduce _ _ n N h (truncReduce _ _ N P h' (s.val i)) =
    truncReduce _ _ n P (h.trans h') (s.val i)
  rw [← hz]
  rfl


lemma red_sub (n N : ℕ) (h : n ≤ N) (s v : V k r hr T a d N) :
    red k r hr T a d n N h (s-v) =
      red k r hr T a d n N h s - red k r hr T a d n N h v := by
  apply Subtype.ext
  funext i
  exact map_sub _ _ _

/-- Every lift of a finite-stage basis remains a basis at the next stage. -/
lemma lifted_basis (h3 : 3 ≤ r) (hd : 0 < d) (n : ℕ)
    (b : Fin (d*r) → V k r hr T a d n)
    (hb : IsBasis k r n hr (T.overlap n) a d b)
    (v : Fin (d*r) → V k r hr T a d (n+1))
    (hv : ∀ j, red k r hr T a d n (n+1) (Nat.le_succ n) (v j) = b j) :
    IsBasis k r (n+1) hr (T.overlap (n+1)) a d v := by
  obtain ⟨w, hw⟩ := positive_section_basis k r (n+1) hr h3
    (T.overlap (n+1)) (T.overlap_spec (n+1)) a d hd
  let e := LinearEquiv.ofBijective (synth k r hr T a d (n+1) w)
    ((isBasis_iff k r hr T a d (n+1) w).mp hw)
  apply (isBasis_iff k r hr T a d (n+1) v).mpr
  apply bijective_of_approx e _ (parameter k (n+1))
    (n+2) (parameter_pow k (n+1))
  intro s
  obtain ⟨c, hc⟩ := ((isBasis_iff k r hr T a d n b).mp hb).2
    (red k r hr T a d n (n+1) (Nat.le_succ n) s)
  choose c' hc' using fun j => truncReduce_surjective (PowerSeries k) PowerSeries.X
    n (n+1) (Nat.le_succ n) (c j)
  have hred : red k r hr T a d n (n+1) (Nat.le_succ n)
      (s - synth k r hr T a d (n+1) v c') = 0 := by
    rw [red_sub, red_synth]
    simp only [hv, hc', hc, sub_self]
  have hz : ∀ i, truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
      n (n+1) (Nat.le_succ n) ((s - synth k r hr T a d (n+1) v c').val i) = 0 :=
    fun i => congrArg (fun z : V k r hr T a d n => z.val i) hred
  obtain ⟨y, hy⟩ := (positive_sections_reduction k r hr h3 T a d hd
    n (n+1) (Nat.le_succ n)).2.2 (s - synth k r hr T a d (n+1) v c') |>.mp hz
  let y' : V k r hr T a d (n+1) := y
  refine ⟨c', parameter k (n+1)^n • y', ?_⟩
  have hs : s - synth k r hr T a d (n+1) v c' =
      parameter k (n+1)^(n+1) • y' := by
    exact Subtype.ext (funext hy)
  rw [smul_smul, ← pow_succ']
  exact sub_eq_iff_eq_add.mp hs |>.trans (add_comm _ _)

lemma exists_basis_lift (h3 : 3 ≤ r) (hd : 0 < d) (n : ℕ)
    (b : Fin (d*r) → V k r hr T a d n)
    (hb : IsBasis k r n hr (T.overlap n) a d b) :
    ∃ v : Fin (d*r) → V k r hr T a d (n+1),
      IsBasis k r (n+1) hr (T.overlap (n+1)) a d v ∧
      ∀ j, red k r hr T a d n (n+1) (Nat.le_succ n) (v j) = b j := by
  choose v hv using fun j => (positive_sections_reduction k r hr h3 T a d hd
    n (n+1) (Nat.le_succ n)).2.1 (b j)
  have hv' (j) : red k r hr T a d n (n+1) (Nat.le_succ n) (v j) = b j :=
    Subtype.ext (funext (hv j))
  exact ⟨v, lifted_basis k r hr T a d h3 hd n b hb v hv', hv'⟩


/-- A recursively lifted family commutes with all reductions, including the
identity and reductions to the special fiber. -/
lemma compatible_bases (h3 : 3 ≤ r) (hd : 0 < d) :
    ∃ b : ∀ n, Fin (d*r) → V k r hr T a d n,
      (∀ n, IsBasis k r n hr (T.overlap n) a d (b n)) ∧
      (∀ n N (h : n ≤ N) j, red k r hr T a d n N h (b N j) = b n j) := by
  let B := fun n => {b : Fin (d*r) → V k r hr T a d n //
    IsBasis k r n hr (T.overlap n) a d b}
  obtain ⟨b0, hb0⟩ := positive_section_basis k r 0 hr h3
    (T.overlap 0) (T.overlap_spec 0) a d hd
  let step : ∀ n, B n → B (n+1) := fun n b =>
    ⟨Classical.choose (exists_basis_lift k r hr T a d h3 hd n b.val b.property),
      (Classical.choose_spec (exists_basis_lift k r hr T a d h3 hd n b.val b.property)).1⟩
  let F : ∀ n, B n := Nat.rec (motive := B) ⟨b0, hb0⟩ step
  have hstep (n) (j) : red k r hr T a d n (n+1) (Nat.le_succ n) ((F (n+1)).val j) =
      (F n).val j :=
    (Classical.choose_spec (exists_basis_lift k r hr T a d h3 hd n (F n).val (F n).property)).2 j
  refine ⟨fun n => (F n).val, fun n => (F n).property, ?_⟩
  intro n N h j
  induction N, h using Nat.le_induction with
  | base =>
    apply Subtype.ext
    funext i
    exact reduce_self _ _ _ _
  | succ N h ih =>
    rw [← red_comp k r hr T a d n N (N+1) h (Nat.le_succ N), hstep, ih]

/-- Completeness and separatedness recover a unique power series from its
compatible genuine quotient classes. -/
lemma powerSeries_limit (c : ∀ n, R k n)
    (hc : ∀ n N (h : n ≤ N), truncReduce (PowerSeries k) PowerSeries.X n N h (c N) = c n) :
    ∃! f : PowerSeries k, ∀ n, trunc (PowerSeries k) PowerSeries.X n f = c n := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  choose v hv using fun n => Ideal.Quotient.mk_surjective (c n)
  let w : ℕ → PowerSeries k
    | 0 => 0
    | n+1 => v n
  have hcompat {m n : ℕ} (h : m ≤ n) :
      SModEq (I^m • ⊤ : Submodule (PowerSeries k) (PowerSeries k)) (w m) (w n) := by
    cases m with
    | zero => simp [I]
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        have hmn : m ≤ n := by omega
        have he : trunc (PowerSeries k) PowerSeries.X m (v m) =
            trunc (PowerSeries k) PowerSeries.X m (v n) := by
          change Ideal.Quotient.mk _ (v m) = _
          rw [hv]
          have hh := hc m n hmn
          rw [← hv n] at hh
          exact hh.symm
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using! he
  obtain ⟨f, hf⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (PowerSeries k)) hcompat
  have hf' (n) : trunc (PowerSeries k) PowerSeries.X n f = c n := by
    have h := hf (n+1)
    have he : trunc (PowerSeries k) PowerSeries.X n (v n) =
        trunc (PowerSeries k) PowerSeries.X n f := by
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using! h
    exact he.symm.trans (hv n)
  refine ⟨f, hf', ?_⟩
  intro g hg
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have he := (hg n).trans (hf' n).symm
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using! he


/-- Uniqueness at finite stages forces the coordinate systems themselves to
be compatible; completeness then gives exactly one full coefficient vector. -/
lemma formal_coordinates
    (b : ∀ n, Fin (d*r) → Sections k r n hr (T.overlap n) a d)
    (hb : ∀ n, IsBasis k r n hr (T.overlap n) a d (b n))
    (hbr : ∀ n N (h : n ≤ N) j i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((b N j).val i) = (b n j).val i)
    (s : ∀ n, Sections k r n hr (T.overlap n) a d)
    (hs : ∀ n N (h : n ≤ N) i,
      truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((s N).val i) = (s n).val i) :
    ∃! c : Fin (d*r) → PowerSeries k, ∀ n i,
      (s n).val i = ∑ j, base k n (trunc (PowerSeries k) PowerSeries.X n (c j)) *
        (b n j).val i := by
  choose c hc hu using fun n => hb n (s n)
  have hcr (n N : ℕ) (h : n ≤ N) :
      (fun j => truncReduce (PowerSeries k) PowerSeries.X n N h (c N j)) = c n := by
    apply hu n
    intro i
    have hh := congrArg
      (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h)
      (hc N i)
    simpa only [hs, map_sum, map_mul, reduce_base, hbr] using hh
  have hlim (j : Fin (d*r)) : ∃! f : PowerSeries k,
      ∀ n, trunc (PowerSeries k) PowerSeries.X n f = c n j :=
    powerSeries_limit k (fun n => c n j) (fun n N h => congrFun (hcr n N h) j)
  choose f hf hfu using hlim
  refine ⟨f, ?_, ?_⟩
  · intro n i
    simpa only [hf] using hc n i
  · intro g hg
    funext j
    apply hfu j
    intro n
    exact congrFun (hu n (fun j => trunc (PowerSeries k) PowerSeries.X n (g j)) (hg n)) j

end CompatibleFormalSectionBasisR0134

/-- The positive section modules admit bases compatible with every prescribed
reduction, and every compatible full section has unique power-series coordinates. -/
theorem compatible_formal_section_basis :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (a : Fin r → kˣ),
    ∀ d : ℕ, 0 < d → ArithmeticThetaPositiveLineR0134.FormalBasisFacts k r hr T a d := by
  intro k _ _ r hr h3 T a d hd
  obtain ⟨b, hb, hbr⟩ := CompatibleFormalSectionBasisR0134.compatible_bases k r hr T a d h3 hd
  have hbr' (n N : ℕ) (h : n ≤ N) (j : Fin (d*r)) (i : Fin r) :
      ArithmeticThetaInfinitesimalPolygonR0129.truncReduce
        (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k)
        n N h ((b N j).val i) = (b n j).val i :=
    congrArg (fun z : CompatibleFormalSectionBasisR0134.V k r hr T a d n => z.val i) (hbr n N h j)
  exact ⟨b, hb, hbr', CompatibleFormalSectionBasisR0134.formal_coordinates k r hr T a d b hb hbr'⟩

end ArithmeticThetaPositiveLineR0134
