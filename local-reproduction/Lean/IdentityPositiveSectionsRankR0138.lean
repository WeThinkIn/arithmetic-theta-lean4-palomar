import IdentityChartIdealR0138
import PositiveSectionBasisR0134

/-! Coordinates for the positive powers of the SINGLE marked ideal. -/
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaIdentitySectionsR0138
namespace IdentityPositiveSectionsRankR0138
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open PolygonCechKernelR0131
open ArithmeticThetaPositiveLineR0134.PositiveSectionBasisR0134
open LaurentPolynomial

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable (L : B k n true ≃+* LaurentPolynomial (R k n))
    (hL : LaurentPresentation k n L)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)

local instance nodeAlgebra : Algebra (R k n) (A k n) := (base k n).toAlgebra
local instance nodeModule : Module (R k n) (A k n) := nodeAlgebra.toModule
local instance nodeAction : DistribMulAction (R k n) (A k n) := nodeModule.toDistribMulAction
local instance nodeScalar : SMul (R k n) (A k n) := ⟨fun c x => base k n c * x⟩
local instance nodeFamilyScalar (r : ℕ) : SMul (R k n) (Fin r → A k n) :=
  ⟨fun c s i => base k n c * s i⟩

/-- The weight left after cancelling only the common horizontal factor. -/
def rwgt (r : ℕ) (hr : 0 < r) (i : Fin r) : LaurentPolynomial (R k n) :=
  if (next r hr i).val + 1 = r then 1 - C (parameter k n) * T (-1) else 1

def lwgt (r : ℕ) (i : Fin r) : LaurentPolynomial (R k n) :=
  if i.val = 0 then 1 - C (parameter k n) * T 1 else 1

def transition (r : ℕ) (d : ℕ) (i : Fin r) : LaurentPolynomial (R k n) :=
  if i.val + 1 = r then (-1)^d * T (-(d : ℤ)) else 1

lemma last_next (r : ℕ) (hr : 0 < r) (i : Fin r) :
    (next r hr i).val = 0 ↔ i.val + 1 = r := by
  exact (show (next r hr i).val = 0 ↔ next r hr i = zeroIndex r hr from
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩).trans
    (IdentityChartIdealR0138.next_zero_iff r hr i)

lemma next_ne_self (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r) (i : Fin r) :
    next r hr i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [next] at hval
  have hi := i.isLt
  by_cases he : i.val + 1 = r
  · simp [he] at hval; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega

include hL hE in
lemma compatible_iff_laurent (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (s : Fin r → A k n) :
    Compatible k r n hr E d s ↔ ∀ i : Fin r,
      leftMap L E (s i) * rwgt (k := k) (n := n) r hr i ^ d =
      rightMap L (s (next r hr i)) * lwgt (k := k) (n := n) r i ^ d *
        transition (k := k) (n := n) r d i := by
  unfold Compatible
  apply forall_congr'
  intro i
  rw [← L.injective.eq_iff]
  simp only [map_mul, map_pow]
  change leftMap L E (s i) * rightMap L (equation k r n (next r hr i)) ^ d =
    rightMap L (s (next r hr i)) * leftMap L E (equation k r n i) ^ d ↔ _
  by_cases hi : i.val + 1 = r
  · have hni := (last_next r hr i).2 hi
    have hi0 : i.val ≠ 0 := by omega
    have hnin : (next r hr i).val + 1 ≠ r := by omega
    have hl : leftMap L E (equation k r n i) = -(1 - T 1) * T (-1) := by
      simp only [equation, if_neg hi0, if_pos hi, one_mul, map_sub, map_one,
        left_y L hL E hE]
      have ht : (T 1 : LaurentPolynomial (R k n)) * T (-1) = 1 := by
        rw [← T_add]; norm_num
      linear_combination -ht
    have hr' : rightMap L (equation k r n (next r hr i)) = 1 - T 1 := by
      simp only [equation, if_pos hni, if_neg hnin, mul_one, map_sub, map_one,
        right_x L hL]
    rw [hl, hr']
    have hreg : IsRegular ((1 - T 1 : LaurentPolynomial (R k n)) ^ d) := by
      have h := laurent_linear_regular (1 : R k n)
      have hn : IsLeftRegular (-(T 1 - C (1 : R k n))) := by
        intro a b hab
        apply h.1
        simpa only [neg_mul, neg_inj] using hab
      have he : -(T 1 - C (1 : R k n)) = 1 - T 1 := by rw [map_one]; ring
      rw [he] at hn
      exact (⟨hn, hn.right_of_commute (fun _ => Commute.all _ _)⟩ : IsRegular (1 - T 1 : LaurentPolynomial (R k n))).pow d
    rw [mul_pow, neg_pow]
    simp only [rwgt, lwgt, transition, if_neg hnin, if_neg hi0, if_pos hi,
      one_pow, mul_one, T_pow, mul_neg_one]
    constructor
    · intro h
      apply hreg.1
      convert h using 1 <;> ring
    · intro h
      have hh := congrArg (((1 - T 1 : LaurentPolynomial (R k n)) ^ d) * ·) h
      convert hh using 1 <;> ring
  · have hni : (next r hr i).val ≠ 0 := mt (last_next r hr i).1 hi
    simp only [equation, if_neg hi, if_neg hni, mul_one, one_mul,
      apply_ite, map_sub, map_one, right_y L hL, left_x L hL E hE,
      rwgt, lwgt, transition, if_neg hi, mul_one]

/-- The actual cancelled overlap map. -/
def difference (r : ℕ) (hr : 0 < r) (d : ℕ) :
    (Fin r → A k n) →ₗ[R k n] (Fin r → LaurentPolynomial (R k n)) where
  toFun s i := leftMap L E (s i) * rwgt (k := k) (n := n) r hr i ^ d -
    rightMap L (s (next r hr i)) * lwgt (k := k) (n := n) r i ^ d *
      transition (k := k) (n := n) r d i
  map_add' s t := by funext i; simp only [Pi.add_apply, map_add]; ring
  map_smul' z s := by
    funext i
    change leftMap L E (base k n z * s i) * _ -
      rightMap L (base k n z * s (next r hr i)) * _ * _ =
        z • (leftMap L E (s i) * _ - rightMap L (s (next r hr i)) * _ * _)
    rw [map_mul, map_mul, left_base L hL E hE, right_base L hL, smul_eq_C_mul]
    ring

lemma compatible_iff_difference (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (s : Fin r → A k n) :
    Compatible k r n hr E d s ↔ difference L hL E hE r hr d s = 0 := by
  rw [compatible_iff_laurent L hL E hE r hr hr3]
  simp only [difference, LinearMap.coe_mk, AddHom.coe_mk,
    funext_iff, Pi.zero_apply, sub_eq_zero]

/-- Free modes occur only on chart zero; degree-zero components retain their
constant pivot. -/
def singlePivotIndex (r : ℕ) (hr : 0 < r) (d : ℕ) :
    (Fin d ⊕ (Fin r × ℤ)) ≃ (Fin r × ℤ) :=
  Equiv.ofBijective
    (fun z => match z with
      | Sum.inl j => (zeroIndex r hr, j)
      | Sum.inr p => if p.2 < 0 then p else
          (next r hr p.1, p.2 + if (next r hr p.1).val = 0 then (d : ℤ) else 0)) (by
      have hinj := (PolygonCechObstructionR0131.shift r hr).injective
      have hsurj := (PolygonCechObstructionR0131.shift r hr).surjective
      constructor
      · intro a b hab
        cases a with
        | inl a =>
          cases b with
          | inl b =>
            apply congrArg Sum.inl
            apply Fin.ext
            have h := congrArg Prod.snd hab
            simpa using h
          | inr b =>
            dsimp only at hab
            split_ifs at hab with hb hz
            · have h := congrArg Prod.snd hab; dsimp at h; omega
            · have h := congrArg Prod.snd hab; dsimp at h; omega
            · have h := congrArg (fun p : Fin r × ℤ => p.1.val) hab
              dsimp [zeroIndex] at h
              exact (hz h.symm).elim
        | inr a =>
          cases b with
          | inl b =>
            dsimp only at hab
            split_ifs at hab with ha hz
            · have h := congrArg Prod.snd hab; dsimp at h; omega
            · have h := congrArg Prod.snd hab; dsimp at h; omega
            · have h := congrArg (fun p : Fin r × ℤ => p.1.val) hab
              dsimp [zeroIndex] at h
              exact (hz h).elim
          | inr b =>
            dsimp only at hab
            by_cases ha : a.2 < 0 <;> by_cases hb : b.2 < 0
            · simpa only [if_pos ha, if_pos hb] using congrArg Sum.inr hab
            · simp only [if_pos ha, if_neg hb] at hab
              have h := congrArg Prod.snd hab
              dsimp at h
              split_ifs at h <;> omega
            · simp only [if_neg ha, if_pos hb] at hab
              have h := congrArg Prod.snd hab
              dsimp at h
              split_ifs at h <;> omega
            · simp only [if_neg ha, if_neg hb, Prod.mk.injEq] at hab
              have hab1 : a.1 = b.1 := hinj hab.1
              apply congrArg Sum.inr
              apply Prod.ext hab1
              have hh := hab.2
              rw [hab1] at hh
              omega
      · rintro ⟨i,j⟩
        by_cases hj : j < 0
        · exact ⟨Sum.inr (i,j), by simp [hj]⟩
        · by_cases hi : i.val = 0
          · by_cases hd : j < d
            · exact ⟨Sum.inl ⟨j.toNat, by omega⟩, Prod.ext (Fin.ext hi.symm) (by simp; omega)⟩
            · obtain ⟨a, ha⟩ := hsurj i
              change next r hr a = i at ha
              exact ⟨Sum.inr (a, j-d), by simp [ha, hi, show ¬j-(d:ℤ)<0 by omega]⟩
          · obtain ⟨a, ha⟩ := hsurj i
            change next r hr a = i at ha
            exact ⟨Sum.inr (a,j), by simp [hj,ha,hi]⟩)

section Chain
variable (S : Type*) [CommRing S]

/-- A finite chain shift of the overlap zero modes, with no wraparound. -/
def zeroShift (r : ℕ) : Module.End S (Fin r → LaurentPolynomial S) where
  toFun x i := if h : 0 < i.val then C ((x ⟨i.val-1, by omega⟩).coeff 0) else 0
  map_add' x y := by
    funext i
    by_cases h : 0 < i.val <;> simp [h, map_add]
  map_smul' c x := by
    funext i
    by_cases h : 0 < i.val <;> simp [h, ← smul_eq_C_mul, map_smul]

lemma zeroShift_pow_vanish (r p : ℕ) (x : Fin r → LaurentPolynomial S)
    (i : Fin r) (hi : i.val < p) : (zeroShift S r ^ p) x i = 0 := by
  induction p generalizing i with
  | zero => omega
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (if h : 0 < i.val then C (((zeroShift S r ^ p) x ⟨i.val-1, by omega⟩).coeff 0) else 0) = 0
    split_ifs with h
    · rw [ih _ (by simp only; omega)]; simp
    · rfl

lemma zeroShift_nilpotent (r : ℕ) : zeroShift S r ^ r = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  exact zeroShift_pow_vanish S r r x i i.isLt

/-- The constant pivot correction is an actual automorphism over every base. -/
def chainEquiv (r : ℕ) : (Fin r → LaurentPolynomial S) ≃ₗ[S]
    (Fin r → LaurentPolynomial S) :=
  LinearEquiv.ofBijective (1 - zeroShift S r)
    ((Module.End.isUnit_iff _).mp
      ((show IsNilpotent (zeroShift S r) from ⟨r, zeroShift_nilpotent S r⟩).isUnit_one_sub))

end Chain

/-- A pivot block with an invertible reduction gives a free kernel over a
nilpotent thickening. The reduction is a proved map, not a rank assumption. -/
def kernelEquivOfPivotReduction {S F Q : Type*} [CommRing S]
    [AddCommGroup F] [Module S F] [AddCommGroup Q] [Module S Q]
    (t : S) (N : ℕ) (ht : t^N=0) (f : (F × Q) →ₗ[S] Q)
    (e : Q ≃ₗ[S] Q) (he : ∀ y, ∃ z, e y - f (0,y) = t • z) :
    LinearMap.ker f ≃ₗ[S] F := by
  let g := e.symm.toLinearMap.comp f
  have hg : ∀ y, ∃ z, y - g (0,y) = t • z := by
    intro y
    obtain ⟨z,hz⟩ := he y
    refine ⟨e.symm z, ?_⟩
    have hh := congrArg e.symm hz
    simpa only [map_sub, map_smul, LinearEquiv.symm_apply_apply, g,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using hh
  exact (kernelEquivCod e.symm f).symm.trans
    (kernelEquivOfNilpotentPivot t N ht g hg)

/-- Unit diagonal of the unscaled pivot block. -/
def diagUnit (r d : ℕ) (p : Fin r × ℤ) : (R k n)ˣ :=
  if p.2 < 0 then 1 else if p.1.val + 1 = r then -((-1)^d) else -1

def singlePivotBasis (r : ℕ) (hr : 0 < r) (d : ℕ) :
    Module.Basis (Fin d ⊕ (Fin r × ℤ)) (R k n) (Fin r → A k n) :=
  ((nodeFamilyBasis L hL E hE r).reindex (singlePivotIndex r hr d).symm).unitsSMul
    (fun z => match z with | Sum.inl _ => 1 | Sum.inr p => (diagUnit (k := k) (n := n) r d p)⁻¹)

lemma singlePivotBasis_pivot (r : ℕ) (hr : 0 < r) (d : ℕ) (p : Fin r × ℤ) :
    singlePivotBasis L hL E hE r hr d (Sum.inr p) =
    (↑((diagUnit (k := k) (n := n) r d p)⁻¹) : R k n) •
      nodeFamilyBasis L hL E hE r (singlePivotIndex r hr d (Sum.inr p)) := by
  simp only [singlePivotBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Units.smul_def]

variable {Q : Type u} [CommRing Q] (q : LaurentPolynomial (R k n) →+* Q)
    (hq : q (C (parameter k n)) = 0)
include hq

lemma quotient_rwgt (r : ℕ) (hr : 0 < r) (i : Fin r) :
    q (rwgt (k := k) (n := n) r hr i) = 1 := by
  unfold rwgt
  split_ifs <;> simp [hq]

lemma quotient_lwgt (r : ℕ) (i : Fin r) :
    q (lwgt (k := k) (n := n) r i) = 1 := by
  unfold lwgt
  split_ifs <;> simp [hq]

lemma quotient_difference_single (r : ℕ) (hr : 0 < r) (d : ℕ)
    (i : Fin r) (j : ℤ) (l : Fin r) :
    q (difference L hL E hE r hr d (Pi.single i (monomial k n j)) l) =
      (if l = i ∧ j ≤ 0 then q (T j) else 0) -
      (if next r hr l = i ∧ 0 ≤ j then q (T j) else 0) *
        q (transition (k := k) (n := n) r d l) := by
  classical
  simp only [difference, LinearMap.coe_mk, AddHom.coe_mk,
    map_sub, map_mul, map_pow, quotient_rwgt q hq, quotient_lwgt q hq,
    one_pow, mul_one, Pi.single_apply, apply_ite, map_zero,
    quotient_left_monomial L hL E hE q hq, quotient_right_monomial L hL E hE q hq]
  split_ifs <;> simp_all

lemma quotient_negative_pivot (r : ℕ) (hr : 0 < r) (d : ℕ)
    (i : Fin r) (j : ℤ) (hj : j < 0) (l : Fin r) :
    q (difference L hL E hE r hr d
      (singlePivotBasis L hL E hE r hr d (Sum.inr (i,j))) l) =
      q (overlapFamilyBasis (k := k) (n := n) r (i,j) l) := by
  rw [singlePivotBasis_pivot]
  have hs : (↑((diagUnit (k := k) (n := n) r d (i,j))⁻¹) : R k n) = 1 := by
    simp [diagUnit, hj]
  rw [hs]
  have hone (v : Fin r → A k n) : (1 : R k n) • v = v := by
    funext a
    change base k n 1 * v a = v a
    rw [map_one, one_mul]
  rw [hone]
  simp only [singlePivotIndex, Equiv.ofBijective_apply, if_pos hj, nodeFamilyBasis_apply]
  rw [quotient_difference_single L hL E hE q hq]
  simp only [show j ≤ 0 by omega, show ¬0 ≤ j by omega, and_true, and_false,
    if_false, zero_mul, sub_zero, overlapFamilyBasis_apply, Pi.single_apply, apply_ite, map_zero]
  split_ifs <;> rfl

lemma quotient_positive_pivot (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d) (i : Fin r) (j : ℤ) (hj : 0 ≤ j) (l : Fin r) :
    q (difference L hL E hE r hr d
      (singlePivotBasis L hL E hE r hr d (Sum.inr (i,j))) l) =
      q (overlapFamilyBasis (k := k) (n := n) r (i,j) l) -
        if j = 0 ∧ i.val + 1 < r then q (Pi.single (M := fun _ : Fin r => LaurentPolynomial (R k n)) (next r hr i) 1 l) else 0 := by
  have hn : ¬ j < 0 := by omega
  have hshift (l : Fin r) : next r hr l = next r hr i ↔ l = i :=
    (PolygonCechObstructionR0131.shift r hr).injective.eq_iff
  rw [singlePivotBasis_pivot, map_smul]
  simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, nodeFamilyBasis_apply,
    singlePivotIndex, Equiv.ofBijective_apply, if_neg hn]
  rw [quotient_difference_single L hL E hE q hq]
  by_cases hi : i.val + 1 = r
  · have hni := (last_next r hr i).2 hi
    have hpos : 0 < j + (d : ℤ) := by omega
    have hu : (↑((diagUnit (k := k) (n := n) r d (i,j))⁻¹) : R k n) *
        (-1 : R k n)^d = -1 := by
      have h := Units.inv_mul (diagUnit (k := k) (n := n) r d (i,j))
      simp only [diagUnit, if_neg hn, if_pos hi, Units.val_neg, Units.val_pow_eq_pow_val,
        Units.val_one] at h ⊢
      linear_combination -h
    have hqU : q (C (↑((diagUnit (k := k) (n := n) r d (i,j))⁻¹) : R k n)) *
        q ((-1 : LaurentPolynomial (R k n))^d) = -1 := by
      simpa only [map_mul, map_neg, map_one, map_pow] using congrArg (fun z => q (C z)) hu
    simp only [if_pos hni, show ¬j+(d:ℤ)≤0 by omega, and_false, if_false,
      show 0≤j+(d:ℤ) by omega, and_true, hshift,
      show ¬(j=0 ∧ i.val+1<r) by omega, sub_zero, zero_sub,
      overlapFamilyBasis_apply, Pi.single_apply, apply_ite, map_zero]
    by_cases hl : l = i
    · subst l
      simp only [if_pos rfl, transition, if_pos hi, map_mul, map_pow, map_neg, map_one]
      have ht : q (T (j + d) : LaurentPolynomial (R k n)) * q (T (-(d:ℤ))) = q (T j) := by
        rw [← map_mul, ← T_add]; congr 2; omega
      calc
        _ = -(q (C (↑((diagUnit (k := k) (n := n) r d (i,j))⁻¹) : R k n)) *
          q ((-1 : LaurentPolynomial (R k n))^d)) *
          (q (T (j+d)) * q (T (-(d:ℤ)))) := by simp only [map_pow, map_neg, map_one, ite_true]; ring
        _ = _ := by rw [hqU, ht]; ring
    · simp [hl]
  · have hni : (next r hr i).val ≠ 0 := mt (last_next r hr i).1 hi
    have hit : i.val + 1 < r := by have hh := i.isLt; omega
    have hu : (↑((diagUnit (k := k) (n := n) r d (i,j))⁻¹) : R k n) = -1 := by
      simp [diagUnit, hn, hi]
    rw [hu]
    simp only [if_neg hni, add_zero, hj, and_true, hshift, map_neg, map_one,
      overlapFamilyBasis_apply, Pi.single_apply, apply_ite, map_zero, hit]
    by_cases hl : l = i
    · subst l
      have hne : i ≠ next r hr i := (next_ne_self r hr hr3 i).symm
      simp [hne, transition, hi]
    · have hle : (j ≤ 0) ↔ j = 0 := by omega
      simp only [if_neg hl, zero_mul, sub_zero, hle]
      by_cases hz : j = 0
      · subst j
        simp only [le_refl, and_true, if_pos rfl, T_zero, map_one]
        split_ifs <;> ring
      · simp [hz]

omit hq in
lemma zeroShift_overlap (r : ℕ) (hr : 0 < r) (i : Fin r) (j : ℤ) :
    zeroShift (R k n) r (overlapFamilyBasis (k := k) (n := n) r (i,j)) =
      if j = 0 ∧ i.val + 1 < r then Pi.single (next r hr i) 1 else 0 := by
  classical
  funext l
  rw [overlapFamilyBasis_apply]
  change (if h : 0 < l.val then C ((Pi.single (M := fun _ : Fin r => LaurentPolynomial (R k n)) i (T j) ⟨l.val-1, by omega⟩).coeff 0) else 0) = _
  by_cases hl : 0 < l.val
  · rw [dif_pos hl]
    have hp : (⟨l.val-1, by omega⟩ : Fin r) = i ↔ l = next r hr i ∧ i.val + 1 < r := by
      constructor
      · intro h
        have hv := congrArg Fin.val h
        have hli := l.isLt
        have hit : i.val + 1 < r := by dsimp at hv; omega
        refine ⟨Fin.ext ?_, hit⟩
        simp only [next, Nat.mod_eq_of_lt hit]
        dsimp at hv
        omega
      · rintro ⟨h,hit⟩
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [next, Nat.mod_eq_of_lt hit] at hv
        dsimp
        omega
    simp only [Pi.single_apply, apply_ite, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, map_zero, T_apply, hp]
    by_cases hj : j=0 <;> by_cases hi : i.val+1<r <;> by_cases hli : l=next r hr i <;>
      simp [hj,hi,hli,eq_comm]
  · have hz : l.val = 0 := by omega
    rw [dif_neg hl]
    by_cases h : j=0 ∧ i.val+1<r
    · rw [if_pos h]
      have hne : l ≠ next r hr i := by
        intro he
        have hv := congrArg Fin.val he
        simp only [next, Nat.mod_eq_of_lt h.2] at hv
        omega
      simp [Pi.single_eq_of_ne hne]
    · simp [h]

lemma quotient_pivot_chain (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d) (p : Fin r × ℤ) (l : Fin r) :
    q (difference L hL E hE r hr d
      (singlePivotBasis L hL E hE r hr d (Sum.inr p)) l) =
    q (chainEquiv (R k n) r (overlapFamilyBasis (k := k) (n := n) r p) l) := by
  change _ = q ((overlapFamilyBasis (k := k) (n := n) r p -
    zeroShift (R k n) r (overlapFamilyBasis (k := k) (n := n) r p)) l)
  rw [zeroShift_overlap r hr p.1 p.2]
  by_cases hj : p.2 < 0
  · rw [quotient_negative_pivot L hL E hE q hq r hr d p.1 p.2 hj l]
    simp [show p.2 ≠ 0 by omega]
  · rw [quotient_positive_pivot L hL E hE q hq r hr hr3 d hd p.1 p.2 (by omega) l]
    split_ifs <;> simp [map_sub]

omit hq in
/-- Every concrete pivot differs from the finite-chain pivot by a multiple
of the actual base parameter. -/
lemma pivot_error (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d) (p : Fin r × ℤ) :
    ∃ z : Fin r → LaurentPolynomial (R k n),
      chainEquiv (R k n) r (overlapFamilyBasis (k := k) (n := n) r p) -
        difference L hL E hE r hr d
          (singlePivotBasis L hL E hE r hr d (Sum.inr p)) = parameter k n • z := by
  classical
  have hp (l : Fin r) := @quotient_pivot_chain k _ _ n L hL E hE
    (LaurentPolynomial (R k n) ⧸ Ideal.span ({C (parameter k n)} : Set (LaurentPolynomial (R k n))))
    (Ideal.Quotient.commRing _) (parameterQuotient (k := k) (n := n))
    (parameterQuotient_parameter (k := k) (n := n)) r hr hr3 d hd p l
  choose z hz using fun l => (parameterQuotient_eq_iff (k := k) (n := n) _ _).mp (hp l).symm
  exact ⟨z, funext hz⟩

omit hq in
/-- Columnwise reduction against a known automorphism suffices for the free
kernel criterion. -/
def kernelEquivOfColumns {S F J : Type*} [CommRing S]
    (t : S) (N : ℕ) (ht : t^N=0)
    (f : ((F ⊕ J) →₀ S) →ₗ[S] (J →₀ S))
    (a : (J →₀ S) ≃ₗ[S] (J →₀ S))
    (hf : ∀ j, ∃ z, a (Finsupp.single j 1) - f (Finsupp.single (Sum.inr j) 1) = t • z) :
    LinearMap.ker f ≃ₗ[S] (F →₀ S) := by
  classical
  let e := Finsupp.sumFinsuppLEquivProdFinsupp (M := S) (α := F) (β := J) S
  let g := f.comp e.symm.toLinearMap
  have hs (j : J) : e.symm (0, Finsupp.single j 1) = Finsupp.single (Sum.inr j) 1 := by
    ext z
    cases z <;> simp [e, Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl,
      Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr]
  have hp : ∀ y : J →₀ S, ∃ z, a y - g (0,y) = t • z := by
    have hh := finsupp_image_divisible (I := J) t
      (a.toLinearMap - g.comp (LinearMap.inr S (F →₀ S) (J →₀ S))) (by
        intro j
        change ∃ z, a (Finsupp.single j 1) - f (e.symm (0,Finsupp.single j 1)) = t • z
        rw [hs]
        exact hf j)
    intro y
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.inr_apply] using hh y
  exact (kernelEquivDom e.symm f).symm.trans
    (kernelEquivOfPivotReduction t N ht g a hp)

omit hq in
/-- The kernel has d structural coordinates, without a finrank shortcut. -/
def kernelCoordinates (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r)
    (d : ℕ) (hd : 0 < d) :
    LinearMap.ker (difference L hL E hE r hr d) ≃ₗ[R k n] (Fin d →₀ R k n) := by
  let b := singlePivotBasis L hL E hE r hr d
  let c := overlapFamilyBasis (k := k) (n := n) r
  let delta := difference L hL E hE r hr d
  let g := delta.comp b.repr.symm.toLinearMap
  let f := c.repr.toLinearMap.comp g
  let a := c.repr.symm.trans ((chainEquiv (R k n) r).trans c.repr)
  have hf (p : Fin r × ℤ) : ∃ z,
      a (Finsupp.single p 1) - f (Finsupp.single (Sum.inr p) 1) = parameter k n • z := by
    obtain ⟨z,hz⟩ := pivot_error L hL E hE r hr hr3 d hd p
    refine ⟨c.repr z, ?_⟩
    have hh := congrArg c.repr hz
    change c.repr (chainEquiv (R k n) r (c p) - delta (b (Sum.inr p))) =
      c.repr (parameter k n • z) at hh
    rw [map_sub, map_smul] at hh
    simpa only [a, f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, Module.Basis.repr_symm_single_one] using hh
  let e := kernelEquivOfColumns (parameter k n) (n+1) (parameter_pow k n) f a hf
  exact (kernelEquivDom b.repr.symm delta).symm.trans
    ((kernelEquivCod c.repr g).symm.trans e)

omit hq in
/-- The set-level section definition and the linear kernel have exactly the
same numerator families. -/
def sectionsKernel (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r) (d : ℕ) :
    Sections k r n hr E d ≃ LinearMap.ker (difference L hL E hE r hr d) where
  toFun s := ⟨s.val, (compatible_iff_difference L hL E hE r hr hr3 d s.val).mp s.property⟩
  invFun s := ⟨s.val, (compatible_iff_difference L hL E hE r hr hr3 d s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit hq in
include L hL hE in
lemma basis_exists (r : ℕ) (hr : 0 < r) (hr3 : 3 ≤ r) (d : ℕ) (hd : 0 < d) :
    ∃ b : Fin d → Sections k r n hr E d, IsBasis k E d b := by
  let b : Module.Basis (Fin d) (R k n) (LinearMap.ker (difference L hL E hE r hr d)) :=
    Finsupp.basisSingleOne.map (kernelCoordinates L hL E hE r hr hr3 d hd).symm
  refine ⟨fun j => (sectionsKernel L hL E hE r hr hr3 d).symm (b j), ?_⟩
  intro s
  exact basis_unique_chart_coordinates _ b (sectionsKernel L hL E hE r hr hr3 d s)

end IdentityPositiveSectionsRankR0138

/-- Every positive power of the single marked divisor has exactly d unique
coordinates over the actual truncated base, including degree one. -/
theorem identity_positive_sections_rank :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ D : ArithmeticThetaInfinitesimalPolygonR0129.Atlas k r n hr E,
    ∀ d : ℕ, 0 < d → ∃ b : Fin d → ArithmeticThetaIdentitySectionsR0138.Sections k r n hr E d,
      ArithmeticThetaIdentitySectionsR0138.IsBasis k E d b := by
  intro k _ _ r n hr hr3 E hE _D d hd
  obtain ⟨L,hL,_⟩ := ArithmeticThetaPolygonCohomologyR0131.truncated_laurent_presentation k n
  exact IdentityPositiveSectionsRankR0138.basis_exists L hL E hE r hr hr3 d hd

end ArithmeticThetaIdentitySectionsR0138
