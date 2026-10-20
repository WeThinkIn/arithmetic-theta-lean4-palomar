module

public import PositiveLineSectionsDefinitionsR0134
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.Basis.SMul

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! Coordinate tools for the positive-section basis construction.
All helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPositiveLineR0134
namespace PositiveSectionBasisR0134
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaPolygonCartierR0133
open PolygonCechKernelR0131

section NilpotentLinearAlgebra
variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- A linear error whose image is divisible by a nilpotent scalar is nilpotent.
No finite generation or freeness assumption is needed. -/
lemma nilpotent_of_image_divisible (t : S) (N : ℕ) (ht : t ^ N = 0)
    (f : Module.End S M) (hf : ∀ x, ∃ y, f x = t • y) : f ^ N = 0 := by
  have hp : ∀ m x, ∃ y, (f ^ m) x = t ^ m • y := by
    intro m
    induction m with
    | zero => intro x; exact ⟨x, by simp⟩
    | succ m ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := hf y
      refine ⟨z, ?_⟩
      rw [pow_succ', Module.End.mul_apply, hy, map_smul, hz, smul_smul, pow_succ]
  ext x
  obtain ⟨y, hy⟩ := hp N x
  simpa [ht] using hy

/-- An endomorphism equal to the identity modulo a nilpotent scalar is
bijective even on an infinite module. -/
lemma bijective_of_nilpotent_error (t : S) (N : ℕ) (ht : t ^ N = 0)
    (f : Module.End S M) (hf : ∀ x, ∃ y, x - f x = t • y) :
    Function.Bijective f := by
  have hn : IsNilpotent (1 - f) :=
    ⟨N, nilpotent_of_image_divisible t N ht (1 - f) hf⟩
  apply (Module.End.isUnit_iff f).mp
  simpa only [sub_sub_cancel] using hn.isUnit_one_sub

/-- A deformation of the second projection retains the first factor as its
kernel. The divisibility condition is a conclusion to establish for the
concrete coordinate map, rather than a freeness assumption. -/
def kernelEquivOfNilpotentError {F Q : Type*} [AddCommGroup F] [Module S F]
    [AddCommGroup Q] [Module S Q] (t : S) (N : ℕ) (ht : t ^ N = 0)
    (f : (F × Q) →ₗ[S] Q) (hf : ∀ x : F × Q, ∃ y, x.2 - f x = t • y) :
    LinearMap.ker f ≃ₗ[S] F := by
  let g : Module.End S (F × Q) := (LinearMap.fst S F Q).prod f
  have hg : Function.Bijective g := by
    apply bijective_of_nilpotent_error t N ht
    intro x
    obtain ⟨y, hy⟩ := hf x
    exact ⟨(0, y), by ext <;> simp [g, hy]⟩
  let e : (F × Q) ≃ₗ[S] (F × Q) := LinearEquiv.ofBijective g hg
  have he (x : F × Q) : e x = (x.1, f x) := rfl
  have hi (y : F) : f (e.symm (y, 0)) = 0 := by
    have h := congrArg Prod.snd (e.apply_symm_apply (y, 0))
    exact h
  refine
    { toFun := fun x => x.val.1
      invFun := fun y => ⟨e.symm (y, 0), hi y⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro x
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply, he]
    exact Prod.ext rfl x.property.symm
  · intro y
    exact congrArg Prod.fst (e.apply_symm_apply (y, 0))

/-- Only the pivot block needs to equal the identity modulo the nilpotent
parameter. The free columns may have arbitrary images. -/
def kernelEquivOfNilpotentPivot {F Q : Type*} [AddCommGroup F] [Module S F]
    [AddCommGroup Q] [Module S Q] (t : S) (N : ℕ) (ht : t ^ N = 0)
    (f : (F × Q) →ₗ[S] Q) (hf : ∀ y : Q, ∃ z, y - f (0, y) = t • z) :
    LinearMap.ker f ≃ₗ[S] F := by
  let g : Module.End S Q := f.comp (LinearMap.inr S F Q)
  have hg : Function.Bijective g := bijective_of_nilpotent_error t N ht g hf
  let e : Q ≃ₗ[S] Q := LinearEquiv.ofBijective g hg
  have he (y : Q) : e y = f (0, y) := rfl
  have hd (x : F × Q) : f x = f (x.1, 0) + e x.2 := by
    rw [he, ← map_add]
    congr 1
    ext <;> simp
  have hi (x : F) : f (x, -(e.symm (f (x, 0)))) = 0 := by
    rw [hd, map_neg, e.apply_symm_apply]
    exact add_neg_cancel _
  refine
    { toFun := fun x => x.val.1
      invFun := fun x => ⟨(x, -(e.symm (f (x, 0)))), hi x⟩
      left_inv := ?_
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  intro x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change -(e.symm (f (x.val.1, 0))) = x.val.2
  apply e.injective
  rw [map_neg, e.apply_symm_apply]
  have hx := x.property
  change f x.val = 0 at hx
  rw [hd] at hx
  exact (eq_neg_of_add_eq_zero_right hx).symm

/-- Checking divisibility on the standard generators checks it on every
finitely supported coefficient vector. -/
lemma finsupp_image_divisible {I Q : Type*} [AddCommGroup Q] [Module S Q]
    (t : S) (f : (I →₀ S) →ₗ[S] Q)
    (hf : ∀ i, ∃ y, f (Finsupp.single i 1) = t • y) :
    ∀ c, ∃ y, f c = t • y := by
  intro c
  classical
  choose y hy using hf
  let g := Finsupp.linearCombination S y
  have hfg : f = t • g := by
    apply Finsupp.lhom_ext
    intro i c
    have hc : Finsupp.single i c = c • Finsupp.single i (1 : S) := by simp
    rw [hc, map_smul, hy]
    change c • (t • y i) = t • g (c • Finsupp.single i 1)
    rw [map_smul]
    simp only [g, Finsupp.linearCombination_single, one_smul]
    exact smul_comm c t (y i)
  exact ⟨g c, by rw [hfg]; rfl⟩

/-- Transport a kernel along a genuine coordinate equivalence in the domain. -/
def kernelEquivDom {V W Q : Type*} [AddCommGroup V] [Module S V]
    [AddCommGroup W] [Module S W] [AddCommGroup Q] [Module S Q]
    (e : V ≃ₗ[S] W) (f : W →ₗ[S] Q) :
    LinearMap.ker (f.comp e.toLinearMap) ≃ₗ[S] LinearMap.ker f where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by
    change f (e (e.symm y.val)) = 0
    simpa using y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' c x := Subtype.ext (e.map_smul c x.val)

/-- Changing coordinates in the codomain does not change the kernel. -/
def kernelEquivCod {V W Q : Type*} [AddCommGroup V] [Module S V]
    [AddCommGroup W] [Module S W] [AddCommGroup Q] [Module S Q]
    (e : W ≃ₗ[S] Q) (f : V →ₗ[S] W) :
    LinearMap.ker (e.toLinearMap.comp f) ≃ₗ[S] LinearMap.ker f where
  toFun x := ⟨x.val, e.injective (by simpa using x.property)⟩
  invFun y := ⟨y.val, by change e (f y.val) = 0; rw [y.property, map_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A pivot-column criterion for a free kernel. Only the pivot columns are
constrained; no rank, finite-generation, or cohomological assumption appears. -/
def kernelEquivOfPivotColumns {F J : Type*} (t : S) (N : ℕ) (ht : t ^ N = 0)
    (f : ((F ⊕ J) →₀ S) →ₗ[S] (J →₀ S))
    (hf : ∀ j, ∃ y, Finsupp.single j 1 - f (Finsupp.single (Sum.inr j) 1) = t • y) :
    LinearMap.ker f ≃ₗ[S] (F →₀ S) := by
  classical
  let e := Finsupp.sumFinsuppLEquivProdFinsupp (M := S) (α := F) (β := J) S
  let g := f.comp e.symm.toLinearMap
  have hs (j : J) : e.symm (0, Finsupp.single j 1) = Finsupp.single (Sum.inr j) 1 := by
    ext z
    cases z <;> simp [e, Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl,
      Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr]
  have hp : ∀ y : J →₀ S, ∃ z, y - g (0, y) = t • z := by
    have hh := finsupp_image_divisible (I := J) t
      (LinearMap.id - g.comp (LinearMap.inr S (F →₀ S) (J →₀ S))) (by
        intro j
        change ∃ y, Finsupp.single j 1 - f (e.symm (0, Finsupp.single j 1)) = t • y
        rw [hs]
        exact hf j)
    intro y
    simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.inr_apply] using hh y
  exact (kernelEquivDom e.symm f).symm.trans (kernelEquivOfNilpotentPivot t N ht g hp)
/-- A module basis of a submodule of chart families has the explicit unique
coordinate property used by the source statement. -/
lemma basis_unique_chart_coordinates {A₀ I J : Type*} [CommRing A₀] [Algebra S A₀]
    [Fintype I] [Fintype J] (V : Submodule S (I → A₀))
    (b : Module.Basis J S V) (s : V) :
    ∃! c : J → S, ∀ i, s.val i = ∑ j, algebraMap S A₀ (c j) * (b j).val i := by
  classical
  refine ⟨fun j => b.repr s j, ?_, ?_⟩
  · intro i
    have h := congrArg (fun w : V => w.val i) (b.sum_repr s)
    simpa only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,
      SetLike.val_smul, Pi.smul_apply, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply] using h.symm
  · intro c hc
    have hv : (∑ j, c j • b j : V) = s := by
      apply Subtype.ext
      funext i
      simpa [Algebra.smul_def, Pi.algebraMap_apply] using (hc i).symm
    funext j
    have h := congrArg (fun w => b.repr w j) hv
    simpa only [b.repr_sum_self] using h
end NilpotentLinearAlgebra

section CoordinateIndices
variable {I : Type*}

/-- The free indices are the `d` nonnegative modes below `d` on each chart.
Negative pivot modes stay on their chart; nonnegative pivot modes are shifted
to the next chart and raised by `d`. -/
def pivotIndex (s : Equiv.Perm I) (d : ℕ) :
    ((I × Fin d) ⊕ (I × ℤ)) ≃ (I × ℤ) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl p => (p.1, (p.2 : ℤ))
      | Sum.inr p => if p.2 < 0 then p else (s p.1, p.2 + d)) (by
      constructor
      · intro x y h
        cases x with
        | inl x =>
          cases y with
          | inl y =>
            have h₁ := congrArg Prod.fst h
            have h₂ := congrArg Prod.snd h
            congr 1
            exact Prod.ext h₁ (Fin.ext (by simpa using h₂))
          | inr y =>
            dsimp only at h
            split_ifs at h with hy
            all_goals have h₂ := congrArg Prod.snd h; simp only at h₂; omega
        | inr x =>
          cases y with
          | inl y =>
            dsimp only at h
            split_ifs at h with hx
            all_goals have h₂ := congrArg Prod.snd h; simp only at h₂; omega
          | inr y =>
            dsimp only at h
            split_ifs at h with hx hy hy
            · exact congrArg Sum.inr h
            · have h₂ := congrArg Prod.snd h; simp only at h₂; omega
            · have h₂ := congrArg Prod.snd h; simp only at h₂; omega
            · have h₁ := congrArg Prod.fst h
              have h₂ := congrArg Prod.snd h
              congr 1
              exact Prod.ext (s.injective h₁) (by simp only at h₂; omega)
      · rintro ⟨i, j⟩
        by_cases hj : j < 0
        · exact ⟨Sum.inr (i, j), by simp [hj]⟩
        · by_cases hd : j < d
          · exact ⟨Sum.inl (i, ⟨j.toNat, by omega⟩), by simp; omega⟩
          · exact ⟨Sum.inr (s.symm i, j - d), by
              simp [show ¬j - (d : ℤ) < 0 by omega]⟩)

@[simp] lemma pivotIndex_free (s : Equiv.Perm I) (d : ℕ) (i : I) (j : Fin d) :
    pivotIndex s d (Sum.inl (i, j)) = (i, (j : ℤ)) := rfl

@[simp] lemma pivotIndex_pivot (s : Equiv.Perm I) (d : ℕ) (i : I) (j : ℤ) :
    pivotIndex s d (Sum.inr (i, j)) = if j < 0 then (i, j) else (s i, j+d) := rfl

/-- Split every finitely supported node coefficient family into its free
window and the reindexed Laurent pivot family. -/
def splitCoefficients (S : Type*) [CommRing S] (s : Equiv.Perm I) (d : ℕ) :
    ((I × ℤ) →₀ S) ≃ₗ[S] (((I × Fin d) →₀ S) × ((I × ℤ) →₀ S)) :=
  (Finsupp.domLCongr (pivotIndex s d).symm).trans (Finsupp.sumFinsuppLEquivProdFinsupp S)

def familyCoefficients (S : Type*) [CommRing S] [Fintype I] :
    ((I × ℤ) →₀ S) ≃ₗ[S] (I → ℤ →₀ S) :=
  (Finsupp.domLCongr (Equiv.sigmaEquivProd I ℤ).symm).trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp (ιs := fun _ : I => ℤ) (M := S) S)

@[simp] lemma familyCoefficients_apply (S : Type*) [CommRing S] [Fintype I]
    (c : (I × ℤ) →₀ S) (i : I) (j : ℤ) : familyCoefficients S c i j = c (i, j) := rfl

@[simp] lemma familyCoefficients_single (S : Type*) [CommRing S] [Fintype I] [DecidableEq I]
    (i : I) (j : ℤ) (c : S) :
    familyCoefficients S (Finsupp.single (i, j) c) =
      Pi.single i (Finsupp.single j c) := by
  classical
  funext z
  ext l
  simp only [familyCoefficients_apply,
    Pi.single_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hz : z = i
  · subst z; simp [Finsupp.single_apply]
  · simp [hz, Ne.symm hz]

def familyLaurentEquiv (S : Type*) [CommRing S] [Fintype I] :
    ((I × ℤ) →₀ S) ≃ₗ[S] (I → LaurentPolynomial S) :=
  (familyCoefficients S).trans (LinearEquiv.piCongrRight fun _ =>
    (AddMonoidAlgebra.coeffLinearEquiv S : LaurentPolynomial S ≃ₗ[S] (ℤ →₀ S)).symm)

@[simp] lemma familyLaurentEquiv_coeff (S : Type*) [CommRing S] [Fintype I]
    (c : (I × ℤ) →₀ S) (i : I) (j : ℤ) :
    (familyLaurentEquiv S c i).coeff j = c (i,j) := rfl

@[simp] lemma familyLaurentEquiv_single (S : Type*) [CommRing S] [Fintype I]
    [DecidableEq I] (i : I) (j : ℤ) :
    familyLaurentEquiv S (Finsupp.single (i,j) 1) =
      Pi.single i (LaurentPolynomial.T j) := by
  funext l
  ext m
  rw [familyLaurentEquiv_coeff]
  by_cases hl : l = i
  · subst l
    simp [Pi.single_eq_same, LaurentPolynomial.T_apply, Finsupp.single_apply,
      AddMonoidAlgebra.coeff_single]
  · simp [Pi.single_eq_of_ne hl, Finsupp.single_apply, Ne.symm hl]
end CoordinateIndices

section LaurentRegularity
open LaurentPolynomial
variable {S : Type*} [CommRing S]

/-- The marked Laurent factor is regular over arbitrary coefficient rings,
including the nonreduced truncated base. -/
lemma laurent_linear_regular (a : S) : IsRegular (T 1 - C a) := by
  have hz : ∀ p : LaurentPolynomial S, (T 1 - C a) * p = 0 → p = 0 := by
    intro p hp
    obtain ⟨m, q, hq⟩ := exists_T_pow p
    have hpoly : (Polynomial.X - Polynomial.C a) * q = 0 := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C, hq,
        ← mul_assoc, hp, zero_mul, map_zero]
    have hq0 : q = 0 := (Polynomial.monic_X_sub_C a).isRegular.left
      (by simpa using hpoly)
    apply (isUnit_T (R := S) (m : ℤ)).mul_left_cancel
    simpa [hq0] using hq.symm
  have hl : IsLeftRegular (T 1 - C a) := by
    intro p q hpq
    change (T 1 - C a) * p = (T 1 - C a) * q at hpq
    exact sub_eq_zero.mp (hz (p - q) (by rw [mul_sub, hpq, sub_self]))
  exact ⟨hl, hl.right_of_commute (fun _ => Commute.all _ _)⟩
end LaurentRegularity

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable (L : B k n true ≃+* LaurentPolynomial (R k n))
    (hL : LaurentPresentation k n L)
    (E : B k n false ≃+* B k n true) (hE : IsAdjacent k n E)

include hL hE

/-- The two actual restrictions jointly detect a truncated node section. -/
lemma restrictions_jointly_injective (x y : A k n)
    (hx : rightMap L x = rightMap L y)
    (hy : leftMap L E x = leftMap L E y) : x = y := by
  classical
  obtain ⟨c, hc⟩ := exists_expansion k n x
  obtain ⟨b, hb⟩ := exists_expansion k n y
  have hcb : c = b := by
    ext j
    by_cases hj : 0 ≤ j
    · have h := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff j) hx
      rw [hc, hb, right_coeff L hL, right_coeff L hL] at h
      simpa [Int.toNat_of_nonpos (show -j ≤ 0 by omega)] using h
    · have h := congrArg (fun p : LaurentPolynomial (R k n) => p.coeff j) hy
      rw [hc, hb, left_coeff L hL E hE, left_coeff L hL E hE] at h
      simpa [Int.toNat_of_nonpos (show j ≤ 0 by omega)] using h
  rw [hc, hb, hcb]

/-- The accepted spanning expansion has unique truncated coefficients. -/
lemma expansion_unique (x : A k n) :
    ∃! c : ℤ →₀ R k n,
      x = c.sum (fun j z => base k n z * monomial k n j) := by
  classical
  obtain ⟨c, hc⟩ := exists_expansion k n x
  refine ⟨c, hc, ?_⟩
  intro b hb
  ext j
  by_cases hj : 0 ≤ j
  · have h := congrArg (fun z => (rightMap L z).coeff j) (hb.symm.trans hc)
    rw [right_coeff L hL, right_coeff L hL] at h
    simpa [Int.toNat_of_nonpos (show -j ≤ 0 by omega)] using h
  · have h := congrArg (fun z => (leftMap L E z).coeff j) (hb.symm.trans hc)
    rw [left_coeff L hL E hE, left_coeff L hL E hE] at h
    simpa [Int.toNat_of_nonpos (show j ≤ 0 by omega)] using h

open LaurentPolynomial

omit hE in
/-- The right restriction retains the marked linear factor explicitly. -/
lemma right_pair (a b : kˣ) :
    rightMap L (pairEquation k n a b) =
      (T 1 - C (markedUnit k n a : R k n)) *
        (C (parameter k n) * T (-1) - C (↑((markedUnit k n b)⁻¹) : R k n)) := by
  simp only [pairEquation, markedEquation, map_mul, map_sub,
    right_x L hL, right_y L hL, right_base L hL]

/-- The left restriction contains the same marked factor on the next chart.
The remaining Laurent factor has nilpotent nonconstant terms. -/
lemma left_pair (a b : kˣ) :
    leftMap L E (pairEquation k n a b) =
      (T 1 - C (markedUnit k n b : R k n)) *
        ((C (parameter k n) * T 1 - C (markedUnit k n a : R k n)) *
          (-C (↑((markedUnit k n b)⁻¹) : R k n))) * T (-1) := by
  simp only [pairEquation, markedEquation, map_mul, map_sub,
    left_x L hL E hE, left_y L hL E hE, left_base L hL E hE]
  have hT : (T 1 : LaurentPolynomial (R k n)) * T (-1) = 1 := by
    rw [← T_add]; norm_num
  have hu : C (markedUnit k n b : R k n) * C (↑((markedUnit k n b)⁻¹) : R k n) =
      (1 : LaurentPolynomial (R k n)) := by rw [← map_mul]; simp
  calc
    _ = (C (parameter k n) * T 1 - C (markedUnit k n a : R k n)) *
        ((T 1 - C (markedUnit k n b : R k n)) *
          (-C (↑((markedUnit k n b)⁻¹) : R k n)) * T (-1)) := by
      congr 1
      calc
        T (-1) - C (↑((markedUnit k n b)⁻¹) : R k n) =
          -(T 1 * T (-1)) * C (↑((markedUnit k n b)⁻¹) : R k n) +
            (C (markedUnit k n b : R k n) * C (↑((markedUnit k n b)⁻¹) : R k n)) *
              T (-1) := by rw [hT, hu]; ring
        _ = _ := by ring
    _ = _ := by ring

/-- The numerator gluing equation after cancellation of the common regular
marked factor. This never inverts a marked equation or the parameter. -/
lemma compatible_iff_laurent (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ)
    (d : ℕ) (s : Fin r → A k n) :
    Compatible k r n hr E a d s ↔ ∀ i : Fin r,
      leftMap L E (s i) *
          (C (parameter k n) * T (-1) -
            C (↑((markedUnit k n (a (next r hr (next r hr i))))⁻¹) : R k n)) ^ d =
        rightMap L (s (next r hr i)) *
          ((C (parameter k n) * T 1 - C (markedUnit k n (a i) : R k n)) *
            (-C (↑((markedUnit k n (a (next r hr i)))⁻¹) : R k n))) ^ d *
          T (-(d : ℤ)) := by
  unfold Compatible
  apply forall_congr'
  intro i
  rw [← L.injective.eq_iff]
  simp only [map_mul, map_pow]
  change leftMap L E (s i) *
      rightMap L (pairEquation k n (a (next r hr i))
        (a (next r hr (next r hr i)))) ^ d =
    rightMap L (s (next r hr i)) *
      leftMap L E (pairEquation k n (a i) (a (next r hr i))) ^ d ↔ _
  rw [right_pair L hL, left_pair L hL E hE]
  simp only [mul_pow, T_pow, mul_neg_one]
  have hreg := (laurent_linear_regular
    (markedUnit k n (a (next r hr i)) : R k n)).pow d
  constructor
  · intro h
    apply hreg.left
    convert h using 1 <;> ring
  · intro h
    have h' := congrArg
      ((T 1 - C (markedUnit k n (a (next r hr i)) : R k n)) ^ d * ·) h
    convert h' using 1 <;> ring

local instance nodeAlgebra : Algebra (R k n) (A k n) := (base k n).toAlgebra
local instance nodeModule : Module (R k n) (A k n) := nodeAlgebra.toModule
local instance nodeAction : DistribMulAction (R k n) (A k n) := nodeModule.toDistribMulAction
local instance nodeScalar : SMul (R k n) (A k n) := ⟨fun c x => base k n c * x⟩
local instance nodeFamilyScalar (r : ℕ) : SMul (R k n) (Fin r → A k n) :=
  ⟨fun c s i => base k n c * s i⟩

/-- Expansion uses exactly the frozen structural map as its scalar action. -/
def nodeExpansion (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    (ℤ →₀ R k n) →ₗ[R k n] A k n :=
  Finsupp.linearCombination (R k n) (monomial k n)

omit hL hE in
lemma nodeExpansion_apply (c : ℤ →₀ R k n) :
    nodeExpansion k n c = c.sum (fun j z => base k n z * monomial k n j) := rfl

/-- A coordinate equivalence for the actual node quotient, without a
fraction field or a flatness hypothesis. -/
def nodeExpansionEquiv : (ℤ →₀ R k n) ≃ₗ[R k n] A k n :=
  LinearEquiv.ofBijective (nodeExpansion k n) (by
    constructor
    · intro c b h
      obtain ⟨v, hv, hu⟩ := expansion_unique L hL E hE (nodeExpansion k n c)
      exact (hu c rfl).trans (hu b h).symm
    · intro x
      obtain ⟨c, hc⟩ := exists_expansion k n x
      exact ⟨c, hc.symm⟩)

omit hL hE in
def rightWeight (b : kˣ) : LaurentPolynomial (R k n) :=
  C (parameter k n) * T (-1) - C (↑((markedUnit k n b)⁻¹) : R k n)

omit hL hE in
def leftWeight (a b : kˣ) : LaurentPolynomial (R k n) :=
  (C (parameter k n) * T 1 - C (markedUnit k n a : R k n)) *
    (-C (↑((markedUnit k n b)⁻¹) : R k n))

/-- The cancelled Cech map is linear over the actual truncated base. -/
def normalizedDifference (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ) :
    (Fin r → A k n) →ₗ[R k n] (Fin r → LaurentPolynomial (R k n)) where
  toFun s i := leftMap L E (s i) * rightWeight (a (next r hr (next r hr i))) ^ d -
    rightMap L (s (next r hr i)) * leftWeight (a i) (a (next r hr i)) ^ d * T (-(d : ℤ))
  map_add' s t := by
    funext i
    simp only [Pi.add_apply, map_add]
    ring
  map_smul' z s := by
    funext i
    change leftMap L E (base k n z * s i) * _ -
      rightMap L (base k n z * s (next r hr i)) * _ * _ =
        z • (leftMap L E (s i) * _ - rightMap L (s (next r hr i)) * _ * _)
    rw [map_mul, map_mul, left_base L hL E hE, right_base L hL, smul_eq_C_mul]
    ring

lemma compatible_iff_normalizedDifference (r : ℕ) (hr : 0 < r)
    (a : Fin r → kˣ) (d : ℕ) (s : Fin r → A k n) :
    Compatible k r n hr E a d s ↔ normalizedDifference L hL E hE r hr a d s = 0 := by
  rw [compatible_iff_laurent L hL E hE]
  simp only [normalizedDifference, LinearMap.coe_mk, AddHom.coe_mk,
    funext_iff, Pi.zero_apply, sub_eq_zero, rightWeight, leftWeight]

/-- Sections are the actual kernel of the cancelled map, as a set of chart
numerators. -/
def sectionsEquivKernel (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ) :
    Sections k r n hr E a d ≃
      LinearMap.ker (normalizedDifference L hL E hE r hr a d) where
  toFun s := ⟨s.val, (compatible_iff_normalizedDifference L hL E hE r hr a d s.val).mp
    s.property⟩
  invFun s := ⟨s.val, (compatible_iff_normalizedDifference L hL E hE r hr a d s.val).mpr
    s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A linear coordinate equivalence for this concrete kernel gives precisely
the frozen unique-coordinate predicate, with its fixed structural scalars. -/
lemma isBasis_of_kernel_basis (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (b : Module.Basis (Fin (d*r)) (R k n)
      (LinearMap.ker (normalizedDifference L hL E hE r hr a d))) :
    IsBasis k r n hr E a d (fun j => (sectionsEquivKernel L hL E hE r hr a d).symm (b j)) := by
  intro s
  exact basis_unique_chart_coordinates _ b
    (sectionsEquivKernel L hL E hE r hr a d s)

/-- Finite families of the genuine node expansions. -/
def familyExpansionEquiv (r : ℕ) :
    ((Fin r × ℤ) →₀ R k n) ≃ₗ[R k n] (Fin r → A k n) :=
  (familyCoefficients (R k n)).trans
    (LinearEquiv.piCongrRight fun _ => nodeExpansionEquiv L hL E hE)

lemma familyExpansion_single (r : ℕ) (i : Fin r) (j : ℤ) :
    familyExpansionEquiv L hL E hE r (Finsupp.single (i, j) 1) =
      Pi.single i (monomial k n j) := by
  classical
  funext z
  change nodeExpansionEquiv L hL E hE (familyCoefficients (R k n)
    (Finsupp.single (i, j) 1) z) = _
  rw [familyCoefficients_single]
  by_cases hz : z = i
  · subst z
    simp only [Pi.single_eq_same]
    change nodeExpansion k n (Finsupp.single j 1) = monomial k n j
    simp only [nodeExpansion_apply, Finsupp.sum_single_index, map_zero, zero_mul,
      map_one, one_mul]
  · simp [Pi.single_eq_of_ne hz]

omit hL hE in
def parameterQuotient : LaurentPolynomial (R k n) →+*
    LaurentPolynomial (R k n) ⧸ Ideal.span ({C (parameter k n)} : Set (LaurentPolynomial (R k n))) :=
  Ideal.Quotient.mk _

omit hL hE in
lemma parameterQuotient_parameter :
    parameterQuotient (k := k) (n := n) (C (parameter k n)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

omit hL hE in
lemma parameterQuotient_eq_iff (x y : LaurentPolynomial (R k n)) :
    parameterQuotient (k := k) (n := n) x = parameterQuotient (k := k) (n := n) y ↔ ∃ z, x - y = parameter k n • z := by
  rw [← sub_eq_zero, ← map_sub, parameterQuotient, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simp only [smul_eq_C_mul, dvd_def]

variable {Q : Type u} [CommRing Q] (q : LaurentPolynomial (R k n) →+* Q)
    (hq : q (C (parameter k n)) = 0)
include hq

lemma quotient_right_monomial (j : ℤ) :
    q (rightMap L (monomial k n j)) =
      if 0 ≤ j then q (T j) else 0 := by
  rw [right_monomial L hL, map_mul]
  by_cases hj : 0 ≤ j
  · simp [hj, Int.toNat_of_nonpos (show -j ≤ 0 by omega)]
  · rw [if_neg hj, map_pow, map_pow, hq,
      zero_pow (show (-j).toNat ≠ 0 by omega), zero_mul]

lemma quotient_left_monomial (j : ℤ) :
    q (leftMap L E (monomial k n j)) =
      if j ≤ 0 then q (T j) else 0 := by
  rw [left_monomial L hL E hE, map_mul]
  by_cases hj : j ≤ 0
  · simp [hj, Int.toNat_of_nonpos hj]
  · rw [if_neg hj, map_pow, map_pow, hq,
      zero_pow (show j.toNat ≠ 0 by omega), zero_mul]

omit hL hE in
lemma quotient_rightWeight (b : kˣ) :
    q (rightWeight (k := k) (n := n) b) =
      q (C (-(↑((markedUnit k n b)⁻¹) : R k n))) := by
  simp [rightWeight, hq]

omit hL hE in
lemma quotient_leftWeight (a b : kˣ) :
    q (leftWeight (k := k) (n := n) a b) =
      q (C ((markedUnit k n a : R k n) * (↑((markedUnit k n b)⁻¹) : R k n))) := by
  simp [leftWeight, hq]

/-- A negative pivot has one nonzero column after killing the parameter. -/
lemma quotient_negative_column (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (i : Fin r) (j : ℤ) (hj : j < 0) (l : Fin r) :
    q (normalizedDifference L hL E hE r hr a d (Pi.single i (monomial k n j)) l) =
      q ((Pi.single (M := fun _ : Fin r => LaurentPolynomial (R k n)) i
        (C ((-(↑((markedUnit k n (a (next r hr (next r hr i))))⁻¹) : R k n)) ^ d) * T j)) l) := by
  classical
  have hlm := quotient_left_monomial L hL E hE q hq j
  have hrm := quotient_right_monomial L hL E hE q hq j
  simp only [if_pos (le_of_lt hj)] at hlm
  rw [if_neg (by omega)] at hrm
  simp only [normalizedDifference, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sub, map_mul, map_pow, Pi.single_apply, apply_ite, map_zero]
  rw [hlm, hrm]
  simp only [ite_self, zero_mul, sub_zero, quotient_rightWeight q hq]
  by_cases hli : l = i
  · subst l
    simp only [if_pos rfl, map_mul, map_pow]
    exact mul_comm _ _
  · simp [hli]

omit hq

def nodeFamilyBasis (r : ℕ) :
    Module.Basis (Fin r × ℤ) (R k n) (Fin r → A k n) :=
  Finsupp.basisSingleOne.map (familyExpansionEquiv L hL E hE r)

lemma nodeFamilyBasis_apply (r : ℕ) (p : Fin r × ℤ) :
    nodeFamilyBasis L hL E hE r p = Pi.single p.1 (monomial k n p.2) := by
  simp only [nodeFamilyBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  exact familyExpansion_single L hL E hE r p.1 p.2

def overlapFamilyBasis (r : ℕ) :
    Module.Basis (Fin r × ℤ) (R k n) (Fin r → LaurentPolynomial (R k n)) :=
  Finsupp.basisSingleOne.map (familyLaurentEquiv (R k n))

omit hL hE in
lemma overlapFamilyBasis_apply (r : ℕ) (p : Fin r × ℤ) :
    overlapFamilyBasis (k := k) (n := n) r p = Pi.single p.1 (T p.2) := by
  simp only [overlapFamilyBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  exact familyLaurentEquiv_single (R k n) p.1 p.2

def pivotUnit (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (p : Fin r × ℤ) : (R k n)ˣ :=
  if p.2 < 0 then (-((markedUnit k n (a (next r hr (next r hr p.1))))⁻¹))^d
  else -((markedUnit k n (a p.1) * (markedUnit k n (a (next r hr p.1)))⁻¹)^d)

def pivotBasis (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ) :
    Module.Basis ((Fin r × Fin d) ⊕ (Fin r × ℤ)) (R k n) (Fin r → A k n) :=
  ((nodeFamilyBasis L hL E hE r).reindex
    (pivotIndex (PolygonCechObstructionR0131.shift r hr) d).symm).unitsSMul
      (fun z => match z with | Sum.inl _ => 1 | Sum.inr p => (pivotUnit (k := k) (n := n) r hr a d p)⁻¹)

lemma pivotBasis_pivot (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (p : Fin r × ℤ) :
    pivotBasis L hL E hE r hr a d (Sum.inr p) =
      @SMul.smul (R k n) (Fin r → A k n) _ (↑((pivotUnit (k := k) (n := n) r hr a d p)⁻¹) : R k n)
        (nodeFamilyBasis L hL E hE r
          (pivotIndex (PolygonCechObstructionR0131.shift r hr) d (Sum.inr p))) := by
  simp only [pivotBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Units.smul_def]
  rfl

include hq in
/-- A positive pivot is moved from the next chart to its preceding overlap. -/
lemma quotient_positive_column (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) (i : Fin r) (j : ℤ) (hj : 0 ≤ j) (l : Fin r) :
    q (normalizedDifference L hL E hE r hr a d
      (Pi.single (next r hr i) (monomial k n (j + d))) l) =
      q ((Pi.single (M := fun _ : Fin r => LaurentPolynomial (R k n)) i
        (C (-(((markedUnit k n (a i) : R k n) *
          (↑((markedUnit k n (a (next r hr i)))⁻¹) : R k n)) ^ d)) * T j)) l) := by
  classical
  have hpos : 0 < j + (d : ℤ) := by omega
  have hlm := quotient_left_monomial L hL E hE q hq (j+d)
  have hrm := quotient_right_monomial L hL E hE q hq (j+d)
  rw [if_neg (by omega)] at hlm
  rw [if_pos (le_of_lt hpos)] at hrm
  have hs : next r hr l = next r hr i ↔ l = i :=
    (PolygonCechObstructionR0131.shift r hr).injective.eq_iff
  simp only [normalizedDifference, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sub, map_mul, map_pow, Pi.single_apply, apply_ite, map_zero]
  rw [hlm, hrm]
  simp only [ite_self, zero_mul, zero_sub, quotient_leftWeight q hq, hs]
  by_cases hli : l = i
  · subst l
    simp only [ite_true, if_pos rfl, map_mul, map_neg, map_pow, mul_pow]
    have hT : q (T (j+(d : ℤ))) * q (T (-(d : ℤ))) = q (T j) := by
      rw [← map_mul, ← T_add]
      congr 2
      omega
    calc
      _ = -(q (T (j + (d : ℤ))) * q (T (-(d : ℤ)))) *
        q (C ((markedUnit k n (a i) : R k n) *
          (↑((markedUnit k n (a (next r hr i)))⁻¹) : R k n))) ^ d := by
          simp only [map_mul, mul_pow]; ring
      _ = _ := by rw [hT]; simp only [map_mul, mul_pow]; ring
  · simp [hli]

include hq in
lemma quotient_raw_pivot (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) (p : Fin r × ℤ) (l : Fin r) :
    q (normalizedDifference L hL E hE r hr a d
      (nodeFamilyBasis L hL E hE r
        (pivotIndex (PolygonCechObstructionR0131.shift r hr) d (Sum.inr p))) l) =
      q (C (pivotUnit (k := k) (n := n) r hr a d p : R k n) *
        overlapFamilyBasis (k := k) (n := n) r p l) := by
  classical
  rcases p with ⟨i, j⟩
  rw [pivotIndex_pivot]
  by_cases hj : j < 0
  · rw [if_pos hj, nodeFamilyBasis_apply,
      quotient_negative_column L hL E hE q hq r hr a d i j hj l]
    simp only [pivotUnit, if_pos hj, Units.val_pow_eq_pow_val, Units.val_neg,
      overlapFamilyBasis_apply]
    by_cases hl : l = i
    · subst l; rw [Pi.single_eq_same, Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hl]
  · rw [if_neg hj, nodeFamilyBasis_apply]
    change q (normalizedDifference L hL E hE r hr a d
      (Pi.single (next r hr i) (monomial k n (j+d))) l) = _
    rw [quotient_positive_column L hL E hE q hq r hr a d hd i j (by omega) l]
    simp only [pivotUnit, if_neg hj, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_mul, overlapFamilyBasis_apply]
    by_cases hl : l = i
    · subst l; rw [Pi.single_eq_same, Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hl]

include hq in
lemma quotient_normalized_pivot (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) (p : Fin r × ℤ) (l : Fin r) :
    q (normalizedDifference L hL E hE r hr a d
      (pivotBasis L hL E hE r hr a d (Sum.inr p)) l) =
      q (overlapFamilyBasis (k := k) (n := n) r p l) := by
  rw [pivotBasis_pivot]
  change q ((normalizedDifference L hL E hE r hr a d)
    ((↑((pivotUnit (k := k) (n := n) r hr a d p)⁻¹) : R k n) •
      nodeFamilyBasis L hL E hE r
        (pivotIndex (PolygonCechObstructionR0131.shift r hr) d (Sum.inr p))) l) = _
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_C_mul, map_mul]
  rw [quotient_raw_pivot L hL E hE q hq r hr a d hd p l, map_mul, ← mul_assoc]
  have hu := congrArg (fun z : R k n => q (C z))
    (Units.inv_mul (pivotUnit (k := k) (n := n) r hr a d p))
  simp only [map_mul, map_one] at hu
  rw [hu, one_mul]

/-- The actual normalized pivot errors are divisible by the base parameter. -/
lemma pivot_error_divisible (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) (p : Fin r × ℤ) :
    ∃ z : Fin r → LaurentPolynomial (R k n),
      overlapFamilyBasis (k := k) (n := n) r p -
        normalizedDifference L hL E hE r hr a d
          (pivotBasis L hL E hE r hr a d (Sum.inr p)) = parameter k n • z := by
  classical
  have hp (l : Fin r) : parameterQuotient (k := k) (n := n)
      (normalizedDifference L hL E hE r hr a d
        (pivotBasis L hL E hE r hr a d (Sum.inr p)) l) =
      parameterQuotient (k := k) (n := n)
        (overlapFamilyBasis (k := k) (n := n) r p l) := by
    exact @quotient_normalized_pivot k _ _ n L hL E hE
      (LaurentPolynomial (R k n) ⧸ Ideal.span ({C (parameter k n)} : Set (LaurentPolynomial (R k n))))
      (Ideal.Quotient.commRing _) (parameterQuotient (k := k) (n := n))
      (parameterQuotient_parameter (k := k) (n := n)) r hr a d hd p l
  choose z hz using fun l => (parameterQuotient_eq_iff (k := k) (n := n) _ _).mp (hp l).symm
  exact ⟨z, funext hz⟩

/-- The concrete positive kernel has precisely the free window as its
coordinate module. All pivot hypotheses have now been proved on the atlas. -/
def positiveKernelCoordinates (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) :
    LinearMap.ker (normalizedDifference L hL E hE r hr a d) ≃ₗ[R k n]
      ((Fin r × Fin d) →₀ R k n) := by
  let b := pivotBasis L hL E hE r hr a d
  let c := overlapFamilyBasis (k := k) (n := n) r
  let delta := normalizedDifference L hL E hE r hr a d
  let g := delta.comp b.repr.symm.toLinearMap
  let f := c.repr.toLinearMap.comp g
  have hf (p : Fin r × ℤ) : ∃ z,
      Finsupp.single p 1 - f (Finsupp.single (Sum.inr p) 1) = parameter k n • z := by
    obtain ⟨z, hz⟩ := pivot_error_divisible L hL E hE r hr a d hd p
    refine ⟨c.repr z, ?_⟩
    have hh := congrArg c.repr hz
    change c.repr (c p - delta (b (Sum.inr p))) = c.repr (parameter k n • z) at hh
    rw [map_sub, map_smul, c.repr_self] at hh
    simpa only [f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.repr_symm_single_one] using hh
  let e := kernelEquivOfPivotColumns (parameter k n) (n+1) (parameter_pow k n) f hf
  exact (kernelEquivDom b.repr.symm delta).symm.trans
    ((kernelEquivCod c.repr g).symm.trans e)

/-- Reindex the free window by the exact cardinal specified in the contract. -/
def positiveKernelBasis (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ)
    (hd : 0 < d) :
    Module.Basis (Fin (d*r)) (R k n)
      (LinearMap.ker (normalizedDifference L hL E hE r hr a d)) :=
  (Finsupp.basisSingleOne.map (positiveKernelCoordinates L hL E hE r hr a d hd).symm).reindex
    (Fintype.equivOfCardEq (by simp [Nat.mul_comm]))

lemma basis_exists (r : ℕ) (hr : 0 < r) (a : Fin r → kˣ) (d : ℕ) (hd : 0 < d) :
    ∃ b : Fin (d*r) → Sections k r n hr E a d,
      IsBasis k r n hr E a d b := by
  let b := positiveKernelBasis L hL E hE r hr a d hd
  exact ⟨fun j => (sectionsEquivKernel L hL E hE r hr a d).symm (b j),
    isBasis_of_kernel_basis L hL E hE r hr a d b⟩

end PositiveSectionBasisR0134

/-- Every positive degree has exactly `d*r` unique structural coordinates on
the actual truncated cyclic polygon, uniformly in all frozen input data. -/
theorem positive_section_basis :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : ArithmeticThetaInfinitesimalPolygonR0129.B k n false ≃+*
      ArithmeticThetaInfinitesimalPolygonR0129.B k n true),
    ArithmeticThetaInfinitesimalPolygonR0129.IsAdjacent k n E →
    ∀ (a : Fin r → kˣ), ∀ d : ℕ, 0 < d →
    ∃ b : Fin (d*r) → Sections k r n hr E a d, IsBasis k r n hr E a d b := by
  intro k _ _ r n hr _ E hE a d hd
  obtain ⟨L, hL, _⟩ := ArithmeticThetaPolygonCohomologyR0131.truncated_laurent_presentation k n
  exact PositiveSectionBasisR0134.basis_exists L hL E hE r hr a d hd

end ArithmeticThetaPositiveLineR0134
