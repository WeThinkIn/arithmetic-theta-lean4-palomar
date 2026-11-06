module

public import TruncatedLaurentPresentationR0131
public import PolygonCohomologyDefinitionsR0131

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-! The residue and exactness of the explicit finite cyclic Cech complex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
namespace PolygonCechObstructionR0131
open ArithmeticThetaInfinitesimalPolygonR0129
open LaurentPolynomial

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}
variable {E : B k n false ≃+* B k n true}
variable {L : B k n true ≃+* LaurentPolynomial (R k n)}

def rx (L : B k n true ≃+* LaurentPolynomial (R k n)) :
    A k n →+* LaurentPolynomial (R k n) := L.toRingHom.comp (restriction k n true)
def ry (E : B k n false ≃+* B k n true)
    (L : B k n true ≃+* LaurentPolynomial (R k n)) :
    A k n →+* LaurentPolynomial (R k n) :=
  L.toRingHom.comp (E.toRingHom.comp (restriction k n false))

lemma rx_base (hL : LaurentPresentation k n L) (c : R k n) :
    rx L (base k n c) = C c := RingHom.congr_fun hL.1 c
lemma ry_base (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L) (c : R k n) :
    ry E L (base k n c) = C c := by
  change L (E (restriction k n false (base k n c))) = _
  rw [show E (restriction k n false (base k n c)) =
      restriction k n true (base k n c) from RingHom.congr_fun (adjacent_base hE) c]
  exact rx_base hL c
lemma rx_x (hL : LaurentPresentation k n L) : rx L (coordX k n) = T 1 := hL.2
lemma ry_y (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L) :
    ry E L (coordY k n) = T (-1) := by
  apply (isUnit_T (R := R k n) 1).mul_right_cancel
  have h := congrArg L (adjacent_y_mul_x hE)
  simpa only [map_mul, map_one, hL.2, ← T_add, neg_add_cancel, T_zero, ry, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using h
lemma rx_y (hL : LaurentPresentation k n L) :
    rx L (coordY k n) = C (parameter k n) * T (-1) := by
  apply (isUnit_T (R := R k n) 1).mul_left_cancel
  rw [← rx_x hL, ← map_mul, coordX_mul_coordY, rx_base hL, rx_x hL]
  rw [mul_left_comm, ← T_add]; simp
lemma ry_x (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L) :
    ry E L (coordX k n) = C (parameter k n) * T 1 := by
  apply (isUnit_T (R := R k n) (-1)).mul_right_cancel
  rw [← ry_y hE hL, ← map_mul, coordX_mul_coordY, ry_base hE hL, ry_y hE hL]
  rw [mul_assoc, ← T_add]; simp

lemma coeff_CT (c : R k n) (j : ℤ) : (C c * T j).coeff 0 = if j = 0 then c else 0 := by
  rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma coeff_zero_agree (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (a : A k n) : (ry E L a).coeff 0 = (rx L a).coeff 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha : a ∈ Submodule.span (PowerSeries k)
      (Set.range (ArithmeticThetaNodeCharts.normalMonomial k)) := by
    rw [ArithmeticThetaNodeCharts.normal_span]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    cases j with
    | ofNat d =>
      change (ry E L (trunc _ _ n (ArithmeticThetaNodeCharts.normalMonomial k (d : ℤ)))).coeff 0 = _
      rw [ArithmeticThetaNodeCharts.normalMonomial_nat, map_pow]
      change (ry E L (coordX k n ^ d)).coeff 0 = (rx L (coordX k n ^ d)).coeff 0
      simp only [map_pow, ry_x hE hL, rx_x hL, mul_pow, T_pow]
      rw [← map_pow C]
      cases d with
      | zero => simp
      | succ d =>
        simp only [coeff_CT, T_apply, mul_one]
        split_ifs <;> first | omega | rfl
    | negSucc d =>
      have hm : ArithmeticThetaNodeCharts.normalMonomial k (Int.negSucc d) =
          ArithmeticThetaNodeCharts.y k ^ (d+1) := by
        simp [ArithmeticThetaNodeCharts.normalMonomial]
      change (ry E L (trunc _ _ n _)).coeff 0 = _
      rw [hm, map_pow]
      change (ry E L (coordY k n ^ (d+1))).coeff 0 = (rx L (coordY k n ^ (d+1))).coeff 0
      simp only [map_pow, ry_y hE hL, rx_y hL, mul_pow, T_pow]
      rw [← map_pow C]
      simp only [coeff_CT, T_apply, mul_neg, mul_one]
      split_ifs <;> first | omega | rfl
  | zero => simp
  | add a b ha hb ia ib => simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using congrArg₂ (· + ·) ia ib
  | smul c a ha ih =>
    simp only [Algebra.smul_def]
    change (ry E L (trunc _ _ n (algebraMap (PowerSeries k) _ c * a))).coeff 0 = _
    rw [map_mul]
    change (ry E L (base k n (trunc _ _ n c) * trunc _ _ n a)).coeff 0 =
      (rx L (base k n (trunc _ _ n c) * trunc _ _ n a)).coeff 0
    simp only [map_mul, ry_base hE hL, rx_base hL, ← smul_eq_C_mul,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    exact congrArg (trunc _ _ n c * ·) ih



variable (r : ℕ) (hr : 0 < r)

def shift : Equiv.Perm (Fin r) :=
  Equiv.ofBijective (next r hr) ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨next_surjective r hr, rfl⟩)

lemma shift_apply (i : Fin r) : shift r hr i = next r hr i := rfl

def delta : (Fin r → A k n) →+ (Fin r → LaurentPolynomial (R k n)) where
  toFun a i := ry E L (a i) - rx L (a (shift r hr i))
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp; abel

lemma delta_single (i : Fin r) (a : A k n) :
    delta (E := E) (L := L) r hr (Pi.single (shift r hr i) a) =
      Pi.single (shift r hr i) (ry E L a) - Pi.single i (rx L a) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [delta, Pi.single_apply, apply_ite]
  · have hs : shift r hr j ≠ shift r hr i := fun h' => h ((shift r hr).injective h')
    by_cases hj : j = shift r hr i <;> simp only [delta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.single_apply, if_neg h, if_neg hs, map_zero, sub_zero]
    all_goals split_ifs <;> simp_all

lemma residue_delta (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (a : Fin r → A k n) : ∑ i, (delta (E := E) (L := L) r hr a i).coeff 0 = 0 := by
  simp only [delta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, coeff_zero_agree hE hL, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (Equiv.sum_comp (shift r hr) (fun i => (rx L (a i)).coeff 0)).symm

/-- A nilpotent coefficient kills any mode transported around an arbitrary shift. -/
lemma nilpotent_transport {S I G : Type*} [CommRing S] [AddCommGroup G]
    (s : I → I) (F : I → S → G) (q : S) (hq : IsNilpotent q)
    (h0 : ∀ i, F i 0 = 0) (hs : ∀ i c, F i c = F (s i) (q*c)) :
    ∀ i c, F i c = 0 := by
  obtain ⟨N, hN⟩ := hq
  have aux : ∀ m i c, q^m*c = 0 → F i c = 0 := by
    intro m
    induction m with
    | zero => intro i c hc; simp only [pow_zero, one_mul] at hc; simpa [hc] using h0 i
    | succ m ih =>
      intro i c hc
      rw [hs]
      apply ih
      simpa only [pow_succ, mul_assoc] using hc
  intro i c
  exact aux N i c (by rw [hN, zero_mul])



lemma images_x (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (c : R k n) (d : ℕ) :
    rx L (base k n c * coordX k n ^ d) = C c * T (d : ℤ) ∧
    ry E L (base k n c * coordX k n ^ d) =
      C (parameter k n ^ d * c) * T (d : ℤ) := by
  constructor
  · simp only [map_mul, map_pow, rx_base hL, rx_x hL, T_pow, mul_one]
  · simp only [map_mul, map_pow, ry_base hE hL, ry_x hE hL, mul_pow, T_pow, mul_one]
    rw [← map_pow C, ← mul_assoc, ← map_mul, mul_comm c]
    rw [map_mul]

lemma images_y (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (c : R k n) (d : ℕ) :
    rx L (base k n c * coordY k n ^ d) =
      C (parameter k n ^ d * c) * T (-(d : ℤ)) ∧
    ry E L (base k n c * coordY k n ^ d) = C c * T (-(d : ℤ)) := by
  constructor
  · simp only [map_mul, map_pow, rx_base hL, rx_y hL, mul_pow, T_pow, mul_neg, mul_one]
    rw [← map_pow C, ← mul_assoc, ← map_mul, mul_comm c]
    rw [map_mul]
  · simp only [map_mul, map_pow, ry_base hE hL, ry_y hE hL, T_pow, mul_neg, mul_one]

variable {r hr}
variable {G : Type*} [AddCommGroup G]
variable (q : (Fin r → LaurentPolynomial (R k n)) →+ G)
variable (hq : ∀ a, q (delta (E := E) (L := L) r hr a) = 0)
include hq

lemma boundary_relation (i : Fin r) (a : A k n) :
    q (Pi.single (shift r hr i) (ry E L a)) = q (Pi.single i (rx L a)) := by
  have h := hq (Pi.single (shift r hr i) a)
  rw [delta_single, map_sub, sub_eq_zero] at h
  exact h

lemma positive_mode (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (d : ℕ) (hd : 0 < d) (i : Fin r) (c : R k n) :
    q (Pi.single i (C c * T (d : ℤ))) = 0 := by
  apply nilpotent_transport (shift r hr)
    (fun i c => q (Pi.single i (C c * T (d : ℤ)))) (parameter k n ^ d)
    (⟨n+1, by rw [← pow_mul, Nat.mul_comm d, pow_mul, parameter_pow, zero_pow hd.ne']⟩)
  · intro j; simp
  · intro j b
    have h := boundary_relation q hq j (base k n b * coordX k n ^ d)
    rw [(images_x hE hL b d).1, (images_x hE hL b d).2] at h
    exact h.symm

lemma negative_mode (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (d : ℕ) (hd : 0 < d) (i : Fin r) (c : R k n) :
    q (Pi.single i (C c * T (-(d : ℤ)))) = 0 := by
  apply nilpotent_transport (shift r hr).symm
    (fun i c => q (Pi.single i (C c * T (-(d : ℤ))))) (parameter k n ^ d)
    (⟨n+1, by rw [← pow_mul, Nat.mul_comm d, pow_mul, parameter_pow, zero_pow hd.ne']⟩)
  · intro j; simp
  · intro j b
    have h := boundary_relation q hq ((shift r hr).symm j) (base k n b * coordY k n ^ d)
    rw [(images_y hE hL b d).1, (images_y hE hL b d).2,
      Equiv.apply_symm_apply] at h
    exact h

lemma constant_mode (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (i : Fin r) (c : R k n) :
    q (Pi.single i (C c)) = q (Pi.single (⟨0, hr⟩ : Fin r) (C c)) := by
  have hs (j : Fin r) : q (Pi.single (shift r hr j) (C c)) = q (Pi.single j (C c)) := by
    have h := boundary_relation q hq j (base k n c)
    simpa only [rx_base hL, ry_base hE hL] using h
  have aux : ∀ m (hm : m < r), q (Pi.single (⟨m, hm⟩ : Fin r) (C c)) =
      q (Pi.single (⟨0, hr⟩ : Fin r) (C c)) := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have he : shift r hr ⟨m, hm'⟩ = ⟨m+1, hm⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hm
      rw [← he, hs]
      exact ih hm'
  exact aux i.val i.isLt



lemma single_class (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (i : Fin r) (b : LaurentPolynomial (R k n)) :
    q (Pi.single i b) = q (Pi.single (⟨0, hr⟩ : Fin r) (C (b.coeff 0))) := by
  classical
  induction b using LaurentPolynomial.induction_on' with
  | add b c hb hc =>
    simpa only [Pi.single_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      using congrArg₂ (· + ·) hb hc
  | C_mul_T j c =>
    rw [coeff_CT]
    cases j with
    | ofNat d =>
      cases d with
      | zero => simpa using constant_mode q hq hE hL i c
      | succ d =>
        rw [if_neg (show Int.ofNat (d+1) ≠ (0 : ℤ) by intro h; cases h)]
        simpa using positive_mode q hq hE hL (d+1) (by omega) i c
    | negSucc d =>
      rw [if_neg (show Int.negSucc d ≠ (0 : ℤ) by omega)]
      have he : (Int.negSucc d : ℤ) = -((d+1 : ℕ) : ℤ) := by omega
      rw [he]
      simpa using negative_mode q hq hE hL (d+1) (by omega) i c

lemma tuple_class (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (b : Fin r → LaurentPolynomial (R k n)) :
    q b = q (Pi.single (⟨0, hr⟩ : Fin r) (C (∑ i, (b i).coeff 0))) := by
  classical
  calc
    q b = q (∑ i, Pi.single i (b i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, q (Pi.single i (b i)) := map_sum _ _ _
    _ = ∑ i, q (Pi.single (⟨0, hr⟩ : Fin r) (C ((b i).coeff 0))) := by
      apply Finset.sum_congr rfl; intro i hi; exact single_class q hq hE hL i (b i)
    _ = q (Pi.single (⟨0, hr⟩ : Fin r) (C (∑ i, (b i).coeff 0))) := by
      rw [map_sum, ← map_sum q]
      congr 1
      funext j
      by_cases hj : j = (⟨0, hr⟩ : Fin r) <;> simp [Pi.single_apply, Finset.sum_apply, hj]

omit hq in
lemma exact_delta (hE : IsAdjacent k n E) (hL : LaurentPresentation k n L)
    (b : Fin r → LaurentPolynomial (R k n)) :
    (∑ i, (b i).coeff 0) = 0 ↔ ∃ a, delta (E := E) (L := L) r hr a = b := by
  constructor
  · intro hb
    let D := delta (E := E) (L := L) r hr
    let Q := QuotientAddGroup.mk' D.range
    have hQ (a : Fin r → A k n) : Q (D a) = 0 := by
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩
    have h := tuple_class Q hQ hE hL b
    rw [hb] at h
    have hz : Q b = 0 := by simpa using h
    exact (QuotientAddGroup.eq_zero_iff _).mp hz
  · rintro ⟨a, rfl⟩
    exact residue_delta r hr hE hL a

end PolygonCechObstructionR0131
open ArithmeticThetaInfinitesimalPolygonR0129 PolygonCechObstructionR0131

/-- Surjective cyclic residue and exactness on the actual coordinate overlaps. -/
theorem polygon_cech_obstruction :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (E : B k n false ≃+* B k n true), IsAdjacent k n E →
    ∀ (L : B k n true ≃+* LaurentPolynomial (R k n)), LaurentPresentation k n L →
    Function.Surjective (residue k r n L) ∧
      (∀ b : Fin r → B k n true, residue k r n L b = 0 ↔
        ∃ a : Fin r → A k n, difference k r n hr E a = b) := by
  intro k _ _ r n hr _ E hE L hL
  classical
  constructor
  · intro c
    refine ⟨fun i => L.symm (if i = (⟨0, hr⟩ : Fin r) then LaurentPolynomial.C c else 0), ?_⟩
    unfold residue
    simp only [RingEquiv.apply_symm_apply]
    calc
      _ = ∑ i : Fin r, if i = ⟨0, hr⟩ then c else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i = (⟨0, hr⟩ : Fin r) <;> simp [h]
      _ = c := by simp
  · intro b
    have h := exact_delta (r := r) (hr := hr) hE hL (fun i => L (b i))
    change (∑ i, (L (b i)).coeff 0) = 0 ↔ _
    rw [h]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      funext i
      apply L.injective
      have hi := congrFun ha i
      simpa only [delta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, difference, ry, rx,
        RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        shift_apply, map_sub] using hi
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      funext i
      have hi := congrArg L (congrFun ha i)
      simpa only [delta, AddMonoidHom.coe_mk, ZeroHom.coe_mk, difference, ry, rx,
        RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        shift_apply, map_sub] using hi

end ArithmeticThetaPolygonCohomologyR0131
