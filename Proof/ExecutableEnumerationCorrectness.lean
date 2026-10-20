module

public import CofactorSearchBounds
public import ComputableIntegerBoxes

@[expose] public section

namespace ArithmeticThetaEnumeration

private theorem box_shell_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm)
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (B m : ℕ) (hm : m ≤ B) (x : Fin n → ℤ) :
    x ∈ (searchBox A B).filter (fun y => normNumerator A y = 2 * (m : ℤ)) ↔
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ) := by
  rw [Finset.mem_filter]
  have hn : (normNumerator A x : ℚ) =
      2 * ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) := by
    simpa [normNumerator] using integer_numerator_identity n A x
  constructor
  · rintro ⟨_, he⟩
    have he' : (normNumerator A x : ℚ) = 2 * (m : ℚ) := by exact_mod_cast he
    linarith
  · intro he
    constructor
    · apply (box_membership n A B x).mpr
      apply computed_radius_complete n A hs hp B x
      rw [he]
      exact_mod_cast hm
    · have he' : (normNumerator A x : ℚ) = 2 * (m : ℚ) := by rw [hn, he]
      exact_mod_cast he'

theorem shell_membership_exact (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (_heven : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (m : ℕ) (x : Fin n → ℤ) :
    x ∈ shellVectors A m ↔
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ) :=
  box_shell_iff n A hs hp m m le_rfl x

theorem representation_count_exact (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (heven : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (m : ℕ) :
    representationCount A m = Nat.card {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun i => (x i : ℚ)) = (m : ℚ)} :=
by
  calc
    representationCount A m = Nat.card {x : Fin n → ℤ // x ∈ shellVectors A m} := by
      simp [representationCount]
    _ = _ := Nat.card_congr
      (Equiv.subtypeEquivRight (shell_membership_exact n A hs heven hp m))

theorem coefficient_prefix_exact (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (heven : ∀ i, Even (A i i))
    (hp : ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef)
    (B : ℕ) :
    (coefficientsUpTo A B).length = B + 1 ∧ ∀ a : Fin (B + 1),
      (coefficientsUpTo A B).getD a.val 0 = Nat.card {x : Fin n → ℤ //
        ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
          (fun i => (x i : ℚ)) = (a.val : ℚ)} := by
  constructor
  · simp [coefficientsUpTo]
  · intro a
    unfold coefficientsUpTo
    rw [List.getD_eq_getElem _ _ (by simpa using a.isLt), List.getElem_ofFn]
    have hsets : (searchBox A B).filter
        (fun x => normNumerator A x = 2 * (a.val : ℤ)) = shellVectors A a.val := by
      ext x
      exact (box_shell_iff n A hs hp B a.val (by omega) x).trans
        (shell_membership_exact n A hs heven hp a.val x).symm
    change ((searchBox A B).filter
      (fun x => normNumerator A x = 2 * (a.val : ℤ))).card = _
    rw [hsets]
    exact representation_count_exact n A hs heven hp a.val

end ArithmeticThetaEnumeration
