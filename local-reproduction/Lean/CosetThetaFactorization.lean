import CosetFiniteIndex
import OrthogonalCosetArithmetic
import UnaryThetaProducts
import LatticeShellFinite

/-! Complete coset factorization after an exact common-denominator substitution. -/
namespace ArithmeticThetaCosets
open scoped BigOperators

lemma denominator_weight_pos (D m : ℕ) (hD : D ≠ 0) (hm : 0 < m)
    (hd : 2 * m ∣ D) : 0 < D / (2 * m) := by
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hd) (by omega)

lemma scaled_energy (n : ℕ) (m : Fin n → ℕ) (D : ℕ)
    (hm : ∀ j, 0 < m j) (hd : ∀ j, 2 * m j ∣ D) (r : Fin n → ℤ) :
    ((∑ j, ((D / (2 * m j) : ℕ) : ℤ) * r j ^ 2 : ℤ) : ℚ) =
      (D : ℚ) * ∑ j, (r j : ℚ) ^ 2 / (2 * (m j : ℚ)) := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hmul : ((D / (2 * m j) : ℕ) : ℚ) * (2 * (m j : ℚ)) = D := by
    exact_mod_cast (Nat.div_mul_cancel (hd j))
  have hmj : (m j : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hm j))
  have hn : (2 * (m j : ℚ)) ≠ 0 := mul_ne_zero (by norm_num) hmj
  rw [← hmul]
  field_simp

/-- Translating by a residue parametrizes all and only its congruence class. -/
noncomputable def residueParam (n : ℕ) (m : Fin n → ℕ) (ν : Fin n → ℤ)
    (hm : ∀ j, 0 < m j) :
    (Fin n → ℤ) ≃ {r : Fin n → ℤ // ∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)} := by
  let f : (Fin n → ℤ) → {r : Fin n → ℤ // ∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)} :=
    fun k => ⟨fun j => ν j + (m j : ℤ) * k j, fun j => by
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-k j, by ring⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro k l h
    have he := congrArg Subtype.val h
    funext j
    have hml : (m j : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (hm j))
    exact mul_left_cancel₀ hml (add_left_cancel (congrFun he j))
  · intro r
    choose k hk using fun j => (r.property j).symm.dvd
    refine ⟨k, Subtype.ext ?_⟩
    funext j
    change ν j + (m j : ℤ) * k j = r.val j
    rw [← hk j]
    ring

/-- Restricting the residue parametrization to an exact scaled norm shell. -/
noncomputable def cosetShellEquiv (n : ℕ) (m : Fin n → ℕ) (ν : Fin n → ℤ)
    (hm : ∀ j, 0 < m j) (D : ℕ) (hD : D ≠ 0) (hd : ∀ j, 2 * m j ∣ D)
    (q : (Fin n → ℤ) → ℚ)
    (hq : ∀ k, q k = ∑ j, ((ν j + (m j : ℤ) * k j : ℤ) : ℚ)^2 /
      (2 * (m j : ℚ))) (a : ℕ) :
    {k : Fin n → ℤ // q k = (a : ℚ)} ≃
      TupleShell n m (fun j => D / (2 * m j)) ν (D * a) := by
  let e := residueParam n m ν hm
  have he (k : Fin n → ℤ) :
      q k = (a : ℚ) ↔
      (∑ j, ((D / (2 * m j) : ℕ) : ℤ) * ((e k).val j)^2) = ((D * a : ℕ) : ℤ) := by
    have hscale := scaled_energy n m D hm hd (e k).val
    have hform : (∑ j, (((e k).val j : ℤ) : ℚ)^2 / (2 * (m j : ℚ))) = q k :=
      (hq k).symm
    rw [hform] at hscale
    have hn : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    constructor
    · intro h
      apply Int.cast_injective (α := ℚ)
      rw [hscale, h]
      simp
    · intro h
      have h' := congrArg (fun z : ℤ => (z : ℚ)) h
      rw [hscale] at h'
      push_cast at h'
      exact mul_left_cancel₀ hn h'
  exact (e.subtypeEquiv he).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

theorem expanded_identity_faithful : ∀ (D : ℕ) (hD : D ≠ 0) (f g : PowerSeries ℤ),
    PowerSeries.expand D hD f = PowerSeries.expand D hD g ↔ f = g := by
  intro D hD f g
  constructor
  · intro h
    apply PowerSeries.ext
    intro a
    have hh := congrArg (PowerSeries.coeff (D * a)) h
    simpa only [PowerSeries.coeff_expand_mul] using hh
  · exact congrArg (PowerSeries.expand D hD)

/-- The full theta series decomposes into all actual coset unary products. -/
theorem full_theta_factorization : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), A.IsSymm → (∀ j, Even (A j j)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → B.det ≠ 0 → (∀ j, 0 < m j ∧ Even (m j)) → B.transpose * A * B = Matrix.diagonal (fun j => (m j : ℤ)) → ∀ (D : ℕ) (hD : D ≠ 0), (∀ j : Fin n, 2 * m j ∣ D) → ∃ (e : Fin (Int.natAbs B.det) ≃ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B))) (ρ : Fin (Int.natAbs B.det) → (Fin n → ℤ)), ((∀ i : Fin (Int.natAbs B.det), (LinearMap.range (Matrix.mulVecLin B)).mkQ (ρ i) = e i) ∧ Function.Bijective (fun p : Fin (Int.natAbs B.det) × (Fin n → ℤ) => ρ p.1 + B.mulVec p.2)) ∧ PowerSeries.expand D hD (PowerSeries.mk (fun a : ℕ => (Nat.card {x : (Fin n → ℤ) // ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') (fun j => (x j : ℚ)) = (a : ℚ)} : ℤ)) : PowerSeries ℤ) = (∑ i : Fin (Int.natAbs B.det), ∏ j : Fin n, (PowerSeries.mk (fun a : ℕ => (Nat.card {r : ℤ // Int.ModEq (m j : ℤ) r (((B.transpose * A).mulVec (ρ i)) j) ∧ ((D / (2 * m j) : ℕ) : ℤ) * r ^ 2 = (a : ℤ)} : ℤ)) : PowerSeries ℤ)) := by
  intro n A B m hsym heven hpos hdet hm hgram D hD hd
  classical
  let Q : (Fin n → ℤ) → ℚ := fun x =>
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') (fun j => (x j : ℚ))
  let (a : ℕ) : Finite {x : Fin n → ℤ // Q x = (a : ℚ)} :=
    (ArithmeticThetaLattice.exact_shell_finite n
      ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm') hpos (a : ℚ)).to_subtype
  let w : Fin n → ℕ := fun j => D / (2 * m j)
  have hw : ∀ j, 0 < w j := fun j => denominator_weight_pos D (m j) hD (hm j).1 (hd j)
  obtain ⟨e, ρ, hρ, hbij⟩ := representatives_bijection n B hdet
  let ν : Fin (Int.natAbs B.det) → (Fin n → ℤ) := fun i => (B.transpose * A).mulVec (ρ i)
  refine ⟨e, ρ, ⟨hρ, hbij⟩, ?_⟩
  change PowerSeries.expand D hD
    (PowerSeries.mk (fun a => (Nat.card {x : Fin n → ℤ // Q x = (a : ℚ)} : ℤ))) =
    ∑ i, ∏ j, (PowerSeries.mk (fun a => (Nat.card (UnaryShell (m j) (w j) (ν i j) a) : ℤ)))
  have hprod (i : Fin (Int.natAbs B.det)) := unary_product_coefficients n m w (ν i) hw
  simp_rw [← hprod]
  apply PowerSeries.ext
  intro a
  simp only [map_sum, PowerSeries.coeff_mk]
  by_cases ha : D ∣ a
  · obtain ⟨b, rfl⟩ := ha
    rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
    let E := Equiv.ofBijective (fun p : Fin (Int.natAbs B.det) × (Fin n → ℤ) =>
      ρ p.1 + B.mulVec p.2) hbij
    let Es : {p : Fin (Int.natAbs B.det) × (Fin n → ℤ) // Q (ρ p.1 + B.mulVec p.2) = (b : ℚ)} ≃
        {x : Fin n → ℤ // Q x = (b : ℚ)} := E.subtypeEquiv (fun _ => Iff.rfl)
    let Et := Equiv.subtypeProdEquivSigmaSubtype
      (fun (i : Fin (Int.natAbs B.det)) (k : Fin n → ℤ) => Q (ρ i + B.mulVec k) = (b : ℚ))
    let Er := Equiv.sigmaCongrRight (fun i : Fin (Int.natAbs B.det) =>
      cosetShellEquiv n m (ν i) (fun j => (hm j).1) D hD hd
        (fun k => Q (ρ i + B.mulVec k))
        (fun k => (orthogonal_residue_formula n A B m hsym hdet
          (fun j => (hm j).1) hgram (ρ i) k).2) b)
    let (i : Fin (Int.natAbs B.det)) : Finite (TupleShell n m w (ν i) (D * b)) :=
      (tuple_shell_finite n m w (ν i) hw (D * b)).to_subtype
    have hc := Nat.card_congr (Es.symm.trans (Et.trans Er))
    rw [Nat.card_sigma] at hc
    exact_mod_cast hc
  · rw [PowerSeries.coeff_expand_of_not_dvd D hD _ ha]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hempty : IsEmpty (TupleShell n m w (ν i) a) := by
      constructor
      intro r
      obtain ⟨b, hb⟩ := total_exponent_integrality n A B m hsym heven hpos hdet hm hgram
        (ρ i) r.val r.property.1
      have he := scaled_energy n m D (fun j => (hm j).1) hd r.val
      rw [hb] at he
      have hr : (∑ j, (w j : ℤ) * r.val j ^ 2) = (a : ℤ) := r.property.2
      change ((∑ j, (w j : ℤ) * r.val j ^ 2 : ℤ) : ℚ) = (D : ℚ) * b at he
      rw [hr] at he
      have hab : a = D * b := by exact_mod_cast he
      exact ha ⟨b, hab⟩
    let := hempty
    simp only [Nat.card_of_isEmpty, Nat.cast_zero]

end ArithmeticThetaCosets
