import AnnularTorsionPrerequisiteDefinitionsR0053
import Mathlib.FieldTheory.KummerExtension

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace ArithmeticThetaAnnularTorsionPrereqR0053

theorem r_gon_representatives :
    ∀ (k : Type u) [Field k] [CharZero k] (r c : ℕ) (ζ : k),
      0 < r → 1 < c → c ∣ r → Nat.Coprime c 6 → IsPrimitiveRoot ζ c →
      (∀ a : Fin c, torsionExponent r c a.val < r ∧
        torsionExponent r c a.val * c = r * a.val) ∧
      (∀ a b : Fin c,
        torsionScalar k r c a.val b.val ζ ^ c =
          (PowerSeries.X : PowerSeries k) ^ (r * a.val)) ∧
      Function.Injective (fun p : Fin c × Fin c =>
        torsionScalar k r c p.1.val p.2.val ζ) ∧
      (∏ a : Fin c, ∏ b : Fin c,
        (Polynomial.X - Polynomial.C
          (torsionScalar k r c a.val b.val ζ))) =
        (∏ a : Fin c,
          ((Polynomial.X : Polynomial (PowerSeries k)) ^ c -
            Polynomial.C ((PowerSeries.X : PowerSeries k) ^ (r * a.val)))) := by
  intro k _ _ r c ζ hr hc hdiv hcop hζ
  have hcpos : 0 < c := by omega
  have hζps : IsPrimitiveRoot (PowerSeries.C ζ : PowerSeries k) c :=
    hζ.map_of_injective PowerSeries.C_injective
  have hexp (a : Fin c) : torsionExponent r c a.val < r ∧
      torsionExponent r c a.val * c = r * a.val := by
    constructor
    · unfold torsionExponent
      apply (Nat.div_lt_iff_lt_mul hcpos).2
      exact Nat.mul_lt_mul_of_pos_left a.isLt hr
    · unfold torsionExponent
      obtain ⟨d, rfl⟩ := hdiv
      have hda : c * d * a.val / c = d * a.val := by
        calc
          c * d * a.val / c = (d * a.val) * c / c := by
            congr 1
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          _ = d * a.val := Nat.mul_div_left _ hcpos
      rw [hda]
      ring
  have hpow (a b : Fin c) :
      torsionScalar k r c a.val b.val ζ ^ c =
        (PowerSeries.X : PowerSeries k) ^ (r * a.val) := by
    unfold torsionScalar
    have hz : (PowerSeries.C (ζ ^ b.val) : PowerSeries k) ^ c = 1 := by
      rw [← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one,
        one_pow, map_one]
    rw [mul_pow, hz, one_mul]
    rw [← pow_mul]
    congr 1
    exact (hexp a).2
  have hinj : Function.Injective (fun p : Fin c × Fin c =>
      torsionScalar k r c p.1.val p.2.val ζ) := by
    intro p q hpq
    have hpc := congrArg (fun x : PowerSeries k => x ^ c) hpq
    rw [hpow p.1 p.2, hpow q.1 q.2] at hpc
    have ha : p.1.val = q.1.val := by
      have hmul : r * p.1.val = r * q.1.val := by
        by_contra hne
        have hc := congrArg (PowerSeries.coeff (R := k) (r * p.1.val)) hpc
        simpa [PowerSeries.coeff_X_pow, hne] using hc
      
      exact Nat.eq_of_mul_eq_mul_left hr hmul
    have haval : p.1 = q.1 := Fin.ext ha
    have hpq' : torsionScalar k r c p.1.val p.2.val ζ =
        torsionScalar k r c p.1.val q.2.val ζ := by
      simpa [haval] using hpq
    have hmono : (PowerSeries.X : PowerSeries k) ^ torsionExponent r c p.1.val ≠ 0 := by
      exact pow_ne_zero _ (PowerSeries.X_ne_zero)
    have hC : PowerSeries.C (ζ ^ p.2.val) =
        PowerSeries.C (ζ ^ q.2.val) := by
      exact (mul_right_inj' (M₀ := PowerSeries k) hmono).mp
        (by simpa [torsionScalar] using hpq')
    have hroot : ζ ^ p.2.val = ζ ^ q.2.val := PowerSeries.C_injective hC
    have hb := hζ.pow_inj p.2.isLt q.2.isLt hroot
    exact Prod.ext haval (Fin.ext hb)
  have hfactor (a : Fin c) :
      ∏ b : Fin c,
        (Polynomial.X - Polynomial.C
          (torsionScalar k r c a.val b.val ζ)) =
        (Polynomial.X : Polynomial (PowerSeries k)) ^ c -
          Polynomial.C ((PowerSeries.X : PowerSeries k) ^ (r * a.val)) := by
    let α : PowerSeries k := PowerSeries.X ^ torsionExponent r c a.val
    have he : α ^ c = (PowerSeries.X : PowerSeries k) ^ (r * a.val) := by
      dsimp [α]
      rw [← pow_mul, (hexp a).2]
    have hprod := X_pow_sub_C_eq_prod hζps hcpos he
    let g : ℕ → Polynomial (PowerSeries k) := fun i =>
      Polynomial.X - Polynomial.C (torsionScalar k r c a.val i ζ)
    have hfin : (∏ b : Fin c, g b.val) =
        ∏ i ∈ Finset.range c, g i := by
      rw [Finset.prod_fin_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp [hi, g]
    rw [show (∏ b : Fin c,
        (Polynomial.X - Polynomial.C
          (torsionScalar k r c a.val b.val ζ))) =
        ∏ b : Fin c, g b.val by rfl]
    rw [hfin]
    simpa [g, α, torsionScalar, mul_comm] using hprod.symm
  refine ⟨?_, ?_, hinj, ?_⟩
  · intro a
    exact hexp a
  · intro a b
    exact hpow a b
  · classical
    refine Finset.prod_congr rfl ?_
    intro a ha
    exact hfactor a

end ArithmeticThetaAnnularTorsionPrereqR0053
