module

public import LiteralSiegelGammaR0160
public import DiscriminantEtaSubstitutionR0160
public import LaurentGammaExistenceR0064

@[expose] public section

/-! Exact power comparison between the accepted unary product and the literal
raised Siegel value. All implementation helpers are private to this module. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaUnaryKatoPowerR0160
namespace UnaryKatoProduct
open ArithmeticThetaUnaryProduct ArithmeticThetaLaurentNormR0064
open ArithmeticThetaMarkedKatoValuesR0159 ArithmeticThetaNormFiniteR0063

private theorem K_nat (N : ℕ) : (1+12*N)^2-1 = 24*N+144*N^2 := by
  have : (1+12*N)^2 = (24*N+144*N^2)+1 := by ring
  omega

private theorem K_divisible (N : ℕ) (hN : Even N) :
    48 * (((1+12*N)^2-1)/48) = (1+12*N)^2-1 := by
  apply Nat.mul_div_cancel'
  obtain ⟨n, rfl⟩ := hN
  rw [K_nat]
  exact ⟨n+12*n^2, by ring⟩

private theorem shift_cast (d m n : ℕ) (ν : ℤ) (hd : 0 < d) (hm : 0 < m)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    (shift (24*d*m^2) (1+12*(m*n)) (d*unaryA m ν) : ℤ) =
      6*(n : ℤ)*((m : ℤ)+2*ν) := by
  let L : ℤ := 6*(n : ℤ)*((m : ℤ)+2*ν)
  have hL : 0 ≤ L := mul_nonneg (by positivity) (by omega)
  have hLc : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL
  have he : (24*d*m^2)*L.toNat = ((1+12*(m*n))-1)*(d*unaryA m ν) := by
    apply Int.ofNat_inj.mp
    simp only [Nat.add_sub_cancel_left]
    push_cast
    rw [hLc, (unary_parameters m ν hm hν).1]
    dsimp [L]
    ring
  unfold shift
  rw [← he, Nat.mul_div_right _ (by positivity : 0 < 24*d*m^2)]
  exact hLc

private theorem exponent (d m N : ℕ) (ν : ℤ) (hd : 0 < d) (hm : 0 < m)
    (hmN : m ∣ N) (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) :
    let r := 24*d*m^2
    let j := d*unaryA m ν
    let c := 1+12*N
    let L : ℤ := shift r c j
    (r : ℤ)*(K c/12)+(j : ℤ)*p c+(j : ℤ)*L+
        (r : ℤ)*(L*(L-1)/2) =
      ((d*unaryB ν : ℕ) : ℤ)*(((1+12*N)^2-1 : ℕ) : ℤ) -
        ((d*m^2 : ℕ) : ℤ)*(((1+12*N)^2-1 : ℕ) : ℤ) := by
  obtain ⟨n, rfl⟩ := hmN
  dsimp only
  rw [shift_cast d m n ν hd hm hν, K_nat]
  have hk : K (1+12*(m*n))/12 = 2*(m : ℤ)*n+12*((m : ℤ)*n)^2 := by
    unfold K
    push_cast
    rw [show (1+12*((m : ℤ)*n))^2-1 =
      (2*(m : ℤ)*n+12*((m : ℤ)*n)^2)*12 by ring, Int.mul_ediv_cancel]
    all_goals norm_num
  have hp : p (1+12*(m*n)) = -6*((m : ℤ)*n)*(1+12*((m : ℤ)*n)) := by
    unfold p triangle
    push_cast
    rw [show (1+12*((m : ℤ)*n))*(1+12*((m : ℤ)*n)-1) =
      (6*((m : ℤ)*n)*(1+12*((m : ℤ)*n)))*2 by ring, Int.mul_ediv_cancel]
    all_goals norm_num
  have hl : (6*(n : ℤ)*((m : ℤ)+2*ν)*(6*(n : ℤ)*((m : ℤ)+2*ν)-1))/2 =
      3*(n : ℤ)*((m : ℤ)+2*ν)*(6*(n : ℤ)*((m : ℤ)+2*ν)-1) := by
    rw [show 6*(n : ℤ)*((m : ℤ)+2*ν)*(6*(n : ℤ)*((m : ℤ)+2*ν)-1) =
      (3*(n : ℤ)*((m : ℤ)+2*ν)*(6*(n : ℤ)*((m : ℤ)+2*ν)-1))*2 by ring,
      Int.mul_ediv_cancel]
    all_goals norm_num
  rw [hk, hp, hl]
  push_cast
  rw [(unary_parameters m ν hm hν).1, unaryB_cast]
  ring

private theorem unary_factorization (k : Type) [Field k] [CharZero k]
    (d m : ℕ) (ν : ℤ) (hd : 0 < d) (hm : 0 < m)
    (hν : -(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) (γ : LaurentSeries k)
    (hγ : IsGamma k (24*d*m^2) (d*unaryA m ν) (-1) γ) :
    unary k d m ν = t k ^ (d*unaryB ν) *
      integerSeries k (PowerSeries.subst (PowerSeries.X^d) (etaProduct (24*m^2))) * γ := by
  have hs := literal_siegel_gamma k d (24*m^2) (unaryA m ν) hd (by positivity)
    (unary_parameters m ν hm hν).2
  have hγeq : integerSeries k (PowerSeries.subst (PowerSeries.X^d)
      (siegelProduct (24*m^2) (unaryA m ν))) = γ := by
    have he : d*(24*m^2) = 24*d*m^2 := by ring
    rw [he] at hs
    obtain ⟨g, hg, hu⟩ := gamma_exists_unique k (24*d*m^2) (d*unaryA m ν) (-1)
      (by positivity) (neg_ne_zero.mpr one_ne_zero)
    exact (hu _ hs).trans (hu _ hγ).symm
  have hsubst := PowerSeries.HasSubst.X_pow (R := ℤ) (Nat.ne_of_gt hd)
  rw [unary, cleared_unary_product m ν hm hν, ← eta_mul_siegel _ _
    (unary_parameters m ν hm hν).2,
    PowerSeries.subst_mul hsubst, PowerSeries.subst_mul hsubst,
    PowerSeries.subst_pow hsubst, PowerSeries.subst_X hsubst,
    map_mul, map_mul, hγeq]
  have ht : integerSeries k ((PowerSeries.X^d)^unaryB ν) = t k^(d*unaryB ν) := by
    simp [integerSeries, ← pow_mul, t, HahnSeries.ofPowerSeries_X_pow,
      HahnSeries.single_pow]
  rw [ht]
  ring

private theorem power_algebra {F : Type} [Field F] (t e g : F) (ht : t ≠ 0)
    (a b n : ℕ) :
    (t^b*e*g)^n = (t^a*e)^n * (t^((b : ℤ)*n-(a : ℤ)*n)*g^n) := by
  simp only [mul_pow]
  simp only [← zpow_natCast, ← zpow_mul]
  calc
    _ = (t^((a : ℤ)*n) * t^((b : ℤ)*n-(a : ℤ)*n)) * (e^(n : ℤ)*g^(n : ℤ)) := by
      rw [← zpow_add₀ ht]
      rw [show (a : ℤ)*n + ((b : ℤ)*n-(a : ℤ)*n) = (b : ℤ)*n by ring]
      ring
    _ = _ := by ring

end UnaryKatoProduct

/-- The complete unary power identity with the literal discriminant and the
exact signed integral Siegel exponent, including the normalized endpoint. -/
theorem unary_kato_product :
    ∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ) (ν : ℤ),
      0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N →
      (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∀ (γ : LaurentSeries k),
      ArithmeticThetaLaurentNormR0064.IsGamma k (24*d*m^2)
        (d*ArithmeticThetaUnaryProduct.unaryA m ν) (-1) γ →
      unary k d m ν ^ ((1+12*N)^2-1) =
        discriminant k (24*d*m^2) ^ (((1+12*N)^2-1)/48) *
          ArithmeticThetaMarkedKatoValuesR0159.siegelPower k (24*d*m^2)
            (1+12*N) (d*ArithmeticThetaUnaryProduct.unaryA m ν) (-1) γ := by
  intro k _ _ d m N ν hd hm _hem _hN heN hmN hν γ hγ
  rw [UnaryKatoProduct.unary_factorization k d m ν hd hm hν γ hγ,
    (discriminant_eta_substitution k d m hd hm).1, ← pow_mul,
    UnaryKatoProduct.K_divisible N heN]
  unfold ArithmeticThetaMarkedKatoValuesR0159.siegelPower
  simp only [map_neg, map_one, neg_neg, one_zpow, one_mul]
  rw [UnaryKatoProduct.exponent d m N ν hd hm hmN hν]
  exact UnaryKatoProduct.power_algebra _ _ _ (by
    simp [ArithmeticThetaLaurentNormR0064.t]) _ _ _

end ArithmeticThetaUnaryKatoPowerR0160

#print axioms ArithmeticThetaUnaryKatoPowerR0160.unary_kato_product
