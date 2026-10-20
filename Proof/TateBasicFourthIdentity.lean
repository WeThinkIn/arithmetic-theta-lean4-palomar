module

public import TateGeneralAddition
public import TateThetaJacobiBridge

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
universe u
open scoped PowerSeries.WithPiTopology
namespace BasicEuler
open ArithmeticThetaFormalNorm
variable {k : Type u} [Field k]
noncomputable def basicEulerPartial (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  ∏ r ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (d*r+i))

noncomputable def basicEulerSeries (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk (fun n => PowerSeries.coeff n (basicEulerPartial d i a (n+1)))

theorem basicEuler_stable (d i : ℕ) (a : k) (hd : 0 < d) (n N : ℕ) (hN : n < N) :
    PowerSeries.coeff n (basicEulerPartial d i a N) = PowerSeries.coeff n (basicEulerSeries d i a) := by
  simp only [basicEulerSeries, PowerSeries.coeff_mk]
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    have he : n < d*N+i := by nlinarith
    rw [basicEulerPartial, Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      ← mul_assoc, PowerSeries.coeff_mul_X_pow', if_neg (by omega), sub_zero]
    exact ih

local instance : UniformSpace k := ⊥
local instance : DiscreteUniformity k := ⟨rfl⟩

theorem basicTendstoEuler (d i : ℕ) (a : k) (hd : 0 < d) :
    Filter.Tendsto (basicEulerPartial d i a) Filter.atTop (nhds (basicEulerSeries d i a)) := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto k _ _ _).mpr
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n+1)
  intro N hN
  exact basicEuler_stable d i a hd n N hN

theorem basicEulerPairPartial (d i N : ℕ) :
    basicEulerPartial d i (1 : k) N * basicEulerPartial d i (-1 : k) N =
      basicEulerPartial (2*d) (2*i) (1 : k) N := by
  unfold basicEulerPartial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  simp only [map_one, map_neg, one_mul, neg_mul, sub_neg_eq_add]
  have he : 2*d*r+2*i = (d*r+i)*2 := by ring
  rw [he, pow_mul]
  ring

theorem basicEulerPair (d i : ℕ) (hd : 0 < d) :
    basicEulerSeries d i (1 : k) * basicEulerSeries d i (-1 : k) =
      basicEulerSeries (2*d) (2*i) (1 : k) := by
  have h := (basicTendstoEuler d i (1 : k) hd).mul (basicTendstoEuler d i (-1 : k) hd)
  simp only [basicEulerPairPartial] at h
  exact tendsto_nhds_unique h (basicTendstoEuler (2*d) (2*i) 1 (by omega))

theorem basicEulerSplitPartial (d N : ℕ) (a : k) :
    basicEulerPartial d d a (2*N) =
      basicEulerPartial (2*d) d a N * basicEulerPartial (2*d) (2*d) a N := by
  induction N with
  | zero => simp [basicEulerPartial]
  | succ N ih =>
    have he : 2*(N+1) = (2*N+1)+1 := by omega
    simp only [he, basicEulerPartial, Finset.prod_range_succ] at *
    rw [ih]
    have h1 : d*(2*N)+d=2*d*N+d := by ring
    have h2 : d*(2*N+1)+d=2*d*N+2*d := by ring
    rw [h1,h2]
    ring

theorem basicEulerSplit (d : ℕ) (a : k) (hd : 0 < d) :
    basicEulerSeries d d a = basicEulerSeries (2*d) d a * basicEulerSeries (2*d) (2*d) a := by
  have ht : Filter.Tendsto (fun N : ℕ => 2*N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => show N ≤ 2*N by omega) Filter.tendsto_id
  have h := (basicTendstoEuler d d a hd).comp ht
  simp only [Function.comp_def, basicEulerSplitPartial] at h
  exact tendsto_nhds_unique h ((basicTendstoEuler (2*d) d a (by omega)).mul
    (basicTendstoEuler (2*d) (2*d) a (by omega)))

theorem basicEulerShift (d : ℕ) (a : k) (hd : 0 < d) :
    basicEulerSeries d 0 a = (1-PowerSeries.C a) * basicEulerSeries d d a := by
  have ht : Filter.Tendsto (fun N : ℕ => N+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_add_right N 1) Filter.tendsto_id
  have h := (basicTendstoEuler d 0 a hd).comp ht
  have he (N : ℕ) : basicEulerPartial d 0 a (N+1) =
      (1-PowerSeries.C a) * basicEulerPartial d d a N := by
    unfold basicEulerPartial
    rw [Finset.prod_range_succ']
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero, mul_one, Nat.mul_add]
    ring
  simp only [Function.comp_def, he] at h
  exact tendsto_nhds_unique h (Filter.Tendsto.const_mul (1-PowerSeries.C a)
    (basicTendstoEuler d d a hd))

theorem basicFullGammaEuler (d i : ℕ) (a b : k) (hd : 0 < d) (hi : i ≤ d) :
    fullGamma d i a b = basicEulerSeries d i a * basicEulerSeries d (d-i) b := by
  have he (N : ℕ) : partialGamma d i a b N =
      basicEulerPartial d i a N * basicEulerPartial d (d-i) b N := by
    unfold partialGamma basicEulerPartial
    congr 1
    apply Finset.prod_congr rfl
    intro r hr
    have hn : d*(r+1)-i=d*r+(d-i) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hn]
  apply PowerSeries.ext
  intro n
  simp only [fullGamma, PowerSeries.coeff_mk, he, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [basicEuler_stable d i a hd p.1 (n+1) (by omega),
      basicEuler_stable d (d-i) b hd p.2 (n+1) (by omega)]

theorem basicEulerConstant (d i : ℕ) (a : k) (hi : 0 < i) :
    PowerSeries.coeff 0 (basicEulerSeries d i a) = 1 := by
  simp [basicEulerSeries, basicEulerPartial, show i ≠ 0 by omega]

theorem basicEulerCancellation (d : ℕ) (hd : 0 < d) :
    basicEulerSeries (2*d) d (1 : k) * basicEulerSeries d d (-1 : k) = 1 := by
  have hn : basicEulerSeries (2*d) (2*d) (1 : k) ≠ 0 := by
    intro h
    have hc := basicEulerConstant (2*d) (2*d) (1 : k) (by omega)
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  apply mul_right_cancel₀ hn
  calc
    _ = (basicEulerSeries (2*d) d (1 : k) * basicEulerSeries (2*d) (2*d) (1 : k)) *
        basicEulerSeries d d (-1 : k) := by ring
    _ = basicEulerSeries d d (1 : k) * basicEulerSeries d d (-1 : k) := by
      rw [← basicEulerSplit d (1 : k) hd]
    _ = basicEulerSeries (2*d) (2*d) (1 : k) := basicEulerPair d d hd
    _ = _ := by ring

theorem basicEulerABC (m : ℕ) (hm : 0 < m) :
    basicEulerSeries (2*m) m (1 : k) * basicEulerSeries (2*m) m (-1 : k) *
      basicEulerSeries (2*m) (2*m) (-1 : k) = 1 := by
  rw [mul_assoc, ← basicEulerSplit m (-1 : k) hm]
  exact basicEulerCancellation m hm

end BasicEuler

namespace ArithmeticThetaTateSeries
open ArithmeticThetaTateIdentities

/-- The unary theta fourth-power identity at the marked four-torsion normalization. -/
theorem basic_fourth :
    ∀ {k : Type u} [Field k] [CharZero k],
      theta k ^ 4 = 4 * (tateX 2 1 (1:k) - tateX 2 0 (-1:k)) := by
  intro k _ _
  have ha : Admissible 2 1 (1 : k) := by
    refine ⟨by omega, by omega, one_ne_zero, ?_⟩
    intro h
    omega
  have hb : Admissible 2 0 (-1 : k) := by
    refine ⟨by omega, by omega, by simp, ?_⟩
    intro h
    norm_num
  have hadd := general_annular_addition (k := k) 2 1 0 (1 : k) (-1 : k) ha hb
  have heuler := BasicEuler.basicEulerABC (k := k) 1 (by omega)
  have htheta := theta_jacobi_bridge (k := k)
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
  rw [map_pow, map_mul, map_sub]
  rw [htheta.2]
  have hs : (HahnSeries.single (0 : ℤ) (-1 : k) : LaurentSeries k) = -1 := by
    simp
  have harg : ((1 : k) / (-1 : k)) = (-1 : k) := by
    field_simp
  have hmul : (1 : k) * (-1 : k) = (-1 : k) := by ring
  simp [harg, hmul, hs] at hadd
  have hfull :
      ArithmeticThetaFormalNorm.fullGamma 2 1 (1 : k) ((1 : k)⁻¹) *
          ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹) *
          ArithmeticThetaFormalNorm.fullGamma 2 0 (-1 : k) ((-1 : k)⁻¹) = 2 := by
    rw [inv_one, inv_neg, inv_one,
      BasicEuler.basicFullGammaEuler 2 1 1 1 (by omega) (by omega),
      BasicEuler.basicFullGammaEuler 2 1 (-1) (-1) (by omega) (by omega),
      BasicEuler.basicFullGammaEuler 2 0 (-1) (-1) (by omega) (by omega),
      show 2 - 1 = 1 by omega, Nat.sub_zero,
      BasicEuler.basicEulerShift 2 (-1 : k) (by omega)]
    simp only [map_neg, map_one]
    calc
      _ = 2 * (BasicEuler.basicEulerSeries 2 1 (1 : k) *
        BasicEuler.basicEulerSeries 2 1 (-1 : k) *
        BasicEuler.basicEulerSeries 2 2 (-1 : k)) ^ 2 := by ring
      _ = 2 := by rw [BasicEuler.basicEulerABC (k := k) 1 (by omega)]; ring
  have htwo :
      gammaLaurent 2 (1 : ℤ) (1 : k) *
          gammaLaurent 2 (1 : ℤ) (-1 : k) *
          gammaLaurent 2 (0 : ℤ) (-1 : k) = 2 := by
    have hg1 := gamma_annulus 2 1 (1 : k) (by omega)
    have hgn := gamma_annulus 2 1 (-1 : k) (by omega)
    have hg0 := gamma_annulus 2 0 (-1 : k) (by omega)
    have hg1' : gammaLaurent 2 (1 : ℤ) (1 : k) =
        toLaurent k (ArithmeticThetaFormalNorm.fullGamma 2 1 (1 : k) ((1 : k)⁻¹)) := by
      convert hg1 using 1 <;> norm_num
    have hgn' : gammaLaurent 2 (1 : ℤ) (-1 : k) =
        toLaurent k (ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹)) := by
      convert hgn using 1 <;> norm_num
    have hg0' : gammaLaurent 2 (0 : ℤ) (-1 : k) =
        toLaurent k (ArithmeticThetaFormalNorm.fullGamma 2 0 (-1 : k) ((-1 : k)⁻¹)) := by
      convert hg0 using 1 <;> norm_num
    rw [hg1', hgn', hg0']
    simpa only [map_mul, map_ofNat] using congrArg (toLaurent k) hfull
  have hnonzero :
      gammaLaurent 2 (1 : ℤ) (1 : k) *
          gammaLaurent 2 (0 : ℤ) (-1 : k) ≠ 0 := by
    apply mul_ne_zero
    · exact gamma_admissible_ne_zero 2 1 (1 : k) ha
    · exact gamma_admissible_ne_zero 2 0 (-1 : k) hb
  have hdiff :
      toLaurent k (tateX 2 1 (1 : k)) - toLaurent k (tateX 2 0 (-1 : k)) =
        (toLaurent k (PowerSeries.map (Int.castRingHom k)
          (ArithmeticThetaUnaryProduct.etaProduct 2))) ^ 4 *
          (gammaLaurent 2 (1 : ℤ) (-1 : k)) ^ 4 / 4 := by
    let D := toLaurent k (tateX 2 1 (1 : k)) - toLaurent k (tateX 2 0 (-1 : k))
    let E := toLaurent k (PowerSeries.map (Int.castRingHom k)
      (ArithmeticThetaUnaryProduct.etaProduct 2))
    let A := gammaLaurent 2 (1 : ℤ) (1 : k)
    let B := gammaLaurent 2 (1 : ℤ) (-1 : k)
    let C := gammaLaurent 2 (0 : ℤ) (-1 : k)
    have hadd2 : D * A^2 * C^2 = E^4 * B^2 := by
      calc
        D * A^2 * C^2 = E^4 * B * B := by simpa [D, E, A, B, C] using hadd
        _ = E^4 * B^2 := by ring
    have hcross : 4 * D = E^4 * B^4 := by
      calc
        4 * D = D * (A * B * C)^2 := by rw [htwo]; ring
        _ = (D * A^2 * C^2) * B^2 := by ring
        _ = (E^4 * B^2) * B^2 := by rw [hadd2]
        _ = E^4 * B^4 := by ring
    have h4 : (4 : LaurentSeries k) ≠ 0 := by
      intro h
      have hcast : (4 : LaurentSeries k) = HahnSeries.C (4 : k) :=
        (map_ofNat (HahnSeries.C) 4).symm
      rw [hcast, HahnSeries.C_apply] at h
      simp at h
    apply (eq_div_iff h4).2
    simpa [D, E, B, mul_comm, mul_left_comm, mul_assoc] using hcross
  have hgamma : gammaLaurent 2 (1 : ℤ) (-1 : k) =
      toLaurent k (ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹)) :=
    gamma_annulus 2 1 (-1 : k) (by omega)
  have hgamma' : (HahnSeries.ofPowerSeries ℤ k)
      (ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹)) =
      gammaLaurent 2 (1 : ℤ) (-1 : k) := hgamma.symm
  have hdiff' : toLaurent k (tateX 2 1 (1 : k) - tateX 2 0 (-1 : k)) =
      (toLaurent k (PowerSeries.map (Int.castRingHom k)
        (ArithmeticThetaUnaryProduct.etaProduct 2))) ^ 4 *
        (gammaLaurent 2 (1 : ℤ) (-1 : k)) ^ 4 / 4 := by
    rw [map_sub]
    exact hdiff
  have hdiff'' : (HahnSeries.ofPowerSeries ℤ k)
      (tateX 2 1 (1 : k) - tateX 2 0 (-1 : k)) =
      (toLaurent k (PowerSeries.map (Int.castRingHom k)
        (ArithmeticThetaUnaryProduct.etaProduct 2))) ^ 4 *
        (gammaLaurent 2 (1 : ℤ) (-1 : k)) ^ 4 / 4 := hdiff'
  rw [← map_sub, hdiff'']
  have h4final : (4 : LaurentSeries k) ≠ 0 := by
    intro h
    have hcast : (4 : LaurentSeries k) = HahnSeries.C (4 : k) :=
      (map_ofNat (HahnSeries.C) 4).symm
    rw [hcast, HahnSeries.C_apply] at h
    simp at h
  calc
    (HahnSeries.ofPowerSeries ℤ k
        ((PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct 2)) *
          ArithmeticThetaFormalNorm.fullGamma 2 1 (-1 : k) ((-1 : k)⁻¹))) ^ 4 =
        (toLaurent k (PowerSeries.map (Int.castRingHom k)
          (ArithmeticThetaUnaryProduct.etaProduct 2))) ^ 4 *
          (gammaLaurent 2 (1 : ℤ) (-1 : k)) ^ 4 := by
      rw [map_mul, mul_pow, hgamma']
      rfl
    _ = (HahnSeries.ofPowerSeries ℤ k (4 : PowerSeries k)) *
        ((toLaurent k (PowerSeries.map (Int.castRingHom k)
          (ArithmeticThetaUnaryProduct.etaProduct 2))) ^ 4 *
          (gammaLaurent 2 (1 : ℤ) (-1 : k)) ^ 4 / 4) := by
      rw [map_ofNat]
      field_simp [h4final]

end ArithmeticThetaTateSeries

#print axioms ArithmeticThetaTateSeries.basic_fourth
