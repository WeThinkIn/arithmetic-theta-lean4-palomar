module

public import GeneralDPlusEvenUnimodularR0242
public import GeneralDPlusCoordinatesR0242
public import GeneralDPlusBasisMetricR0242
public import GeneralDPlusDefinitionsR0242
public import Rank16Theta
public import IntegrationDefinitions

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArithmeticThetaGeneralDPlusR0242
namespace ThetaRealization
open ArithmeticThetaRank16

lemma realization_injective (n : ℕ) : Function.Injective (doubledRealization n) := by
  intro x y h
  ext i
  have hi := congrFun h i
  dsimp [doubledRealization] at hi
  exact_mod_cast (by linarith : (x i : ℚ) = (y i : ℚ))

lemma realization_norm (n m : ℕ) (y : Fin n → ℤ) :
    (∑ i, (doubledRealization n y i)^2)/2 = (m : ℚ) ↔
      normNumerator n y = (8*m : ℕ) := by
  change (∑ i, ((y i : ℚ)/2)^2)/2 = (m : ℚ) ↔ _
  rw [rational_norm]
  constructor
  · intro h
    have hq : (normNumerator n y : ℚ) = ((8*m : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq
  · intro h
    rw [h]
    push_cast
    ring

def realizeShell (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    NormShell n (8*m) → OriginalShell n m := fun y =>
  ⟨doubledRealization n y.val, (general_dplus_coordinates n hn).1 y.val |>.mp y.property.1,
    (realization_norm n m y.val).mpr y.property.2⟩

lemma realizeShell_bijective (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    Function.Bijective (realizeShell n hn m) := by
  constructor
  · intro x y h
    exact Subtype.ext (realization_injective n (congrArg Subtype.val h))
  · intro v
    obtain ⟨z, hz, _⟩ := (general_dplus_coordinates n hn).2 v.val |>.mp v.property.1
    let y := (doubledBasis n).mulVec z
    have he : doubledRealization n y = v.val := by
      simpa only [doubled_basis_mul] using hz
    refine ⟨⟨y, Coordinates.doubled_basis_member hn z, ?_⟩, Subtype.ext he⟩
    apply (realization_norm n m y).mp
    rw [he]
    exact v.property.2

noncomputable def shellEquiv (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    OriginalShell n m ≃ NormShell n (8*m) :=
  (Equiv.ofBijective (realizeShell n hn m) (realizeShell_bijective n hn m)).symm

lemma shellEquiv_realizes (n : ℕ) (hn : 8 ∣ n) (m : ℕ) (v : OriginalShell n m) :
    doubledRealization n (shellEquiv n hn m v).val = v.val := by
  exact congrArg Subtype.val ((shellEquiv n hn m).symm_apply_apply v)

theorem originalShell_finite (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    Finite (OriginalShell n m) :=
  Finite.of_equiv (NormShell n (8*m)) (shellEquiv n hn m).symm

lemma original_theta (n : ℕ) (hn : 8 ∣ n) : originalTheta n = theta n := by
  apply PowerSeries.ext
  intro m
  simp only [originalTheta, theta, PowerSeries.coeff_mk]
  exact_mod_cast Nat.card_congr (shellEquiv n hn m)

lemma basis_norm (n : ℕ) (hn : 8 ∣ n) (z : Fin n → ℤ) :
    ((1/2 : ℚ) • ((latticeGram n).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (z i : ℚ)) =
    (∑ i, ((latticeBasis n).mulVec (fun j => (z j : ℚ)) i)^2)/2 := by
  rw [← (general_dplus_basis_metric n hn).2]
  simp only [smul_apply, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', smul_eq_mul]
  change (1/2 : ℚ) * ((fun i => (z i : ℚ)) ⬝ᵥ
    ((latticeBasis n).transpose * latticeBasis n).mulVec (fun i => (z i : ℚ))) = _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, ← pow_two]
  ring

abbrev MatrixShell (n m : ℕ) :=
  {z : Fin n → ℤ //
    ((1/2 : ℚ) • ((latticeGram n).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (z i : ℚ)) = (m : ℚ)}

def basisShell (n : ℕ) (hn : 8 ∣ n) (m : ℕ) : MatrixShell n m → OriginalShell n m :=
  fun z => ⟨(latticeBasis n).mulVec (fun i => (z.val i : ℚ)),
    (Coordinates.original_basis_image n hn _).mpr ⟨z.val, rfl⟩,
    (basis_norm n hn z.val).symm.trans z.property⟩

lemma basisShell_bijective (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    Function.Bijective (basisShell n hn m) := by
  constructor
  · intro x y h
    exact Subtype.ext (Coordinates.lattice_basis_injective n hn (congrArg Subtype.val h))
  · intro v
    obtain ⟨z, hz, _⟩ := (general_dplus_coordinates n hn).2 v.val |>.mp v.property.1
    refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
    rw [basis_norm n hn, hz]
    exact v.property.2

noncomputable def matrixShellEquiv (n : ℕ) (hn : 8 ∣ n) (m : ℕ) :
    MatrixShell n m ≃ OriginalShell n m :=
  Equiv.ofBijective (basisShell n hn m) (basisShell_bijective n hn m)

lemma computed_theta (n : ℕ) (hn : 8 ∣ n) :
    ArithmeticThetaComputed.theta (latticeGram n) =
      PowerSeries.map (Int.castRingHom ℂ) (originalTheta n) := by
  apply PowerSeries.ext
  intro m
  simp only [ArithmeticThetaComputed.theta, originalTheta, PowerSeries.coeff_mk,
    PowerSeries.coeff_map, Int.coe_castRingHom, Int.cast_natCast]
  exact_mod_cast Nat.card_congr (matrixShellEquiv n hn m)

end ThetaRealization

/-- The actual rational lattice theta series agrees in every coefficient with
the doubled and matrix models, in all ranks divisible by eight. -/
theorem general_dplus_theta_realization : ∀ n : ℕ, 8 ∣ n →
    (∀ m : ℕ, ∃ e : OriginalShell n m ≃ ArithmeticThetaRank16.NormShell n (8 * m),
      ∀ v, ArithmeticThetaRank16.doubledRealization n (e v).val = v.val) ∧
    originalTheta n = ArithmeticThetaRank16.theta n ∧
    ArithmeticThetaComputed.theta (ArithmeticThetaRank16.latticeGram n) =
      PowerSeries.map (Int.castRingHom ℂ) (originalTheta n) ∧
    (0 < n → (2 : PowerSeries ℤ) * PowerSeries.expand 8 (by decide) (originalTheta n) =
      ArithmeticThetaHadamard.a ^ n + ArithmeticThetaHadamard.b ^ n +
        ArithmeticThetaHadamard.c ^ n) := by
  intro n hn
  refine ⟨fun m => ⟨ThetaRealization.shellEquiv n hn m,
      ThetaRealization.shellEquiv_realizes n hn m⟩,
    ThetaRealization.original_theta n hn, ThetaRealization.computed_theta n hn, ?_⟩
  intro hpos
  rw [ThetaRealization.original_theta n hn, ArithmeticThetaRank16.expand_actual.1 n hn]
  exact ArithmeticThetaRank16.parity_selection n hpos hn

end ArithmeticThetaGeneralDPlusR0242

#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization
