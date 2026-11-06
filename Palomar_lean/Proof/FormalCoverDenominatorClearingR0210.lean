module

public import FormalOpenRestrictionsR0210

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverR0210
namespace FormalCoverDenominatorClearing

variable (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))

/-- Every restriction system preserves the actual structural scalars. -/
lemma map_scalar (ρ : Restrictions k X f) (U V : X.Opens) (h : V ≤ U)
    (r : PowerSeries k) :
    ρ.map U V h (scalar k X f U r) = scalar k X f V r := by
  rw [FormalOpenRestrictions.unique k X f ρ
    (FormalOpenRestrictions.restrictions k X f)]
  exact FormalOpenRestrictions.map_scalar k X f U V h r

lemma map_parameter (ρ : Restrictions k X f) (U V : X.Opens) (h : V ≤ U) :
    ρ.map U V h (parameter k X f U) = parameter k X f V :=
  map_scalar k X f ρ U V h PowerSeries.X

lemma genericMap_scalar (ρ : Restrictions k X f) (U V : X.Opens) (h : V ≤ U)
    (r : PowerSeries k) :
    ρ.genericMap U V h (genericScalar k X f U r) = genericScalar k X f V r := by
  change ρ.genericMap U V h (localize k X f U (scalar k X f U r)) = _
  rw [ρ.generic_extends, map_scalar]
  rfl

lemma localize_parameter_pow (U : X.Opens) (n : ℕ) :
    localize k X f U (parameter k X f U ^ n) =
      genericScalar k X f U (PowerSeries.X ^ n) := by
  change localize k X f U (scalar k X f U PowerSeries.X ^ n) =
    localize k X f U (scalar k X f U (PowerSeries.X ^ n))
  simp only [map_pow]

/-- Raising the annihilating exponent needs no cancellation hypothesis. -/
lemma raise_power {A : Type*} [CommRing A] (t x y : A) {m n : ℕ}
    (hmn : m ≤ n) (h : t ^ m * x = t ^ m * y) :
    t ^ n * x = t ^ n * y := by
  have hn : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
  rw [hn, pow_add, mul_assoc, mul_assoc, h]

/-- A first finite bound clears chart denominators; compatibility is not yet asserted. -/
lemma chart_numerators (C : Cover k X f)
    (z : ∀ i, GenericRing k X f (C.opens i)) :
    ∃ (b : ℕ) (a : ∀ i, FormalRing k X f (C.opens i)),
      ∀ i, localize k X f (C.opens i) (a i) =
        genericScalar k X f (C.opens i) (PowerSeries.X ^ b) * z i := by
  classical
  have h : ∀ i, ∃ (n : ℕ) (a : FormalRing k X f (C.opens i)),
      localize k X f (C.opens i) a =
        genericScalar k X f (C.opens i) (PowerSeries.X ^ n) * z i := by
    intro i
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (parameter k X f (C.opens i)) (z i)
    refine ⟨n, a, ?_⟩
    rw [← localize_parameter_pow, map_pow, mul_comm]
    exact ha.symm
  choose n a ha using h
  let b := Finset.univ.sup n
  have hn : ∀ i, n i ≤ b := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨b, fun i => parameter k X f (C.opens i) ^ (b - n i) * a i, ?_⟩
  intro i
  rw [map_mul, localize_parameter_pow, ha i, ← mul_assoc, ← map_mul,
    ← pow_add, Nat.sub_add_cancel (hn i)]

/-- Equality after localization is killed by one parameter power on each overlap. -/
lemma overlap_power (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, GenericRing k X f (C.opens i)) (hz : LocalCompatible k X f ρ C z)
    (b : ℕ) (a : ∀ i, FormalRing k X f (C.opens i))
    (ha : ∀ i, localize k X f (C.opens i) (a i) =
      genericScalar k X f (C.opens i) (PowerSeries.X ^ b) * z i) :
    ∀ i j, ∃ n : ℕ,
      parameter k X f (C.opens i ⊓ C.opens j) ^ n *
        ρ.map (C.opens i) (C.opens i ⊓ C.opens j) inf_le_left (a i) =
      parameter k X f (C.opens i ⊓ C.opens j) ^ n *
        ρ.map (C.opens j) (C.opens i ⊓ C.opens j) inf_le_right (a j) := by
  intro i j
  apply IsLocalization.Away.exists_of_eq (parameter k X f (C.opens i ⊓ C.opens j))
    (S := GenericRing k X f (C.opens i ⊓ C.opens j))
  change localize k X f _ _ = localize k X f _ _
  rw [← ρ.generic_extends, ← ρ.generic_extends, ha i, ha j,
    map_mul, map_mul, genericMap_scalar, genericMap_scalar, hz i j]

end FormalCoverDenominatorClearing

/-- Uniformly clear both the chart denominators and the overlap discrepancies. -/
theorem formal_cover_denominator_clearing
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))
    (ρ : Restrictions k X f) (C : Cover k X f)
    (z : ∀ i, GenericRing k X f (C.opens i)) :
    LocalCompatible k X f ρ C z →
      ∃ (b : ℕ) (w : ∀ i, FormalRing k X f (C.opens i)),
        Compatible k X f ρ C w ∧
        ∀ i, localize k X f (C.opens i) (w i) =
          genericScalar k X f (C.opens i) (PowerSeries.X ^ b) * z i := by
  classical
  intro hz
  obtain ⟨b, a, ha⟩ := FormalCoverDenominatorClearing.chart_numerators k X f C z
  choose n hn using FormalCoverDenominatorClearing.overlap_power k X f ρ C z hz b a ha
  let d := Finset.univ.sup (fun ij : Fin C.count × Fin C.count => n ij.1 ij.2)
  have hnd : ∀ i j, n i j ≤ d := fun i j =>
    Finset.le_sup (f := fun ij : Fin C.count × Fin C.count => n ij.1 ij.2)
      (Finset.mem_univ (i, j))
  refine ⟨d + b, fun i => parameter k X f (C.opens i) ^ d * a i, ?_, ?_⟩
  · intro i j
    simp only [map_mul, map_pow, FormalCoverDenominatorClearing.map_parameter]
    exact FormalCoverDenominatorClearing.raise_power _ _ _ (hnd i j) (hn i j)
  · intro i
    rw [map_mul, FormalCoverDenominatorClearing.localize_parameter_pow, ha i,
      ← mul_assoc, ← map_mul, ← pow_add]

end ArithmeticThetaFormalCoverR0210

#print axioms ArithmeticThetaFormalCoverR0210.formal_cover_denominator_clearing
