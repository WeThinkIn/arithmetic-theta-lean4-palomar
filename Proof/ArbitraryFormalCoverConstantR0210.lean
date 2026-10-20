module

public import FormalCoverAlgebraizationR0210
public import FormalCoverDenominatorClearingR0210

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverR0210
namespace ArbitraryFormalCoverConstant

variable (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))

lemma global_scalar (U : X.Opens) (r : PowerSeries k) :
    globalRestriction k X f U
      (ArithmeticThetaFormalConstants.structuralMap (PowerSeries k) X f ⊤ r) =
      scalar k X f U r := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
  change ofSection k X f U
    ((X.presheaf.map (homOfLE le_top).op).hom
      (ArithmeticThetaFormalConstants.structuralMap (PowerSeries k) X f ⊤ r)) =
      ofSection k X f U (ArithmeticThetaFormalConstants.structuralMap (PowerSeries k) X f U r)
  congr 1
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom f (show U ≤ ⊤ from le_top)).commutes r

lemma localize_injective (U : X.Opens) [IsDomain (FormalRing k X f U)]
    (ht : parameter k X f U ≠ 0) : Function.Injective (localize k X f U) := by
  intro a b h
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (parameter k X f U)
    (S := GenericRing k X f U) h
  exact mul_left_cancel₀ (pow_ne_zero n ht) hn

lemma global_injective [IsProper f] (ρ : Restrictions k X f) (C : Cover k X f)
    (a b : Γ(X, ⊤))
    (h : ∀ i, globalRestriction k X f (C.opens i) a =
      globalRestriction k X f (C.opens i) b) : a = b := by
  have hz : Compatible k X f ρ C (fun _ => 0) := by
    intro i j
    simp only [map_zero]
  obtain ⟨g, _, hu⟩ := formal_cover_algebraization k X f ρ C (fun _ => 0) hz
  have h0 : (0 : Γ(X, ⊤)) = g := hu 0 (by intro i; exact map_zero _)
  have hd : a - b = g := hu (a-b) (by intro i; rw [map_sub, h i, sub_self])
  exact sub_eq_zero.mp (hd.trans h0.symm)

lemma regularize (C : Cover k X f) (hC : ChartConditions k X f C)
    (v : ∀ i, Fractions k X f (C.opens i)) (hv : NoPole k X f C v) :
    ∀ i, ∃ z : GenericRing k X f (C.opens i), toFraction k X f (C.opens i) z = v i := by
  intro i
  let : IsDomain (FormalRing k X f (C.opens i)) := (hC i).1
  let : IsNoetherianRing (FormalRing k X f (C.opens i)) := (hC i).2.1
  let : IsIntegrallyClosed (FormalRing k X f (C.opens i)) := (hC i).2.2.1
  let : IsDomain (GenericRing k X f (C.opens i)) := Localization.Away.isDomain (hC i).2.2.2
  let : IsNoetherianRing (GenericRing k X f (C.opens i)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (parameter k X f (C.opens i))) _ inferInstance
  let : IsIntegrallyClosed (GenericRing k X f (C.opens i)) :=
    isIntegrallyClosed_of_isLocalization _ _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (hC i).2.2.2)
  exact ArithmeticThetaSectionCompletion.normal_domain_height_one_intersection
    (GenericRing k X f (C.opens i)) (Fractions k X f (C.opens i)) (v i) (hv i)

lemma domain_one_ne_zero (R : Type*) [CommRing R] [IsDomain R] : (1 : R) ≠ 0 :=
  one_ne_zero

lemma regular_compatible (ρ : Restrictions k X f) (C : Cover k X f)
    (hC : ChartConditions k X f C) (v : ∀ i, Fractions k X f (C.opens i))
    (hv : RationalCompatible k X f ρ C v)
    (z : ∀ i, GenericRing k X f (C.opens i))
    (hz : ∀ i, toFraction k X f (C.opens i) (z i) = v i) :
    LocalCompatible k X f ρ C z := by
  have hone (i : Fin C.count) : (1 : GenericRing k X f (C.opens i)) ≠ 0 := by
    let : IsDomain (FormalRing k X f (C.opens i)) := (hC i).1
    let : IsDomain (GenericRing k X f (C.opens i)) := Localization.Away.isDomain (hC i).2.2.2
    exact domain_one_ne_zero (GenericRing k X f (C.opens i))
  intro i j
  have h := hv i j (z i) 1 (z j) 1 (hone i) (hone j)
    (by rw [map_one, mul_one, hz i]) (by rw [map_one, mul_one, hz j])
  simpa only [map_one, mul_one] using h

end ArbitraryFormalCoverConstant
open ArbitraryFormalCoverConstant

/-- No-pole rational families on arbitrary finite formal covers come from a
unique Laurent scalar through the actual structural maps. -/
theorem arbitrary_formal_cover_constant
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))
    [CharZero k] [Flat f] [IsProper f]
    [Smooth (ArithmeticThetaFormalConstants.genericStructure k X f)]
    [GeometricallyConnected (ArithmeticThetaFormalConstants.genericStructure k X f)] :
    ∃ ρ : Restrictions k X f, ∀ C : Cover k X f,
      ChartConditions k X f C → ∀ v : (∀ i, Fractions k X f (C.opens i)),
      RationalCompatible k X f ρ C v → NoPole k X f C v →
      ∃! c : LaurentSeries k, FractionConstant k X f C v c := by
  classical
  obtain ⟨ρ, _⟩ := formal_open_restrictions k X f
  refine ⟨ρ, ?_⟩
  intro C hC v hv hnopole
  choose z hz using regularize k X f C hC v hnopole
  have hcompat := regular_compatible k X f ρ C hC v hv z hz
  obtain ⟨n, w, hw, hwi⟩ := formal_cover_denominator_clearing k X f ρ C z hcompat
  obtain ⟨a, ha, _⟩ := formal_cover_algebraization k X f ρ C w hw
  obtain ⟨r, hr⟩ := (ArithmeticThetaFormalConstants.proper_model_global_constants k X f).surjective a
  have hri (i : Fin C.count) : genericScalar k X f (C.opens i) r =
      genericScalar k X f (C.opens i) (PowerSeries.X ^ n) * z i := by
    change localize k X f (C.opens i) (scalar k X f (C.opens i) r) = _
    rw [← global_scalar, hr, ha i, hwi i]
  let A := algebraMap (PowerSeries k) (LaurentSeries k)
  have hA : Function.Injective A := IsFractionRing.injective _ _
  have ht (m : ℕ) : A ((PowerSeries.X : PowerSeries k)^m) ≠ 0 := by
    exact fun h => (pow_ne_zero m PowerSeries.X_ne_zero) (hA (h.trans (map_zero A).symm))
  let c : LaurentSeries k := A r / A ((PowerSeries.X : PowerSeries k)^n)
  have hc : A r = A ((PowerSeries.X : PowerSeries k)^n) * c :=
    (mul_div_cancel₀ (A r) (ht n)).symm
  refine ⟨c, ⟨n, r, hc, ?_⟩, ?_⟩
  · intro i
    rw [hri i, map_mul, hz i]
  · intro d hd
    obtain ⟨m, s, hs, hsi⟩ := hd
    have he : (PowerSeries.X : PowerSeries k)^n * s = PowerSeries.X^m * r := by
      apply (ArithmeticThetaFormalConstants.proper_model_global_constants k X f).injective
      apply global_injective k X f ρ C
      intro i
      rw [global_scalar, global_scalar]
      let : IsDomain (FormalRing k X f (C.opens i)) := (hC i).1
      let : IsDomain (GenericRing k X f (C.opens i)) := Localization.Away.isDomain (hC i).2.2.2
      apply localize_injective k X f (C.opens i) (hC i).2.2.2
      apply IsFractionRing.injective (GenericRing k X f (C.opens i)) (Fractions k X f (C.opens i))
      change toFraction k X f (C.opens i) (genericScalar k X f (C.opens i) (PowerSeries.X^n*s)) =
        toFraction k X f (C.opens i) (genericScalar k X f (C.opens i) (PowerSeries.X^m*r))
      rw [map_mul, map_mul, map_mul, map_mul, hsi i, hri i, map_mul, hz i]
      ac_rfl
    have heA := congrArg A he
    rw [map_mul, map_mul] at heA
    change A (PowerSeries.X^n) * A s = A (PowerSeries.X^m) * A r at heA
    rw [hs, hc] at heA
    apply mul_left_cancel₀ (mul_ne_zero (ht n) (ht m))
    simpa only [← mul_assoc, mul_comm (A (PowerSeries.X^m)) (A (PowerSeries.X^n))] using heA

end ArithmeticThetaFormalCoverR0210

#print axioms ArithmeticThetaFormalCoverR0210.arbitrary_formal_cover_constant
