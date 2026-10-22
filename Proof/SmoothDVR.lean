module

public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Formal smoothness of essentially finite-type DVRs

The two local algebra lemmas below adapt the proofs in the installed FLT library:
`S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.lean`
and `S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField.lean`.
They are reproduced here with fresh compilation and no dependency on FLT wrappers.
-/

set_option autoImplicit false
universe u v
namespace ArithmeticThetaNormalizedCurve

open IsLocalRing Polynomial

attribute [local instance] Ideal.Quotient.field

/-- A nonzero principal maximal ideal gives formal smoothness when the residue
field extension is algebraic and separable. The polynomial coordinate and its
étaleness are constructed in the proof. -/
theorem formallySmooth_of_separable_residue
    (K₀ : Type u) [Field K₀] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u})
    [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)] [Algebra.IsSeparable K₀ (ResidueField 𝒪)] :
    Algebra.FormallySmooth K₀ 𝒪 := by
  classical

  let A : Subalgebra K₀ 𝒪 := Algebra.EssFiniteType.subalgebra K₀ 𝒪
  let M : Submonoid A := Algebra.EssFiniteType.submonoid K₀ 𝒪
  haveI hlocM : IsLocalization M 𝒪 := Algebra.EssFiniteType.isLocalization K₀ 𝒪
  obtain ⟨⟨a, sM⟩, has⟩ := IsLocalization.surj M u

  have hsunit : IsUnit (algebraMap A 𝒪 (sM : A)) := IsLocalization.map_units 𝒪 sM
  have hspan : maximalIdeal 𝒪 = Ideal.span {algebraMap A 𝒪 a} := by
    rw [hu, ← has]
    exact (Ideal.span_singleton_mul_right_unit hsunit u).symm
  have ha𝔪 : algebraMap A 𝒪 a ∈ maximalIdeal 𝒪 := hspan ▸ Ideal.mem_span_singleton_self _
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hu0
    have : u * algebraMap A 𝒪 (sM : A) = 0 := by rw [has, map_zero]
    exact (hsunit.mul_left_eq_zero).mp this

  let Q : Ideal A := (maximalIdeal 𝒪).comap (algebraMap A 𝒪)
  haveI hQprime : Q.IsPrime := Ideal.IsPrime.comap _
  have haQ : a ∈ Q := ha𝔪
  have hMQ : M = Q.primeCompl := by
    ext x
    change IsUnit (algebraMap A 𝒪 x) ↔ x ∉ Q
    change _ ↔ algebraMap A 𝒪 x ∉ maximalIdeal 𝒪
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
  haveI hlocQ : IsLocalization.AtPrime 𝒪 Q := by
    change IsLocalization Q.primeCompl 𝒪
    rw [← hMQ]; exact hlocM

  let eA : 𝒪 ≃ₐ[A] Localization.AtPrime Q := IsLocalization.algEquiv Q.primeCompl 𝒪 (Localization.AtPrime Q)
  let eK : 𝒪 ≃ₐ[K₀] Localization.AtPrime Q := eA.restrictScalars K₀

  have hQtop : Q ≠ ⊤ := hQprime.ne_top
  have ha : Transcendental K₀ a := by
    intro halg
    have hint : IsIntegral K₀ a := halg.isIntegral
    have hc : (minpoly K₀ a).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint ha0
    have h := minpoly.aeval K₀ a
    rw [← (minpoly K₀ a).X_mul_divX_add, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    have key : algebraMap K₀ A ((minpoly K₀ a).coeff 0) = -(a * Polynomial.aeval a (minpoly K₀ a).divX) :=
      eq_neg_of_add_eq_zero_right h
    exact hQtop (Q.eq_top_of_isUnit_mem (key ▸ Q.neg_mem (Q.mul_mem_right _ haQ)) ((IsUnit.mk0 _ hc).map _))

  letI alg : Algebra K₀[X] A := (Polynomial.aeval a : K₀[X] →ₐ[K₀] A).toRingHom.toAlgebra
  have halg : ∀ f : K₀[X], algebraMap K₀[X] A f = Polynomial.aeval a f := fun _ => rfl
  haveI : IsScalarTower K₀ K₀[X] A :=
    IsScalarTower.of_algebraMap_eq fun k => ((Polynomial.aeval a).commutes k).symm
  haveI : IsScalarTower K₀ K₀[X] (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K₀ A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀ K₀[X] A]
  haveI : Module.IsTorsionFree K₀[X] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ha)
  haveI : Module.Flat K₀[X] A := inferInstance
  haveI : Algebra.FiniteType K₀[X] A := Algebra.FiniteType.of_restrictScalars_finiteType K₀ K₀[X] A
  haveI : Algebra.FinitePresentation K₀[X] A := (Algebra.FinitePresentation.of_finiteType).mp ‹_›

  let ι : (A ⧸ Q) →ₐ[K₀] ResidueField 𝒪 :=
    Ideal.quotientMapₐ (maximalIdeal 𝒪) (IsScalarTower.toAlgHom K₀ A 𝒪) le_rfl
  have hι : Function.Injective ι := Ideal.quotientMap_injective
  haveI : Algebra.IsAlgebraic K₀ (A ⧸ Q) := Algebra.IsAlgebraic.of_injective ι hι
  haveI : Algebra.IsIntegral K₀ (A ⧸ Q) := Algebra.IsAlgebraic.isIntegral
  haveI hQmax : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField' (Field.toIsField K₀))
  haveI : Algebra.IsSeparable K₀ (A ⧸ Q) := Algebra.IsSeparable.of_algHom _ _ ι

  have hXp : (X : K₀[X]) ∈ Q.under K₀[X] := by
    change algebraMap K₀[X] A X ∈ Q
    rwa [halg, Polynomial.aeval_X]
  haveI : (Q.under K₀[X]).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h =>
      Polynomial.X_ne_zero ((Submodule.eq_bot_iff _).mp h X hXp)
  letI := Localization.AtPrime.algebraOfLiesOver (Q.under K₀[X]) Q
  haveI : Algebra.IsSeparable (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable K₀ (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q)

  haveI : Algebra.IsUnramifiedAt K₀[X] Q := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := Q.under K₀[X])]
    refine ⟨Algebra.isSeparable_residueField_iff.mpr inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hf
    · intro z hz

      have hz' : eA.symm z ∈ maximalIdeal 𝒪 := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
        exact fun h => hz (by simpa using h.map eA)
      rw [hspan, Ideal.mem_span_singleton'] at hz'
      obtain ⟨r, hr⟩ := hz'
      have hz'' : z = eA r * algebraMap K₀[X] (Localization.AtPrime Q) X := by
        rw [IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q), halg, Polynomial.aeval_X,
          ← eA.commutes a, ← map_mul, hr, AlgEquiv.apply_symm_apply]
      rw [hz'']
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hXp)

  haveI : Algebra.IsEtaleAt K₀[X] Q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  haveI : Algebra.FormallySmooth K₀[X] (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth K₀ (Localization.AtPrime Q) :=
    Algebra.FormallySmooth.comp K₀ K₀[X] (Localization.AtPrime Q)
  exact Algebra.FormallySmooth.of_equiv eK.symm

open IsLocalRing

/-- Lift a separating transcendence basis to reduce to algebraic separable
residue fields. This retains essential finite type throughout. -/
theorem formallySmooth_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by
  classical

  haveI : Algebra.EssFiniteType K (ResidueField 𝒪) :=
    Algebra.EssFiniteType.comp K 𝒪 (ResidueField 𝒪)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K (ResidueField 𝒪)
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) ((↑) : s → ResidueField 𝒪)) :=
    algebraicIndependent_iff_injective_aeval.1 hs.1

  choose t ht using fun x : s => IsLocalRing.residue_surjective (R := 𝒪) (x : ResidueField 𝒪)
  let P := MvPolynomial s K
  let φ : P →ₐ[K] 𝒪 := MvPolynomial.aeval t
  have hφres : ∀ f : P, IsLocalRing.residue 𝒪 (φ f) = MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) f := by
    intro f
    have hcomp : ((IsScalarTower.toAlgHom K 𝒪 (ResidueField 𝒪)).comp φ) =
        MvPolynomial.aeval ((↑) : s → ResidueField 𝒪) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp [φ, ht i]
    exact congrArg (fun g : P →ₐ[K] ResidueField 𝒪 => g f) hcomp

  have hunit : ∀ f : P, f ≠ 0 → IsUnit (φ f) := by
    intro f hf
    by_contra h
    have hmem : φ f ∈ maximalIdeal 𝒪 := h
    have h0 : IsLocalRing.residue 𝒪 (φ f) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hφres] at h0
    exact hf (hinj (by rw [h0, map_zero]))

  let K₀ := FractionRing P
  let ψ : K₀ →ₐ[K] 𝒪 := IsLocalization.liftAlgHom (M := nonZeroDivisors P) (f := φ)
    (fun y => hunit y.1 (nonZeroDivisors.ne_zero y.2))
  letI : Algebra K₀ 𝒪 := ψ.toRingHom.toAlgebra
  have hψ : ∀ z : K₀, algebraMap K₀ 𝒪 z = ψ z := fun _ => rfl
  haveI : IsScalarTower K K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hψ, ψ.commutes]
  letI : Algebra P 𝒪 := φ.toRingHom.toAlgebra
  have hφ : ∀ f : P, algebraMap P 𝒪 f = φ f := fun _ => rfl
  haveI : IsScalarTower P K₀ 𝒪 := IsScalarTower.of_algebraMap_eq fun f => by
    rw [hψ, hφ]
    change φ f = IsLocalization.lift (M := nonZeroDivisors P) _ (algebraMap P K₀ f)
    rw [IsLocalization.lift_eq]
    rfl

  haveI : Algebra.FormallySmooth P K₀ := Algebra.FormallySmooth.of_isLocalization (Rₘ := K₀) (nonZeroDivisors P)
  haveI : Algebra.FormallySmooth K K₀ := Algebra.FormallySmooth.comp K P K₀
  haveI : Algebra.EssFiniteType K₀ 𝒪 := Algebra.EssFiniteType.of_comp K K₀ 𝒪

  let F : IntermediateField K (ResidueField 𝒪) := IntermediateField.adjoin K (Set.range ((↑) : s → ResidueField 𝒪))
  let e : K₀ ≃ₐ[K] F := hs.1.aevalEquivField
  have hrange : (Set.range ((↑) : s → ResidueField 𝒪)) = (s : Set (ResidueField 𝒪)) := by
    ext x; simp
  haveI : Algebra.IsSeparable F (ResidueField 𝒪) := by
    have : F = IntermediateField.adjoin K (s : Set (ResidueField 𝒪)) := by rw [← hrange]
    rw [this]; exact hsep
  have hcompat : (algebraMap K₀ (ResidueField 𝒪)).comp (e.symm.toRingEquiv : F →+* K₀) =
      (RingEquiv.refl (ResidueField 𝒪) : ResidueField 𝒪 →+* ResidueField 𝒪).comp (algebraMap F (ResidueField 𝒪)) := by

    have key : (algebraMap K₀ (ResidueField 𝒪)) = (algebraMap F (ResidueField 𝒪)).comp (e.toRingEquiv : K₀ →+* F) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors P) ?_
      ext f
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.C f)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.C f) =
          ((e (algebraMap P K₀ (MvPolynomial.C f)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [IsScalarTower.algebraMap_apply K₀ 𝒪 (ResidueField 𝒪), ← IsScalarTower.algebraMap_apply P K₀ 𝒪]
        change IsLocalRing.residue 𝒪 (φ (MvPolynomial.X _)) = _
        rw [hφres]
        change MvPolynomial.aeval _ (MvPolynomial.X _) =
          ((e (algebraMap P K₀ (MvPolynomial.X _)) : F) : ResidueField 𝒪)
        rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    rw [key]
    ext x
    simp
  haveI : Algebra.IsSeparable K₀ (ResidueField 𝒪) :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : F ≃+* K₀) (RingEquiv.refl (ResidueField 𝒪)) hcompat
  haveI : Algebra.IsAlgebraic K₀ (ResidueField 𝒪) := Algebra.IsSeparable.isAlgebraic _ _

  haveI := formallySmooth_of_separable_residue K₀ 𝒪 u hu0 hu
  exact Algebra.FormallySmooth.comp K K₀ 𝒪


/-- Every essentially finite-type DVR over a characteristic-zero field is
formally smooth over that field. -/
theorem dvr_formallySmooth :
    ∀ (k : Type u) [Field k] [CharZero k] (A : Type v) [CommRing A]
      [IsDomain A] [Algebra k A] [IsDiscreteValuationRing A]
      [Algebra.EssFiniteType k A], Algebra.FormallySmooth k A := by
  intro k _ _ A _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact formallySmooth_of_perfectField k A π hπ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ)

end ArithmeticThetaNormalizedCurve

#print axioms ArithmeticThetaNormalizedCurve.dvr_formallySmooth
