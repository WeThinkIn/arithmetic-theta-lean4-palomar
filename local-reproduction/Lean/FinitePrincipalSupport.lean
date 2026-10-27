import Mathlib
import FunctionOrders
import SmoothPrerequisites
import CurveDegreeDefinitions

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped nonZeroDivisors

-- Re-export the scheme names used by the frozen contract's exact-type probe.
-- The proof itself continues to use the actual Mathlib declarations.
export AlgebraicGeometry (Scheme Spec IsIntegral IsLocallyNoetherian IsProper)

universe u
noncomputable section

namespace ArithmeticThetaCurveDegree

private lemma finite_zero_locus_of_dimension_one
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] (a : R) (ha : a ≠ 0) :
    (PrimeSpectrum.zeroLocus ({a} : Set R)).Finite := by
  let I : Ideal R := Ideal.span ({a} : Set R)
  have hmin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  have hsub : PrimeSpectrum.zeroLocus ({a} : Set R) ⊆
      (fun p : I.minimalPrimes => (⟨p.1, p.2.1.1⟩ : PrimeSpectrum R)) '' (Set.univ : Set I.minimalPrimes) := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
      (I := I) (J := p.asIdeal) (Ideal.span_le.mpr (by simpa [I] using hp))
    have haq : a ∈ q := by
      exact Ideal.span_le.mp hq.1.2 (by simp [I])
    have hqne : q ≠ ⊥ := by
      intro hq0
      exact ha (by simpa [hq0] using haq)
    have hqmax : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hqne hq.1.1
    have hpeq : q = p.asIdeal := hqmax.eq_of_le p.isPrime.ne_top hqp
    refine ⟨⟨q, hq⟩, trivial, ?_⟩
    exact PrimeSpectrum.ext hpeq
  letI : Finite I.minimalPrimes := hmin.to_subtype
  apply Set.Finite.subset
    (Set.Finite.image (fun p : I.minimalPrimes => (⟨p.1, p.2.1.1⟩ : PrimeSpectrum R))
      (Set.toFinite (Set.univ : Set I.minimalPrimes)))
  exact hsub

private lemma finite_nonunit_germs
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hdim : Ring.DimensionLEOne Γ(X, U)) (a : Γ(X, U)) (ha : a ≠ 0) :
    Set.Finite {x : U | ¬ IsUnit (X.presheaf.germ U x x.2 a)} := by
  letI : Ring.DimensionLEOne Γ(X, U) := hdim
  let f : U → PrimeSpectrum Γ(X, U) := hU.primeIdealOf
  have hf : Function.Injective f := hU.isoSpec.hom.injective
  have hz : (PrimeSpectrum.zeroLocus ({a} : Set Γ(X, U))).Finite := by
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact finite_zero_locus_of_dimension_one Γ(X, U) a ha
  apply Set.Finite.of_finite_image (f := f)
  · apply hz.subset
    rintro p ⟨x, hx, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    rw [Set.singleton_subset_iff]
    by_contra hnot
    apply hx
    let y : Spec (CommRingCat.of Γ(X, U)) := ⟨(f x).asIdeal, (f x).isPrime⟩
    have hy : y = f x := by rfl
    have hbasic : hU.fromSpec y ∈ X.basicOpen a := by
      change y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a
      rw [hU.fromSpec_preimage_basicOpen]
      change a ∉ y.asIdeal
      simpa [y] using hnot
    rw [hy, hU.fromSpec_primeIdealOf x] at hbasic
    exact (Scheme.mem_basicOpen X a x.1 x.2).mp hbasic
  · intro x hx y hy hxy
    exact hf hxy

private lemma dimension_one_of_chart
    (X : Scheme.{u}) (hcurve : OneDimensionalCharts X)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Ring.DimensionLEOne Γ(X, U) := hcurve U hU

private lemma ord_of_germ_isUnit
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (x : X) (hx : x ∈ U)
    (a : Γ(X, U)) (ha : IsUnit (X.presheaf.germ U x hx a)) :
    Scheme.ord (X.germToFunctionField U a) x = 0 := by
  by_cases hco : Order.coheight x = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hco.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hco]
    have h1 : Scheme.ordHom x hco (X.germToFunctionField U a) = 1 := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx a]
      change Ring.ordFrac (X.presheaf.stalk x)
        (algebraMap (X.presheaf.stalk x) X.functionField
          (X.presheaf.germ U x hx a)) = 1
      rw [Ring.ordFrac_of_isUnit ha]
    rw [h1]
    simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hco _

private lemma support_on_chart
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) (hg : g ≠ 0) :
    Set.Finite {x : X | ∃ hx : x ∈ U, Scheme.ord g x ≠ 0} := by
  let R := Γ(X, U)
  let K := X.functionField
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : Ring.DimensionLEOne R := hcurve U hU
  letI : Nonempty U := inferInstance
  letI : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨z, hz⟩ := IsLocalization.surj (R⁰ : Submonoid R) g
  let a : R := z.1
  let b : R⁰ := z.2
  have hga : a ≠ 0 := by
    intro ha
    have hbm : (algebraMap R K) (b : R) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).2
        (mem_nonZeroDivisors_iff_ne_zero.mp b.2)
    exact hg (by simpa [a, ha] using hz)
  have hsub : {x : X | ∃ hx : x ∈ U, Scheme.ord g x ≠ 0} ⊆
      {x : X | ∃ hx : x ∈ U, ¬ IsUnit (X.presheaf.germ U x hx a)} ∪
      {x : X | ∃ hx : x ∈ U, ¬ IsUnit (X.presheaf.germ U x hx (b : R))} := by
    intro x hx
    obtain ⟨hxU, hxord⟩ := hx
    by_cases haunit : IsUnit (X.presheaf.germ U x hxU a)
    · by_cases hbunit : IsUnit (X.presheaf.germ U x hxU (b : R))
      · exfalso
        have hmul := Scheme.ord_mul (X := X) (x := x) hg (show (algebraMap R K) (b : R) ≠ 0 from
          (map_ne_zero_iff (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)).2
            (mem_nonZeroDivisors_iff_ne_zero.mp b.2))
        have horda : Scheme.ord ((algebraMap R K) a) x = 0 := by
          exact ord_of_germ_isUnit X U x hxU a haunit
        have hordb : Scheme.ord ((algebraMap R K) (b : R)) x = 0 := by
          exact ord_of_germ_isUnit X U x hxU (b : R) hbunit
        have heq : Scheme.ord (g * (algebraMap R K) (b : R)) x =
            Scheme.ord ((algebraMap R K) a) x := by rw [hz]
        rw [hmul, horda, hordb] at heq
        exact hxord (by simpa using heq)
      · exact Or.inr ⟨hxU, hbunit⟩
    · exact Or.inl ⟨hxU, haunit⟩
  have hfin :=
    (finite_nonunit_germs X U hU (hcurve U hU) a hga).image (fun x : U => (x : X))
  have hfin' :=
    (finite_nonunit_germs X U hU (hcurve U hU) (b : R)
      (mem_nonZeroDivisors_iff_ne_zero.mp b.2)).image (fun x : U => (x : X))
  apply (hfin.union hfin').subset
  intro x hx
  rcases hsub hx with h | h
  · rcases h with ⟨hxU, h⟩
    exact Or.inl ⟨⟨x, hxU⟩, by simpa using h, rfl⟩
  · rcases h with ⟨hxU, h⟩
    exact Or.inr ⟨⟨x, hxU⟩, by simpa using h, rfl⟩

/-- A nonzero function on a proper one-dimensional integral scheme has finite order support. -/
theorem finite_principal_support
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hcurve : OneDimensionalCharts X) (g : X.functionField) :
    g ≠ 0 → Set.Finite {x : X | principalOrder X g x ≠ 0} := by
  intro hg
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let 𝒰₀ := X.affineCover
  let 𝒰 := 𝒰₀.finiteSubcover
  have hcover : ∀ x : X, ∃ i : 𝒰.I₀, ∃ y : 𝒰.X i, 𝒰.f i y = x := by
    intro x
    exact 𝒰.exists_eq x
  let S : 𝒰.I₀ → Set X := fun i =>
    {x : X | ∃ hx : x ∈ (𝒰.f i).opensRange, Scheme.ord g x ≠ 0}
  have hSi : ∀ i : 𝒰.I₀, (S i).Finite := by
    intro i
    let V := (𝒰.f i).opensRange
    let hV : IsAffineOpen V := isAffineOpen_opensRange _
    letI : Nonempty (𝒰.X i) := by
      change Nonempty (𝒰₀.X (𝒰₀.idx i.1))
      exact ⟨(𝒰₀.covers i.1).choose⟩
    letI : Nonempty V := by
      obtain ⟨y⟩ := (inferInstance : Nonempty (𝒰.X i))
      exact ⟨⟨𝒰.f i y, ⟨y, rfl⟩⟩⟩
    have hs := support_on_chart X V hV hcurve g hg
    simpa [S, V] using hs
  let hindices : (Set.univ : Set 𝒰.I₀).Finite := Set.toFinite _
  apply Set.Finite.subset (hindices.biUnion (fun i _ => hSi i))
  intro x hx
  obtain ⟨i, y, rfl⟩ := hcover x
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨by trivial, ⟨⟨y, rfl⟩, hx⟩⟩⟩

end ArithmeticThetaCurveDegree

#print axioms ArithmeticThetaCurveDegree.finite_principal_support
