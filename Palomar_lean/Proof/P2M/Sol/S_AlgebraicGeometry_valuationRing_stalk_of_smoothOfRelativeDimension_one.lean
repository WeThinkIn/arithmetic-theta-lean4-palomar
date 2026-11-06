module

public import Mathlib.Tactic.ReduceModChar
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.PicardGroup
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace SmoothCurveStalk

theorem valuationRing_of_surjective {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B := by
  have : PreValuationRing B := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    obtain ⟨c, h | h⟩ := ValuationRing.cond a b
    · exact ⟨f c, Or.inl (by rw [← map_mul, h])⟩
    · exact ⟨f c, Or.inr (by rw [← map_mul, h])⟩⟩
  exact ⟨⟩

theorem valuationRing_localization_atPrime {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsDomain B] [IsNoetherianRing B] [Algebra.EssFiniteType R B]
    (q : Ideal B) [q.IsPrime] [Algebra.IsUnramifiedAt R q] (hp : (q.under R).IsPrincipal) :
    ValuationRing (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hprinc : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    rw [← hmap]
    obtain ⟨π, hπ⟩ := hp
    refine ⟨⟨algebraMap R _ π, ?_⟩⟩
    rw [hπ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
      Ideal.submodule_span_eq]
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (Localization.AtPrime q)).out 5 2).mp hprinc

theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type*) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective

end SmoothCurveStalk

open SmoothCurveStalk in
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by

  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x

  have hU' : U = ⊤ := top_unique fun y _ => by
    haveI : Subsingleton ↥(Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim y (c x)]
    exact e hxV
  subst hU'
  let ι : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hφ : ((c.appLE ⊤ V e).hom.comp ι.toRingHom).IsStandardSmoothOfRelativeDimension 1 := by
    simpa using hstd.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv ι)

  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  algebraize [g]

  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : IsDomain Γ(C, V) := IsIntegral.component_integral V
  haveI : IsNoetherianRing Γ(C, V) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 1) K) Γ(C, V)
  haveI := isPrincipalIdealRing_mvPolynomial_fin_one K
  let q : Ideal Γ(C, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hq : ValuationRing (Localization.AtPrime q) :=
    valuationRing_localization_atPrime (R := MvPolynomial (Fin 1) K) q
      (IsPrincipalIdealRing.principal _)

  show ValuationRing (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  letI := C.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  let eqv := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  exact valuationRing_of_surjective eqv.toRingEquiv.toRingHom eqv.surjective

end
