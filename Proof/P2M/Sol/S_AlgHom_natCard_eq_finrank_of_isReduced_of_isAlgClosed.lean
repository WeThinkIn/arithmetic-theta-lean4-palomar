module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
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
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed

namespace B9

theorem natCard_algHom_eq_finrank (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] : Nat.card (B →ₐ[K] K) = Module.finrank K B := by
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _

  have hquot : ∀ I : MaximalSpectrum B, Module.finrank K (B ⧸ I.asIdeal) = 1 := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)
    have e : K ≃ₗ[K] (B ⧸ I.asIdeal) :=
      LinearEquiv.ofBijective (Algebra.linearMap K (B ⧸ I.asIdeal)) hbij
    rw [← e.finrank_eq, Module.finrank_self]

  let e : B ≃ₐ[K] ((I : MaximalSpectrum B) → B ⧸ I.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := IsArtinianRing.equivPi B) (fun r => by
      ext I
      rfl)

  have hfin : Module.finrank K B = Fintype.card (MaximalSpectrum B) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [hquot]

  have hker_max : ∀ φ : B →ₐ[K] K, (RingHom.ker φ.toRingHom).IsMaximal := fun φ =>
    RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun k => ⟨algebraMap K B k, by simp⟩)
  let kerMap : (B →ₐ[K] K) → MaximalSpectrum B := fun φ => ⟨RingHom.ker φ.toRingHom, hker_max φ⟩
  have hinj : Function.Injective kerMap := by
    intro φ ψ h
    have hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal h
    apply AlgHom.ext
    intro b

    have h1 : b - algebraMap K B (φ b) ∈ RingHom.ker ψ.toRingHom := by
      rw [← hk, RingHom.mem_ker]
      simp
    rw [RingHom.mem_ker] at h1
    have : ψ b - φ b = 0 := by
      simpa [map_sub, AlgHom.commutes] using h1
    linear_combination -this
  have hsurj : Function.Surjective kerMap := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)

    let eI : K ≃ₐ[K] (B ⧸ I.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ I.asIdeal)) hbij
    let φ : B →ₐ[K] K := (eI.symm : (B ⧸ I.asIdeal) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K I.asIdeal)
    refine ⟨φ, ?_⟩
    apply MaximalSpectrum.ext
    show RingHom.ker φ.toRingHom = I.asIdeal
    ext b
    rw [RingHom.mem_ker]
    show eI.symm (Ideal.Quotient.mk I.asIdeal b) = 0 ↔ b ∈ I.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_eq_zero_iff _ eI.symm.injective]
  haveI : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  rw [hfin, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩
end B9

theorem solution (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Nat.card (B →ₐ[K] K) = Module.finrank K B :=
  B9.natCard_algHom_eq_finrank K B
