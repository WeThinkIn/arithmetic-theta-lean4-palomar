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
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Topology.Sheaves.Init
public import P2M.Util

@[expose] public section
namespace P2MW.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat

set_option autoImplicit false

universe u

open TensorProduct

namespace QFDescent

theorem Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.QuasiFinite T (T ⊗[R] S)] : Algebra.QuasiFinite R S := by
  refine ⟨fun P _ => ?_⟩

  obtain ⟨⟨Q, hQprime⟩, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := T) ⟨P, ‹_›⟩
  have hQP : Q.comap (algebraMap R T) = P := congrArg PrimeSpectrum.asIdeal hQ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩

  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T) hQP.symm).toRingHom.toAlgebra
  haveI : IsScalarTower R P.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => ((Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T) hQP.symm).commutes r).symm

  have hfin : Module.Finite Q.ResidueField (Q.Fiber (T ⊗[R] S)) := Algebra.QuasiFinite.finite_fiber Q
  let e₁ := Algebra.TensorProduct.cancelBaseChange R T Q.ResidueField Q.ResidueField S
  let e₂ := Algebra.TensorProduct.cancelBaseChange R P.ResidueField Q.ResidueField Q.ResidueField S
  haveI : Module.Finite Q.ResidueField (Q.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[R] S)) :=
    Module.Finite.equiv (e₁.trans e₂.symm).toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (R := P.ResidueField) Q.ResidueField
    (M := P.ResidueField ⊗[R] S)

end QFDescent

namespace RingHom
p2m_export "RingHom" "QuasiFinite.respectsIso Finite QuasiFinite CodescendsAlong faithfullyFlat_algebraMap_iff FaithfullyFlat mk quasiFinite_algebraMap toAlgebra"
p2m_open "RingHom"

namespace QuasiFinite p2m_export "RingHom.QuasiFinite" "toAlgebra respectsIso" end QuasiFinite
p2m_open_scoped "RingHom.QuasiFinite" in
theorem QuasiFinite.codescendsAlong_faithfullyFlat' : CodescendsAlong QuasiFinite FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact QFDescent.Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat S

end RingHom

theorem solution :
    RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
      (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) :=
  RingHom.QuasiFinite.codescendsAlong_faithfullyFlat'
