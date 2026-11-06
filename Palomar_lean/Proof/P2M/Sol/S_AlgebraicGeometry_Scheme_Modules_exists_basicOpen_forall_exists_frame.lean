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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
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
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.ENatToNat
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤)) (𝔭 : PrimeSpectrum R)
    (hgen : ∀ x : X, f x = 𝔭 → ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by
  classical

  let W : Set X := {x | ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨i, U, hxU, hU⟩
    exact ⟨U, fun y hy => ⟨i, U, hy, hU⟩, U.isOpen, hxU⟩
  let Z : Set (PrimeSpectrum R) := f.base '' Wᶜ
  have hZ : IsClosed Z := f.isClosedMap _ hW.isClosed_compl
  have h𝔭Z : 𝔭 ∈ Zᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hgen x hfx)
  obtain ⟨_, ⟨g, rfl⟩, hg𝔭, hgZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭Z hZ.isOpen_compl
  refine ⟨g, hg𝔭, fun x hx => ?_⟩
  by_contra hx'
  exact hgZ hx ⟨x, hx', rfl⟩
