import GeometricPrerequisiteDefinitions
import UnitRootAlgebra
import ProperFormalFunctions
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open AlgebraicGeometry CategoryTheory Opposite
universe u
noncomputable section

/-! Ordinary semantics for root covers and actual formal sheaf sections. -/
namespace ArithmeticThetaRootTorsor

/-- The distinguished quotient root, with its actual unit-root algebra as codomain. -/
def rootElement (R : Type*) [CommRing R] (N : ℕ) (a : Rˣ) :
    ArithmeticThetaGeometricPrerequisites.unitRootAlgebra R N a :=
  AdjoinRoot.root (Polynomial.X ^ N - Polynomial.C (a : R))


/-- A section is everywhere a generator in actual local trivializations. -/
def IsGeneratingSection (X : Scheme.{u}) (M : X.Modules) (s : Γ(M, ⊤)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
    (e : ArithmeticThetaLineRoot.LocalFrame X M U),
    IsUnit ((e.equiv U le_rfl).symm
      (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s))

/-- The actual canonical iterated pullback of a section, transported over a
commutative triangle by the library pullback-composition and equality maps. -/
def pullbackSectionOver {S T X : Scheme.{u}} (p : T ⟶ X) (f : S ⟶ X)
    (H : X.Modules) (g : {g : S ⟶ T // g ≫ p = f})
    (v : Γ((Scheme.Modules.pullback p).obj H, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj H, ⊤) :=
  ((Scheme.Modules.pullbackCongr g.property).hom.app H).app ⊤
    (((Scheme.Modules.pullbackComp g.val p).hom.app H).app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection g.val
        ((Scheme.Modules.pullback p).obj H) v))

/-- Roots on a test scheme, formed using the genuine tensor-power section map. -/
def RootSections {X S : Scheme.{u}} (H : X.Modules) (N : ℕ)
    (d : Γ(ArithmeticThetaTensorPower.tensorPower X H N, ⊤)) (f : S ⟶ X) :=
  {w : Γ((Scheme.Modules.pullback f).obj H, ⊤) //
    ArithmeticThetaTensorPower.tensorPowerSection S
      ((Scheme.Modules.pullback f).obj H) N ⊤ w =
    ArithmeticThetaNormalizedSections.pullbackPowerSection f H N d}

/-- Actual line-valued sections on each infinitesimal thickening. -/
def FormalLineSections (X : Scheme.{u}) (I : X.IdealSheafData) (H : X.Modules) :=
  ∀ n : ℕ, Γ((Scheme.Modules.pullback (I ^ n).subschemeι).obj H, ⊤)

/-- Compatibility under actual closed-immersion pullbacks, including the
canonical pullback-composition comparison. -/
def CompatibleFormalLineSections (X : Scheme.{u}) (I : X.IdealSheafData)
    (H : X.Modules) (s : FormalLineSections X I H) : Prop :=
  ∀ (m n : ℕ) (h : I ^ n ≤ I ^ m),
    pullbackSectionOver (I ^ n).subschemeι (I ^ m).subschemeι H
      ⟨Scheme.IdealSheafData.inclusion h,
        Scheme.IdealSheafData.inclusion_subschemeι h⟩ (s n) = s m

end ArithmeticThetaRootTorsor

namespace ArithmeticThetaLevelCount
/-- Primitive pairs in the actual residue ring. -/
def PrimitivePair (L : ℕ) := {v : ZMod L × ZMod L // IsCoprime v.1 v.2}
/-- Simultaneous sign orbits; Quot takes the equivalence closure of this relation. -/
def SignedPrimitivePair (L : ℕ) := Quot (fun a b : PrimitivePair L => b.val = -a.val)
/-- The rational product occurring in the manuscript, with no cardinality assumption. -/
def levelIndex (L : ℕ) : ℚ := (L : ℚ) ^ 3 * ∏ p ∈ L.primeFactors, (1 - (p : ℚ)⁻¹ ^ 2)
end ArithmeticThetaLevelCount
