module
public import Mathlib
public import GeometricComponentCuspBoundR0184
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
def componentOpen (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, componentIsOpen k L D X x⟩
abbrev Component (x : X.space) : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion (x : X.space) : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
def cuspSet (x : X.space) : Set (Component k L D X x) := {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps (x : X.space) := {y : Component k L D X x // y ∈ cuspSet k L D X x}
theorem componentOpen_eq_original (x : X.space) : componentOpen k L D X x = ArithmeticThetaComponentDegreeR0184.componentOpen k L D X x := by
  apply TopologicalSpace.Opens.ext
  rfl
theorem geometricComponentCuspBound :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaPalomarComponent485.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaPalomarComponent485.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  intro k _ _ _ L hL heven D X x
  exact ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound k L hL heven D X x
theorem recover_original_029 :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by
  intro k _ _ _ L hL heven D X x
  exact geometricComponentCuspBound k L hL heven D X x
end ArithmeticThetaPalomarComponent485
