module
public import SplitSquareCoverDegreeR0239
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
end ArithmeticThetaPalomarComponent485
namespace ArithmeticThetaPalomarSplit516
theorem splitSquareCoverDegree : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (x : X.space) (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H)) (b n : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.projection k L D X x) b), ArithmeticThetaSharpCoverR0194.SquareCoverDegree k L D X H x J b n C := by
  exact ArithmeticThetaCyclotomicModularityR0239.split_square_cover_degree
theorem recover_original_074 : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ L), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (x : X.space) (J : ArithmeticThetaSquareLinesR0192.SquareLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.hodge k L D X x H)) (b n : ℕ) (C : ArithmeticThetaSimultaneousUnaryR0187.RootCover k (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.projection k L D X x) b), ArithmeticThetaSharpCoverR0194.SquareCoverDegree k L D X H x J b n C := splitSquareCoverDegree
end ArithmeticThetaPalomarSplit516
