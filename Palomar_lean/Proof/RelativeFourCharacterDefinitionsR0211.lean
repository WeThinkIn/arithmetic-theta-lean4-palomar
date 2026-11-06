module

public import RelativeAlphaNaturalityR0190
public import GeometricFourCharacterR0118
public import CoordinateChangeCovarianceR0115
public import GeometricFourPairingDefinitionsR0118
public import GlobalFourTorsionDefinitionsR0190

@[expose] public section

/-! The actual relative marking action and its geometric four-pairing value.
No character law, action existence, or scalar existence is a definition field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)

/-- The source right action: the jth column gives a*x+b*y. -/
def Changes {T : Scheme.{u}} (t : T ⟶ Base R)
    (M M' : FullLevel R W G 4 t) (A : ArithmeticThetaFourTorsion.Mat4) : Prop :=
  M'.x = G.mul t (G.nsmul t (A 0 0).val M.x) (G.nsmul t (A 1 0).val M.y) ∧
  M'.y = G.mul t (G.nsmul t (A 0 1).val M.x) (G.nsmul t (A 1 1).val M.y)

variable [Algebra ℚ R] (M : FullLevel R W G 4 (𝟙 (Base R)))

/-- Affine coordinates on the original curve, before completing the square. -/
def Coordinates (e : Fin 3 → R) (x y : Fin 2 → R) : Prop :=
  Labels R W G 4 M e ∧ SplitCubic R W e ∧
  HasCoordinates R W M.x.val (x 0) (y 0) ∧
  HasCoordinates R W M.y.val (x 1) (y 1)

/-- Identification with the same curve's completed-square fiber; all point
coordinates are images of the actual marked section coordinates. -/
def FiberCoordinates (e : Fin 3 → R) (x y : Fin 2 → R)
    (F : Type u) [Field F] (ι : R →+* F)
    (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e)) : Prop :=
  ∀ i : Fin 2, b i ≠ 0 ∧
    ArithmeticThetaMarkingR0115.pointX F (ι ∘ e) (b i) = ι (x i) ∧
    ArithmeticThetaMarkingR0115.pointY F (ι ∘ e) (b i) =
      ι (completedY R W (x i) (y i))

/-- A scalar on the base identified on every characteristic-zero field fiber
with the existing moved-divisor Weil pairing, for every choice of its local
data. Nonempty coordinate data is required; fiber and local-data existence
are separately proved providers, not assumed pairing identities. -/
def GeometricPhase (z : R) : Prop :=
  (∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y) ∧
  ∀ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y →
    ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F)
      (b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e)),
      FiberCoordinates R W e x y F ι b →
      ∀ D : ArithmeticThetaGeometricPairingR0118.LocalData F (ι ∘ e),
        ι z = ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1)

/-- Both marking sections are transported through the specified Cartesian map. -/
def MarkingCompatible (S : Type u) [CommRing S] (Ws : WeierstrassCurve S)
    (Gs : Law S Ws) (Ms : FullLevel S Ws Gs 4 (𝟙 (Base S)))
    (ι : R →+* S) (f : Curve S Ws ⟶ Curve R W) : Prop :=
  Ms.x.val ≫ f = baseMap R S ι ≫ M.x.val ∧
  Ms.y.val ≫ f = baseMap R S ι ≫ M.y.val

end ArithmeticThetaRelativeFourCharacterR0211
