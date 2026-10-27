import RelativeKatoExistenceR0169

/-! Relative Kato specialization uses sheaf maps, including non-dominant base
change. All ideals, sections and evaluations below belong to the specified
projective Weierstrass family. This file contains definitions only. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

variable (R : Type u) [CommRing R] [IsDomain R]
variable (W : WeierstrassCurve R) (G : Law R W)

/-- The actual identity Cartier ideal and its multiplication pullback. -/
def identityIdeal : (Curve R W).IdealSheafData := (origin R W).ker

def torsionIdeal (n : ℕ) : (Curve R W).IdealSheafData :=
  (identityIdeal R W).comap (G.schemeNsmul n)

variable [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
variable [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]

/-- Exactly the normalization already constructed in r0169, without assuming
any new specialization, evaluation, or Cartier equation. -/
def Normalized (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  IsRelativeKato R W G c g ∧
  ∀ C : GenericComparison R W G,
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction (FractionRing R)
      (W.map (algebraMap R (FractionRing R))) C.law c (C.field g)

/-- Upgrade codimension-one orders to an actual local Cartier equation. -/
def CartierRatio (c : ℕ) (g : (Curve R W).functionField) : Prop :=
  ∀ (U : (Curve R W).affineOpens) [Nonempty U.1]
    (a b : (Curve R W).presheaf.obj (Opposite.op U.1)),
    IsRegular a → IsRegular b →
    (identityIdeal R W).ideal U = Ideal.span ({a} : Set _) →
    (torsionIdeal R W G c).ideal U = Ideal.span ({b} : Set _) →
    ∃ ε : ((Curve R W).presheaf.obj (Opposite.op U.1))ˣ,
      g * (Curve R W).germToFunctionField U.1 b =
        (Curve R W).germToFunctionField U.1 ((ε : _) * a^(c^2))

variable (S : Type u) [CommRing S] [IsDomain S]
variable (Ws : WeierstrassCurve S) (Gs : Law S Ws)

/-- Actual pointed Cartesian family comparison; no rational map on function
fields is required when the base map is a specialization. -/
def IsBaseChange (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W) : Prop :=
  IsPullback b (structureMap S Ws) (structureMap R W)
    (Spec.map (CommRingCat.ofHom ι)) ∧
  (origin S Ws ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ origin R W) ∧
  (∀ n : ℕ, Gs.schemeNsmul n ≫ b = b ≫ G.schemeNsmul n)

variable [IsIntegral (Curve S Ws)]

/-- Complete sections pull back through the specified sheaf map on all opens.
The target section is compared to its own rational Kato function, not to an
undefined pullback of the source function field. -/
def UnitPullback (b : Curve S Ws ⟶ Curve R W) (c : ℕ)
    (g : (Curve R W).functionField) (gs : (Curve S Ws).functionField) : Prop :=
  ∀ (U : (Curve R W).Opens) (V : (Curve S Ws).Opens)
    [Nonempty U] [Nonempty V] (e : V ≤ b ⁻¹ᵁ U)
    (a : (Curve R W).presheaf.obj (Opposite.op U)),
    (∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W)) →
    (Curve R W).germToFunctionField U a = g →
    IsUnit (b.appLE U V e a) ∧
      (Curve S Ws).germToFunctionField V (b.appLE U V e a) = gs

/-- Evaluation at an actual section on a genuine open neighborhood of its
whole image. The witness includes a nonempty open, a regular unit, its full
rational restriction, and the actual scheme section-ring map. -/
def HasValue (P : Spec (CommRingCat.of R) ⟶ Curve R W)
    (g : (Curve R W).functionField) (v : R) : Prop :=
  ∃ (U : (Curve R W).Opens) (hU : Nonempty U)
    (e : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U)
    (a : (Curve R W).presheaf.obj (Opposite.op U)),
      IsUnit a ∧ @Scheme.germToFunctionField (Curve R W) _ U hU a = g ∧
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (P.appLE U ⊤ e a) = v

end ArithmeticThetaRelativeKatoNaturalityR0170
