module

public import FullLevelProjectiveRatiosR0194
public import NoetherianPositiveCohomologyR0203
public import GlobalUnitTwoThreeNormRigidityR0254

@[expose] public section

/-! Relative theta-line lifts on the entire elliptic family.  These are
ordinary definitions of the actual line, maps and required equalities.
Existence and uniqueness are the new proof obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaLiftsR0255
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

abbrev base := Spec (CommRingCat.of R)
abbrev zero : base (R := R) ⟶ E.curve := (E.law.one (𝟙 _)).val
abbrev point := SchemeHomOver (𝟙 (base (R := R))) E.projection

/-- O(m[0]) tensor the pullback of the m-th power of the actual Hodge line. -/
def thetaLine (m : ℕ) : E.curve.Modules :=
  MonoidalCategory.tensorObj (Scheme.Modules.dual (((zero E).ker ^ m).module))
    ((Scheme.Modules.pullback E.projection).obj
      (((Scheme.Modules.pullback (zero E)).obj E.projection.kaehler).tensorPow m))

def inverse : E.curve ⟶ E.curve :=
  (E.law.inv E.projection ⟨𝟙 E.curve, Category.id_comp E.projection⟩).val
def translation (P : point E) : E.curve ⟶ E.curve :=
  E.law.translate (E.law.nsmul (𝟙 _) 2 P)
def negative (P : point E) : base (R := R) ⟶ E.curve :=
  (E.law.inv (𝟙 _) P).val
def reflection (P : point E) : E.curve ⟶ E.curve :=
  translation E P ≫ inverse E

abbrev Lift (m : ℕ) (f : E.curve ⟶ E.curve) :=
  (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine E m

def fixedComparison (m : ℕ) (o : base (R := R) ⟶ E.curve)
    (f : E.curve ⟶ E.curve) (h : o ≫ f = o) :
    (Scheme.Modules.pullback o).obj ((Scheme.Modules.pullback f).obj (thetaLine E m)) ≅
      (Scheme.Modules.pullback o).obj (thetaLine E m) :=
  (Scheme.Modules.pullbackComp o f).app _ ≪≫ (Scheme.Modules.pullbackCongr h).app _

def squareComparison (m : ℕ) (f : E.curve ⟶ E.curve) (h : f ≫ f = 𝟙 _) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback f).obj (thetaLine E m)) ≅
      thetaLine E m :=
  (Scheme.Modules.pullbackComp f f).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫ (Scheme.Modules.pullbackId _).app _

/-- Identity on the actual identity fibre, and the actual involution law. -/
def NormalizedInversion (m : ℕ) (ι : Lift E m (inverse E)) : Prop :=
  (∃ h : zero E ≫ inverse E = zero E,
    (Scheme.Modules.pullback (zero E)).mapIso ι = fixedComparison E m (zero E) (inverse E) h) ∧
  (∃ h : inverse E ≫ inverse E = 𝟙 E.curve,
    (Scheme.Modules.pullback (inverse E)).mapIso ι ≪≫ ι = squareComparison E m (inverse E) h)

/-- The composite lies over translation followed by inversion. -/
def reflectionLift (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E)) (α : Lift E m (translation E P)) :
    Lift E m (reflection E P) :=
  ((Scheme.Modules.pullbackComp (translation E P) (inverse E)).app _).symm ≪≫
    (Scheme.Modules.pullback (translation E P)).mapIso ι ≪≫ α

/-- Normalization at the actual fixed section -P; this is an equality of
sheaf maps over the whole base, not equality only on geometric fibres. -/
def MidpointNormalized (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E)) (α : Lift E m (translation E P)) : Prop :=
  ∃ h : negative E P ≫ reflection E P = negative E P,
    (Scheme.Modules.pullback (negative E P)).mapIso (reflectionLift E m P ι α) =
      fixedComparison E m (negative E P) (reflection E P) h

/-- The symmetric-lift square equation, including canonical pullback comparison. -/
def Symmetric (m : ℕ) (P : point E)
    (ι : Lift E m (inverse E)) (α : Lift E m (translation E P)) : Prop :=
  ∃ h : reflection E P ≫ reflection E P = 𝟙 E.curve,
    (Scheme.Modules.pullback (reflection E P)).mapIso (reflectionLift E m P ι α) ≪≫
      reflectionLift E m P ι α = squareComparison E m (reflection E P) h

end ArithmeticThetaRelativeThetaLiftsR0255
