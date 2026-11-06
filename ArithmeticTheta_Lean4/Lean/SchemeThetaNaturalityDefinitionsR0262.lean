import SchemeGeometricSchrodingerR0261
import SchemeSymmetricSignsR0259

/-! Canonical comparison maps for the same theta line on pointed Cartesian
elliptic families. These are definitions, not proofs of their naturality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)

abbrev thetaComparison (m : ℕ) :=
  SchemeThetaSectionCohomology.thetaComparison E F b f hc hz m

/-- Transport uses the actual Cartier/conormal comparison, not an arbitrary
line isomorphism or an independently chosen frame. -/
def transportedLift (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (h : g' ≫ f = f ≫ g) (α : Lift E m g) : Lift F m g' :=
  (Scheme.Modules.pullback g').mapIso (thetaComparison E F b f hc hz m).symm ≪≫
    (Scheme.Modules.pullbackComp g' f).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫
    ((Scheme.Modules.pullbackComp f g).app _).symm ≪≫
    (Scheme.Modules.pullback f).mapIso α ≪≫ thetaComparison E F b f hc hz m

def LiftCorresponds (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (α : Lift E m g) (α' : Lift F m g') : Prop :=
  ∃ h : g' ≫ f = f ≫ g, α' = transportedLift E F b f hc hz m g g' h α

/-- The comparison between the actual pushforwards is the adjoint of the
pulled-back counit followed by the fixed theta-line comparison. -/
def pushforwardMap (m : ℕ) :
    (Scheme.Modules.pullback b).obj (V E m) ⟶ V F m :=
  (Scheme.Modules.pullbackPushforwardAdjunction F.p).homEquiv _ _
    (((Scheme.Modules.pullbackComp F.p b).app (V E m)).hom ≫
      ((Scheme.Modules.pullbackCongr hc.w.symm).app (V E m)).hom ≫
      ((Scheme.Modules.pullbackComp f E.p).app (V E m)).inv ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m)) ≫
      (thetaComparison E F b f hc hz m).hom)

def fiberComparison (m : ℕ) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)) ≅
      (Scheme.Modules.pullback F.zero).obj (thetaLine F m) :=
  (Scheme.Modules.pullbackComp b E.zero).app _ ≪≫
    (Scheme.Modules.pullbackCongr hz.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp F.zero f).app _).symm ≪≫
    (Scheme.Modules.pullback F.zero).mapIso (thetaComparison E F b f hc hz m)

def Intertwines (m : ℕ) (A : End (V E m)) (A' : End (V F m)) : Prop :=
  (Scheme.Modules.pullback b).map A ≫ pushforwardMap E F b f hc hz m =
    pushforwardMap E F b f hc hz m ≫ A'

/-- Both kernel and every evaluation component use the same comparison. -/
def InvariantComponents (m : ℕ) (A B : End (V E m)) (A' B' : End (V F m)) : Prop :=
  ∃! e : (Scheme.Modules.pullback b).obj (fixed A) ≅ fixed A',
    e.hom ≫ fixedι A' =
      (Scheme.Modules.pullback b).map (fixedι A) ≫ pushforwardMap E F b f hc hz m ∧
    (∀ i : Fin m,
      e.hom ≫ fixedι A' ≫ (B' ^ i.val) =
        (Scheme.Modules.pullback b).map (fixedι A ≫ (B ^ i.val)) ≫
          pushforwardMap E F b f hc hz m) ∧
    (∀ i : Fin m,
      (Scheme.Modules.pullback b).map (component E m A B i) ≫
          (fiberComparison E F b f hc hz m).hom =
        e.hom ≫ component F m A' B' i)

def NormalizationNatural (m : ℕ) : Prop :=
  (∀ (ι : Lift E m (inverse E)), NormalizedInversion E m ι →
    ∀ (ι' : Lift F m (inverse F)), NormalizedInversion F m ι' →
      LiftCorresponds E F b f hc hz m (inverse E) (inverse F) ι ι') ∧
  (∀ (P : point E) (Q : point F), Q.val ≫ f = b ≫ P.val →
    ∀ (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F)),
      NormalizedInversion E m ι → NormalizedInversion F m ι' →
    ∀ (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q)),
      (LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α' →
        (MidpointNormalized E m P ι α → MidpointNormalized F m Q ι' α') ∧
        (Symmetric E m P ι α → Symmetric F m Q ι' α')) ∧
      (MidpointNormalized E m P ι α → MidpointNormalized F m Q ι' α' →
        LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α α'))

def baseUnit (c : (S.presheaf.obj (Opposite.op ⊤))ˣ) :
    (T.presheaf.obj (Opposite.op ⊤))ˣ := Units.map b.appTop.hom.toMonoidHom c

def signUnit (X : Scheme.{u}) (ε : Bool) : (X.presheaf.obj (Opposite.op ⊤))ˣ :=
  if ε then -1 else 1

/-- Alignment to prescribed symmetric test lifts uses only two global constant
signs. The base, level and test morphism are not replaced by a cover. -/
def SignAlignment (m : ℕ) (M : FullLevel E (2*m)) (N : FullLevel F (2*m))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (α' : Lift F m (translation F N.x)) (β' : Lift F m (translation F N.y)) : Prop :=
  ∃! signs : Bool × Bool,
    LiftCorresponds E F b f hc hz m (translation E M.x) (translation F N.x)
      (scaled E m (signUnit S signs.1) α) α' ∧
    LiftCorresponds E F b f hc hz m (translation E M.y) (translation F N.y)
      (scaled E m (signUnit S signs.2) β) β'

/-- All normalized geometric data on both families are constructed together,
and the actual maps compare their operators, invariant lines and evaluations. -/
def GeometricNaturality (m : ℕ) (M : FullLevel E (2*m)) (N : FullLevel F (2*m)) : Prop :=
  ∃ (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (α' : Lift F m (translation F N.x)) (β' : Lift F m (translation F N.y))
    (c : (S.presheaf.obj (Opposite.op ⊤))ˣ)
    (A B : End (V E m)) (A' B' : End (V F m)),
    NormalizedInversion E m ι ∧ NormalizedInversion F m ι' ∧
    MidpointNormalized E m M.x ι α ∧ MidpointNormalized E m M.y ι β ∧
    MidpointNormalized F m N.x ι' α' ∧ MidpointNormalized F m N.y ι' β' ∧
    Symmetric E m M.x ι α ∧ Symmetric E m M.y ι β ∧
    Symmetric F m N.x ι' α' ∧ Symmetric F m N.y ι' β' ∧
    LiftCorresponds E F b f hc hz m (inverse E) (inverse F) ι ι' ∧
    LiftCorresponds E F b f hc hz m (translation E M.x) (translation F N.x) α α' ∧
    LiftCorresponds E F b f hc hz m (translation E M.y) (translation F N.y) β β' ∧
    PrimitiveUnit (S := S) m c ∧ PrimitiveUnit (S := T) m (baseUnit b c) ∧
    Commutator E m M.x M.y α β c ∧ Commutator F m N.x N.y α' β' (baseUnit b c) ∧
    IsAction E m (translation E M.x) α A ∧ IsAction E m (translation E M.y) β B ∧
    IsAction F m (translation F N.x) α' A' ∧ IsAction F m (translation F N.y) β' B' ∧
    Relations m A B c ∧ Relations m A' B' (baseUnit b c) ∧
    IsIso (pushforwardMap E F b f hc hz m) ∧
    Intertwines E F b f hc hz m A A' ∧ Intertwines E F b f hc hz m B B' ∧
    Scheme.Modules.IsInvertible (fixed A) ∧ Scheme.Modules.IsInvertible (fixed A') ∧
    Orbit m A B c ∧ Orbit m A' B' (baseUnit b c) ∧
    InvariantComponents E F b f hc hz m A B A' B' ∧
    (∀ (a : Lift F m (translation F N.x)) (d : Lift F m (translation F N.y)),
      _root_.IsPreconnected (Set.univ : Set T) → Nonempty T →
      Symmetric F m N.x ι' a → Symmetric F m N.y ι' d →
      SignAlignment E F b f hc hz m M N α β a d)

end ArithmeticThetaSchemeThetaNaturalityR0262
