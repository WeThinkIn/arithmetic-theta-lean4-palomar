module

public import RelativeGeometricNaturalityR0258
public import RelativeSchrodingerDefinitionsR0257

@[expose] public section

/-! Actual theta lines and lifts over arbitrary scheme bases.
These definitions state construction targets; no target proof is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open scoped TensorProduct

variable {S : Scheme.{u}} (E : Family S)
abbrev point := SchemeHomOver (𝟙 S) E.p
abbrev multiple (P : point E) (n : ℕ) := ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) n P

def thetaLine (m : ℕ) : E.curve.Modules :=
  tensorObj (Scheme.Modules.dual ((E.zero.ker ^ m).module))
    ((Scheme.Modules.pullback E.p).obj
      ((ArithmeticThetaSchemeHodgeR0205.Cotangent E).tensorPow m))

/-- On affine bases the conormal Hodge line maps to the actual differential Hodge
line by the accepted conormal derivative; no frame is selected. -/
def affineThetaComparison {R : Type u} [CommRing R]
    (F : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R) (m : ℕ) :
    thetaLine (ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F) m ≅
      ArithmeticThetaRelativeThetaLiftsR0255.thetaLine F m := by
  let G := ArithmeticThetaRelativeThetaLiftsR0255.RelativeNormalizedThetaInversion.relativeFamily F
  letI := ArithmeticThetaSchemeHodgeR0205.AffineConormalHodgeNaturality.differential_isIso G
  exact (Iso.refl _) ⊗ᵢ ((Scheme.Modules.pullback F.projection).mapIso
    (Scheme.Modules.tensorPowMapIso (asIso (ArithmeticThetaSchemeHodgeR0205.affineDifferential G)) m))

def inverse : E.curve ⟶ E.curve :=
  (E.law.inv E.p ⟨𝟙 E.curve, Category.id_comp E.p⟩).val

def translation (P : point E) : E.curve ⟶ E.curve :=
  (E.law.mul E.p ⟨𝟙 E.curve, Category.id_comp E.p⟩
    ⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩).val

def negative (P : point E) : S ⟶ E.curve := (E.law.inv (𝟙 S) P).val
abbrev reflection (P : point E) := translation E P ≫ inverse E
abbrev Lift (m : ℕ) (f : E.curve ⟶ E.curve) :=
  (Scheme.Modules.pullback f).obj (thetaLine E m) ≅ thetaLine E m

def fixedComparison (m : ℕ) (o : S ⟶ E.curve) (f : E.curve ⟶ E.curve)
    (h : o ≫ f = o) :
    (Scheme.Modules.pullback o).obj ((Scheme.Modules.pullback f).obj (thetaLine E m)) ≅
      (Scheme.Modules.pullback o).obj (thetaLine E m) :=
  (Scheme.Modules.pullbackComp o f).app _ ≪≫ (Scheme.Modules.pullbackCongr h).app _

def squareComparison (m : ℕ) (f : E.curve ⟶ E.curve) (h : f ≫ f = 𝟙 _) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback f).obj (thetaLine E m)) ≅
      thetaLine E m :=
  (Scheme.Modules.pullbackComp f f).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫ (Scheme.Modules.pullbackId _).app _

def NormalizedInversion (m : ℕ) (ι : Lift E m (inverse E)) : Prop :=
  (∃ h : E.zero ≫ inverse E = E.zero,
    (Scheme.Modules.pullback E.zero).mapIso ι = fixedComparison E m E.zero (inverse E) h) ∧
  (∃ h : inverse E ≫ inverse E = 𝟙 E.curve,
    (Scheme.Modules.pullback (inverse E)).mapIso ι ≪≫ ι = squareComparison E m (inverse E) h)

def compose (m : ℕ) (f g : E.curve ⟶ E.curve)
    (α : Lift E m f) (β : Lift E m g) : Lift E m (f ≫ g) :=
  ((Scheme.Modules.pullbackComp f g).app _).symm ≪≫
    (Scheme.Modules.pullback f).mapIso β ≪≫ α

def reflectionLift (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) : Lift E m (reflection E P) :=
  compose E m (translation E P) (inverse E) α ι

def MidpointNormalized (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) : Prop :=
  ∃ h : negative E P ≫ reflection E P = negative E P,
    (Scheme.Modules.pullback (negative E P)).mapIso (reflectionLift E m P ι α) =
      fixedComparison E m (negative E P) (reflection E P) h

def Symmetric (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) : Prop :=
  ∃ h : reflection E P ≫ reflection E P = 𝟙 E.curve,
    (Scheme.Modules.pullback (reflection E P)).mapIso (reflectionLift E m P ι α) ≪≫
      reflectionLift E m P ι α = squareComparison E m (reflection E P) h

def scalar (c : Γ(S, ⊤)ˣ) : Γ(E.curve, ⊤)ˣ :=
  Units.map E.p.appTop.hom.toMonoidHom c

def scaled (m : ℕ) {f : E.curve ⟶ E.curve} (c : Γ(S, ⊤)ˣ) (α : Lift E m f) : Lift E m f :=
  α ≪≫ P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulIso
    (scalar E c) (thetaLine E m)

def identityLift (m : ℕ) : Lift E m (𝟙 E.curve) := (Scheme.Modules.pullbackId E.curve).app _

def changeMap (m : ℕ) {f g : E.curve ⟶ E.curve} (h : f = g) (α : Lift E m g) : Lift E m f :=
  (Scheme.Modules.pullbackCongr h).app _ ≪≫ α

def CyclicSystem (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (A : ∀ n : ℕ, Lift E m (translation E (multiple E P n))) : Prop :=
  (∀ n, MidpointNormalized E m (multiple E P n) ι (A n) ∧
    Symmetric E m (multiple E P n) ι (A n)) ∧
  (∃ h : translation E (multiple E P 0) = 𝟙 E.curve,
    A 0 = changeMap E m h (identityLift E m)) ∧
  (∀ a b : ℕ, ∃ h : translation E (multiple E P a) ≫ translation E (multiple E P b) =
      translation E (multiple E P (a+b)),
    compose E m _ _ (A a) (A b) = changeMap E m h (A (a+b))) ∧
  (∀ a : ℕ, ∃ h : translation E (multiple E P (a+m)) = translation E (multiple E P a),
    A (a+m) = changeMap E m h (A a))

def Commutator (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q)) (c : Γ(S, ⊤)ˣ) : Prop :=
  ∃ h : translation E P ≫ translation E Q = translation E Q ≫ translation E P,
    compose E m _ _ α β = scaled E m c (changeMap E m h (compose E m _ _ β α))

/-- Primitivity is checked in the actual global base ring; invertibility is local
on the base and retains nilpotents and disconnected components. -/
def PrimitiveUnit (m : ℕ) (c : Γ(S, ⊤)ˣ) : Prop :=
  c ^ m = 1 ∧ ∀ i : Fin m, i.val ≠ 0 → IsUnit ((c : Γ(S, ⊤)) ^ i.val - 1)

/-- Every affine test uses the pullback of this same global theta line. The scalar
action is through the actual structural morphism, also for nonflat tests. -/
def SectionFacts (m : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] (b : Base R ⟶ S),
    let f := pullback.snd E.p b
    let L := (Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f L ⊤
    ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A],
      let t := Scheme.TwoAffineOpenCover.specMap R A
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd f t)
        ((Scheme.Modules.pullback (pullback.fst f t)).obj L) ((pullback.fst f t) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(L, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (pullback.fst f t)).obj L, (pullback.fst f t) ⁻¹ᵁ ⊤),
        ∀ (a : A) (w : Γ(L, ⊤)), e (a ⊗ₜ[R] w) =
          a • Scheme.Modules.pullbackLocalSection (pullback.fst f t) w

/-- Whole-scheme normalized marking, with both coherent cyclic systems and the
primitive geometric commutator; section cohomology refers to the same line. -/
def MarkingExists (m : ℕ) (M : FullLevel E (2*m)) : Prop :=
  SectionFacts E m ∧
  ∃ ι : Lift E m (inverse E), NormalizedInversion E m ι ∧
    (∃! A : (∀ n : ℕ, Lift E m (translation E (multiple E M.x n))), CyclicSystem E m M.x ι A) ∧
    (∃! B : (∀ n : ℕ, Lift E m (translation E (multiple E M.y n))), CyclicSystem E m M.y ι B) ∧
    ∃ (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y)),
      MidpointNormalized E m M.x ι α ∧ Symmetric E m M.x ι α ∧
      MidpointNormalized E m M.y ι β ∧ Symmetric E m M.y ι β ∧
      ∃! c : Γ(S, ⊤)ˣ, Commutator E m M.x M.y α β c ∧ PrimitiveUnit m c

end ArithmeticThetaSchemeThetaMarkingR0259
