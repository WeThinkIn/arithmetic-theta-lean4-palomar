module

public import RelativeGeometricSchrodingerR0257

@[expose] public section

/-! Canonical geometric scalar extension of the rigidified theta line.
Only definitions occur here. Naturality and comparison assertions are proof targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaNaturalityR0258
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256 ArithmeticThetaRelativeSchrodingerR0257
open scoped TensorProduct

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
variable (S : Type u) [CommRing S] [Algebra R S]

abbrev baseMap := Scheme.TwoAffineOpenCover.specMap R S
abbrev family := RelativePrimitiveThetaCommutator.baseChangedFamily E (baseMap (R := R) S)
abbrev curveMap : (family E S).curve ⟶ E.curve := pullback.fst E.projection (baseMap (R := R) S)

def pointBaseChange (P : point E) : point (family E S) :=
  ⟨pullback.lift (baseMap (R := R) S ≫ P.val) (𝟙 _)
    (by rw [Category.assoc, P.property]; simp), pullback.lift_snd _ _ _⟩

/-- Use the actual differential base-change map, with its pointed Cartesian square. -/
def hodgeComparison :
    (Scheme.Modules.pullback (baseMap (R := R) S)).obj
      (RelativeNormalizedThetaInversion.hodge E) ≅
        RelativeNormalizedThetaInversion.hodge (family E S) :=
  ArithmeticThetaSchemeHodgeR0205.affineHodgeComparison
    (RelativeNormalizedThetaInversion.relativeFamily E)
    (RelativeNormalizedThetaInversion.relativeFamily (family E S)) (algebraMap R S)
    (curveMap E S) (IsPullback.of_hasPullback _ _)
    (RelativePrimitiveThetaCommutator.baseChanged_zero E (baseMap (R := R) S))

/-- The Hodge tensor power, without choosing a generator over either ring. -/
def hodgePowerComparison (m : ℕ) :
    (Scheme.Modules.pullback (baseMap (R := R) S)).obj
      ((RelativeNormalizedThetaInversion.hodge E).tensorPow m) ≅
        (RelativeNormalizedThetaInversion.hodge (family E S)).tensorPow m :=
  Scheme.Modules.pullbackTensorPowIso _ _ m ≪≫
    Scheme.Modules.tensorPowMapIso (hodgeComparison E S) m

/-- The fixed comparison uses the accepted Cartier ideal map and the actual
Hodge differential map; an arbitrary line isomorphism is not an input. -/
def thetaComparison (m : ℕ) :
    (Scheme.Modules.pullback (curveMap E S)).obj (thetaLine E m) ≅
      thetaLine (family E S) m :=
  Scheme.Modules.pullbackTensorObjIso (curveMap E S) _ _ ≪≫
    (RelativePrimitiveThetaCommutator.baseChanged_originPowerIso E (baseMap (R := R) S) m ⊗ᵢ
      ((Scheme.Modules.pullbackComp (curveMap E S) E.projection).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.condition (f := E.projection)
          (g := baseMap (R := R) S))).app _ ≪≫
        ((Scheme.Modules.pullbackComp (family E S).projection (baseMap (R := R) S)).app _).symm ≪≫
        (Scheme.Modules.pullback (family E S).projection).mapIso (hodgePowerComparison E S m)))

/-- Conjugate the actual pullback lift by the fixed theta comparison. -/
def transportedLift (m : ℕ) (f : E.curve ⟶ E.curve)
    (g : (family E S).curve ⟶ (family E S).curve)
    (h : curveMap E S ≫ f = g ≫ curveMap E S) (α : Lift E m f) :
    Lift (family E S) m g :=
  (Scheme.Modules.pullback g).mapIso (thetaComparison E S m).symm ≪≫
    RelativePrimitiveThetaCommutator.PullbackLifts.lift (curveMap E S) f g h α ≪≫
      thetaComparison E S m

/-- Correspondence includes the underlying geometric commuting square. -/
def LiftCorresponds (m : ℕ) (f : E.curve ⟶ E.curve)
    (g : (family E S).curve ⟶ (family E S).curve)
    (α : Lift E m f) (β : Lift (family E S) m g) : Prop :=
  ∃ h : curveMap E S ≫ f = g ≫ curveMap E S,
    transportedLift E S m f g h α = β

def sectionPull (m : ℕ) (w : sections E m) : sections (family E S) m :=
  (thetaComparison E S m).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (curveMap E S) w)

/-- Actual normalized inversion, including m=0, is independent of scalar extension. -/
def InversionNatural (m : ℕ) : Prop :=
  ∀ (ι : Lift E m (inverse E)) (ιS : Lift (family E S) m (inverse (family E S))),
    NormalizedInversion E m ι → NormalizedInversion (family E S) m ιS →
      LiftCorresponds E S m (inverse E) (inverse (family E S)) ι ιS

/-- Midpoint normalization at -P fixes the whole-family scalar, not just fibres. -/
def MidpointNatural (m : ℕ) (P : point E) : Prop :=
  ∀ (ι : Lift E m (inverse E)) (ιS : Lift (family E S) m (inverse (family E S)))
    (α : Lift E m (translation E P))
    (αS : Lift (family E S) m (translation (family E S) (pointBaseChange E S P))),
    NormalizedInversion E m ι → NormalizedInversion (family E S) m ιS →
    MidpointNormalized E m P ι α →
    MidpointNormalized (family E S) m (pointBaseChange E S P) ιS αS →
    LiftCorresponds E S m (translation E P)
      (translation (family E S) (pointBaseChange E S P)) α αS

/-- One canonical tensor-section equivalence intertwines every corresponding
translation lift. It is specified on every pure tensor, including zero. -/
def SectionsNatural (m : ℕ) : Prop :=
  letI := sectionModule E m
  letI := sectionModule (family E S) m
  ∃ e : S ⊗[R] sections E m ≃ₗ[S] sections (family E S) m,
    (∀ (s : S) (w : sections E m), e (s ⊗ₜ[R] w) = s • sectionPull E S m w) ∧
    ∀ (P : point E) (α : Lift E m (translation E P))
      (αS : Lift (family E S) m (translation (family E S) (pointBaseChange E S P))),
      LiftCorresponds E S m (translation E P)
        (translation (family E S) (pointBaseChange E S P)) α αS →
      ∀ v : S ⊗[R] sections E m,
        e ((RelativePrimitiveThetaCommutator.thetaAct E m P α).baseChange S v) =
          RelativePrimitiveThetaCommutator.thetaAct (family E S) m (pointBaseChange E S P) αS (e v)

/-- Concrete relative comparison across the geometric base-change map, with
both pairs of normalized lifts constructed and the fixed line transported. -/
def GeometricNaturality (m : ℕ) (M : FamilyLevel R E (2*m)) : Prop :=
  ∃ (ι : Lift E m (inverse E)) (ιS : Lift (family E S) m (inverse (family E S)))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (αS : Lift (family E S) m (translation (family E S) (pointBaseChange E S M.x)))
    (βS : Lift (family E S) m (translation (family E S) (pointBaseChange E S M.y)))
    (c : Rˣ),
    NormalizedInversion E m ι ∧ NormalizedInversion (family E S) m ιS ∧
    MidpointNormalized E m M.x ι α ∧ Symmetric E m M.x ι α ∧
    MidpointNormalized E m M.y ι β ∧ Symmetric E m M.y ι β ∧
    MidpointNormalized (family E S) m (pointBaseChange E S M.x) ιS αS ∧
    Symmetric (family E S) m (pointBaseChange E S M.x) ιS αS ∧
    MidpointNormalized (family E S) m (pointBaseChange E S M.y) ιS βS ∧
    Symmetric (family E S) m (pointBaseChange E S M.y) ιS βS ∧
    LiftCorresponds E S m (inverse E) (inverse (family E S)) ι ιS ∧
    LiftCorresponds E S m (translation E M.x)
      (translation (family E S) (pointBaseChange E S M.x)) α αS ∧
    LiftCorresponds E S m (translation E M.y)
      (translation (family E S) (pointBaseChange E S M.y)) β βS ∧
    Commutator E m M.x M.y α β c ∧ PrimitiveUnit m c ∧
    Commutator (family E S) m (pointBaseChange E S M.x) (pointBaseChange E S M.y)
      αS βS (Units.map (algebraMap R S).toMonoidHom c) ∧
    (letI := sectionModule E m
     letI := sectionModule (family E S) m
     let A := RelativePrimitiveThetaCommutator.thetaAct E m M.x α
     let B := RelativePrimitiveThetaCommutator.thetaAct E m M.y β
     let AS := RelativePrimitiveThetaCommutator.thetaAct (family E S) m (pointBaseChange E S M.x) αS
     let BS := RelativePrimitiveThetaCommutator.thetaAct (family E S) m (pointBaseChange E S M.y) βS
     A ^ m = 1 ∧ B ^ m = 1 ∧ AS ^ m = 1 ∧ BS ^ m = 1 ∧
     OrbitComparison R (sections E m) m A B c ∧
     OrbitComparison S (sections (family E S) m) m AS BS (Units.map (algebraMap R S).toMonoidHom c) ∧
     ∃ (e : S ⊗[R] sections E m ≃ₗ[S] sections (family E S) m)
       (eL : S ⊗[R] Fixed R (sections E m) A ≃ₗ[S] Fixed S (sections (family E S) m) AS),
       (∀ (s : S) (w : sections E m), e (s ⊗ₜ[R] w) = s • sectionPull E S m w) ∧
       (∀ v, e (A.baseChange S v) = AS (e v)) ∧
       (∀ v, e (B.baseChange S v) = BS (e v)) ∧
       (∀ (s : S) (w : Fixed R (sections E m) A),
         (eL (s ⊗ₜ[R] w)).val = e (s ⊗ₜ[R] w.val)) ∧
       (∀ (s : S) (w : Fin m → Fixed R (sections E m) A),
         e (s ⊗ₜ[R] (∑ i : Fin m, (B ^ i.val) (w i).val)) =
           ∑ i : Fin m, (BS ^ i.val) (eL (s ⊗ₜ[R] w i)).val))

end ArithmeticThetaRelativeThetaNaturalityR0258
