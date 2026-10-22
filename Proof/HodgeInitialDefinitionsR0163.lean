module

public import ActualDiscriminantCotangentTensorR0162
public import InitialTensorNaturalityR0162
public import NormalizedIntegralHodgeFrameR0149
public import PullbackTensorSections
public import IntegralHodgeDefinitionsR0149
public import ConormalInitialDefinitionsR0162
public import PullbackTensor
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section

/-! The actual identity cotangent fiber, Hodge sheaf and full Taylor comparison.
These definitions specify the maps on geometric representatives. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaHodgeInitialR0163
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaConormalInitialR0162
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaIntegralHodgeR0149
open ArithmeticThetaCompactifiedDifferentialR0145

/-- Scalars act through the actual global sections isomorphism of Spec R. -/
abbrev sectionModule (R : Type u) [CommRing R]
    (F : (Spec (CommRingCat.of R)).Modules) : Module R Γ(F, ⊤) :=
  Module.compHom Γ(F, ⊤) (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

attribute [local instance] sectionModule

abbrev SectionTensor (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) (n : ℕ) :=
  PiTensorProduct K (fun _ : Fin n => Γ(F, ⊤))

def IsTensorSections (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) (n : ℕ)
    (e : SectionTensor K F n ≃ₗ[K] Γ(tensorPower (Spec (CommRingCat.of K)) F n, ⊤)) : Prop :=
  ∀ x : Fin n → Γ(F, ⊤), e (PiTensorProduct.tprod K x) =
    tensorProductSection (Spec (CommRingCat.of K)) F n ⊤ x

def TensorSections (K : Type u) [Field K]
    (F : (Spec (CommRingCat.of K)).Modules) (n : ℕ) : Prop :=
  ∃! e : SectionTensor K F n ≃ₗ[K] Γ(tensorPower (Spec (CommRingCat.of K)) F n, ⊤),
    IsTensorSections K F n e

def powerCongr {S : Scheme.{u}} {F H : S.Modules} (e : F ≅ H) :
    (n : ℕ) → tensorPower S F n ≅ tensorPower S H n
  | 0 => Iso.refl _
  | n+1 => sheafTensorCongr S (powerCongr e n) e

def powerFrame {S : Scheme.{u}} {F : S.Modules}
    (e : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ F) :
    (n : ℕ) → (SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅ tensorPower S F n
  | 0 => Iso.refl _
  | n+1 => (tensorLeftUnitIso S (SheafOfModules.unit S.ringCatSheaf)).symm ≪≫
      sheafTensorCongr S (powerFrame e n) e

variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}

abbrev HodgePower (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (n : ℕ) :=
  tensorPower (Spec (CommRingCat.of (LaurentSeries k))) (Hodge k M s hs) n

/-- A canonical comparison, characterized by actual differentials on every
neighborhood of the specified point, followed by actual pullback of sections. -/
def IsHodgeComparison (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) : Prop :=
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) := (originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs).toAlgebra
  ∀ (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k),
    ε.toRingHom = (Scheme.stalkClosedPointTo (Origin k M s hs)).hom →
    ∃! e : DifferentialFiber ε ≃ₗ[LaurentSeries k] Γ(Hodge k M s hs, ⊤),
      ∀ (U : (genericScheme k M).Opens)
        (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
        (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
        (Hodge k M s hs).presheaf.map (homOfLE (show (genericPoint k M s hs) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          (e (differentialClass ε ((genericScheme k M).presheaf.germ U _ hx a))) =
        Scheme.Modules.pullbackLocalSection (genericPoint k M s hs) (differentialAt k M U a)

/-- The full formal equality for the actual normalized differential, with
u=z-1: the coefficient derivation is (1+u) d/du. -/
def LogarithmicTaylor (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)] (δ : Frame k M) : Prop :=
  ∀ (ε : OriginStalk k M s hs →+* LaurentSeries k)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k)),
    ActualTaylor k M s hs ε κ →
    ∀ (U : (genericScheme k M).Opens)
      (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
      (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
      κ ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) =
        (1 + PowerSeries.X) * PowerSeries.derivative (R := LaurentSeries k)
          (κ ((genericScheme k M).presheaf.germ U _ hx a))

/-- The canonical Hodge tensor associated to an actual initial class of 5g.
Its witnesses are actual representatives and canonically characterized maps.
Uniqueness of the represented section is a target, not an assumed field. -/
def RepresentsInitial (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)]
    (g : (genericScheme k M).functionField) (d : Γ(HodgePower k M s hs 24, ⊤)) : Prop :=
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) := (originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs).toAlgebra
  ∃ (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (κ : OriginStalk k M s hs →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k))
    (c : DifferentialTensor ε 24 ≃ₗ[LaurentSeries k] Grade ε 24)
    (e : DifferentialFiber ε ≃ₗ[LaurentSeries k] Γ(Hodge k M s hs, ⊤))
    (v : SectionTensor (LaurentSeries k) (Hodge k M s hs) 24 ≃ₗ[LaurentSeries k]
      Γ(HodgePower k M s hs 24, ⊤)) (b : ↥(ideal ε ^ 24)),
    ActualTaylor k M s hs ε.toRingHom κ.toRingHom ∧
    IsDifferentialPower ε 24 c ∧
    (∀ (U : (genericScheme k M).Opens)
      (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
      (a : (genericScheme k M).presheaf.obj (Opposite.op U)),
      (Hodge k M s hs).presheaf.map (homOfLE (show (genericPoint k M s hs) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (e (differentialClass ε ((genericScheme k M).presheaf.germ U _ hx a))) =
      Scheme.Modules.pullbackLocalSection (genericPoint k M s hs) (differentialAt k M U a)) ∧
    IsTensorSections (LaurentSeries k) (Hodge k M s hs) 24 v ∧
    algebraMap (OriginStalk k M s hs) (genericScheme k M).functionField b.1 = 5*g ∧
    d = v (PiTensorProduct.map (fun _ : Fin 24 => e.toLinearMap) (c.symm (gradeClass ε 24 b)))

def ExactHodgeExpansion (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (δ : Frame k M)
    (d : Γ(HodgePower k M s hs 24, ⊤)) : Prop :=
  d ≠ 0 ∧ d = (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
    (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) •
    tensorPowerSection (Spec (CommRingCat.of (LaurentSeries k)))
      (Hodge k M s hs) 24 ⊤ (hodgeSection k M s hs δ 1)

abbrev IntegralPower (M : Model k T) (s : baseScheme k ⟶ M.X) (n : ℕ) :=
  tensorPower (baseScheme k) (IntegralHodge k M s) n

def powerRestriction (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (b : GenericComparison k M) (n : ℕ)
    (q : Γ(IntegralPower k M s n, ⊤)) : Γ(HodgePower k M s hs n, ⊤) :=
  (powerCongr (fiberComparison k M s hs b) n).hom.app ⊤
    ((pullback_tensorPower_iso _ _ (genericBase k) (IntegralHodge k M s) n).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection (genericBase k) q))

def powerCoefficient (M : Model k T) (s : baseScheme k ⟶ M.X)
    (E : IntegralFrame k M s) (n : ℕ) (q : Γ(IntegralPower k M s n, ⊤)) : PowerSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    (Scheme.Modules.Hom.app (powerFrame E n).inv ⊤ q)

def discriminantSeries (r : ℕ) : PowerSeries k :=
  PowerSeries.subst (PowerSeries.X^r)
    (PowerSeries.map (algebraMap ℚ k)
      (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48))

end ArithmeticThetaHodgeInitialR0163
