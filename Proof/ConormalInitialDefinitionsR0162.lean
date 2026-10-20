module

public import GeometricDiscriminantInitialR0161
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

/-! Actual conormal, graded ideal, and differential fibers for the identity
initial term. All maps are specified on representatives; no target is assumed. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace ArithmeticThetaConormalInitialR0162
open CategoryTheory AlgebraicGeometry
variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]

abbrev ideal (ε : A →ₐ[K] K) : Ideal A := RingHom.ker ε.toRingHom
abbrev nextPower (ε : A →ₐ[K] K) (n : ℕ) : Submodule A ↥(ideal ε ^ n) :=
  Submodule.comap (ideal ε ^ n).subtype (ideal ε ^ (n+1))
abbrev Grade (ε : A →ₐ[K] K) (n : ℕ) := ↥(ideal ε ^ n) ⧸ nextPower ε n

def gradeClass (ε : A →ₐ[K] K) (n : ℕ) (b : ↥(ideal ε ^ n)) : Grade ε n :=
  Submodule.Quotient.mk b

abbrev ConormalTensor (ε : A →ₐ[K] K) (n : ℕ) :=
  PiTensorProduct K (fun _ : Fin n => (ideal ε).Cotangent)

/-- The actual relative differential module restricted to the augmented point. -/
abbrev DifferentialFiber (ε : A →ₐ[K] K) :=
  KaehlerDifferential K A ⧸
    (ideal ε • (⊤ : Submodule A (KaehlerDifferential K A)))

def differentialClass (ε : A →ₐ[K] K) (a : A) : DifferentialFiber ε :=
  Submodule.Quotient.mk (KaehlerDifferential.D K A a)

abbrev DifferentialTensor (ε : A →ₐ[K] K) (n : ℕ) :=
  PiTensorProduct K (fun _ : Fin n => DifferentialFiber ε)

def IsConormal (ε : A →ₐ[K] K)
    (e : (ideal ε).Cotangent ≃ₗ[K] DifferentialFiber ε) : Prop :=
  ∀ x : ideal ε, e ((ideal ε).toCotangent x) = differentialClass ε x.1

def IsMultiplication (ε : A →ₐ[K] K) (n : ℕ)
    (e : ConormalTensor ε n ≃ₗ[K] Grade ε n) : Prop :=
  ∀ (x : Fin n → ideal ε) (b : ↥(ideal ε ^ n)),
    b.1 = ∏ i, (x i).1 →
    e (PiTensorProduct.tprod K (fun i => (ideal ε).toCotangent (x i))) =
      gradeClass ε n b

def IsDifferentialPower (ε : A →ₐ[K] K) (n : ℕ)
    (e : DifferentialTensor ε n ≃ₗ[K] Grade ε n) : Prop :=
  ∀ (x : Fin n → ideal ε) (b : ↥(ideal ε ^ n)),
    b.1 = ∏ i, (x i).1 →
    e (PiTensorProduct.tprod K (fun i => differentialClass ε (x i).1)) =
      gradeClass ε n b

def IsTaylor (ε : A →ₐ[K] K) (κ : A →ₐ[K] PowerSeries K) : Prop :=
  (∀ a, PowerSeries.constantCoeff (κ a) = ε a) ∧
  ∀ (a : A) (n : ℕ), a ∈ ideal ε ^ n ↔
    ∀ i : ℕ, i < n → PowerSeries.coeff i (κ a) = 0

def IsCoefficient (ε : A →ₐ[K] K) (κ : A →ₐ[K] PowerSeries K) (n : ℕ)
    (e : Grade ε n ≃ₗ[K] K) : Prop :=
  ∀ b : ↥(ideal ε ^ n), e (gradeClass ε n b) = PowerSeries.coeff n (κ b.1)

variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161

/-- Scalar map is the structural map followed by the actual germ at the identity. -/
def originScalar (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) :
    LaurentSeries k →+* OriginStalk k M s hs :=
  ((genericScheme k M).presheaf.germ ⊤
    (Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k))) (by trivial)).hom.comp
    ((genericStructure k M).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom)

/-- Every expansion map is tied to the accepted geometric chart square.
The additional algebra structures below use originScalar, not a free action. -/
def ActualTaylor (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (genericScheme k M)]
    (ε : OriginStalk k M s hs →+* LaurentSeries k)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k)) : Prop :=
  ε = (Scheme.stalkClosedPointTo (Origin k M s hs)).hom ∧
  ∃ (χ : Fin r → (ArithmeticThetaKatoAnnularR0152.chartScheme k ⟶ M.X))
    (φ : Fin r → (genericScheme k M).functionField →+* ChartField k)
    (σ : Chart k →+* Bivariate k) (Ψ : ChartField k →+* Iterated k),
    (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartMap k M j (χ j)) ∧
    (∀ j, ArithmeticThetaKatoAnnularR0152.IsChartFieldMap k M (χ j) (φ j)) ∧
    IsChartTaylor k σ ∧ ExtendsTaylor k σ Ψ ∧
    IsOriginTaylor k M s hs
      (Ψ.comp (φ (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr))) κ

/-- The actual geometric provider for the split augmentation, regular ideal,
and scalar-preserving Taylor map used by the algebraic comparisons. -/
def OriginAugmentedTaylor (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)] : Prop :=
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) := (originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs).toAlgebra
  ∃ (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (κ : OriginStalk k M s hs →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k)),
    ActualTaylor k M s hs ε.toRingHom κ.toRingHom ∧
    ideal ε = IsLocalRing.maximalIdeal (OriginStalk k M s hs) ∧
    (ideal ε).IsPrincipal ∧ ideal ε ≠ ⊥ ∧ IsTaylor ε κ

/-- Canonical relative cotangent tensor form of 5 in_0(g_5) on the ACTUAL
identity stalk. Sheaf-level Hodge comparison and global moduli descent are
separate remaining obligations. -/
def DiscriminantTensor (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (genericScheme k M)]
    (g : (genericScheme k M).functionField) : Prop :=
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) := (originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs).toAlgebra
  ∃ (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (κ : OriginStalk k M s hs →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k))
    (e : DifferentialTensor ε 24 ≃ₗ[LaurentSeries k] Grade ε 24)
    (b : ↥(ideal ε ^ 24)) (π : ideal ε),
    ActualTaylor k M s hs ε.toRingHom κ.toRingHom ∧
    IsDifferentialPower ε 24 e ∧
    algebraMap (OriginStalk k M s hs) (genericScheme k M).functionField b.1 = 5*g ∧
    PowerSeries.coeff 1 (κ π.1) = 1 ∧
    e.symm (gradeClass ε 24 b) =
      ArithmeticThetaUnaryKatoPowerR0160.discriminant k r •
        PiTensorProduct.tprod (LaurentSeries k)
          (fun _ : Fin 24 => differentialClass ε π.1) ∧
    e.symm (gradeClass ε 24 b) ≠ 0

end ArithmeticThetaConormalInitialR0162
