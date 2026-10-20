module

public import ActualDiscriminantCotangentTensorR0162
public import InitialTensorNaturalityR0162
public import Mathlib.RingTheory.Kaehler.TensorProduct

@[expose] public section

/-! Scalar extension of the actual augmented initial-term construction. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
universe u v w z
namespace ArithmeticThetaInitialBaseChangeR0164
open TensorProduct
open ArithmeticThetaConormalInitialR0162
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

abbrev Extended := TensorProduct K L A

def inclusion : A →ₐ[K] Extended K L A := Algebra.TensorProduct.includeRight

def augmentation (ε : A →ₐ[K] K) : Extended K L A →ₐ[L] L :=
  AlgHom.liftEquiv K L A L ((Algebra.ofId K L).comp ε)

def taylor (κ : A →ₐ[K] PowerSeries K) : Extended K L A →ₐ[L] PowerSeries L :=
  AlgHom.liftEquiv K L A (PowerSeries L)
    ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp κ)

abbrev PowerEquiv (ε : A →ₐ[K] K) (n : ℕ) :=
  TensorProduct K L ↥(ideal ε ^ n) ≃ₗ[L] ↥(ideal (augmentation K L A ε) ^ n)

def IsPowerEquiv (ε : A →ₐ[K] K) (n : ℕ) (e : PowerEquiv K L A ε n) : Prop :=
  ∀ (l : L) (a : ↥(ideal ε ^ n)),
    (e (l ⊗ₜ[K] a)).1 = l • inclusion K L A a.1

abbrev GradeEquiv (ε : A →ₐ[K] K) (n : ℕ) :=
  TensorProduct K L (Grade ε n) ≃ₗ[L] Grade (augmentation K L A ε) n

def IsGradeEquiv (ε : A →ₐ[K] K) (n : ℕ) (e : GradeEquiv K L A ε n) : Prop :=
  ∀ (l : L) (a : ↥(ideal ε ^ n))
    (b : ↥(ideal (augmentation K L A ε) ^ n)),
    b.1 = inclusion K L A a.1 →
    e (l ⊗ₜ[K] gradeClass ε n a) = l • gradeClass (augmentation K L A ε) n b

abbrev FiberEquiv (ε : A →ₐ[K] K) :=
  TensorProduct K L (DifferentialFiber ε) ≃ₗ[L] DifferentialFiber (augmentation K L A ε)

def IsFiberEquiv (ε : A →ₐ[K] K) (e : FiberEquiv K L A ε) : Prop :=
  ∀ (l : L) (a : A), e (l ⊗ₜ[K] differentialClass ε a) =
    l • differentialClass (augmentation K L A ε) (inclusion K L A a)

variable (V : Type z) [AddCommGroup V] [Module K V]
abbrev TensorEquiv (n : ℕ) :=
  TensorProduct K L (PiTensorProduct K (fun _ : Fin n => V)) ≃ₗ[L]
    PiTensorProduct L (fun _ : Fin n => TensorProduct K L V)

def IsTensorEquiv (n : ℕ) (e : TensorEquiv K L V n) : Prop :=
  ∀ (l : L) (x : Fin n → V),
    e (l ⊗ₜ[K] PiTensorProduct.tprod K x) =
      l • PiTensorProduct.tprod L (fun i => (1 : L) ⊗ₜ[K] x i)

/-- The entire canonical comparison square, with its actual maps specified on
representatives. No base-changed domain or finite-dimensionality is assumed. -/
def InitialTransport (ε : A →ₐ[K] K) (n : ℕ)
    (eA : DifferentialTensor ε n ≃ₗ[K] Grade ε n) : Prop :=
  ∃ (p : GradeEquiv K L A ε n) (q : FiberEquiv K L A ε)
    (t : TensorEquiv K L (DifferentialFiber ε) n)
    (eB : DifferentialTensor (augmentation K L A ε) n ≃ₗ[L]
      Grade (augmentation K L A ε) n),
    IsGradeEquiv K L A ε n p ∧ IsFiberEquiv K L A ε q ∧
    IsTensorEquiv K L (DifferentialFiber ε) n t ∧
    IsDifferentialPower (augmentation K L A ε) n eB ∧
    (∀ eB', IsDifferentialPower (augmentation K L A ε) n eB' → eB' = eB) ∧
    (∀ (l : L) (x : DifferentialTensor ε n),
      eB (PiTensorProduct.congr (fun _ : Fin n => q) (t (l ⊗ₜ[K] x))) =
        p (l ⊗ₜ[K] eA x)) ∧
    (∀ x : DifferentialTensor ε n,
      PiTensorProduct.congr (fun _ : Fin n => q) (t ((1 : L) ⊗ₜ[K] x)) = 0 ↔ x = 0)

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
variable (k : Type) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r}
variable {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}

/-- Scalar extension of the actual geometric initial tensor. The original germ,
Taylor square, representative of 5g, and differential power map are retained. -/
def ActualInitialExtension (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)]
    (g : (genericScheme k M).functionField)
    (F : Type v) [Field F] [Algebra (LaurentSeries k) F] : Prop :=
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) := (originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _ (originScalar k M s hs).toAlgebra
  ∃ (ε : OriginStalk k M s hs →ₐ[LaurentSeries k] LaurentSeries k)
    (κ : OriginStalk k M s hs →ₐ[LaurentSeries k] PowerSeries (LaurentSeries k))
    (eA : DifferentialTensor ε 24 ≃ₗ[LaurentSeries k] Grade ε 24)
    (b : ↥(ideal ε ^ 24)) (π : ideal ε),
    ActualTaylor k M s hs ε.toRingHom κ.toRingHom ∧
    IsTaylor ε κ ∧ IsDifferentialPower ε 24 eA ∧
    algebraMap (OriginStalk k M s hs) (genericScheme k M).functionField b.1 = 5*g ∧
    PowerSeries.coeff 1 (κ π.1) = 1 ∧
    InitialTransport (LaurentSeries k) F (OriginStalk k M s hs) ε 24 eA ∧
    IsTaylor (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε)
      (taylor (LaurentSeries k) F (OriginStalk k M s hs) κ) ∧
    ∃ (eB : DifferentialTensor (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε) 24 ≃ₗ[F]
        Grade (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε) 24)
      (bF : ↥(ideal (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε) ^ 24)),
      IsDifferentialPower (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε) 24 eB ∧
      bF.1 = inclusion (LaurentSeries k) F (OriginStalk k M s hs) b.1 ∧
      eB.symm (gradeClass _ 24 bF) =
        algebraMap (LaurentSeries k) F (ArithmeticThetaUnaryKatoPowerR0160.discriminant k r) •
          PiTensorProduct.tprod F (fun _ : Fin 24 =>
            differentialClass (augmentation (LaurentSeries k) F (OriginStalk k M s hs) ε)
              (inclusion (LaurentSeries k) F (OriginStalk k M s hs) π.1)) ∧
      eB.symm (gradeClass _ 24 bF) ≠ 0

end ArithmeticThetaInitialBaseChangeR0164
