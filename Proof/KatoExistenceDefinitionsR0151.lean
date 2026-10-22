module

public import ActualNormalizedKatoUniquenessR0150
public import CoprimeTorsionDivisorNormR0150
public import GeometricNormBaseChangeR0150
public import GeometricNormDefinitionsR0150

@[expose] public section

/-! Predicates on the actual Tate curve and its geometric base changes.
No function, divisor, norm equality or base-change provider is postulated. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaKatoExistenceR0151
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaGeometricNormR0150

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Actual principal orders, including nonsplit closed points. -/
def HasKatoDivisor (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (g : (genericScheme k M).functionField) : Prop :=
  g ≠ 0 ∧ ∀ x : genericScheme k M, Scheme.ord g x = katoOrder k M s hs G c x

/-- The norm for every actual positive multiplication prime to c. -/
def IsKatoFunction (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ)
    [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)]
    (g : (genericScheme k M).functionField) : Prop :=
  HasKatoDivisor k M s hs G c g ∧
    ∀ (d : ℕ), 0 < d → Nat.Coprime c d →
      ∀ (φ : (genericScheme k M).functionField →+* (genericScheme k M).functionField),
        IsFieldMap (multiplication k M G d) φ → fieldNorm φ g = g

/-- A genuine field-base-change square preserving the chosen origins and
multiplication morphisms. These geometric hypotheses do not mention functions. -/
def IsTateBaseChange
    (k' : Type u) [Field k'] [CharZero k']
    {r' : ℕ} {hr' : 0 < r'} {T' : Tower k' r' hr'}
    (M : Model k T) (M' : Model k' T')
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k))
    (s' : baseScheme k' ⟶ M'.X) (hs' : s' ≫ M'.p = 𝟙 (baseScheme k'))
    (G : Law k M) (G' : Law k' M')
    (ι : LaurentSeries k →+* LaurentSeries k')
    (b : genericScheme k' M' ⟶ genericScheme k M) : Prop :=
  IsPullback b (genericStructure k' M') (genericStructure k M)
    (Spec.map (CommRingCat.ofHom ι)) ∧
  (genericPoint k' M' s' hs' ≫ b =
    Spec.map (CommRingCat.ofHom ι) ≫ genericPoint k M s hs) ∧
  (∀ n : ℕ, multiplication k' M' G' n ≫ b = b ≫ multiplication k M G n)

end ArithmeticThetaKatoExistenceR0151
