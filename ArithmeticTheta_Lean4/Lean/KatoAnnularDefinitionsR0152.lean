import ActualKatoFunctionExistenceR0151
import ActualKatoFieldBaseChangeR0151
import LocalThetaRatioConstantR0088
import FiniteStageCompletionComparisonR0129
import MarkedExactTorsionR0146

/-! Actual maps from the completed annular charts to the algebraized model.
Every comparison uses the fixed finite-stage charts and structural maps. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaKatoAnnularR0152
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaMarkedGroupLawR0146

variable (k : Type u) [Field k] [CharZero k]
abbrev Chart := ArithmeticThetaAnnularTorsionPrereqR0053.Chart k
abbrev ChartField := ArithmeticThetaLocalOrdersR0066.FunctionField k

def chartScheme : Scheme.{u} := Spec (CommRingCat.of (Chart k))

def reduction (n : ℕ) : Chart k →+* A k n :=
  (Classical.choose (finite_stage_completion_comparison k n)).toRingHom.comp
    (trunc (Chart k) (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) n)

def chartBase : chartScheme k ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (ArithmeticThetaAnnularTorsionPrereqR0053.base k))

def chartToField : Chart k →+* ChartField k :=
  (ArithmeticThetaLocalOrdersR0066.toFunctionField k).comp
    (ArithmeticThetaAnnularTorsionPrereqR0053.toGeneric k)

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The same completed chart at every thickness, above the actual base. -/
def IsChartMap (M : Model k T) (j : Fin r)
    (χ : chartScheme k ⟶ M.X) : Prop :=
  χ ≫ M.p = chartBase k ∧ ∀ n : ℕ,
    Spec.map (CommRingCat.ofHom (reduction k n)) ≫ χ =
      (T.atlas n).chart j ≫ M.inclusion n

/-- Pullback on rational functions is determined by the actual generic-point
square into M. This is not a freely selected expansion functional. -/
def IsChartFieldMap (M : Model k T)
    [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X)
    (φ : (genericScheme k M).functionField →+* ChartField k) : Prop :=
  Spec.map (CommRingCat.ofHom φ) ≫
      (genericScheme k M).fromSpecStalk (_root_.genericPoint (genericScheme k M)) ≫
      genericInclusion k M =
    Spec.map (CommRingCat.ofHom (chartToField k)) ≫ χ

/-- Equation of the specified marked section on a completed chart; both ends
of the period are included through the actual cyclic successor. -/
def markedEquation (j i : Fin r) (a : kˣ) : Chart k :=
  (if j = i then ArithmeticThetaAnnularTorsionPrereqR0053.cx k -
    ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C (a : k)) else 1) *
  (if next r hr j = i then ArithmeticThetaAnnularTorsionPrereqR0053.cy k -
    ArithmeticThetaAnnularTorsionPrereqR0053.base k (PowerSeries.C ((a⁻¹ : kˣ) : k)) else 1)

def markedChartIdeal (M : Model k T) (p : baseScheme k ⟶ M.X)
    (χ : chartScheme k ⟶ M.X) : Ideal (Chart k) := by
  letI : IsAffine (chartScheme k) := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Chart k))))
  exact Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (Chart k))).hom.hom
    ((p.ker.comap χ).ideal ⟨⊤, isAffineOpen_top (chartScheme k)⟩)

/-- The c-torsion marks have component 2a in the 2c-polygon. -/
def torsionIndex (c : ℕ) (a : Fin c) : Fin (2*c) := ⟨2*a.val, by omega⟩

/-- Equality of actual closed-subscheme ideals, retaining the complete
multiplication fiber rather than just its rational points. -/
def SplitKernel {c : ℕ} {hr : 0 < 2*c} {T : Tower k (2*c) hr}
    (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M)
    (p : Fin c × Fin c → (baseScheme k ⟶ M.X))
    (hp : ∀ ab, p ab ≫ M.p = 𝟙 (baseScheme k)) : Prop :=
  (genericPoint k M s hs).ker.comap
      (ArithmeticThetaHodgeFourTorsionR0147.multiplication k M G c) =
    ⨅ ab : Fin c × Fin c, (genericPoint k M (p ab) (hp ab)).ker

end ArithmeticThetaKatoAnnularR0152
