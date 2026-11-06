import PairingShiftIndependenceR0118
import BasisCoordinateGeometryR0115

/-! Identification on the same cubic through equality transport of the coordinate
ring, its fraction field, the point group, and the complete local expansions. -/
noncomputable section
universe u
namespace ArithmeticThetaGeometricPairingR0118
open WeierstrassCurve.Affine

namespace SameCurve
variable {k : Type u} [Field k] [DecidableEq k]

def x (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W 0)
def y (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W 0)
def px (W : WeierstrassCurve.Affine k) : W.Point → k
  | .zero => 0
  | .some a _ _ => a
def py (W : WeierstrassCurve.Affine k) : W.Point → k
  | .zero => 0
  | .some _ b _ => b

def miller (W : WeierstrassCurve.Affine k) (a : k) : W.Point → W.FunctionField
  | .zero => 1
  | .some p q _ =>
    (algebraMap W.CoordinateRing W.FunctionField
      (CoordinateRing.YClass W (WeierstrassCurve.Affine.linePolynomial p q
        (W.slope p p q q)))) ^ 2 / (x W - algebraMap k W.FunctionField a)

def translated (W : WeierstrassCurve.Affine k) : W.Point → W.FunctionField × W.FunctionField
  | .zero => (x W, y W)
  | .some a b _ =>
    let s := (y W - algebraMap k W.FunctionField b) /
      (x W - algebraMap k W.FunctionField a)
    let X := s ^ 2 - algebraMap k W.FunctionField W.a₂ - x W -
      algebraMap k W.FunctionField a
    (X, -y W + s * (x W - X))

def val (W : WeierstrassCurve.Affine k)
    (T : W.Point → W.FunctionField ≃ₐ[k] W.FunctionField)
    (E : W.FunctionField →ₐ[k] LaurentSeries k)
    (f : W.FunctionField) (P : W.Point) : k := (E (T P f)).coeff 0

def moved (W : WeierstrassCurve.Affine k)
    (T : W.Point → W.FunctionField ≃ₐ[k] W.FunctionField)
    (E : W.FunctionField →ₐ[k] LaurentSeries k)
    (a b : k) (P Q Z : W.Point) : k :=
  val W T E (miller W a P) (Q + Z) / val W T E (miller W a P) Z *
    (val W T E (miller W b Q) (-Z) / val W T E (miller W b Q) (P - Z))

def phase (W : WeierstrassCurve.Affine k) (a b : k) (P Q : W.Point) : k :=
  ((py W Q - py W P - W.slope (px W P) (px W P) (py W P) (py W P) *
      (px W Q - px W P)) ^ 2 / (px W Q - a)) /
  ((py W P - py W Q - W.slope (px W Q) (px W Q) (py W Q) (py W Q) *
      (px W P - px W Q)) ^ 2 / (px W P - b))

omit [DecidableEq k]

/-- The coordinate-ring identification induced by equality of the cubics. -/
def coordinateRingIdentification (W W' : WeierstrassCurve.Affine k) (h : W = W') :
    W.CoordinateRing ≃ₐ[k] W'.CoordinateRing := by
  subst W'
  exact AlgEquiv.refl

/-- Its corresponding identification of the actual fraction fields. -/
def functionFieldIdentification (W W' : WeierstrassCurve.Affine k) (h : W = W') :
    W.FunctionField ≃ₐ[k] W'.FunctionField := by
  subst W'
  exact AlgEquiv.refl

/-- This field identification extends the coordinate-ring identification. -/
theorem identification_algebraMap (W W' : WeierstrassCurve.Affine k) (h : W = W')
    (f : W.CoordinateRing) :
    functionFieldIdentification W W' h (algebraMap W.CoordinateRing W.FunctionField f) =
      algebraMap W'.CoordinateRing W'.FunctionField
        (coordinateRingIdentification W W' h f) := by
  subst W'
  rfl

/-- Equality transport preserves the entire Laurent expansion, not only its
constant coefficient or leading term. -/
theorem expansion_identification (W W' : WeierstrassCurve.Affine k) (h : W = W')
    (T : W.Point → W.FunctionField ≃ₐ[k] W.FunctionField)
    (E : W.FunctionField →ₐ[k] LaurentSeries k)
    (P : W.Point) (f : W.FunctionField) :
    let T' : W'.Point → W'.FunctionField ≃ₐ[k] W'.FunctionField := h ▸ T
    let E' : W'.FunctionField →ₐ[k] LaurentSeries k := h ▸ E
    let P' : W'.Point := h ▸ P
    E' (T' P' (functionFieldIdentification W W' h f)) = E (T P f) := by
  subst W'
  rfl

end SameCurve
/-- Equality elimination transports the actual coordinate ring, fraction field,
point group, translation automorphisms, and Laurent expansion homomorphism
simultaneously. The root tuple is only used for the two vertical denominators. -/
theorem moved_phase_on_equal_curve
    (k : Type u) [Field k] [CharZero k] [DecidableEq k]
    (l : Fin 3 → k) (hl : Function.Injective l)
    (W : WeierstrassCurve.Affine k) (hW : W = Curve k l)
    (T : W.Point → W.FunctionField ≃ₐ[k] W.FunctionField)
    (hT : ∀ P, T P (SameCurve.x W) = (SameCurve.translated W P).1 ∧
      T P (SameCurve.y W) = (SameCurve.translated W P).2)
    (h : PowerSeries k) (E : W.FunctionField →ₐ[k] LaurentSeries k)
    (hh : ArithmeticThetaMillerR0114.branchEquation k l h)
    (hE : E (SameCurve.x W) = ArithmeticThetaMillerR0114.infinityX k h ∧
      E (SameCurve.y W) = ArithmeticThetaMillerR0114.infinityY k h)
    (P Q Z : W.Point)
    (hP : ∃ hp : W.Nonsingular (l 0) 0, 2 • P = Point.some (l 0) 0 hp)
    (hQ : ∃ hq : W.Nonsingular (l 1) 0, 2 • Q = Point.some (l 1) 0 hq)
    (hZ : Z ≠ 0 ∧ Z ≠ P ∧ Q + Z ≠ 0 ∧ Q + Z ≠ P) :
    SameCurve.moved W T E (l 0) (l 1) P Q Z =
      SameCurve.phase W (l 0) (l 1) P Q := by
  subst W
  have ht : ArithmeticThetaReciprocityR0116.IsTranslationSystem k l T := by
    intro R
    have ht := hT R
    have ha₂ : (Curve k l).a₂ = -(l 0 + l 1 + l 2) := rfl
    cases R <;> simpa only [SameCurve.translated, SameCurve.x, SameCurve.y,
      ArithmeticThetaReciprocityR0116.translatedCoordinates,
      ArithmeticThetaMillerR0114.xFunction, ArithmeticThetaMillerR0114.yFunction,
      ha₂, map_neg, sub_neg_eq_add] using ht
  have hm := ArithmeticThetaReciprocityR0116.arithmetic_moved_phase k l hl
    T ht h E hh hE P Q Z hP hQ hZ
  have hnP : P ≠ 0 := by
    intro hz
    obtain ⟨hp, hd⟩ := hP
    rw [hz, smul_zero] at hd
    exact (Point.some_ne_zero hp) hd.symm
  have hnQ : Q ≠ 0 := by
    intro hz
    obtain ⟨hq, hd⟩ := hQ
    rw [hz, smul_zero] at hd
    exact (Point.some_ne_zero hq) hd.symm
  cases P with
  | zero => exact False.elim (hnP rfl)
  | some p q hp =>
    cases Q with
    | zero => exact False.elim (hnQ rfl)
    | some a b hq =>
      simpa only [SameCurve.moved, SameCurve.miller, SameCurve.val,
        SameCurve.phase, SameCurve.px, SameCurve.py, SameCurve.x,
        ArithmeticThetaReciprocityR0116.movedPairing,
        ArithmeticThetaReciprocityR0116.millerAt,
        ArithmeticThetaReciprocityR0116.localValue,
        ArithmeticThetaReciprocityR0116.expansion,
        ArithmeticThetaReciprocityR0116.fixedLabelPhase,
        ArithmeticThetaMillerR0114.millerFunction,
        ArithmeticThetaMillerR0114.millerRatio,
        ArithmeticThetaMillerR0114.millerValue,
        ArithmeticThetaMillerR0114.tangentValue,
        ArithmeticThetaMillerR0114.tangentClass,
        ArithmeticThetaMillerR0114.tangentSlope,
        ArithmeticThetaMillerR0114.xFunction] using hm

/-- The accepted intrinsic phase is the actual moved-divisor pairing for every
ordered full-four basis, without a restriction on the original root labels. -/
theorem marking_pairing_identification :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Function.Injective e → ∀ D : LocalData k e,
      ∀ b : ArithmeticThetaMarkingR0115.Marking k e,
      ArithmeticThetaMarkingR0115.IsBasis k e b →
      pairing k e D (b 0) (b 1) = ArithmeticThetaMarkingR0115.phase k e b := by
  intro k _ _ _ e he D b hb
  obtain ⟨hfinite, ⟨σ, hlabels⟩, hcurve, hd, _, _⟩ :=
    ArithmeticThetaMarkingR0115.basis_coordinate_geometry k e he b hb
  let l := ArithmeticThetaMarkingR0115.labels k e b
  have hl : Function.Injective l := by
    change Function.Injective (ArithmeticThetaMarkingR0115.labels k e b)
    rw [hlabels]
    exact he.comp σ.injective
  have hh : ArithmeticThetaMillerR0114.branchEquation k l D.branch := by
    refine ⟨D.branch_spec.1, ?_⟩
    have hp := Equiv.prod_comp σ (fun i => D.branch - PowerSeries.C (e i) * PowerSeries.X ^ 2)
    rw [D.branch_spec.2]
    simpa only [l, hlabels, Function.comp_apply] using hp.symm
  have ht : ∀ P, D.translations P (SameCurve.x (Curve k e)) =
      (SameCurve.translated (Curve k e) P).1 ∧
      D.translations P (SameCurve.y (Curve k e)) =
      (SameCurve.translated (Curve k e) P).2 := by
    intro P
    have ht := D.translations_spec P
    have ha₂ : (Curve k e).a₂ = -(e 0 + e 1 + e 2) := rfl
    cases P <;> simpa only [SameCurve.translated, SameCurve.x, SameCurve.y,
      ArithmeticThetaReciprocityR0116.translatedCoordinates,
      ArithmeticThetaMillerR0114.xFunction, ArithmeticThetaMillerR0114.yFunction,
      ha₂, map_neg, sub_neg_eq_add] using ht
  have hf (i : Fin 2) : fourFunction k e (b i) =
      SameCurve.miller (Curve k e) (l i.castSucc) (b i) := by
    obtain ⟨hi, hdi⟩ := hd i
    have hx : ArithmeticThetaMarkingR0115.pointX k e (2 • b i) = l i.castSucc := by
      rw [hdi]
      rfl
    have hy := (hfinite i).2
    cases hp : b i with
    | zero => rfl
    | some x y h =>
      have hy' : y ≠ 0 := by
        simpa only [hp, ArithmeticThetaMarkingR0115.pointY] using hy
      simp only [hp] at hx
      simp only [fourFunction, if_neg hy', hx, SameCurve.miller, SameCurve.x,
        ArithmeticThetaMillerR0114.tangentClass,
        ArithmeticThetaMillerR0114.tangentSlope,
        ArithmeticThetaMillerR0114.xFunction]
  obtain ⟨z, hz⟩ := (all_four_miller_provider k e he D).2 b hb (b 0) (b 1)
    (hb.1 0) (hb.1 1)
  let Z := ArithmeticThetaMarkingR0115.coordinates k e b z
  have hshift := ((pairing_shift_independence k e he D b hb (b 0) (b 1)
    (hb.1 0) (hb.1 1)).1 Z hz).2.2.2.2
  rw [← hshift]
  have hm := moved_phase_on_equal_curve k l hl (Curve k e) hcurve
    D.translations ht D.branch D.embedding hh D.embedding_spec
    (b 0) (b 1) Z (hd 0) (hd 1) hz
  have hmoved : movedValue k e D (b 0) (b 1) Z =
      SameCurve.moved (Curve k e) D.translations D.embedding (l 0) (l 1)
        (b 0) (b 1) Z := by
    simp only [movedValue, hf, SameCurve.moved, value,
      ArithmeticThetaReciprocityR0116.localValue,
      ArithmeticThetaReciprocityR0116.expansion, SameCurve.val]
    rfl
  rw [hmoved, hm]
  dsimp only [SameCurve.phase, ArithmeticThetaMarkingR0115.phase,
    ArithmeticThetaMarkingR0115.tangent, ArithmeticThetaMillerR0114.tangentValue,
    ArithmeticThetaMillerR0114.tangentSlope]
  cases h0 : b 0 <;> cases h1 : b 1 <;> rfl

end ArithmeticThetaGeometricPairingR0118
