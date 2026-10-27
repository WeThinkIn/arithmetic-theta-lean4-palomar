import RelativeGeometricPhaseR0211
import RelativeMarkingActionR0211
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativePhaseMarkingInvariance
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open WeierstrassCurve.Affine WeierstrassProjModel

section Field
variable {F : Type u} [Field F] [CharZero F] [DecidableEq F]

def px (V : WeierstrassCurve F) : V.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

def py (V : WeierstrassCurve F) : V.toAffine.Point → F
  | .zero => 0
  | .some _ y _ => y

def phaseOn (V : WeierstrassCurve F) (b : Fin 2 → V.toAffine.Point) : F :=
  let tangent := fun P Q => py V Q - py V P -
    V.toAffine.slope (px V P) (px V P) (py V P) (py V P) * (px V Q - px V P)
  (tangent (b 0) (b 1)^2 / (px V (b 1) - px V (2 • b 0))) /
    (tangent (b 1) (b 0)^2 / (px V (b 0) - px V (2 • b 1)))

lemma phaseOn_split (e : Fin 3 → F) (b : ArithmeticThetaMarkingR0115.Marking F e) :
    phaseOn (ArithmeticThetaMarkingR0115.Curve F e) b =
      ArithmeticThetaMarkingR0115.phase F e b := by
  have hx (P : (ArithmeticThetaMarkingR0115.Curve F e).Point) :
      px _ P = ArithmeticThetaMarkingR0115.pointX F e P := by cases P <;> rfl
  have hy (P : (ArithmeticThetaMarkingR0115.Curve F e).Point) :
      py _ P = ArithmeticThetaMarkingR0115.pointY F e P := by cases P <;> rfl
  simp only [phaseOn, hx, hy, ArithmeticThetaMarkingR0115.phase,
    ArithmeticThetaMarkingR0115.tangent, ArithmeticThetaMarkingR0115.labels,
    ArithmeticThetaMillerR0114.tangentValue, ArithmeticThetaMillerR0114.tangentSlope,
    Matrix.cons_val_zero, Matrix.cons_val_one]

def castPoint {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst V'
  exact AddEquiv.refl _

lemma castPoint_some {V V' : WeierstrassCurve F} (h : V = V')
    (x y : F) (hp : V.toAffine.Nonsingular x y) :
    ∃ hp', castPoint h (.some x y hp) = .some x y hp' := by
  subst V'
  exact ⟨hp, rfl⟩

lemma phaseOn_cast {V V' : WeierstrassCurve F} (h : V = V')
    (b : Fin 2 → V.toAffine.Point) :
    phaseOn V' (castPoint h ∘ b) = phaseOn V b := by
  subst V'
  rfl

def completeChange (V : WeierstrassCurve F) : WeierstrassCurve.VariableChange F :=
  ⟨1, 0, -V.a₁/2, -V.a₃/2⟩

def completeMap (V : WeierstrassCurve F) :
    V.toAffine.Point →+ ((completeChange V) • V).toAffine.Point :=
  { toFun := Point.vcInvFun (completeChange V) V
    map_zero' := rfl
    map_add' := Point.vcInvFun_add (completeChange V) V }

lemma completeMap_some (V : WeierstrassCurve F) (x y : F)
    (h : V.toAffine.Nonsingular x y) :
    ∃ h', completeMap V (.some x y h) =
      .some x (y + (V.a₁*x+V.a₃)/2) h' := by
  have hh := (nonsingular_variableChange_iff (C := completeChange V) (W := V)
    (vcXInv (completeChange V) x) (vcYInv (completeChange V) x y)).mpr
    (by simpa only [vcX_vcXInv, vcY_vcYInv] using h)
  have hx : vcXInv (completeChange V) x = x := by simp [vcXInv, completeChange]
  have hy : vcYInv (completeChange V) x y = y + (V.a₁*x+V.a₃)/2 := by
    simp only [vcYInv, completeChange, inv_one, Units.val_one, one_pow, one_mul, sub_zero]
    ring
  refine ⟨by simpa only [hx, hy] using hh, ?_⟩
  change Point.some _ _ _ = Point.some _ _ _
  rw [Point.some.injEq]
  exact ⟨hx, hy⟩

end Field
variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

lemma completed_curve (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F) :
    completeChange (W.map ι) • W.map ι = ArithmeticThetaMillerR0114.Curve F (ι ∘ e) := by
  obtain ⟨ha, hb, hc⟩ := RelativeSplitFiberBasis.coefficients W G M hC.1 hC.2.1
  have hrat (q : ℚ) : ι (algebraMap ℚ R q) = (q : F) :=
    map_ratCast (ι.comp (algebraMap ℚ R)) q
  have haF := congrArg ι ha
  have hbF := congrArg ι hb
  have hcF := congrArg ι hc
  simp only [map_add, map_neg, map_mul, map_pow, hrat] at haF hbF hcF
  norm_num at haF hbF hcF
  apply WeierstrassCurve.ext
  all_goals simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, completeChange, inv_one, Units.val_one,
    one_pow, one_mul, ArithmeticThetaMillerR0114.Curve,
    ArithmeticThetaFourTorsion.splitCurve, WeierstrassCurve.map, Function.comp_apply]
  · ring
  · linear_combination haF
  · ring
  · linear_combination hbF
  · linear_combination hcF

include hG in
lemma evaluation_exists (F : Type u) [Field F] [DecidableEq F] (ι : R →+* F) :
    ∃ ev : SchemeHomOver (𝟙 (Base R)) (structureMap R W) → (W.map ι).toAffine.Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      (∀ n P, ev (G.nsmul (𝟙 _) n P) = n • ev P) ∧
      ∀ P x y, HasCoordinates R W P.val x y →
        ∃ h, ev P = Point.some (ι x) (ι y) h := by
  letI : Algebra R F := ι.toAlgebra
  let f := Spec.map (CommRingCat.ofHom ι)
  obtain ⟨E, hE, _, hc⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists W G
      (by simpa [origin] using hG.1 (𝟙 (Base R)))
  let ev := fun P : SchemeHomOver (𝟙 (Base R)) (structureMap R W) =>
    E F (schemeHomOverComp f (Category.comp_id f) P)
  have hmul (P Q) : ev (G.mul (𝟙 _) P Q) = ev P + ev Q := by
    dsimp [ev]
    rw [G.mul_natural, hE.1]
  have hzero : ev (G.one (𝟙 _)) = 0 := by
    have hh := hmul (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at hh
    exact add_left_cancel (show ev (G.one (𝟙 _)) + ev (G.one (𝟙 _)) =
      ev (G.one (𝟙 _)) + 0 by simpa using hh.symm)
  refine ⟨ev, hmul, ?_, ?_⟩
  · intro n P
    induction n with
    | zero => simpa only [G.nsmul_zero, zero_nsmul] using hzero
    | succ n ih => simpa only [G.nsmul_succ, hmul, ih, succ_nsmul, add_comm]
  · intro P x y hP
    obtain ⟨_, χ, hχ, hx, hy⟩ := hP
    have hχ' : (schemeHomOverComp f (Category.comp_id f) P).val =
        Spec.map (CommRingCat.ofHom (ι.comp χ)) ≫ WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective := by
      change f ≫ P.val = _
      rw [hχ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    obtain ⟨h, hh⟩ := hc F _ (ι.comp χ) hχ'
    simp only [RingHom.comp_apply, hx, hy] at h hh
    exact ⟨h, hh⟩

include hG in
lemma phase_comparison (F : Type u) [Field F] [CharZero F] [DecidableEq F]
    (ι : R →+* F)
    (ev : SchemeHomOver (𝟙 (Base R)) (structureMap R W) → (W.map ι).toAffine.Point)
    (hc : ∀ P x y, HasCoordinates R W P.val x y →
      ∃ h, ev P = Point.some (ι x) (ι y) h)
    (M : FullLevel R W G 4 (𝟙 (Base R))) (z : R) (hz : GeometricPhase R W G M z) :
    let V := completeChange (W.map ι) • W.map ι
    let a := fun i : Fin 2 => completeMap (W.map ι) (ev (![M.x, M.y] i))
    ι z = phaseOn V a ∧
      ∃ e : Fin 3 → F, Function.Injective e ∧
        ∃ h : V = ArithmeticThetaMillerR0114.Curve F e,
          ArithmeticThetaMarkingR0115.IsBasis F e (castPoint h ∘ a) := by
  dsimp only
  obtain ⟨e, x, y, hC⟩ := hz.1
  let hV := completed_curve W G M e x y hC F ι
  let a := fun i : Fin 2 => completeMap (W.map ι) (ev (![M.x, M.y] i))
  let b := castPoint hV ∘ a
  have hb : FiberCoordinates R W e x y F ι b := by
    intro i
    have hp : HasCoordinates R W (![M.x, M.y] i).val (x i) (y i) := by
      fin_cases i
      · exact hC.2.2.1
      · exact hC.2.2.2
    obtain ⟨h, hh⟩ := hc _ _ _ hp
    obtain ⟨h', hh'⟩ := completeMap_some (W.map ι) (ι (x i)) (ι (y i)) h
    obtain ⟨h'', hh''⟩ := castPoint_some hV _ _ h'
    have he : b i = Point.some _ _ h'' := by
      dsimp [b, a, Function.comp_apply]
      rw [hh, hh', hh'']
    have hrat (q : ℚ) : ι (algebraMap ℚ R q) = (q : F) :=
      map_ratCast (ι.comp (algebraMap ℚ R)) q
    refine ⟨by rw [he]; exact Point.some_ne_zero _, ?_, ?_⟩
    · rw [he]; rfl
    · rw [he]
      change ι (y i) + (ι W.a₁ * ι (x i) + ι W.a₃)/2 = _
      simp only [completedY, map_add, map_mul, hrat]
      norm_num
      ring
  obtain ⟨he, _, hB⟩ := (relative_split_fiber_basis R W G hG M).2 e x y hC F ι
  have hbas := (hB b hb).1
  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character F (ι ∘ e) he
  refine ⟨?_, ι ∘ e, he, hV, hbas⟩
  calc
    ι z = ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1) :=
      hz.2 e x y hC F ι b hb D
    _ = ArithmeticThetaMarkingR0115.phase F (ι ∘ e) b :=
      ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F (ι ∘ e) he D b hbas
    _ = phaseOn _ a := (phaseOn_split (ι ∘ e) b).symm.trans (phaseOn_cast hV a)

end RelativePhaseMarkingInvariance
open RelativePhaseMarkingInvariance
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- Every determinant-one change of actual marking sections preserves the
regular geometric phase. Equality is tested on the actual generic fiber. -/
theorem relative_phase_marking_invariance :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ (M M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (A : ArithmeticThetaFourTorsion.Mat4), A.det = 1 → ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M M' A → ∀ z z' : R, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z → ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M' z' → z' = z := by
  intro R _ _ _ _ _ W _ G hG M M' A hA hchange z z' hz hz'
  classical
  let F := FractionRing R
  let f : R →+* F := algebraMap R F
  have hf : Function.Injective f := IsFractionRing.injective R F
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  letI : CharZero F := charZero_of_injective_algebraMap hf
  obtain ⟨ev, hmul, hn, hc⟩ := evaluation_exists W G hG F f
  let V := completeChange (W.map f) • W.map f
  let a := fun i : Fin 2 => completeMap (W.map f) (ev (![M.x, M.y] i))
  let a' := fun i : Fin 2 => completeMap (W.map f) (ev (![M'.x, M'.y] i))
  obtain ⟨heq, e, he, hV, hB⟩ := phase_comparison W G hG F f ev hc M z hz
  have heq' := (phase_comparison W G hG F f ev hc M' z' hz').1
  change f z = phaseOn V a at heq
  change f z' = phaseOn V a' at heq'
  change ArithmeticThetaMarkingR0115.IsBasis F e (castPoint hV ∘ a) at hB
  have hact : castPoint hV ∘ a' =
      ArithmeticThetaMarkingR0115.act F e (castPoint hV ∘ a) A := by
    funext i
    fin_cases i
    · change castPoint hV (completeMap (W.map f) (ev M'.x)) = _
      rw [hchange.1]
      simp only [hmul, hn, map_add, map_nsmul]
      rfl
    · change castPoint hV (completeMap (W.map f) (ev M'.y)) = _
      rw [hchange.2]
      simp only [hmul, hn, map_add, map_nsmul]
      rfl
  obtain ⟨D, hD⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character F e he
  have hBa := ArithmeticThetaMarkingR0115.basis_act (castPoint hV ∘ a) hB A hA
  have hinv : ArithmeticThetaMarkingR0115.phase F e
      (ArithmeticThetaMarkingR0115.act F e (castPoint hV ∘ a) A) =
      ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a) := by
    rw [← ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F e he D _ hBa,
      ← ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F e he D _ hB]
    exact (hD _ hB).2.2 A hA
  apply hf
  rw [heq', heq]
  calc
    phaseOn V a' = phaseOn _ (castPoint hV ∘ a') := (phaseOn_cast hV a').symm
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a') := phaseOn_split e _
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a) := by rw [hact]; exact hinv
    _ = phaseOn V a := (phaseOn_split e _).symm.trans (phaseOn_cast hV a)

#print axioms relative_phase_marking_invariance

end ArithmeticThetaRelativeFourCharacterR0211
