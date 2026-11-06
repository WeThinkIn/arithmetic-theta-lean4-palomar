module

public import RelativeFourCharacterDefinitionsR0211
public import IndependentHalvesFourBasisR0114
public import RelativeFourTorsionRootR0190

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativeSplitFiberBasis
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
lemma coordinates_exists (M : FullLevel R W G 4 (𝟙 (Base R))) :
    ∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y := by
  obtain ⟨e, x₁, y₁, he, hs, hp⟩ :=
    RelativeFourTorsionRoot.coordinates W G hG 4 (by decide) (by decide) M
  have ha : Disjoint (Set.range M.x.val) (Set.range (origin R W)) := by
    simpa only [Fin.val_one, Fin.val_zero, G.nsmul_one_apply, G.nsmul_zero, G.mul_one]
      using M.avoids 1 0 (Or.inl (by decide))
  obtain ⟨χ, hχ⟩ := TwoTorsionAffineCoordinates.exists_chart_factorization W _ ha
  refine ⟨e, ![χ (xOverZ W.toProjective), x₁],
    ![χ (yOverZ W.toProjective), y₁], he, hs, ?_, ?_⟩
  · exact ⟨M.x.property, χ, hχ, rfl, rfl⟩
  · simpa [quarterPoint, G.nsmul_one_apply, G.one_mul] using hp

lemma fiber_roots {e : Fin 3 → R} (hs : SplitCubic R W e)
    (F : Type u) [Field F] (ι : R →+* F) : Function.Injective (ι ∘ e) := by
  intro i j hij
  by_contra hne
  have hu := (hs.1 i j hne).map ι
  apply hu.ne_zero
  simpa only [map_sub, Function.comp_apply, sub_eq_zero] using hij

lemma fiber_unique {e : Fin 3 → R} {x y : Fin 2 → R}
    (F : Type u) [Field F] (ι : R →+* F)
    (b c : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e))
    (hb : FiberCoordinates R W e x y F ι b)
    (hc : FiberCoordinates R W e x y F ι c) : b = c := by
  funext i
  obtain ⟨hbn, hbx, hby⟩ := hb i
  obtain ⟨hcn, hcx, hcy⟩ := hc i
  cases hb' : b i with
  | zero => exact (hbn hb').elim
  | some a d ha =>
    cases hc' : c i with
    | zero => exact (hcn hc').elim
    | some a' d' ha' =>
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      simpa only [hb', hc', ArithmeticThetaMarkingR0115.pointX,
        ArithmeticThetaMarkingR0115.pointY] using
        And.intro (hbx.trans hcx.symm) (hby.trans hcy.symm)

lemma coefficients {e : Fin 3 → R} (M : FullLevel R W G 4 (𝟙 (Base R)))
    (he : Labels R W G 4 M e) (hs : SplitCubic R W e) :
    W.a₂ + algebraMap ℚ R (1/4) * W.a₁^2 = -(e 0+e 1+e 2) ∧
    W.a₄ + algebraMap ℚ R (1/2) * W.a₁*W.a₃ = e 0*e 1+e 0*e 2+e 1*e 2 ∧
    W.a₆ + algebraMap ℚ R (1/4) * W.a₃^2 = -(e 0*e 1*e 2) := by
  exact TwoTorsionSplitCubicR0177.cubic_coefficients _ _ _ _ _ _
    (sub_ne_zero.mp (hs.1 0 1 (by decide)).ne_zero)
    (sub_ne_zero.mp (hs.1 1 2 (by decide)).ne_zero)
    (sub_ne_zero.mp (hs.1 0 2 (by decide)).ne_zero)
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))

/-- Completing the square transports the doubled X coordinate. The doubled
Y coordinate is then forced to vanish by the split equation at a root. -/
lemma completed_half {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (V : WeierstrassCurve.Affine F) (e : Fin 3 → F) (i : Fin 3) (x y : F)
    (ha : V.a₂ + V.a₁^2/4 = -(e 0+e 1+e 2))
    (hb : V.a₄ + V.a₁*V.a₃/2 = e 0*e 1+e 0*e 2+e 1*e 2)
    (hc : V.a₆ + V.a₃^2/4 = -(e 0*e 1*e 2))
    (he : V.Equation x y) (hn : y ≠ V.negY x y)
    (hd : V.addX x x (V.slope x x y y) = e i) :
    ∃ h : (ArithmeticThetaMillerR0114.Curve F e).Nonsingular
        x (y+(V.a₁*x+V.a₃)/2),
      ArithmeticThetaMillerR0114.IsHalfPoint F e i
        (WeierstrassCurve.Affine.Point.some x (y+(V.a₁*x+V.a₃)/2) h) := by
  let Y := y+(V.a₁*x+V.a₃)/2
  let S := ArithmeticThetaMillerR0114.Curve F e
  have ha' : V.a₂ = -(e 0+e 1+e 2)-V.a₁^2/4 := by linear_combination ha
  have hb' : V.a₄ = e 0*e 1+e 0*e 2+e 1*e 2-V.a₁*V.a₃/2 := by linear_combination hb
  have hc' : V.a₆ = -(e 0*e 1*e 2)-V.a₃^2/4 := by linear_combination hc
  have hy : Y ≠ 0 := by
    intro hz
    apply hn
    change y = -y - V.a₁*x - V.a₃
    dsimp [Y] at hz
    linear_combination 2*hz
  have hnS : Y ≠ S.negY x Y := by
    change Y ≠ -Y - 0*x - 0
    intro h
    apply hy
    linear_combination (1/2 : F)*h
  have heS : S.Equation x Y := by
    rw [WeierstrassCurve.Affine.equation_iff] at he ⊢
    simp only [S, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      zero_mul, add_zero]
    rw [ha', hb', hc'] at he
    dsimp [Y]
    linear_combination he
  have hs : S.Nonsingular x Y :=
    (WeierstrassCurve.Affine.nonsingular_iff ..).mpr ⟨heS, Or.inr hnS⟩
  have hslope : V.slope x x y y = S.slope x x Y Y - V.a₁/2 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hnS]
    simp only [S, ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve,
      WeierstrassCurve.Affine.negY, zero_mul, sub_zero, sub_neg_eq_add]
    rw [ha', hb']
    have hD : y - (-y - V.a₁*x - V.a₃) = 2*Y := by dsimp [Y]; ring
    rw [hD, ← two_mul Y]
    field_simp
    dsimp [Y]
    ring
  have hX : S.addX x x (S.slope x x Y Y) = e i := by
    rw [← hd, hslope]
    simp only [WeierstrassCurve.Affine.addX, S, ArithmeticThetaMillerR0114.Curve,
      ArithmeticThetaFourTorsion.splitCurve, zero_mul, add_zero]
    rw [ha']
    ring
  have hsum := WeierstrassCurve.Affine.nonsingular_add hs hs
    (fun hxy => hnS hxy.2)
  have hY : S.addY x x Y (S.slope x x Y Y) = 0 := by
    have heq := (ArithmeticThetaFourTorsion.split_equation (e 0) (e 1) (e 2) _ _).mp hsum.1
    rw [hX] at heq
    have hz : (e i-e 0)*(e i-e 1)*(e i-e 2) = 0 := by fin_cases i <;> simp
    rw [hz] at heq
    exact mul_self_eq_zero.mp (by simpa only [pow_two] using heq)
  refine ⟨hs, ?_⟩
  have hr : S.Nonsingular (e i) 0 := by simpa only [hX, hY] using hsum
  refine ⟨hr, ?_⟩
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnS,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

include hG in
lemma fiber_half (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F)
    (i : Fin 2) :
    ∃ h : (ArithmeticThetaMillerR0114.Curve F (ι ∘ e)).Nonsingular
        (ι (x i)) (ι (completedY R W (x i) (y i))),
      ArithmeticThetaMillerR0114.IsHalfPoint F (ι ∘ e) i.castSucc
        (WeierstrassCurve.Affine.Point.some _ _ h) := by
  letI : Algebra R F := ι.toAlgebra
  let V := (W.toProjective.baseChange F).toAffine
  let P : SchemeHomOver (𝟙 (Base R)) (structureMap R W) := ![M.x, M.y] i
  let Q := G.nsmul (𝟙 (Base R)) 2 P
  have hp : HasCoordinates R W P.val (x i) (y i) := by
    fin_cases i
    · exact hC.2.2.1
    · exact hC.2.2.2
  have hq : HasCoordinates R W Q.val (e i.castSucc)
      (-(algebraMap ℚ R (1/2)) * (W.a₁ * e i.castSucc + W.a₃)) := by
    fin_cases i
    · exact hC.1 0
    · exact hC.1 1
  obtain ⟨hn, hd⟩ := RelativeFourTorsionRoot.field_double W G hG F
    P Q rfl (x i) (y i) _ _ hp hq
  obtain ⟨ha, hb, hc⟩ := coefficients W G M hC.1 hC.2.1
  have hrat (q : ℚ) : ι (algebraMap ℚ R q) = (q : F) :=
    map_ratCast (ι.comp (algebraMap ℚ R)) q
  have haF := congrArg ι ha
  have hbF := congrArg ι hb
  have hcF := congrArg ι hc
  simp only [map_add, map_neg, map_mul, map_pow, hrat] at haF hbF hcF
  norm_num at haF hbF hcF
  have heq : V.Equation (ι (x i)) (ι (y i)) := by
    have h := congrArg ι ((WeierstrassCurve.Affine.equation_iff ..).mp
      (TwoTorsionSplitCubicR0177.equation hp))
    rw [WeierstrassCurve.Affine.equation_iff]
    change ι (y i)^2 + ι W.a₁ * ι (x i) * ι (y i) + ι W.a₃ * ι (y i) =
      ι (x i)^3 + ι W.a₂ * ι (x i)^2 + ι W.a₄ * ι (x i) + ι W.a₆
    simpa only [map_add, map_mul, map_pow] using h
  have hY : ι (completedY R W (x i) (y i)) =
      ι (y i)+(V.a₁*ι (x i)+V.a₃)/2 := by
    change ι (completedY R W (x i) (y i)) =
      ι (y i)+(ι W.a₁*ι (x i)+ι W.a₃)/2
    simp only [completedY, map_add, map_mul, hrat]
    norm_num
    ring
  rw [hY]
  exact completed_half V (ι ∘ e) i.castSucc (ι (x i)) (ι (y i))
    (by change ι W.a₂ + (ι W.a₁)^2/4 = _; dsimp only [Function.comp_apply]; linear_combination haF)
    (by change ι W.a₄ + ι W.a₁*ι W.a₃/2 = _; dsimp only [Function.comp_apply]; linear_combination hbF)
    (by change ι W.a₆ + (ι W.a₃)^2/4 = _; dsimp only [Function.comp_apply]; linear_combination hcF) heq hn hd

lemma halves_basis {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (e : Fin 3 → F) (he : Function.Injective e)
    (b : ArithmeticThetaMarkingR0115.Marking F e)
    (hb : ∀ i : Fin 2, ArithmeticThetaMillerR0114.IsHalfPoint F e i.castSucc (b i)) :
    ArithmeticThetaMarkingR0115.IsBasis F e b ∧
      ArithmeticThetaMarkingR0115.labels F e b = e := by
  have h4 (i : Fin 2) : 4 • b i = 0 := by
    obtain ⟨h, hd⟩ := hb i
    have ht : 2 • WeierstrassCurve.Affine.Point.some (e i.castSucc) 0 h = 0 := by
      rw [two_nsmul]
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [WeierstrassCurve.Affine.negY, ArithmeticThetaMillerR0114.Curve,
        ArithmeticThetaFourTorsion.splitCurve]
    calc
      4 • b i = 2 • (2 • b i) := by rw [← mul_nsmul]
      _ = 0 := by rw [hd, ht]
  have hall := ArithmeticThetaMillerR0114.independent_halves_four_basis
    F e he (b 0) (b 1) (hb 0) (hb 1)
  constructor
  · refine ⟨h4, ?_, ?_⟩
    · intro a c hac
      have ht : 4 • ArithmeticThetaMarkingR0115.coordinates F e b a = 0 := by
        simp only [ArithmeticThetaMarkingR0115.coordinates, nsmul_add,
          smul_comm 4, h4, nsmul_zero, add_zero]
      obtain ⟨z, hz, hu⟩ := (hall _).mp ht
      exact (hu a rfl).trans (hu c hac.symm).symm
    · intro T hT
      obtain ⟨z, hz, _⟩ := (hall T).mp hT
      exact ⟨z, hz⟩
  · obtain ⟨h0, hd0⟩ := hb 0
    obtain ⟨h1, hd1⟩ := hb 1
    have h2 := (ArithmeticThetaFourTorsion.split_smooth (e 0) (e 1) (e 2)
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))).2.2.2
    have hadd : WeierstrassCurve.Affine.Point.some (e 0) 0 h0 +
        WeierstrassCurve.Affine.Point.some (e 1) 0 h1 =
        WeierstrassCurve.Affine.Point.some (e 2) 0 h2 := by
      have h01 : e 0 ≠ e 1 := he.ne (by decide)
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne h01,
        WeierstrassCurve.Affine.Point.some.injEq]
      simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        ArithmeticThetaMillerR0114.Curve, ArithmeticThetaFourTorsion.splitCurve]
      simp [WeierstrassCurve.Affine.slope_of_X_ne h01]
      ring
    funext i
    fin_cases i <;>
      simp [ArithmeticThetaMarkingR0115.labels, hd0, hd1, hadd,
        ArithmeticThetaMarkingR0115.pointX]

end RelativeSplitFiberBasis


/-- The actual marked sections give the unique completed-square fiber marking,
which is a basis of all rational four-torsion with the prescribed doubled labels. -/
theorem relative_split_fiber_basis :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∃ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y) ∧ (∀ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y → ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F),  Function.Injective (ι ∘ e) ∧ (∃! b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b) ∧ (∀ b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b → ArithmeticThetaMarkingR0115.IsBasis F (ι ∘ e) b ∧ ArithmeticThetaMarkingR0115.labels F (ι ∘ e) b = ι ∘ e)) := by
  intro R _ _ _ _ _ W _ G hG M
  refine ⟨RelativeSplitFiberBasis.coordinates_exists W G hG M, ?_⟩
  intro e x y hC F _ _ _ ι
  have he := RelativeSplitFiberBasis.fiber_roots W hC.2.1 F ι
  have hh := RelativeSplitFiberBasis.fiber_half W G hG M e x y hC F ι
  choose h hs using hh
  let b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e) :=
    fun i => WeierstrassCurve.Affine.Point.some (ι (x i))
      (ι (ArithmeticThetaGlobalFourTorsionR0190.completedY R W (x i) (y i))) (h i)
  have hb : FiberCoordinates R W e x y F ι b := by
    intro i
    exact ⟨WeierstrassCurve.Affine.Point.some_ne_zero _, rfl, rfl⟩
  refine ⟨he, ⟨b, hb, ?_⟩, ?_⟩
  · intro c hc
    exact RelativeSplitFiberBasis.fiber_unique W F ι c b hc hb
  · intro c hc
    have hcb := RelativeSplitFiberBasis.fiber_unique W F ι c b hc hb
    subst c
    exact RelativeSplitFiberBasis.halves_basis (ι ∘ e) he b hs

#print axioms relative_split_fiber_basis

end ArithmeticThetaRelativeFourCharacterR0211
