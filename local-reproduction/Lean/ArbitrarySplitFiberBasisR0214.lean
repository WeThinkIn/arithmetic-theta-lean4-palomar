import RelativeSplitFiberBasisR0211
import ArbitraryFourTorsionRootR0214

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitrarySplitFiberBasis
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeFourCharacterR0211
open WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
lemma coordinates_exists (M : FullLevel R W G 4 (𝟙 (Base R))) :
    ∃ (e : Fin 3 → R) (x y : Fin 2 → R), Coordinates R W G M e x y := by
  obtain ⟨e, x₁, y₁, g, he, hs, hp, _⟩ :=
    arbitrary_four_torsion_root R W G hG 4 (by decide) (by decide) M
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
  exact ArithmeticThetaArbitraryAffineR0202.ArbitrarySplitCubic.cubic_coefficients _ _ _ _ _ _
    (hs.1 0 1 (by decide))
    (hs.1 1 2 (by decide))
    (hs.1 0 2 (by decide))
    (TwoTorsionSplitCubicR0177.root_equation (he 0))
    (TwoTorsionSplitCubicR0177.root_equation (he 1))
    (TwoTorsionSplitCubicR0177.root_equation (he 2))

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
  obtain ⟨hn, hd⟩ := ArbitraryFourTorsionRoot.field_double W G hG F
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
  exact RelativeSplitFiberBasis.completed_half V (ι ∘ e) i.castSucc (ι (x i)) (ι (y i))
    (by change ι W.a₂ + (ι W.a₁)^2/4 = _; dsimp only [Function.comp_apply]; linear_combination haF)
    (by change ι W.a₄ + ι W.a₁*ι W.a₃/2 = _; dsimp only [Function.comp_apply]; linear_combination hbF)
    (by change ι W.a₆ + (ι W.a₃)^2/4 = _; dsimp only [Function.comp_apply]; linear_combination hcF) heq hn hd

end ArbitrarySplitFiberBasis

open ArithmeticThetaRelativeFourCharacterR0211

/-- Actual full-four coordinates over an arbitrary rational base give the unique
completed-square marking, a full basis with the specified doubled labels,
on every characteristic-zero field-valued point. -/
theorem arbitrary_split_fiber_basis :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), (∃ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y) ∧ (∀ (e : Fin 3 → R) (x y : Fin 2 → R), ArithmeticThetaRelativeFourCharacterR0211.Coordinates R W G M e x y → ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F),  Function.Injective (ι ∘ e) ∧ (∃! b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b) ∧ (∀ b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e), ArithmeticThetaRelativeFourCharacterR0211.FiberCoordinates R W e x y F ι b → ArithmeticThetaMarkingR0115.IsBasis F (ι ∘ e) b ∧ ArithmeticThetaMarkingR0115.labels F (ι ∘ e) b = ι ∘ e)) := by
  intro R _ _ W _ G hG M
  refine ⟨ArbitrarySplitFiberBasis.coordinates_exists W G hG M, ?_⟩
  intro e x y hC F _ _ _ ι
  have he := ArbitrarySplitFiberBasis.fiber_roots W hC.2.1 F ι
  have hh := ArbitrarySplitFiberBasis.fiber_half W G hG M e x y hC F ι
  choose h hs using hh
  let b : ArithmeticThetaMarkingR0115.Marking F (ι ∘ e) :=
    fun i => WeierstrassCurve.Affine.Point.some (ι (x i))
      (ι (ArithmeticThetaGlobalFourTorsionR0190.completedY R W (x i) (y i))) (h i)
  have hb : FiberCoordinates R W e x y F ι b := by
    intro i
    exact ⟨WeierstrassCurve.Affine.Point.some_ne_zero _, rfl, rfl⟩
  refine ⟨he, ⟨b, hb, ?_⟩, ?_⟩
  · intro c hc
    exact ArbitrarySplitFiberBasis.fiber_unique W F ι c b hc hb
  · intro c hc
    have hcb := ArbitrarySplitFiberBasis.fiber_unique W F ι c b hc hb
    subst c
    exact RelativeSplitFiberBasis.halves_basis (ι ∘ e) he b hs


#print axioms arbitrary_split_fiber_basis
end ArithmeticThetaArbitraryFourCharacterR0214
