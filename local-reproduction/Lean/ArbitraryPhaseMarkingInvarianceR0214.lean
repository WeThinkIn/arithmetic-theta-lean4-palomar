import ArbitraryGeometricPhaseR0214
import RelativePhaseMarkingInvarianceR0211

/-! Determinant-one invariance over arbitrary rational rings. Field comparison
is upgraded to exact equality by the square identity and a unit sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryPhaseMarkingInvariance
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190 ArithmeticThetaRelativeFourCharacterR0211
open ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance
open WeierstrassCurve.Affine WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)

lemma completed_curve (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y : Fin 2 → R) (hC : Coordinates R W G M e x y)
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (ι : R →+* F) :
    completeChange (W.map ι) • W.map ι = ArithmeticThetaMillerR0114.Curve F (ι ∘ e) := by
  obtain ⟨ha, hb, hc⟩ := ArbitrarySplitFiberBasis.coefficients W G M hC.1 hC.2.1
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

omit W G hG in
lemma evaluation_from_domain {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    (U : WeierstrassCurve T) [U.IsElliptic] (H : Law T U)
    (hH : ∀ {S : Scheme.{u}} (s : S ⟶ Base T),
      (H.one s).val = s ≫ (kwZeroSect T U).val)
    (c : T →+* R) (G : Law R (U.map c)) (hG : IsOriginLaw R (U.map c) G)
    (F : Type u) [Field F] [DecidableEq F] (ι : R →+* F) :
    ∃ ev : SchemeHomOver (𝟙 (Base R)) (structureMap R (U.map c)) →
        ((U.map c).map ι).toAffine.Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      (∀ n P, ev (G.nsmul (𝟙 _) n P) = n • ev P) ∧
      ∀ P x y, HasCoordinates R (U.map c) P.val x y →
        ∃ h, ev P = Point.some (ι x) (ι y) h := by
  classical
  obtain ⟨φ, hφ, hcoef⟩ := exists_isCoefficientHom U.toProjective c
  have hcart := isPullback_projMap_of_isCoefficientHom U.toProjective c φ hφ hcoef
  obtain ⟨G', hmul, hone⟩ := RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback c
    (projModelStrCR U.toProjective) (projModelStrCR (U.toProjective.map c))
    (Proj.map φ hφ) hcart H
  have hone' := fun {S : Scheme.{u}} (s : S ⟶ Base R) =>
    one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback U.toProjective c φ hφ hcoef hcart
      H G' (fun t => hH t) (fun t => hone t) s
  have he : (G.one (𝟙 (Base R))).val = (G'.one (𝟙 (Base R))).val := by
    rw [hG.1, hone']
    rfl
  let push (P : SchemeHomOver (𝟙 (Base R)) (structureMap R (U.map c))) :
      SchemeHomOver ((𝟙 (Base R)) ≫ Spec.map (CommRingCat.ofHom c)) (structureMap _ U) :=
    ⟨P.val ≫ Proj.map φ hφ, by
      change (P.val ≫ Proj.map φ hφ) ≫ projModelStrCR U.toProjective = _
      rw [Category.assoc, hcart.w, ← Category.assoc]
      exact congrArg (· ≫ Spec.map (CommRingCat.ofHom c)) P.property⟩
  have hpush (P Q) : push (G.mul (𝟙 _) P Q) = H.mul _ (push P) (push Q) := by
    apply Subtype.ext
    change (G.mul (𝟙 _) P Q).val ≫ Proj.map φ hφ = _
    rw [RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (U.toProjective.map c) G G' he]
    exact hmul (𝟙 _) P Q
  letI : Algebra T F := (ι.comp c).toAlgebra
  let f := Spec.map (CommRingCat.ofHom ι)
  have hf : f ≫ ((𝟙 (Base R)) ≫ Spec.map (CommRingCat.ofHom c)) =
      Spec.map (CommRingCat.ofHom (algebraMap _ F)) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom c) (CommRingCat.ofHom ι)).symm
  obtain ⟨E, hE, _, hcoords⟩ :=
    ArithmeticThetaMarkedGroupLawR0146.ProjectivePointsEvaluation.coordinateEvaluationExists U H
      (by simpa using hH (𝟙 _))
  let ev := fun P => E F (schemeHomOverComp f hf (push P))
  have hmul' (P Q) : ev (G.mul (𝟙 _) P Q) = ev P + ev Q := by
    dsimp [ev]
    rw [hpush, H.mul_natural, hE.1]
  have hzero : ev (G.one (𝟙 _)) = 0 := by
    have hh := hmul' (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at hh
    exact add_left_cancel (show ev (G.one (𝟙 _)) + ev (G.one (𝟙 _)) =
      ev (G.one (𝟙 _)) + 0 by simpa using hh.symm)
  refine ⟨ev, hmul', ?_, ?_⟩
  · intro n P
    induction n with
    | zero => simpa only [G.nsmul_zero, zero_nsmul] using hzero
    | succ n ih => rw [G.nsmul_succ, hmul', ih, succ_nsmul, add_comm]
  · intro P x y hp
    obtain ⟨θ, hθ, hxθ, hyθ⟩ := exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
      U.toProjective c φ hφ hcoef
    obtain ⟨_, χ, hχ, hx, hy⟩ := hp
    have hfac : (push P).val = Spec.map (CommRingCat.ofHom (χ.comp θ)) ≫ chartInclusion _ U := by
      change P.val ≫ Proj.map φ hφ = _
      rw [hχ, Category.assoc]
      change Spec.map (CommRingCat.ofHom χ) ≫ (zChartι (U.toProjective.map c) ≫ Proj.map φ hφ) = _
      rw [hθ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hfacF : (schemeHomOverComp f hf (push P)).val =
        Spec.map (CommRingCat.ofHom (ι.comp (χ.comp θ))) ≫ chartInclusion _ U := by
      change f ≫ (push P).val = _
      rw [hfac]
      simp only [f, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    obtain ⟨h, hh⟩ := hcoords F _ (ι.comp (χ.comp θ)) hfacF
    simp only [RingHom.comp_apply, hxθ, hyθ, hx, hy] at h hh
    exact ⟨h, hh⟩

include hG in
lemma evaluation_exists (F : Type u) [Field F] [DecidableEq F] (ι : R →+* F) :
    ∃ ev : SchemeHomOver (𝟙 (Base R)) (structureMap R W) → (W.map ι).toAffine.Point,
      (∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q) ∧
      (∀ n P, ev (G.nsmul (𝟙 _) n P) = n • ev P) ∧
      ∀ P x y, HasCoordinates R W P.val x y →
        ∃ h, ev P = Point.some (ι x) (ι y) h := by
  classical
  obtain ⟨c, hc⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_universal_map W
  subst W
  let U := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.SmoothUniversalCurve.{u}
  obtain ⟨H, hH⟩ := ArithmeticThetaArbitraryAffineR0202.ArbitraryTwoCoordinates.exists_origin_law U
  exact evaluation_from_domain U H (fun t => hH t) c G hG F ι

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
  obtain ⟨he, _, hB⟩ := (arbitrary_split_fiber_basis R W G hG M).2 e x y hC F ι
  have hbas := (hB b hb).1
  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character F (ι ∘ e) he
  refine ⟨?_, ι ∘ e, he, hV, hbas⟩
  calc
    ι z = ArithmeticThetaGeometricPairingR0118.pairing F (ι ∘ e) D (b 0) (b 1) :=
      hz.2 e x y hC F ι b hb D
    _ = ArithmeticThetaMarkingR0115.phase F (ι ∘ e) b :=
      ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F (ι ∘ e) he D b hbas
    _ = phaseOn _ a := (phaseOn_split (ι ∘ e) b).symm.trans (phaseOn_cast hV a)

include hG in
lemma field_invariance (M M' : FullLevel R W G 4 (𝟙 (Base R)))
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : A.det = 1)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z z' : R) (hz : GeometricPhase R W G M z) (hz' : GeometricPhase R W G M' z')
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (f : R →+* F) : f z' = f z := by
  classical
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
  rw [heq', heq]
  calc
    phaseOn V a' = phaseOn _ (castPoint hV ∘ a') := (phaseOn_cast hV a').symm
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a') := phaseOn_split e _
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a) := by rw [hact]; exact hinv
    _ = phaseOn V a := (phaseOn_split e _).symm.trans (phaseOn_cast hV a)

end ArbitraryPhaseMarkingInvariance

open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaRelativeFourCharacterR0211

/-- The actual normalized Miller phase is unchanged by every determinant-one
change of full-four marking, including over nonreduced and zero rings. -/
theorem arbitrary_phase_marking_invariance :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ (M M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (A : ArithmeticThetaFourTorsion.Mat4), A.det = 1 → ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M M' A → ∀ z z' : R, ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z → ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M' z' → z' = z := by
  intro R _ _ W _ G hG M M' A hA hchange z z' hz hz'
  classical
  obtain ⟨hgeom, hunit, hs, _⟩ := (arbitrary_geometric_phase R W G hG M).2 z hz
  obtain ⟨hgeom', _, hs', _⟩ := (arbitrary_geometric_phase R W G hG M').2 z' hz'
  have hsum : IsUnit (z'+z) := by
    by_contra hu
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {z'+z}) (fun h => hu (Ideal.span_singleton_eq_top.mp h))
    letI : I.IsMaximal := hI
    letI := Ideal.Quotient.field I
    let f : R →+* R ⧸ I := Ideal.Quotient.mk I
    letI : Algebra ℚ (R ⧸ I) := (f.comp (algebraMap ℚ R)).toAlgebra
    letI : CharZero (R ⧸ I) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (R ⧸ I)).injective
    have heq := ArbitraryPhaseMarkingInvariance.field_invariance W G hG M M' A hA
      hchange z z' hgeom hgeom' (R ⧸ I) f
    have hn : f (z'+z) ≠ 0 := by
      rw [map_add, heq, ← two_mul]
      exact mul_ne_zero (by norm_num) ((hunit.map f).ne_zero)
    apply hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hle (Ideal.subset_span (Set.mem_singleton _)))
  apply hsum.mul_right_cancel
  linear_combination hs' - hs

#print axioms arbitrary_phase_marking_invariance
end ArithmeticThetaArbitraryFourCharacterR0214
