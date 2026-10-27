import RelativePhaseMarkingInvarianceR0211

/-! The field character acts on the coefficient of the same normalized relative
differential. The generic fiber detects coefficient equality in the base ring. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
noncomputable section
universe u
namespace ArithmeticThetaRelativeFourCharacterR0211
namespace RelativeAlphaCharacter
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open RelativePhaseMarkingInvariance
open WeierstrassCurve.Affine

section Field
variable {F : Type u} [Field F] [CharZero F] [DecidableEq F]

def rootOn (V : WeierstrassCurve F) (b : Fin 2 → V.toAffine.Point) : F :=
  ArithmeticThetaFourTorsion.rootExpression
    (px V (2 • b 0)) (px V (2 • b 1)) (px V (2 • b 0 + 2 • b 1))
    (px V (b 1)) (py V (b 1))

lemma rootOn_split (e : Fin 3 → F) (b : ArithmeticThetaMarkingR0115.Marking F e) :
    rootOn (ArithmeticThetaMarkingR0115.Curve F e) b =
      ArithmeticThetaMarkingR0115.root F e b := by
  have hx (P : (ArithmeticThetaMarkingR0115.Curve F e).Point) :
      px _ P = ArithmeticThetaMarkingR0115.pointX F e P := by cases P <;> rfl
  have hy (P : (ArithmeticThetaMarkingR0115.Curve F e).Point) :
      py _ P = ArithmeticThetaMarkingR0115.pointY F e P := by cases P <;> rfl
  simp only [rootOn, hx, hy, ArithmeticThetaMarkingR0115.root,
    ArithmeticThetaMarkingR0115.labels, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]

lemma rootOn_cast {V V' : WeierstrassCurve F} (h : V = V')
    (b : Fin 2 → V.toAffine.Point) :
    rootOn V' (castPoint h ∘ b) = rootOn V b := by
  subst V'
  rfl

end Field

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
  (G : Law R W)

lemma complete_coordinates (F : Type u) [Field F] [CharZero F] [DecidableEq F]
    (ι : R →+* F)
    (ev : SchemeHomOver (𝟙 (Base R)) (structureMap R W) → (W.map ι).toAffine.Point)
    (hc : ∀ P x y, HasCoordinates R W P.val x y →
      ∃ h, ev P = Point.some (ι x) (ι y) h)
    (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W)) (x y : R)
    (hp : HasCoordinates R W P.val x y) :
    px (completeChange (W.map ι) • W.map ι) (completeMap (W.map ι) (ev P)) = ι x ∧
    py (completeChange (W.map ι) • W.map ι) (completeMap (W.map ι) (ev P)) =
      ι (completedY R W x y) := by
  obtain ⟨h, hh⟩ := hc P x y hp
  obtain ⟨h', hh'⟩ := completeMap_some (W.map ι) (ι x) (ι y) h
  rw [hh, hh']
  refine ⟨rfl, ?_⟩
  change ι y + (ι W.a₁ * ι x + ι W.a₃) / 2 = _
  have hrat (q : ℚ) : ι (algebraMap ℚ R q) = (q : F) :=
    map_ratCast (ι.comp (algebraMap ℚ R)) q
  simp only [completedY, map_add, map_mul, hrat]
  norm_num
  ring

/-- The original root data evaluates to the literal root on the completed
square curve, including the three actual doubled labels. -/
lemma root_comparison (F : Type u) [Field F] [CharZero F] [DecidableEq F]
    (ι : R →+* F)
    (ev : SchemeHomOver (𝟙 (Base R)) (structureMap R W) → (W.map ι).toAffine.Point)
    (hm : ∀ P Q, ev (G.mul (𝟙 _) P Q) = ev P + ev Q)
    (hn : ∀ n P, ev (G.nsmul (𝟙 _) n P) = n • ev P)
    (hc : ∀ P x y, HasCoordinates R W P.val x y →
      ∃ h, ev P = Point.some (ι x) (ι y) h)
    (M : FullLevel R W G 4 (𝟙 (Base R)))
    (e : Fin 3 → R) (x y g : R) (hg : RootData R W G 4 M e x y g) :
    ι g = rootOn (completeChange (W.map ι) • W.map ι)
      (fun i : Fin 2 => completeMap (W.map ι) (ev (![M.x, M.y] i))) := by
  let V := completeChange (W.map ι) • W.map ι
  let q := fun P => completeMap (W.map ι) (ev P)
  have hqmul P Q : q (G.mul (𝟙 _) P Q) = q P + q Q := by
    simp only [q, hm, map_add]
  have hqn n P : q (G.nsmul (𝟙 _) n P) = n • q P := by
    simp only [q, hn, map_nsmul]
  have he0 : px V (2 • q M.x) = ι (e 0) := by
    have hh := (complete_coordinates W F ι ev hc
      (G.nsmul (𝟙 _) 2 M.x) (e 0) _ (hg.1 0)).1
    simpa only [← hqn] using hh
  have he1 : px V (2 • q M.y) = ι (e 1) := by
    have hh := (complete_coordinates W F ι ev hc
      (G.nsmul (𝟙 _) 2 M.y) (e 1) _ (hg.1 1)).1
    simpa only [← hqn] using hh
  have he2 : px V (2 • q M.x + 2 • q M.y) = ι (e 2) := by
    have hh := (complete_coordinates W F ι ev hc
      (G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x) (G.nsmul (𝟙 _) 2 M.y))
      (e 2) _ (hg.1 2)).1
    change px V (q (G.mul (𝟙 _) (G.nsmul (𝟙 _) 2 M.x)
      (G.nsmul (𝟙 _) 2 M.y))) = _ at hh
    simpa only [hqmul, hqn] using hh
  have hxy := complete_coordinates W F ι ev hc
    (G.nsmul (𝟙 _) 1 M.y) x y hg.2.2.1
  change px V (q (G.nsmul (𝟙 _) 1 M.y)) = ι x ∧
    py V (q (G.nsmul (𝟙 _) 1 M.y)) = ι (completedY R W x y) at hxy
  simp only [hqn, one_nsmul] at hxy
  change ι g = ArithmeticThetaFourTorsion.rootExpression
    (px V (2 • q M.x)) (px V (2 • q M.y)) (px V (2 • q M.x + 2 • q M.y))
    (px V (q M.y)) (py V (q M.y))
  rw [he0, he1, he2, hxy.1, hxy.2]
  unfold ArithmeticThetaFourTorsion.rootExpression
  have hy0 : ι (completedY R W x y) ≠ 0 := (hg.2.2.2.1.map ι).ne_zero
  apply (eq_div_iff (mul_ne_zero (by norm_num) hy0)).mpr
  have hh := congrArg ι hg.2.2.2.2.2.1
  simp only [map_mul, map_ofNat, map_sub, map_pow] at hh
  simpa only [mul_comm] using hh

/-- Compare both coefficients on one and the same generic-fiber presentation.
The actual section action gives the right action after evaluation. -/
lemma coefficient_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R)))
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : ArithmeticThetaFourTorsion.PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : GeometricPhase R W G M z)
    (e e' : Fin 3 → R) (x y g x' y' g' : R)
    (hg : RootData R W G 4 M e x y g) (hg' : RootData R W G 4 M' e' x' y' g') :
    g' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val * g := by
  classical
  let F := FractionRing R
  let f : R →+* F := algebraMap R F
  have hf : Function.Injective f := IsFractionRing.injective R F
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  let : CharZero F := charZero_of_injective_algebraMap hf
  obtain ⟨ev, hm, hn, hc⟩ := evaluation_exists W G hG F f
  let V := completeChange (W.map f) • W.map f
  let b := fun i : Fin 2 => completeMap (W.map f) (ev (![M.x, M.y] i))
  let b' := fun i : Fin 2 => completeMap (W.map f) (ev (![M'.x, M'.y] i))
  obtain ⟨hzF, es, hes, hV, hB⟩ := phase_comparison W G hG F f ev hc M z hz
  change f z = phaseOn V b at hzF
  change ArithmeticThetaMarkingR0115.IsBasis F es (castPoint hV ∘ b) at hB
  have hact : castPoint hV ∘ b' =
      ArithmeticThetaMarkingR0115.act F es (castPoint hV ∘ b) A := by
    funext i
    fin_cases i
    · change castPoint hV (completeMap (W.map f) (ev M'.x)) = _
      rw [hchange.1]
      simp only [hm, hn, map_add, map_nsmul]
      rfl
    · change castPoint hV (completeMap (W.map f) (ev M'.y)) = _
      rw [hchange.2]
      simp only [hm, hn, map_add, map_nsmul]
      rfl
  have hgF : f g = rootOn V b := root_comparison W G F f ev hm hn hc M e x y g hg
  have hgF' : f g' = rootOn V b' := root_comparison W G F f ev hm hn hc M' e' x' y' g' hg'
  have hphase : ArithmeticThetaMarkingR0115.phase F es (castPoint hV ∘ b) = f z :=
    (phaseOn_split es _).symm.trans ((phaseOn_cast hV b).trans hzF.symm)
  apply hf
  rw [map_mul, map_pow, hgF', hgF]
  calc
    rootOn V b' = ArithmeticThetaMarkingR0115.root F es (castPoint hV ∘ b') :=
      (rootOn_cast hV b').symm.trans (rootOn_split es _)
    _ = (f z) ^ (ArithmeticThetaFourTorsion.characterExponent A).val *
        ArithmeticThetaMarkingR0115.root F es (castPoint hV ∘ b) := by
      rw [hact, ArithmeticThetaMarkingR0115.full_marking_character F es hes _ hB A hA, hphase]
    _ = (f z) ^ (ArithmeticThetaFourTorsion.characterExponent A).val * rootOn V b := by
      rw [← rootOn_split, rootOn_cast]

/-- Use the accepted intrinsic section provider, identify normalized frames,
and apply the coefficient equation via the actual structural scalar map. -/
lemma section_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R)))
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : ArithmeticThetaFourTorsion.PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : GeometricPhase R W G M z)
    (a a' : Γ(Hodge R W, ⊤))
    (ha : RealizesAlpha R W G 4 M a) (ha' : RealizesAlpha R W G 4 M' a') :
    a' = ArithmeticThetaOpenHodgeR0180.scalar R
      (z ^ (ArithmeticThetaFourTorsion.characterExponent A).val) • a := by
  obtain ⟨a₀, ha₀, _⟩ := (relative_alpha_naturality R W G hG 4 (by decide) (dvd_refl 4) M).1
  obtain ⟨a₁, ha₁, _⟩ := (relative_alpha_naturality R W G hG 4 (by decide) (dvd_refl 4) M').1
  rw [RelativeAlphaNaturality.realizes_unique R W G 4 M ha ha₀.1,
    RelativeAlphaNaturality.realizes_unique R W G 4 M' ha' ha₁.1]
  obtain ⟨e, x, y, g, δ, hg, hδ, heq⟩ := ha₀.1
  obtain ⟨e', x', y', g', δ', hg', hδ', heq'⟩ := ha₁.1
  have hgcoef := coefficient_character W G hG M M' A hA hchange z hz e e' x y g x' y' g' hg hg'
  rw [heq, heq', RelativeNormalizedDifferential.normalized_frames_equal R W δ δ' hδ hδ',
    hgcoef, smul_smul]
  have hscalar (r s : R) : ArithmeticThetaOpenHodgeR0180.scalar R (r*s) =
      ArithmeticThetaOpenHodgeR0180.scalar R r * ArithmeticThetaOpenHodgeR0180.scalar R s :=
    map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r s
  rw [show 2 * (z ^ (ArithmeticThetaFourTorsion.characterExponent A).val * g) =
    z ^ (ArithmeticThetaFourTorsion.characterExponent A).val * (2*g) by ring, hscalar]

end RelativeAlphaCharacter
/-- The full character on the actual intrinsic relative Hodge section. -/
theorem relative_alpha_character :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∃ z : R, ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z ∧ IsUnit z ∧ IsPrimitiveRoot z 4 ∧ (∀ A : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M M' A ∧ ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M' z ∧ (∀ a a' : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 M a → ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 M' a' → a' = ArithmeticThetaOpenHodgeR0180.scalar R (z ^ (ArithmeticThetaFourTorsion.characterExponent A).val) • a)) := by
  intro R _ _ _ _ _ W _ G hG M
  obtain ⟨z, hz, _⟩ := relative_geometric_phase R W G hG M
  refine ⟨z, hz.1, hz.2.1, hz.2.2, ?_⟩
  intro A hA
  obtain ⟨M', hchange, _⟩ := (relative_marking_action R W G hG _
    (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))).1 M A hA.1
  obtain ⟨z', hz', _⟩ := relative_geometric_phase R W G hG M'
  have heq := relative_phase_marking_invariance R W G hG M M' A hA.1 hchange z z' hz.1 hz'.1
  have hzM' : GeometricPhase R W G M' z := heq ▸ hz'.1
  exact ⟨M', hchange, hzM', RelativeAlphaCharacter.section_character W G hG M M' A hA hchange z hz.1⟩

#print axioms RelativeAlphaCharacter.root_comparison
#print axioms RelativeAlphaCharacter.coefficient_character
#print axioms RelativeAlphaCharacter.section_character
#print axioms relative_alpha_character

end ArithmeticThetaRelativeFourCharacterR0211
