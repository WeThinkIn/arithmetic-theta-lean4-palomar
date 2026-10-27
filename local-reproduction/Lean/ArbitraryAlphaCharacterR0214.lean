import ArbitraryAlphaNaturalityR0214
import ArbitraryPhaseMarkingInvarianceR0214
import RelativeAlphaCharacterR0211

/-! The exact character over arbitrary rational algebras. Square identities
control nilpotents; field comparisons select the sign by a unit-sum argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option maxRecDepth 100000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryAlphaCharacter
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190 ArithmeticThetaRelativeFourCharacterR0211
open ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance
open ArithmeticThetaRelativeFourCharacterR0211.RelativeAlphaCharacter
open WeierstrassCurve.Affine
open ArithmeticThetaFourTorsion

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)

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

lemma field_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R)))
    (A : ArithmeticThetaFourTorsion.Mat4) (hA : ArithmeticThetaFourTorsion.PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : GeometricPhase R W G M z)
    (e e' : Fin 3 → R) (x y g x' y' g' : R)
    (hg : RootData R W G 4 M e x y g) (hg' : RootData R W G 4 M' e' x' y' g') :
    ∀ (F : Type u) [Field F] [CharZero F] [DecidableEq F] (f : R →+* F),
    f g' = f (z ^ (ArithmeticThetaFourTorsion.characterExponent A).val * g) := by
  classical
  intro F _ _ _ f
  obtain ⟨ev, hm, hn, hc⟩ := ArbitraryPhaseMarkingInvariance.evaluation_exists W G hG F f
  let V := completeChange (W.map f) • W.map f
  let b := fun i : Fin 2 => completeMap (W.map f) (ev (![M.x, M.y] i))
  let b' := fun i : Fin 2 => completeMap (W.map f) (ev (![M'.x, M'.y] i))
  obtain ⟨hzF, es, hes, hV, hB⟩ := ArbitraryPhaseMarkingInvariance.phase_comparison W G hG F f ev hc M z hz
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
  rw [map_mul, map_pow, hgF', hgF]
  calc
    rootOn V b' = ArithmeticThetaMarkingR0115.root F es (castPoint hV ∘ b') :=
      (rootOn_cast hV b').symm.trans (rootOn_split es _)
    _ = (f z) ^ (ArithmeticThetaFourTorsion.characterExponent A).val *
        ArithmeticThetaMarkingR0115.root F es (castPoint hV ∘ b) := by
      rw [hact, ArithmeticThetaMarkingR0115.full_marking_character F es hes _ hB A hA, hphase]
    _ = (f z) ^ (ArithmeticThetaFourTorsion.characterExponent A).val * rootOn V b := by
      rw [← rootOn_split, rootOn_cast]


omit W G in
lemma even_residues : ∀ A : Mat4, PreservesEven A →
    ((A 0 0).val * 2 % 4 = 2 ∧ (A 1 0).val * 2 % 4 = 0 ∧
      (A 0 1).val * 2 % 4 = 0 ∧ (A 1 1).val * 2 % 4 = 2 ∧
      (characterExponent A).val * 2 % 4 = 0) ∨
    ((A 0 0).val * 2 % 4 = 0 ∧ (A 1 0).val * 2 % 4 = 2 ∧
      (A 0 1).val * 2 % 4 = 2 ∧ (A 1 1).val * 2 % 4 = 0 ∧
      (characterExponent A).val * 2 % 4 = 2) := by
  decide

omit W G in
lemma pow_mod_four {H : Type*} [Monoid H] (x : H) (hx : x^4 = 1) (n : ℕ) :
    x^n = x^(n%4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hx, one_pow, mul_one]

/-- The actual doubled labels and character exponent have matching parity. -/
lemma square_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R))) (A : Mat4) (hA : PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : z^2 = -1)
    (e e' : Fin 3 → R) (x y g x' y' g' : R)
    (hg : RootData R W G 4 M e x y g) (hg' : RootData R W G 4 M' e' x' y' g') :
    g'^2 = (z^(characterExponent A).val * g)^2 := by
  letI : CommGroup (SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :=
    { G.pointGroup (𝟙 _) with mul_comm := hG.2 (𝟙 _) }
  have hx4 : M.x^4 = 1 :=
    (FullLevelTorsionSplittingR0175.nsmul_pow G _ 4 M.x).symm.trans M.killed_x
  have hy4 : M.y^4 = 1 :=
    (FullLevelTorsionSplittingR0175.nsmul_pow G _ 4 M.y).symm.trans M.killed_y
  have hcx : M'.x = M.x^(A 0 0).val * M.y^(A 1 0).val := by
    have h := hchange.1
    simp only [FullLevelTorsionSplittingR0175.nsmul_pow G] at h
    exact h
  have hcy : M'.y = M.x^(A 0 1).val * M.y^(A 1 1).val := by
    have h := hchange.2
    simp only [FullLevelTorsionSplittingR0175.nsmul_pow G] at h
    exact h
  have hdoubleX : M'.x^2 = M.x^((A 0 0).val*2%4) * M.y^((A 1 0).val*2%4) := by
    rw [hcx, mul_pow, ← pow_mul, ← pow_mul,
      pow_mod_four M.x hx4, pow_mod_four M.y hy4]
  have hdoubleY : M'.y^2 = M.x^((A 0 1).val*2%4) * M.y^((A 1 1).val*2%4) := by
    rw [hcy, mul_pow, ← pow_mul, ← pow_mul,
      pow_mod_four M.x hx4, pow_mod_four M.y hy4]
  have hz4 : z^4 = 1 := by calc
    z^4 = (z^2)^2 := by ring
    _ = 1 := by rw [hz]; ring
  have hzpow : (z^(characterExponent A).val)^2 = z^((characterExponent A).val*2%4) := by
    rw [← pow_mul, pow_mod_four z hz4]
  have hcoord (N : FullLevel R W G 4 (𝟙 (Base R)))
      (es : Fin 3 → R) (hs : Labels R W G 4 N es) :
      HasCoordinates R W (N.x^2).val (es 0)
        (-(algebraMap ℚ R (1/2)) * (W.a₁ * es 0 + W.a₃)) ∧
      HasCoordinates R W (N.y^2).val (es 1)
        (-(algebraMap ℚ R (1/2)) * (W.a₁ * es 1 + W.a₃)) := by
    have h0 := hs 0
    have h1 := hs 1
    change HasCoordinates R W (G.nsmul (𝟙 _) 2 N.x).val _ _ at h0
    change HasCoordinates R W (G.nsmul (𝟙 _) 2 N.y).val _ _ at h1
    rw [FullLevelTorsionSplittingR0175.nsmul_pow G] at h0 h1
    exact ⟨h0,h1⟩
  obtain ⟨hc0,hc1⟩ := hcoord M e hg.1
  obtain ⟨hc0',hc1'⟩ := hcoord M' e' hg'.1
  rcases even_residues A hA with ⟨h00,h10,h01,h11,hn⟩ | ⟨h00,h10,h01,h11,hn⟩
  · rw [h00,h10,pow_zero,mul_one] at hdoubleX
    rw [h01,h11,pow_zero,one_mul] at hdoubleY
    rw [hdoubleX] at hc0'
    rw [hdoubleY] at hc1'
    have he0 := (ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinates_unique W hc0' hc0).1
    have he1 := (ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinates_unique W hc1' hc1).1
    rw [mul_pow, hzpow, hn, pow_zero, one_mul, hg'.2.2.2.2.2.2, hg.2.2.2.2.2.2, he0, he1]
  · rw [h00,h10,pow_zero,one_mul] at hdoubleX
    rw [h01,h11,pow_zero,mul_one] at hdoubleY
    rw [hdoubleX] at hc0'
    rw [hdoubleY] at hc1'
    have he0 := (ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinates_unique W hc0' hc1).1
    have he1 := (ArithmeticThetaGlobalFourTorsionR0190.RelativeAlphaNaturality.coordinates_unique W hc1' hc0).1
    rw [mul_pow, hzpow, hn, hz, hg'.2.2.2.2.2.2, hg.2.2.2.2.2.2, he0, he1]
    ring

/-- Field comparison selects the sign of the exact square identity. The sum
is a unit at every maximal ideal, so cancellation is valid even with nilpotents. -/
lemma coefficient_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R))) (A : Mat4) (hA : PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : MillerPhase R W G M z)
    (e e' : Fin 3 → R) (x y g x' y' g' : R)
    (hg : RootData R W G 4 M e x y g) (hg' : RootData R W G 4 M' e' x' y' g') :
    g' = z^(characterExponent A).val * g := by
  classical
  obtain ⟨hgeom, hunit, hs, _⟩ := (arbitrary_geometric_phase R W G hG M).2 z hz
  have hsq := square_character W G hG M M' A hA hchange z hs e e' x y g x' y' g' hg hg'
  have hsum : IsUnit (g' + z^(characterExponent A).val * g) := by
    by_contra hu
    obtain ⟨I,hI,hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {g' + z^(characterExponent A).val * g})
      (fun h => hu (Ideal.span_singleton_eq_top.mp h))
    letI : I.IsMaximal := hI
    letI := Ideal.Quotient.field I
    let f : R →+* R ⧸ I := Ideal.Quotient.mk I
    letI : Algebra ℚ (R ⧸ I) := (f.comp (algebraMap ℚ R)).toAlgebra
    letI : CharZero (R ⧸ I) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (R ⧸ I)).injective
    have heq := field_character W G hG M M' A hA hchange z hgeom
      e e' x y g x' y' g' hg hg' (R ⧸ I) f
    have hn : f (g' + z^(characterExponent A).val * g) ≠ 0 := by
      rw [map_add, heq, ← two_mul]
      exact mul_ne_zero (by norm_num)
        ((((hunit.pow _).mul hg.2.2.2.2.1).map f).ne_zero)
    apply hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hle (Ideal.subset_span (Set.mem_singleton _)))
  apply hsum.mul_right_cancel
  linear_combination hsq

/-- The normalized frame is independent of the marking, so its scalar
coefficient transforms by the exact character. -/
lemma section_character (hG : IsOriginLaw R W G)
    (M M' : FullLevel R W G 4 (𝟙 (Base R))) (A : Mat4) (hA : PreservesEven A)
    (hchange : Changes R W G (𝟙 (Base R)) M M' A)
    (z : R) (hz : MillerPhase R W G M z)
    (a a' : Γ(Hodge R W,⊤))
    (ha : RealizesAlpha R W G 4 M a) (ha' : RealizesAlpha R W G 4 M' a') :
    a' = ArithmeticThetaOpenHodgeR0180.scalar R (z^(characterExponent A).val) • a := by
  obtain ⟨e,x,y,g,δ,hg,hδ,rfl⟩ := ha
  obtain ⟨e',x',y',g',δ',hg',hδ',rfl⟩ := ha'
  have he := coefficient_character W G hG M M' A hA hchange z hz
    e e' x y g x' y' g' hg hg'
  rw [arbitrary_normalized_frame_uniqueness R W δ δ' hδ hδ', he, smul_smul]
  have hscalar (r s : R) : ArithmeticThetaOpenHodgeR0180.scalar R (r*s) =
      ArithmeticThetaOpenHodgeR0180.scalar R r * ArithmeticThetaOpenHodgeR0180.scalar R s :=
    map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r s
  rw [show 2 * (z^(characterExponent A).val*g) =
      z^(characterExponent A).val*(2*g) by ring, hscalar]

end ArbitraryAlphaCharacter

/-- The full even-stabilizer character on the actual intrinsic Hodge sections
of an arbitrary rational base, including nonreduced and empty bases. -/
theorem arbitrary_alpha_character :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ∃ z : R, ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z ∧ ArithmeticThetaRelativeFourCharacterR0211.GeometricPhase R W G M z ∧ IsUnit z ∧ z^2 = -1 ∧ (Nontrivial R → IsPrimitiveRoot z 4) ∧ (∀ A : ArithmeticThetaFourTorsion.Mat4, ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M M' A ∧ ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M' z ∧ (∀ a a' : (ArithmeticThetaRelativeDiscriminantR0171.Hodge R W).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 M a → ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 M' a' → a' = ArithmeticThetaOpenHodgeR0180.scalar R (z ^ (ArithmeticThetaFourTorsion.characterExponent A).val) • a)) := by
  intro R _ _ W _ G hG M
  obtain ⟨z,hz,_⟩ := (arbitrary_geometric_phase R W G hG M).1
  obtain ⟨hgeom,hu,hs,hprim⟩ := (arbitrary_geometric_phase R W G hG M).2 z hz
  refine ⟨z,hz,hgeom,hu,hs,hprim,?_⟩
  intro A hA
  obtain ⟨M',hc,_⟩ :=
    (ArithmeticThetaRelativeFourCharacterR0211.relative_marking_action R W G hG _
      (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))).1
      M A hA.1
  obtain ⟨z',hz',_⟩ := (arbitrary_geometric_phase R W G hG M').1
  have heq := arbitrary_phase_marking_invariance R W G hG M M' A hA.1 hc z z' hz hz'
  refine ⟨M',hc,heq ▸ hz',?_⟩
  exact ArbitraryAlphaCharacter.section_character W G hG M M' A hA hc z hz

#print axioms ArbitraryAlphaCharacter.field_character
#print axioms ArbitraryAlphaCharacter.even_residues
#print axioms ArbitraryAlphaCharacter.square_character
#print axioms ArbitraryAlphaCharacter.coefficient_character
#print axioms ArbitraryAlphaCharacter.section_character
#print axioms arbitrary_alpha_character
end ArithmeticThetaArbitraryFourCharacterR0214
