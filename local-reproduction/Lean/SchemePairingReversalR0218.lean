import PhaseSwitchDefinitionsR0218

/-! Reversal of the first actual four-torsion section. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
universe u
namespace ArithmeticThetaPhaseSwitchR0218
namespace SchemePairingReversal
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaSchemeFourCharacterR0215.SchemeFourMarkingActionR0215
open ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211
open ArithmeticThetaFourTorsion

lemma reversal_sq : reversal * reversal = 1 := by decide +kernel

lemma reversal_nonzero (z : Fin 2 → ZMod 4) (hz : z ≠ 0) :
    reversal.mulVec z ≠ 0 := by
  intro h
  have he := congrArg (fun v => reversal.mulVec v) h
  rw [Matrix.mulVec_mulVec, reversal_sq, Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact hz he

variable {S : Scheme.{u}} (E : Family S)

lemma scheme_exists (M : FullLevel E 4) : ∃! N : FullLevel E 4,
    Changes E M N reversal := by
  letI := pointGroup E (𝟙 S)
  let basis (M : FullLevel E 4) : Fin 2 → SchemeHomOver (𝟙 S) E.p :=
    ![M.x, M.y]
  have killed (M : FullLevel E 4) : ∀ i, basis M i ^ 4 = 1 := by
    intro i
    fin_cases i
    · exact (multiple_pow E (𝟙 S) 4 M.x).symm.trans M.killed_x
    · exact (multiple_pow E (𝟙 S) 4 M.y).symm.trans M.killed_y
  let b := basis M
  let b' := act b reversal
  have hb := killed M
  have hb' := act_killed b hb reversal
  have hav : ∀ i j : Fin 4, i.val ≠ 0 ∨ j.val ≠ 0 →
      Disjoint (Set.range (E.law.mul (𝟙 S) (multiple E (𝟙 S) i.val (b' 0))
        (multiple E (𝟙 S) j.val (b' 1))).val) (Set.range (E.zero)) := by
    intro i j hij
    let z : Fin 2 → ZMod 4 := ![i, j]
    have hz : z ≠ 0 := by
      intro h
      rcases hij with hi | hj
      · exact hi (congrArg ZMod.val (congrFun h 0))
      · exact hj (congrArg ZMod.val (congrFun h 1))
    have hn := reversal_nonzero z hz
    let a : Fin 4 := ⟨(reversal.mulVec z 0).val, ZMod.val_lt _⟩
    let c : Fin 4 := ⟨(reversal.mulVec z 1).val, ZMod.val_lt _⟩
    have hac : a.val ≠ 0 ∨ c.val ≠ 0 := by
      by_contra h
      push Not at h
      apply hn
      funext k
      fin_cases k
      · exact (ZMod.val_eq_zero _).mp h.1
      · exact (ZMod.val_eq_zero _).mp h.2
    have he : E.law.mul (𝟙 S) (multiple E (𝟙 S) i.val (b' 0)) (multiple E (𝟙 S) j.val (b' 1)) =
        E.law.mul (𝟙 S) (multiple E (𝟙 S) a.val M.x) (multiple E (𝟙 S) c.val M.y) := by
      simp only [multiple_pow E]
      exact coord_act b hb reversal z
    rw [he]
    exact M.avoids a c hac
  let N : FullLevel E 4 :=
    { x := b' 0
      y := b' 1
      killed_x := (multiple_pow E (𝟙 S) 4 (b' 0)).trans (hb' 0)
      killed_y := (multiple_pow E (𝟙 S) 4 (b' 1)).trans (hb' 1)
      avoids := hav }
  have hN : Changes E M N reversal := by
    simp only [Changes, multiple_pow E]
    exact ⟨rfl, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro N' hN'
  exact fullLevel_ext E N' N (hN'.1.trans hN.1.symm) (hN'.2.trans hN.2.symm)

lemma scheme_points (M N : FullLevel E 4) (h : Changes E M N reversal) :
    N.x = multiple E (𝟙 S) 3 M.x ∧ N.y = M.y := by
  letI := pointGroup E (𝟙 S)
  simp only [Changes, multiple_pow E] at h
  change N.x = M.x^3 * M.y^0 ∧ N.y = M.x^0 * M.y^1 at h
  simpa only [pow_zero, pow_one, one_mul, mul_one, multiple_pow E] using h

lemma pow_three_twice {H : Type*} [Group H] (x : H) (h : x^4 = 1) :
    (x^3)^2 = x^2 := by
  rw [← pow_mul]
  exact (ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175.pow_residue
    x 4 6 h).symm

lemma pow_three_thrice {H : Type*} [Group H] (x : H) (h : x^4 = 1) :
    (x^3)^3 = x := by
  rw [← pow_mul]
  simpa using (ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175.pow_residue
    x 4 9 h).symm

lemma scheme_involution (M N : FullLevel E 4) (h : Changes E M N reversal) :
    Changes E N M reversal := by
  letI := pointGroup E (𝟙 S)
  obtain ⟨hx, hy⟩ := scheme_points E M N h
  have hx4 : M.x^4 = 1 := (multiple_pow E _ 4 M.x).symm.trans M.killed_x
  simp only [multiple_pow E] at hx
  simp only [Changes, multiple_pow E]
  change M.x = N.x^3 * N.y^0 ∧ M.y = N.x^0 * N.y^1
  simp [hx, hy, pow_three_thrice _ hx4]

lemma scheme_even (M N : FullLevel E 4) (h : Changes E M N reversal) :
    ArithmeticThetaUniversalEvaluationR0213.evenPoint E N =
      ArithmeticThetaUniversalEvaluationR0213.evenPoint E M := by
  letI := pointGroup E (𝟙 S)
  obtain ⟨hx, hy⟩ := scheme_points E M N h
  have hx4 : M.x^4 = 1 := (multiple_pow E _ 4 M.x).symm.trans M.killed_x
  simp only [multiple_pow E] at hx
  simp [ArithmeticThetaUniversalEvaluationR0213.evenPoint, multiple_pow E,
    hx, hy, pow_three_twice _ hx4]

section Relative
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaFullLevelCoverR0175.FullLevelTorsionSplittingR0175
open ArithmeticThetaRelativeFourCharacterR0211
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (G : Law R W)
  (hG : IsOriginLaw R W G)
include hG in
lemma relative_exists (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4
    (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))) :
    ∃! N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)),
      ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M N reversal := by
  letI : CommGroup (SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (structureMap R W)) :=
    { G.pointGroup (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) with mul_comm := hG.2 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) }
  let basis (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))) : Fin 2 → SchemeHomOver (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (structureMap R W) :=
    ![M.x, M.y]
  have killed (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))) : ∀ i, basis M i ^ 4 = 1 := by
    intro i
    fin_cases i
    · exact (nsmul_pow G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) 4 M.x).symm.trans M.killed_x
    · exact (nsmul_pow G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) 4 M.y).symm.trans M.killed_y
  let b := basis M
  let b' := act b reversal
  have hb := killed M
  have hb' := act_killed b hb reversal
  have hav : ∀ i j : Fin 4, i.val ≠ 0 ∨ j.val ≠ 0 →
      Disjoint (Set.range (G.mul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) i.val (b' 0))
        (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) j.val (b' 1))).val) (Set.range (origin R W)) := by
    intro i j hij
    let z : Fin 2 → ZMod 4 := ![i, j]
    have hz : z ≠ 0 := by
      intro h
      rcases hij with hi | hj
      · exact hi (congrArg ZMod.val (congrFun h 0))
      · exact hj (congrArg ZMod.val (congrFun h 1))
    have hn := reversal_nonzero z hz
    let a : Fin 4 := ⟨(reversal.mulVec z 0).val, ZMod.val_lt _⟩
    let c : Fin 4 := ⟨(reversal.mulVec z 1).val, ZMod.val_lt _⟩
    have hac : a.val ≠ 0 ∨ c.val ≠ 0 := by
      by_contra h
      push Not at h
      apply hn
      funext k
      fin_cases k
      · exact (ZMod.val_eq_zero _).mp h.1
      · exact (ZMod.val_eq_zero _).mp h.2
    have he : G.mul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) i.val (b' 0)) (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) j.val (b' 1)) =
        G.mul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) a.val M.x) (G.nsmul (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) c.val M.y) := by
      simp only [nsmul_pow G]
      exact coord_act b hb reversal z
    rw [he]
    exact M.avoids a c hac
  let N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) :=
    { x := b' 0
      y := b' 1
      killed_x := (nsmul_pow G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) 4 (b' 0)).trans (hb' 0)
      killed_y := (nsmul_pow G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) 4 (b' 1)).trans (hb' 1)
      avoids := hav }
  have hN : ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) M N reversal := by
    simp only [ArithmeticThetaRelativeFourCharacterR0211.Changes, nsmul_pow G]
    exact ⟨rfl, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro N' hN'
  exact ArithmeticThetaRelativeFourCharacterR0211.RelativeMarkingActionR0211.fullLevel_ext G (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)) N' N (hN'.1.trans hN.1.symm) (hN'.2.trans hN.2.symm)

lemma relative_points (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4
    (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)))
    (h : ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 _) M N reversal) :
    N.x = G.nsmul (𝟙 _) 3 M.x ∧ N.y = M.y := by
  letI := G.pointGroup (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))
  simp only [ArithmeticThetaRelativeFourCharacterR0211.Changes, nsmul_pow G] at h
  change N.x = M.x^3 * M.y^0 ∧ N.y = M.x^0 * M.y^1 at h
  simpa only [pow_zero, pow_one, one_mul, mul_one, nsmul_pow G] using h

lemma relative_alpha [Algebra ℚ R]
    (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4
      (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)))
    (h : ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 _) M N reversal)
    (a : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge R W, ⊤)) :
    ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 M a ↔
      ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G 4 N a := by
  letI := G.pointGroup (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))
  obtain ⟨hx, hy⟩ := relative_points W G M N h
  have hx4 : M.x^4 = 1 := (nsmul_pow G _ 4 M.x).symm.trans M.killed_x
  have hx2 : G.nsmul (𝟙 _) 2 N.x = G.nsmul (𝟙 _) 2 M.x := by
    rw [hx]
    simp only [nsmul_pow G]
    exact pow_three_twice _ hx4
  have hl : ArithmeticThetaGlobalFourTorsionR0190.twoLabel R W G 4 N =
      ArithmeticThetaGlobalFourTorsionR0190.twoLabel R W G 4 M := by
    funext i
    simp only [ArithmeticThetaGlobalFourTorsionR0190.twoLabel, show 4/2 = 2 from rfl,
      hx2, hy]
  simp only [ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha,
    ArithmeticThetaGlobalFourTorsionR0190.RootData,
    ArithmeticThetaGlobalFourTorsionR0190.Labels,
    ArithmeticThetaGlobalFourTorsionR0190.quarterPoint, hl, hy]

open ArithmeticThetaRelativeFourCharacterR0211.RelativePhaseMarkingInvariance
open ArithmeticThetaArbitraryFourCharacterR0214.ArbitraryPhaseMarkingInvariance

lemma field_basis {F : Type u} [Field F] [DecidableEq F] {e : Fin 3 → F}
    (b : ArithmeticThetaMarkingR0115.Marking F e)
    (hb : ArithmeticThetaMarkingR0115.IsBasis F e b) :
    ArithmeticThetaMarkingR0115.IsBasis F e (ArithmeticThetaMarkingR0115.act F e b reversal) := by
  refine ⟨ArithmeticThetaMarkingR0115.act_four_torsion b hb.1 reversal, ?_, ?_⟩
  · intro z w hzw
    rw [ArithmeticThetaMarkingR0115.coordinates_act b hb.1,
      ArithmeticThetaMarkingR0115.coordinates_act b hb.1] at hzw
    have hh := congrArg (fun v => reversal.mulVec v) (hb.2.1 hzw)
    simpa only [Matrix.mulVec_mulVec, reversal_sq, Matrix.one_mulVec] using hh
  · intro T hT
    obtain ⟨z, hz⟩ := hb.2.2 T hT
    refine ⟨reversal.mulVec z, ?_⟩
    rw [ArithmeticThetaMarkingR0115.coordinates_act b hb.1,
      Matrix.mulVec_mulVec, reversal_sq, Matrix.one_mulVec, hz]

variable [Algebra ℚ R] [W.IsElliptic]
include hG in
lemma field_phase (M M' : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4
    (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)))
    (hchange : ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 _) M M' reversal)
    (z z' : R) (hz : GeometricPhase R W G M z) (hz' : GeometricPhase R W G M' z')
    (F : Type u) [Field F] [CharZero F] [DecidableEq F] (f : R →+* F) :
    f z' = (f z)^3 := by
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
      ArithmeticThetaMarkingR0115.act F e (castPoint hV ∘ a) reversal := by
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
  have hBa := field_basis (castPoint hV ∘ a) hB
  have hinv : ArithmeticThetaMarkingR0115.phase F e
      (ArithmeticThetaMarkingR0115.act F e (castPoint hV ∘ a) reversal) =
      ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a)^3 := by
    rw [← ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F e he D _ hBa,
      ← ArithmeticThetaGeometricPairingR0118.marking_pairing_identification F e he D _ hB]
    have hh := ArithmeticThetaGeometricPairingR0118.pairing_coordinates F e he D
      (castPoint hV ∘ a) hB ![3,0] ![0,1]
    simpa [ArithmeticThetaMarkingR0115.act, ArithmeticThetaMarkingR0115.coordinates,
      reversal, show (3 : ZMod 4).val = 3 from rfl,
      show (1 : ZMod 4).val = 1 from rfl] using hh
  rw [heq', heq]
  calc
    phaseOn V a' = phaseOn _ (castPoint hV ∘ a') := (phaseOn_cast hV a').symm
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a') := phaseOn_split e _
    _ = ArithmeticThetaMarkingR0115.phase F e (castPoint hV ∘ a)^3 := by rw [hact]; exact hinv
    _ = (phaseOn V a)^3 := congrArg (fun x : F => x^3)
      ((phaseOn_split e _).symm.trans (phaseOn_cast hV a))

include hG in
lemma relative_phase (M N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4
    (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)))
    (hchange : ArithmeticThetaRelativeFourCharacterR0211.Changes R W G (𝟙 _) M N reversal)
    (z z' : R) (hz : ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z)
    (hz' : ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G N z') :
    z' = -z := by
  classical
  obtain ⟨hgeom, hunit, hs, _⟩ :=
    (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase R W G hG M).2 z hz
  obtain ⟨hgeom', _, hs', _⟩ :=
    (ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_geometric_phase R W G hG N).2 z' hz'
  have hdiff : IsUnit (z'-z) := by
    by_contra hu
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {z'-z}) (fun h => hu (Ideal.span_singleton_eq_top.mp h))
    letI : I.IsMaximal := hI
    letI := Ideal.Quotient.field I
    let f : R →+* R ⧸ I := Ideal.Quotient.mk I
    letI : Algebra ℚ (R ⧸ I) := (f.comp (algebraMap ℚ R)).toAlgebra
    letI : CharZero (R ⧸ I) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (R ⧸ I)).injective
    have heq := field_phase W G hG M N hchange z z' hgeom hgeom' (R ⧸ I) f
    have hsq : (f z)^2 = -1 := by simpa only [map_pow, map_neg, map_one] using congrArg f hs
    have heq' : f z' = -f z := by rw [heq, pow_succ, hsq]; ring
    have hn : f (z'-z) ≠ 0 := by
      rw [map_sub, heq', show -f z - f z = -(2*f z) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) ((hunit.map f).ne_zero))
    apply hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hle (Ideal.subset_span (Set.mem_singleton _)))
  apply hdiff.mul_right_cancel
  linear_combination hs' - hs

end Relative
open ArithmeticThetaSchemeFourCharacterR0215.MarkedAffineTestComparison

def reverseTest (M N : FullLevel E 4) (hN : Changes E M N reversal)
    (P : AffineTest E M) : AffineTest E N := by
  let L := (relative_exists P.equation P.law P.originLaw P.level).choose
  have hL := (relative_exists P.equation P.law P.originLaw P.level).choose_spec.1
  have hz : (family E M P).zero ≫ P.comparison = P.base ≫ E.zero := by
    rw [family_zero]
    exact P.zero_eq
  have hn (x : SchemeHomOver (𝟙 (Base P.ring)) (family E M P).p)
      (y : SchemeHomOver (𝟙 S) E.p)
      (h : x.val ≫ P.comparison = P.base ≫ y.val) (n : ℕ) :
      (P.law.nsmul (𝟙 _) n x).val ≫ P.comparison =
        P.base ≫ (multiple E (𝟙 S) n y).val := by
    rw [← SchemePhaseMarkingInvariance.multiple_eq E M P]
    exact CartesianFullMarking.multiple_comp E (family E M P) P.base P.comparison
      hz P.mul_eq x y h n
  have hx : L.x.val ≫ P.comparison = P.base ≫ N.x.val := by
    rw [hL.1, hN.1]
    exact CartesianFullMarking.mul_comp E (family E M P) P.base P.comparison P.mul_eq
      _ _ _ _ (hn _ _ P.x_eq _) (hn _ _ P.y_eq _)
  have hy : L.y.val ≫ P.comparison = P.base ≫ N.y.val := by
    rw [hL.2, hN.2]
    exact CartesianFullMarking.mul_comp E (family E M P) P.base P.comparison P.mul_eq
      _ _ _ _ (hn _ _ P.x_eq _) (hn _ _ P.y_eq _)
  exact
    { ring := P.ring, equation := P.equation, elliptic := P.elliptic
      law := P.law, originLaw := P.originLaw, base := P.base
      comparison := P.comparison, cartesian := P.cartesian
      zero_eq := P.zero_eq, mul_eq := P.mul_eq, level := L, x_eq := hx, y_eq := hy }

lemma scheme_phase (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (M N : FullLevel E 4) (hN : Changes E M N reversal)
    (z : Γ(S, ⊤)) (hz : MillerPhase E M z) : MillerPhase E N (-z) := by
  obtain ⟨w, hw, _⟩ := (scheme_miller_phase k S σ E N).1
  have heq : w = -z := by
    apply SchemeMillerPhase.section_ext E M k σ
    intro P
    letI := P.elliptic
    let Q := reverseTest E M N hN P
    have hL : ArithmeticThetaRelativeFourCharacterR0211.Changes P.ring P.equation P.law
        (𝟙 _) P.level Q.level reversal :=
      (relative_exists P.equation P.law P.originLaw P.level).choose_spec.1
    have hh := relative_phase P.equation P.law P.originLaw P.level Q.level hL
      (affineScalar E M P z) (affineScalar E N Q w) (hz P) (hw Q)
    simpa only [Q, reverseTest, affineScalar, map_neg] using hh
  simpa only [heq] using hw

lemma scheme_alpha_imp (M N : FullLevel E 4) (hN : Changes E M N reversal)
    (a : Γ(ArithmeticThetaSchemeHodgeR0205.Cotangent E, ⊤))
    (ha : RealizesAlpha E M a) : RealizesAlpha E N a := by
  intro P
  let Q := reverseTest E N M (scheme_involution E M N hN) P
  have hL : ArithmeticThetaRelativeFourCharacterR0211.Changes P.ring P.equation P.law
      (𝟙 _) P.level Q.level reversal :=
    (relative_exists P.equation P.law P.originLaw P.level).choose_spec.1
  have hh := ha Q
  refine ⟨hh.1, ?_⟩
  intro i hi
  exact (relative_alpha P.equation P.law P.level Q.level hL _).mpr (hh.2 i hi)

end SchemePairingReversal
open CategoryTheory AlgebraicGeometry
open SchemePairingReversal

/-- Reversal is uniquely defined on the original scheme and preserves the signed
cotangent alpha, while negating the full normalized Miller regular function. -/
theorem scheme_pairing_reversal :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom (S) (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), (∃! N : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M N ArithmeticThetaPhaseSwitchR0218.reversal) ∧ (∀ N : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M N ArithmeticThetaPhaseSwitchR0218.reversal → ArithmeticThetaSchemeFourCharacterR0215.Changes E N M ArithmeticThetaPhaseSwitchR0218.reversal ∧ ArithmeticThetaUniversalEvaluationR0213.evenPoint E N = ArithmeticThetaUniversalEvaluationR0213.evenPoint E M ∧ (∀ z : S.presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E N (-z)) ∧ (∀ a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a ↔ ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E N a)) := by
  intro k _ _ S σ E M
  refine ⟨scheme_exists E M, ?_⟩
  intro N hN
  refine ⟨scheme_involution E M N hN, scheme_even E M N hN,
    scheme_phase E k σ M N hN, ?_⟩
  intro a
  exact ⟨scheme_alpha_imp E M N hN a,
    scheme_alpha_imp E N M (scheme_involution E M N hN) a⟩

#print axioms scheme_pairing_reversal
end ArithmeticThetaPhaseSwitchR0218
