module

public import ArbitraryGeometricPhaseR0214
public import RelativePhaseBaseChangeR0211
public import ArbitraryCompatibleLocalCoverageR0202

@[expose] public section

/-! Naturality of the exact Miller phase over arbitrary rational rings.
The actual Cartesian chart comparison gives residue-field compatibility.
The already proved square identity makes the sum of the two phases a unit;
cancellation then proves equality in the original ring, retaining nilpotents. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaArbitraryFourCharacterR0214
namespace ArbitraryPhaseBaseChange
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177
open ArithmeticThetaGlobalFourTorsionR0190
open ArithmeticThetaRelativeFourCharacterR0211
open RelativeAlphaNaturality RelativeGeometricPhase RelativePhaseBaseChange

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)

include hG in
/-- Over a field the pointed Cartesian map supplies one actual variable change.
Its chart equations compare both marked points and their doubled labels. -/
lemma field_naturality (M : FullLevel R W G 4 (𝟙 (Base R)))
    (F : Type u) [Field F] [Algebra ℚ F]
    (V : WeierstrassCurve F) [V.IsElliptic] (H : Law F V)
    (hH : IsOriginLaw F V H) (N : FullLevel F V H 4 (𝟙 (Base F)))
    (ι : R →+* F) (b : Curve F V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F V H ι b)
    (hM : MarkingCompatible R W G M F V H N ι b)
    (z : R) (w : F) (hz : MillerPhase R W G M z)
    (hw : MillerPhase F V H N w) : ι z = w := by
  classical
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  obtain ⟨e, x, y, hc⟩ := hz.1
  obtain ⟨d, v, t, hd⟩ := hw.1
  obtain ⟨C,χ,hC,hχ,hχc,hχx,hχy⟩ := cartesian_field_chart W V ι b hb.1 hb.2.1
  have hn (P : SchemeHomOver (𝟙 (Base R)) (structureMap R W))
      (Q : SchemeHomOver (𝟙 (Base F)) (structureMap F V))
      (hPQ : Q.val ≫ b = baseMap R F ι ≫ P.val) (n : ℕ) :
      (H.nsmul (𝟙 _) n Q).val ≫ b = baseMap R F ι ≫ (G.nsmul (𝟙 _) n P).val := by
    rw [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      ← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.assoc,hb.2.2,← Category.assoc,hPQ,Category.assoc]
  have h0 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.x N.x hM.1 2)
    _ _ _ _ (hc.1 0) (hd.1 0) (C.u : F) C.r C.s C.t hχx hχy
  have h1 := coordinate_values_natural W V ι b χ hχ _ _ (hn M.y N.y hM.2 2)
    _ _ _ _ (hc.1 1) (hd.1 1) (C.u : F) C.r C.s C.t hχx hχy
  have hp := coordinate_values_natural W V ι b χ hχ _ _ hM.1
    _ _ _ _ hc.2.2.1 hd.2.2.1 (C.u : F) C.r C.s C.t hχx hχy
  have hq := coordinate_values_natural W V ι b χ hχ _ _ hM.2
    _ _ _ _ hc.2.2.2 hd.2.2.2 (C.u : F) C.r C.s C.t hχx hχy
  have he (i : Fin 2) : ι (e i.castSucc) = (C.u : F)^2*d i.castSucc+C.r := by
    fin_cases i
    · exact h0.1
    · exact h1.1
  have hx (i : Fin 2) : ι (x i) = (C.u : F)^2*v i+C.r := by
    fin_cases i
    · exact hp.1
    · exact hq.1
  have hy (i : Fin 2) : ι (y i) = (C.u : F)^3*t i+(C.u : F)^2*C.s*v i+C.t := by
    fin_cases i
    · exact hp.2
    · exact hq.2
  have hY (i : Fin 2) : ι (completedY R W (x i) (y i)) =
      (C.u : F)^3 * completedY F V (v i) (t i) := by
    rw [completed_y_map, hx, hy, completed_y_variable, hC]
  let Y := fun i => completedY R W (x i) (y i)
  let T := fun i => completedY F V (v i) (t i)
  have hpz := congrArg ι (hz.2 e x y hc).2
  have hpw := (hw.2 d v t hd).2
  simp only [map_mul, map_numerator, map_denominator] at hpz
  obtain ⟨hnum, hden⟩ := polynomial_covariance (ι ∘ e) d (ι ∘ x)
    (fun i => ι (completedY R W (x i) (y i))) v
    (fun i => completedY F V (v i) (t i)) (C.u : F) C.r he hx hY
  dsimp only [Function.comp_def] at hnum hden hpz
  rw [hnum, hden] at hpz
  apply ((C.u.isUnit.pow 16).mul (hw.2 d v t hd).1).mul_left_cancel
  calc
    (C.u : F)^16 * denominator d v T * ι z =
        (C.u : F)^16 * numerator d v T := hpz
    _ = (C.u : F)^16 * denominator d v T * w := by rw [← hpw]; ring

include hG in
/-- Compare both phases after any field-valued specialization of the target.
The intermediate marking is lifted through the actual coefficient square. -/
lemma field_specialization (M : FullLevel R W G 4 (𝟙 (Base R)))
    (S : Type u) [CommRing S] [Algebra ℚ S]
    (V : WeierstrassCurve S) [V.IsElliptic] (H : Law S V)
    (hH : IsOriginLaw S V H) (N : FullLevel S V H 4 (𝟙 (Base S)))
    (ι : R →+* S) (b : Curve S V ⟶ Curve R W)
    (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S V H ι b)
    (hM : MarkingCompatible R W G M S V H N ι b)
    (z : R) (w : S) (hz : MillerPhase R W G M z) (hw : MillerPhase S V H N w)
    (F : Type u) [Field F] [Algebra ℚ F] (κ : S →+* F) : κ (ι z) = κ w := by
  classical
  let Z := V.map κ
  obtain ⟨c, _, hc, hco, _⟩ := NormalFormConstruction.coefficient_comparison V κ
  change origin F Z ≫ c = baseMap S F κ ≫ origin S V at hco
  obtain ⟨J, hm, hj⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      κ (structureMap S V) (structureMap F Z) c hc H
  have hJ : IsOriginLaw F Z J := by
    constructor
    · intro T t
      apply hc.hom_ext
      · simp only [hj, hH.1, Category.assoc]
        rw [hco]
        rfl
      · rw [Category.assoc, BaseChange.origin_over, Category.comp_id]
        exact (J.one t).property
    · intro T t x y
      apply Subtype.ext
      apply hc.hom_ext
      · rw [hm, hm, hH.2]
      · exact (J.mul t x y).property.trans (J.mul t y x).property.symm
  have hBC := ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.pointed_base_change
    H J hH hJ κ c hc hco
  have hd : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange
      R W G F Z J (κ.comp ι) (c ≫ b) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact hc.paste_horiz hb.1
    · rw [← Category.assoc, hBC.2.1, Category.assoc, hb.2.1,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · intro n
      rw [← Category.assoc, hBC.2.2, Category.assoc, hb.2.2, Category.assoc]
  let B : FullLevel S V H 4 ((𝟙 (Base F)) ≫ baseMap S F κ) :=
    BaseChange.restrict N (baseMap S F κ) (by simp)
  let NF : FullLevel F Z J 4 (𝟙 (Base F)) :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up hBC hH hJ B
  have hNx : NF.x.val ≫ c = baseMap S F κ ≫ N.x.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_x hBC hH hJ B
  have hNy : NF.y.val ≫ c = baseMap S F κ ≫ N.y.val :=
    ArithmeticThetaArbitraryAffineR0202.ArbitraryLocalCoverage.MarkingTransport.up_y hBC hH hJ B
  have hFx : NF.x.val ≫ (c ≫ b) = baseMap R F (κ.comp ι) ≫ M.x.val := by
    rw [← Category.assoc, hNx, Category.assoc, hM.1]
    simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hFy : NF.y.val ≫ (c ≫ b) = baseMap R F (κ.comp ι) ≫ M.y.val := by
    rw [← Category.assoc, hNy, Category.assoc, hM.2]
    simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨zf, hzf, _⟩ := (arbitrary_geometric_phase F Z J hJ NF).1
  exact (field_naturality W G hG M F Z J hJ NF (κ.comp ι) (c ≫ b)
    hd ⟨hFx, hFy⟩ z zf hz hzf).trans
    (field_naturality V H hH N F Z J hJ NF κ c
      hBC ⟨hNx, hNy⟩ w zf hw hzf).symm

/-- Simple roots of X²+1 are determined by their residue-field values.
This uses a unit cancellation in the whole ring, without reducedness. -/
lemma square_root_ext {S : Type u} [CommRing S] [Algebra ℚ S]
    (a b : S) (ha : a^2 = -1) (hb : b^2 = -1)
    (h : ∀ (F : Type u) [Field F] [Algebra ℚ F] (κ : S →+* F), κ a = κ b) : a = b := by
  classical
  have hu : IsUnit (a+b) := by
    by_contra hn
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a+b})
      (fun ht => hn (Ideal.span_singleton_eq_top.mp ht))
    letI : I.IsMaximal := hI
    letI := Ideal.Quotient.field I
    let κ : S →+* S ⧸ I := Ideal.Quotient.mk I
    letI : Algebra ℚ (S ⧸ I) := (κ.comp (algebraMap ℚ S)).toAlgebra
    letI : CharZero (S ⧸ I) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (S ⧸ I)).injective
    have he := h (S ⧸ I) κ
    have hz : κ (a+b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))
    have h2 : (2 : S ⧸ I) * κ b = 0 := by
      simpa only [map_add, he, ← two_mul] using hz
    have hb0 : κ b = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have hh := congrArg κ hb
    simp only [map_pow, map_neg, map_one, hb0, zero_pow (by decide : 2 ≠ 0)] at hh
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : S ⧸ I) ≠ 0)) hh.symm
  apply hu.mul_left_cancel
  linear_combination ha-hb

end ArbitraryPhaseBaseChange

/-- The exact normalized Miller phase is natural for the specified pointed
Cartesian family map, with no reducedness, flatness or nontriviality hypothesis. -/
theorem arbitrary_phase_base_change :
∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (S : Type u) [CommRing S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws), ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs → ∀ (Ms : ArithmeticThetaFullLevelCoverR0175.FullLevel S Ws Gs 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base S))) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)), ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b → ArithmeticThetaRelativeFourCharacterR0211.MarkingCompatible R W G M S Ws Gs Ms ι b → ∀ (z : R) (zs : S), ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase R W G M z → ArithmeticThetaArbitraryFourCharacterR0214.MillerPhase S Ws Gs Ms zs → ι z = zs := by
  intro R _ _ W _ G hG M S _ _ V _ H hH N ι b hb hM z w hz hw
  apply ArbitraryPhaseBaseChange.square_root_ext (ι z) w
  · have hs := congrArg ι ((arbitrary_geometric_phase R W G hG M).2 z hz).2.2.1
    simpa only [map_pow, map_neg, map_one] using hs
  · exact ((arbitrary_geometric_phase S V H hH N).2 w hw).2.2.1
  · intro F _ _ κ
    exact ArbitraryPhaseBaseChange.field_specialization W G hG M S V H hH N
      ι b hb hM z w hz hw F κ

#print axioms arbitrary_phase_base_change
end ArithmeticThetaArbitraryFourCharacterR0214
