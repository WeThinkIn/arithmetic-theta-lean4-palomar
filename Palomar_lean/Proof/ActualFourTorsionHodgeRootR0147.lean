module

public import MarkedCoordinateChartR0147
public import ProjectivePointsEvaluationR0146
public import FourTorsionRoot

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaHodgeFourTorsionR0147
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaCubicModelR0144 ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaAlgebraicCoordinatesR0143
namespace ActualFourTorsionHodgeRoot
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma hodgeSection_smul (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (δ : Frame k M) (a : LaurentSeries k) :
    hodgeSection k M s hs δ a =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv a • hodgeSection k M s hs δ 1 := by
  unfold hodgeSection
  rw [map_one, ← Scheme.Modules.Hom.app_smul]
  congr 1
  exact (mul_one ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv a)).symm

lemma hodgeSection_ne_zero (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (δ : Frame k M) {a : LaurentSeries k} (ha : a ≠ 0) :
    hodgeSection k M s hs δ a ≠ 0 := by
  intro h
  have hinv : Function.Injective (Scheme.Modules.Hom.app (hodgeFrame k M s hs δ).hom ⊤) := by
    intro x y hxy
    have := congrArg (Scheme.Modules.Hom.app (hodgeFrame k M s hs δ).inv ⊤) hxy
    simpa only [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using this
  apply ha
  apply (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom.injective
  apply hinv
  simpa only [hodgeSection, map_zero] using h

lemma hodgeSection_square (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (δ : Frame k M) (a b : LaurentSeries k) (hab : a^2 = b) :
    HodgeSquare k M s hs δ (hodgeSection k M s hs δ a) b := by
  unfold HodgeSquare
  rw [hodgeSection_smul k M s hs δ a]
  unfold ArithmeticThetaSheafTensor.tensorSection
  rw [TensorProduct.smul_tmul_smul, map_smul]
  congr 1
  rw [← map_mul, ← pow_two, hab]

lemma coordinates_of_ne (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (e : genericScheme k M ≅ projectiveCurve k r)
    (hec : IsCompactificationIso k M s hs a c e)
    (R : Point k M) (hne : R ≠ pointOver k M (𝟙 _) s hs) :
    ∃ x y, HasCoordinates k M e R x y := by
  have hmem : ∀ x, R.val x ∈ complement k M s := by
    intro x hn
    change R.val x ∈ (s.ker.comap (genericInclusion k M)).support at hn
    have hn := (GenericAffineCubicIsomorphismR0144.generic_identity_support_singleton k M hM s hs x).le hn
    letI := GenericAffineCubicIsomorphismR0144.genericPoint_closed k M hM s hs
    have heq := MarkedCoordinateChart.field_section_ext R.val
      (genericPoint k M s hs) (genericStructure k M) R.property
      (by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, genericStructure]) x hn
    apply hne
    apply Subtype.ext
    simpa only [pointOver, Category.id_comp] using heq
  let l : Spec (CommRingCat.of (LaurentSeries k)) ⟶ complementScheme k M s :=
    IsOpenImmersion.lift (complement k M s).ι R.val (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨_, hmem x⟩, rfl⟩)
  have hl : l ≫ (complement k M s).ι = R.val := IsOpenImmersion.lift_fac _ _ _
  let χ : ChartRing k r →+* LaurentSeries k := (Spec.preimage (l ≫ a.hom ≫ c.hom)).hom
  refine ⟨χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective),
    χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective), χ, ?_, rfl, rfl⟩
  have hχ : Spec.map (CommRingCat.ofHom χ) = l ≫ a.hom ≫ c.hom := Spec.map_preimage _
  rw [hχ, ← hl]
  simp only [Category.assoc, hec.2.1]

local instance : DecidableEq (LaurentSeries k) := Classical.decEq _

open ActualGenericGroupLaw

lemma evaluation_bridge (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr)
    (he : Even r) (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (e : genericScheme k M ≅ projectiveCurve k r)
    (hec : IsCompactificationIso k M s hs a c e)
    (G : Law k M) (hG : IsOriginLaw k M s hs G) :
    ∃ E : Point k M ≃ (ArithmeticThetaFourTorsion.splitCurve
        (root k r 0) (root k r 1) (root k r 2)).Point,
      (∀ P Q, E (G.mul (𝟙 _) P Q) = E P + E Q) ∧
      (∀ P x y, HasCoordinates k M e P x y →
        ∃ hxy, E P = WeierstrassCurve.Affine.Point.some x y hxy) := by
  classical
  have hei : e.inv ≫ genericStructure k M = ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r := by
    rw [← hec.1, Iso.inv_hom_id_assoc]
  let H := transport e.symm hei G
  have hH : (H.one (𝟙 _)).val = origin k r := by
    change (G.one (𝟙 _)).val ≫ e.hom = _
    rw [hG.1]
    simpa only [pointOver, Category.id_comp] using hec.2.2
  obtain ⟨ev, hev⟩ := projective_points_evaluation k r h3 he H hH
  have ht : extensionBase k (LaurentSeries k) = 𝟙 _ := by
    simp [extensionBase, Algebra.algebraMap_self]
  have hex : ∃ evF : SchemeHomOver (extensionBase k (LaurentSeries k))
      (ArithmeticThetaCompactifiedDifferentialR0145.projectiveStructure k r) ≃
      ((curve k r).toProjective.baseChange (LaurentSeries k)).toAffine.Point,
      (∀ P Q, evF (H.mul (extensionBase k (LaurentSeries k)) P Q) = evF P + evF Q) ∧
      (∀ P χ, P.val = Spec.map (CommRingCat.ofHom χ) ≫ chartInclusion k r →
        ∃ hxy, evF P = WeierstrassCurve.Affine.Point.some
          (χ (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective))
          (χ (WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective)) hxy) :=
    ⟨ev (LaurentSeries k), hev.1.1 (LaurentSeries k), hev.2 (LaurentSeries k)⟩
  rw [ht] at hex
  obtain ⟨evF, hm, hc⟩ := hex
  let E := (pointsEquiv e hec.1 (𝟙 _)).trans evF
  refine ⟨E, ?_, ?_⟩
  · intro P Q
    have hback (P : Point k M) :
        pointsEquiv e.symm hei (𝟙 _) (pointsEquiv e hec.1 (𝟙 _) P) = P := by
      apply Subtype.ext
      simp [pointsEquiv]
    have hh := hm (pointsEquiv e hec.1 (𝟙 _) P) (pointsEquiv e hec.1 (𝟙 _) Q)
    change evF ((pointsEquiv e.symm hei (𝟙 _)).symm
      (G.mul (𝟙 _) _ _)) = _ at hh
    rw [hback, hback] at hh
    exact hh
  · intro P x y hP
    obtain ⟨χ, hfac, hx, hy⟩ := hP
    obtain ⟨hxy, hh⟩ := hc (pointsEquiv e hec.1 (𝟙 _) P) χ hfac
    subst x; subst y
    exact ⟨hxy, hh⟩

end ActualFourTorsionHodgeRoot
open ActualFourTorsionHodgeRoot

/-- Actual halves of the labelled half-period point yield an order-four point
and the source square root in the identity pullback of the differential sheaf. -/
theorem actual_four_torsion_hodge_root :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T :
    ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M :
    ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM :
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom
    (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs :
    ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r
    hr) 1 s), ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y :
    ArithmeticThetaIdentitySectionsR0138.Dual k M s 3),
    ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X →
    ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (a : CategoryTheory.Iso
    (ArithmeticThetaCubicModelR0144.complementScheme k M s) (ArithmeticThetaCubicModelR0144.cubicScheme k r)),
    ArithmeticThetaCubicModelR0144.IsCoordinateIso k M s X Y a → ∀ (c : CategoryTheory.Iso
    (ArithmeticThetaCubicModelR0144.cubicScheme k r) (AlgebraicGeometry.Spec (CommRingCat.of
    (ArithmeticThetaCompactifiedDifferentialR0145.ChartRing k r)))),
    ArithmeticThetaCompactifiedDifferentialR0145.IsChartIso k r c → ∀ (e : CategoryTheory.Iso
    (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)
    (ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve k r)),
    ArithmeticThetaCompactifiedDifferentialR0145.IsCompactificationIso k M s hs.1 a c e → ∀ (G :
    ArithmeticThetaMarkedGroupLawR0146.Law k M), ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G →
    ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M),
    ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ∀ (p₂ : Quiver.Hom
    (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hp₂ :
    ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaHodgeFourTorsionR0147.halfIndex r
    hr) 1 p₂) (R : ArithmeticThetaHodgeFourTorsionR0147.Point k M), G.nsmul (CategoryTheory.CategoryStruct.id
    (AlgebraicGeometry.Spec (CommRingCat.of (LaurentSeries k)))) 2 R =
    (ArithmeticThetaMarkedGroupLawR0146.pointOver k M (CategoryTheory.CategoryStruct.id
    (AlgebraicGeometry.Spec (CommRingCat.of (LaurentSeries k)))) p₂ hp₂.1) → ∃ x y : LaurentSeries k,
    ArithmeticThetaHodgeFourTorsionR0147.HasCoordinates k M e R x y ∧ y ≠ 0 ∧ (∀ n : ℕ, G.nsmul
    (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (LaurentSeries k)))) n R = G.one
    (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of (LaurentSeries k)))) ↔ 4 ∣ n) ∧
    (ArithmeticThetaHodgeFourTorsionR0147.alpha k M s hs.1 δ x y) ≠ 0 ∧
    ArithmeticThetaHodgeFourTorsionR0147.HodgeSquare k M s hs.1 δ (ArithmeticThetaHodgeFourTorsionR0147.alpha
    k M s hs.1 δ x y) (4 * (ArithmeticThetaCompactifiedDifferentialR0145.root k r 1 -
    ArithmeticThetaCompactifiedDifferentialR0145.root k r 0)) := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY a ha c hc e hec G hG δ hδ p₂ hp₂ R hd
  classical
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨E, hEmul, hEcoords⟩ := evaluation_bridge k r hr h3 T he M s hs.1 a c e hec G hG
  have hEone : E (G.one (𝟙 _)) = 0 := by
    have hh := hEmul (G.one (𝟙 _)) (G.one (𝟙 _))
    rw [G.one_mul] at hh
    exact add_eq_left.mp hh.symm
  have hEn (n : ℕ) (P : Point k M) : E (G.nsmul (𝟙 _) n P) = n • E P := by
    induction n with
    | zero => simpa using hEone
    | succ n ih => rw [WeierstrassProjModel.RelativeGroupLaw.nsmul_succ, hEmul, ih, succ_nsmul]
  have hhalf : (halfIndex r hr).val ≠ 0 := by
    change r / 2 ≠ 0
    omega
  have hPcoords := marked_coordinate_chart k r hr h3 T he M hM s hs X Y hX hY a ha c hc e hec
    (halfIndex r hr) 1 p₂ hp₂ (Or.inl hhalf)
  have hYzero : ArithmeticThetaTateSeries.tateY r (r/2) (1 : k) = 0 := by
    obtain ⟨m, hm⟩ := he
    have hrm : r = 2*m := by omega
    rw [hrm, Nat.mul_div_right m (by decide : 0 < 2)]
    exact ArithmeticThetaTateIdentities.tateY_midpoint_one m (by omega)
  have hPcoords' : HasCoordinates k M e (pointOver k M (𝟙 _) p₂ hp₂.1) (root k r 1) 0 := by
    simpa only [halfIndex, Units.val_one, hYzero, map_zero, root, rootSeries,
      Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte] using hPcoords
  obtain ⟨hP, hEP⟩ := hEcoords _ _ _ hPcoords'
  have hEd : 2 • E R = WeierstrassCurve.Affine.Point.some (root k r 1) 0 hP := by
    rw [← hEn, hd, hEP]
  obtain ⟨h01, h02, h12⟩ := CompactifiedCoordinateIsomorphism.roots_distinct k h3 he
  have hord := ArithmeticThetaFourTorsion.actual_half_order_four (LaurentSeries k)
    (root k r 0) (root k r 1) (root k r 2) hP (E R) h01 h02 h12 hEd
  have hRne : R ≠ pointOver k M (𝟙 _) s hs.1 := by
    intro hh
    have hRone : R = G.one (𝟙 _) := hh.trans (hG.1 _).symm
    rw [hRone, hEone, nsmul_zero] at hEd
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP hEd.symm
  obtain ⟨x, y, hxy⟩ := coordinates_of_ne k M hM s hs.1 a c e hec R hRne
  obtain ⟨hR, hER⟩ := hEcoords R x y hxy
  obtain ⟨x', y', hR', hER', hy, hg, _⟩ := ArithmeticThetaFourTorsion.actual_half_root
    (LaurentSeries k) (root k r 0) (root k r 1) (root k r 2) hP (E R) h01 h02 h12 hEd
  obtain ⟨hx, hyy⟩ := WeierstrassCurve.Affine.Point.some.inj (hER.symm.trans hER')
  subst x'; subst y'
  refine ⟨x, y, hxy, hy, ?_, ?_, ?_⟩
  · intro n
    rw [← E.injective.eq_iff, hEn, hEone, ← addOrderOf_dvd_iff_nsmul_eq_zero, hord]
  · apply hodgeSection_ne_zero
    apply mul_ne_zero (by norm_num)
    intro hz
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hg
    exact h01 (sub_eq_zero.mp hg.symm).symm
  · apply hodgeSection_square
    rw [mul_pow, hg]
    norm_num

#print axioms actual_four_torsion_hodge_root
end ArithmeticThetaHodgeFourTorsionR0147
