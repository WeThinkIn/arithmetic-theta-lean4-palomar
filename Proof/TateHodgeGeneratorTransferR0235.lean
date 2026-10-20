module

public import BoundaryConstantsDefinitionsR0235

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaBoundaryConstantsR0235
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTateCuspsR0181
namespace TateHodgeGeneratorTransfer

lemma chart_preimage {A B : Type} [CommRing A] [CommRing B]
    {X Y : Scheme} (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j] (b : X ⟶ Y) (χ : A →+* B)
    (h : j ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ i) :
    j ''ᵁ ⊤ ≤ b ⁻¹ᵁ (i ''ᵁ ⊤) := by
  rintro x ⟨z, hz, rfl⟩
  change (j ≫ b) z ∈ i ''ᵁ ⊤
  rw [h]
  exact ⟨_, trivial, rfl⟩

lemma chart_section {A B : Type} [CommRing A] [CommRing B]
    {X Y : Scheme} (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
    (b : X ⟶ Y) (χ : A →+* B)
    (h : j ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ i)
    (v : j ''ᵁ ⊤ ≤ b ⁻¹ᵁ (i ''ᵁ ⊤)) (a : A) :
    b.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) v ((chartRingEquiv i).symm a) =
      (chartRingEquiv j).symm (χ a) := by
  apply (chartRingEquiv j).injective
  rw [RingEquiv.apply_symm_apply]
  change ((b.appLE _ _ v ≫ (j.appIso ⊤).hom ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom ((chartRingEquiv i).symm a)) = _
  rw [Scheme.Hom.appIso_hom', ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
  simp only [h]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom χ)) i
    (i ''ᵁ ⊤) ⊤ ⊤ (Scheme.Hom.preimage_image_eq i ⊤).ge (by simp)]
  have ht : (Spec.map (CommRingCat.ofHom χ)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom χ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [Category.assoc, ht, Scheme.ΓSpecIso_naturality, ← Category.assoc]
  rw [← Scheme.Hom.appIso_hom']
  change χ (chartRingEquiv i ((chartRingEquiv i).symm a)) = _
  rw [RingEquiv.apply_symm_apply]

lemma pull_section_restrict {X Y : Scheme} (b : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) (m : (Scheme.Modules.pullback b).obj M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ b ⁻¹ᵁ U) (s : Γ(M, ⊤)) :
    res N h (m.app _ (Scheme.Modules.pullbackLocalSection b (res M le_top s))) =
      res N (show V ≤ ⊤ from le_top)
        (res N (by simp) (m.app _ (Scheme.Modules.pullbackLocalSection b s))) := by
  rw [hom_res]
  change m.app V (((Scheme.Modules.pullback b).obj M).presheaf.map (homOfLE h).op
    (Scheme.Modules.pullbackLocalSection b (M.presheaf.map (homOfLE le_top).op s))) = _
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection]
  change m.app V (res _ h (res _ _ (Scheme.Modules.pullbackLocalSection b s))) = _
  rw [res_res, ← hom_res, res_res]

lemma normalization_pull {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme} (g : Y ⟶ Spec (CommRingCat.of A))
    (f : X ⟶ Spec (CommRingCat.of B)) (b : X ⟶ Y)
    (hb : b ≫ g = f ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (U : Y.Opens) (V : X.Opens) (h : V ≤ b ⁻¹ᵁ U)
    (x p : Γ(Y,U)) (s : Γ(g.kaehler, ⊤))
    (hn : relativeD g U x = p • res g.kaehler le_top s) :
    relativeD f V (b.appLE U V h x) = b.appLE U V h p •
      res f.kaehler (show V ≤ ⊤ from le_top)
        (res f.kaehler (by simp) ((differentialMap g f b hb).app _
          (Scheme.Modules.pullbackLocalSection b s))) := by
  have hh := congrArg (fun t => res f.kaehler h
    ((differentialMap g f b hb).app _ (Scheme.Modules.pullbackLocalSection b t))) hn
  rw [HodgeBaseChange.differentialMap_D, relativeD_res, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul,
    res_smul,
    pull_section_restrict] at hh
  exact hh

lemma frame_res {X : Scheme} {M : X.Modules}
    (e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ M) (U : X.Opens) :
    res M (show U ≤ ⊤ from le_top) (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(X,⊤))) =
      Scheme.Modules.Hom.app e.hom U (1 : Γ(X,U)) := by
  rw [hom_res]
  change Scheme.Modules.Hom.app e.hom U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op 1) = _
  rw [map_one]

lemma cancel_on_chart {X : Scheme} [IsIntegral X] {M : X.Modules}
    (e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ M)
    (V : X.Opens) [Nonempty V] (p : Γ(X,V)) (hp : p ≠ 0)
    (s t : Γ(M,⊤))
    (h : p • res M (show V ≤ ⊤ from le_top) s =
      p • res M (show V ≤ ⊤ from le_top) t) : s = t := by
  apply frame_restrict_injective e ⊤ V le_top
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv V)).1
  have hh := congrArg (Scheme.Modules.Hom.app e.inv V) h
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at hh
  exact @mul_left_cancel₀ Γ(X,V) _ _ _ p
    (show Γ(X,V) from Scheme.Modules.Hom.app e.inv V _)
    (show Γ(X,V) from Scheme.Modules.Hom.app e.inv V _) hp hh

lemma chart_normalized_congr {R A : Type} [CommRing R] [CommRing A]
    {X : Scheme} (g : X ⟶ Spec (CommRingCat.of R))
    (e : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ g.kaehler)
    (i j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (hij : i = j) (x y : A)
    (hn : relativeD g (i ''ᵁ ⊤) ((chartRingEquiv i).symm x) =
      (2 * (chartRingEquiv i).symm y) • Scheme.Modules.Hom.app e.hom (i ''ᵁ ⊤)
        (1 : Γ(X,i ''ᵁ ⊤))) :
    relativeD g (j ''ᵁ ⊤) ((chartRingEquiv j).symm x) =
      (2 * (chartRingEquiv j).symm y) • Scheme.Modules.Hom.app e.hom (j ''ᵁ ⊤)
        (1 : Γ(X,j ''ᵁ ⊤)) := by
  subst j
  exact hn

lemma curve_section_transfer (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l]
    (ι : k →+* l) (L : ℕ) (hL : 3 ≤ L) (he : Even L)
    (b : Curve (LaurentSeries l) (TateCurve l L) ⟶
      Curve (LaurentSeries k) (TateCurve k L)) (hb : CurveMap ι L b)
    (δ : CurveFrame k L) (ε : CurveFrame l L)
    (hδ : Normalized k L δ) (hε : Normalized l L ε) :
    letI : Algebra (LaurentSeries k) (LaurentSeries l) := (laurentMap ι).toAlgebra
    res _ (by simp) ((HodgeBaseChange.differentialMap
      (structureMap (LaurentSeries k) (TateCurve k L))
      (structureMap (LaurentSeries l) (TateCurve l L)) b hb.1.w).app _
      (Scheme.Modules.pullbackLocalSection b
        (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))))) =
      Scheme.Modules.Hom.app ε.hom ⊤ (1 : Γ(Curve (LaurentSeries l) (TateCurve l L), ⊤)) := by
  letI : Algebra (LaurentSeries k) (LaurentSeries l) := (laurentMap ι).toAlgebra
  letI := TateFullLevelMarking.elliptic l L hL he
  letI := CompactifiedCoordinateIsomorphism.projective_integral l (r := L)
  let i := ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion k L
  let j := ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion l L
  letI : IsOpenImmersion i := CompactifiedCoordinateIsomorphism.chart_open k
  letI : IsOpenImmersion j := CompactifiedCoordinateIsomorphism.chart_open l
  let U := i ''ᵁ ⊤
  let V := j ''ᵁ ⊤
  letI : Nonempty V :=
    ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.zOpen_nonempty
      (LaurentSeries l) (TateCurve l L)
  obtain ⟨χ, hχ, hx, hy, hj⟩ := hb.2.2
  have hji : j ≫ b = Spec.map (CommRingCat.ofHom χ) ≫ i := hj
  have hV := chart_preimage i j b χ hji
  have hn : relativeD (structureMap (LaurentSeries k) (TateCurve k L)) U
      ((chartRingEquiv i).symm (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)) =
      (2 * (chartRingEquiv i).symm (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)) •
      res _ (show U ≤ ⊤ from le_top) (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve (LaurentSeries k) (TateCurve k L), ⊤))) := by
    rw [frame_res]
    exact chart_normalized_congr _ δ (zLeg k L (Iso.refl _)) i (Category.comp_id _) _ _ hδ
  have ht := normalization_pull (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries l) (TateCurve l L)) b hb.1.w U V hV _ _ _ hn
  rw [map_mul, map_ofNat, chart_section i j b χ hji hV,
    chart_section i j b χ hji hV, hx, hy] at ht
  have hnε : relativeD (structureMap (LaurentSeries l) (TateCurve l L)) V
      ((chartRingEquiv j).symm (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve l L).toProjective)) =
      (2 * (chartRingEquiv j).symm (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve l L).toProjective)) •
      res _ (show V ≤ ⊤ from le_top) (Scheme.Modules.Hom.app ε.hom ⊤ (1 : Γ(Curve (LaurentSeries l) (TateCurve l L), ⊤))) := by
    rw [frame_res]
    exact chart_normalized_congr _ ε (zLeg l L (Iso.refl _)) j (Category.comp_id _) _ _ hε
  apply cancel_on_chart ε V _ _ _ _ (ht.symm.trans hnε)
  have hp := ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.zP_ne_zero
    (LaurentSeries l) (TateCurve l L)
  have hp' : (2 * WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve l L).toProjective) ≠ 0 := by
    change (2 * WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve l L).toProjective +
      ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries l) (TateCurve l L) 0 *
        WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve l L).toProjective +
      ArithmeticThetaLegendreComparisonR0177.chartScalar (LaurentSeries l) (TateCurve l L) 0) ≠ 0 at hp
    rw [map_zero, zero_mul, add_zero, add_zero] at hp
    exact hp
  simpa only [map_mul, map_ofNat, map_zero] using
    ((chartRingEquiv j).symm.injective.ne hp')

lemma pointed_global {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme} (g : Y ⟶ Spec (CommRingCat.of A))
    (f : X ⟶ Spec (CommRingCat.of B)) (b : X ⟶ Y)
    (hc : IsPullback b f g (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [SmoothOfRelativeDimension 1 g]
    (s : Spec (CommRingCat.of A) ⟶ Y) (t : Spec (CommRingCat.of B) ⟶ X)
    (hpt : t ≫ b = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ s)
    (m : Γ(g.kaehler,⊤)) :
    res _ (V := ⊤) (by simp) ((pointedDifferentialIso g f b hc s t hpt).hom.app _
      (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (res _ (V := ⊤) (by simp) (Scheme.Modules.pullbackLocalSection s m)))) =
    res _ (V := ⊤) (by simp) (Scheme.Modules.pullbackLocalSection t
      (res _ (V := ⊤) (by simp) ((HodgeBaseChange.differentialMap g f b hc.w).app _
        (Scheme.Modules.pullbackLocalSection b m)))) := by
  simp only [res_refl]
  change ((Scheme.Modules.pullback t).map (HodgeBaseChange.differentialMap g f b hc.w)).app _
    ((squarePullbackIso _ s t b hpt.symm g.kaehler).hom.app _
      (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection s m))) = _
  have h := squarePullbackIso_section _ s t b hpt.symm g.kaehler ⊤ m ⊤ (by simp) (by simp)
  simp only [res_refl] at h
  rw [h]
  exact (Scheme.Modules.pullbackLocalSection_app t
    (HodgeBaseChange.differentialMap g f b hc.w) (Scheme.Modules.pullbackLocalSection b m)).symm

end TateHodgeGeneratorTransfer

/-- The canonical pointed differential comparison preserves the entire normalized
Tate generator, for every normalized choice of the two global frames. -/
theorem tate_hodge_generator_transfer :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ),
    3 ≤ L → Even L → ∀ (A : TateLevel k L)
      (b : Curve (LaurentSeries l) (TateCurve l L) ⟶ Curve (LaurentSeries k) (TateCurve k L))
      (hb : CurveMap ι L b), GeneratorCompatible ι A b hb := by
  intro k l _ _ _ _ ι L hL he A b hb δ ε hδ hε
  letI : Algebra (LaurentSeries k) (LaurentSeries l) := (laurentMap ι).toAlgebra
  letI : (TateCurve k L).IsElliptic := A.elliptic
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k L)) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one (TateCurve k L).toProjective
  have h := TateHodgeGeneratorTransfer.pointed_global
    (structureMap (LaurentSeries k) (TateCurve k L))
    (structureMap (LaurentSeries l) (TateCurve l L)) b hb.1
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries k) (TateCurve k L))
    (ArithmeticThetaRelativeKatoR0169.origin (LaurentSeries l) (TateCurve l L)) hb.2.1
    (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve (LaurentSeries k) (TateCurve k L),⊤)))
  rw [TateHodgeGeneratorTransfer.curve_section_transfer k l ι L hL he b hb δ ε hδ hε] at h
  exact h

#print axioms tate_hodge_generator_transfer
end ArithmeticThetaBoundaryConstantsR0235
