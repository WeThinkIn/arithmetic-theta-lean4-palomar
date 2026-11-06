import BoundaryHodgeDefinitionsR0182

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower

open ArithmeticThetaConormalInitialR0162

/-- Multiplication on the associated graded uses the actual residue map. -/
lemma gradeClass_mul {K A : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (ε : A →ₐ[K] K) (n : ℕ) (u : A) (b : ↥(ideal ε ^ n)) :
    gradeClass ε n ⟨u * b.1, Ideal.mul_mem_left _ _ b.2⟩ =
      ε u • gradeClass ε n b := by
  change CartierGradedTensor.gradeQ ε n _ = ε u • CartierGradedTensor.gradeQ ε n b
  rw [← map_smul, ← sub_eq_zero, ← map_sub, CartierGradedTensor.gradeQ_ker]
  change u * b.1 - ε u • b.1 ∈ ideal ε ^ (n+1)
  rw [Algebra.smul_def, ← sub_mul, pow_succ']
  apply Ideal.mul_mem_mul
  · change ε (u - algebraMap K A (ε u)) = 0
    simp
  · exact b.2

/-- A factorization in the local ring determines the full initial tensor,
including its scalar, under the canonical differential comparison. -/
lemma differential_initial_factor {K A : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (ε : A →ₐ[K] K) (n : ℕ)
    (c : DifferentialTensor ε n ≃ₗ[K] Grade ε n) (hc : IsDifferentialPower ε n c)
    (u : A) (a : ideal ε) (b : ↥(ideal ε ^ n)) (hb : b.1 = u * a.1 ^ n) :
    c.symm (gradeClass ε n b) =
      ε u • PiTensorProduct.tprod K (fun _ : Fin n => differentialClass ε a.1) := by
  let ap : ↥(ideal ε ^ n) := ⟨a.1 ^ n, Ideal.pow_mem_pow a.2 n⟩
  have he : c (PiTensorProduct.tprod K (fun _ : Fin n => differentialClass ε a.1)) =
      gradeClass ε n ap := hc (fun _ => a) ap (by simp [ap])
  have hbe : b = ⟨u * ap.1, Ideal.mul_mem_left _ _ ap.2⟩ := Subtype.ext hb
  rw [hbe, gradeClass_mul, map_smul, ← he, c.symm_apply_apply]

lemma pointed_section_general {F : Type} [Field F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (φ : X ⟶ Y)
    (hc : IsPullback φ g f (Spec.map (CommRingCat.ofHom (algebraMap F F))))
    [SmoothOfRelativeDimension 1 f]
    (q : Spec (CommRingCat.of F) ⟶ Y) (p : Spec (CommRingCat.of F) ⟶ X)
    (hp : p ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap F F)) ≫ q)
    (U : Y.Opens) (ω : Γ(f.kaehler, U)) (V : (Spec (CommRingCat.of F)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap F F))) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h₂ : V ≤ p ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₁
      ((pointedDifferentialIso f g φ hc q p hp).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap F F)))
          (Scheme.Modules.pullbackLocalSection q ω))) =
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection p
        ((differentialMap f g φ hc.w).app _ (Scheme.Modules.pullbackLocalSection φ ω))) := by
  change res _ h₁ (((Scheme.Modules.pullback p).map
    (differentialMap f g φ hc.w)).app _
      ((squarePullbackIso _ q p φ hp.symm f.kaehler).hom.app _
        (Scheme.Modules.pullbackLocalSection _ (Scheme.Modules.pullbackLocalSection q ω)))) = _
  rw [hom_res, squarePullbackIso_section _ q p φ hp.symm f.kaehler U ω V h₁ h₂,
    ← hom_res, ← Scheme.Modules.pullbackLocalSection_app]

/-- Global sections transported through a specified geometric pullback isomorphism. -/
def transportSection {X Y : Scheme} (p : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (s : Γ(M,⊤)) : Γ(N,⊤) :=
  res N (by simp) (e.hom.app _ (Scheme.Modules.pullbackLocalSection p s))

lemma transportSection_injective {X Y : Scheme} (p : X ⟶ Y) [IsIso p]
    (M : Y.Modules) (N : X.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ N) :
    Function.Injective (transportSection p M N e) := by
  have hp := Scheme.Modules.bijective_unit_app_of_le_opensRange p M ⊤
    (by simp [Scheme.Hom.opensRange_of_isIso])
  have he := ConcreteCategory.bijective_of_isIso (e.hom.app (p ⁻¹ᵁ ⊤))
  have hr := GlobalFamilyDiscriminantR0180.res_bijective N
    (show (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤ by simp) le_top
  exact (hr.comp (he.comp hp)).1

lemma transportSection_restrict {X Y : Scheme} (p : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (s : Γ(M,⊤))
    (U : Y.Opens) (V : X.Opens) (h : V ≤ p ⁻¹ᵁ U) :
    res N le_top (transportSection p M N e s) =
      res N h (e.hom.app _ (Scheme.Modules.pullbackLocalSection p (res M le_top s))) := by
  unfold transportSection
  rw [InitialHodgeSection.res_res, ← InitialSectionNaturality.pullback_res,
    ← hom_res, InitialHodgeSection.res_res]

lemma transportSection_smul {X Y : Scheme} (p : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (a : Γ(Y,⊤)) (s : Γ(M,⊤)) :
    transportSection p M N e (a • s) =
      p.appLE ⊤ ⊤ (by simp) a • transportSection p M N e s := by
  unfold transportSection
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul]
  rfl

lemma transportSection_tensor {X Y : Scheme} (p : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N) (n : ℕ) (s : Γ(M,⊤)) :
    transportSection p (tensorPower Y M n) (tensorPower X N n)
      (tensorComparison p M N e n) (tensorPowerSection Y M n ⊤ s) =
        tensorPowerSection X N n ⊤ (transportSection p M N e s) := by
  unfold transportSection
  rw [tensorComparison_section]
  exact tensorPowerSection_restrict X N n _ _ _ _

section FrameTransport
open ArithmeticThetaPullback
open ArithmeticThetaCompactifiedDifferentialR0145
variable {F : Type} [Field F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (E : X ≅ Y) (hE : E.hom ≫ f = g)
    [SmoothOfRelativeDimension 1 f]

include hE in
lemma iso_cartesian : IsPullback E.hom g f
    (Spec.map (CommRingCat.ofHom (algebraMap F F))) := by
  simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.of_horiz_isIso ⟨by simpa using hE⟩

def pulledCurveFrame (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ g.kaehler := by
  have hw : E.hom ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)) := by
    simpa using hE
  letI := differentialMap_isIso f g E.hom hw (iso_cartesian f g E hE)
  exact (pullback_unit_iso X Y E.hom).symm ≪≫
    (Scheme.Modules.pullback E.hom).mapIso δ ≪≫ asIso (differentialMap f g E.hom hw)

lemma pulledCurveFrame_one
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) :
    Scheme.Modules.Hom.app (pulledCurveFrame f g E hE δ).hom (E.hom ⁻¹ᵁ U) (1 : Γ(X, E.hom ⁻¹ᵁ U)) =
      (differentialMap f g E.hom (by simpa using hE)).app _
        (Scheme.Modules.pullbackLocalSection E.hom
          (Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y, U)))) := by
  change (differentialMap f g E.hom _).app _
    (((Scheme.Modules.pullback E.hom).map δ.hom).app _
      ((pullback_unit_iso X Y E.hom).inv.app _ (1 : Γ(X, E.hom ⁻¹ᵁ U)))) = _
  have hunit : (pullback_unit_iso X Y E.hom).inv.app (E.hom ⁻¹ᵁ U)
      (1 : Γ(X, E.hom ⁻¹ᵁ U)) =
      Scheme.Modules.pullbackLocalSection E.hom
        (L := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (1 : Γ(Y, U)) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((pullback_unit_iso X Y E.hom).hom.app (E.hom ⁻¹ᵁ U))).1
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply,
      pullback_unit_local_section]
  rw [hunit, ← Scheme.Modules.pullbackLocalSection_app]

lemma pulledCurveFrame_normalized
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) (x y : Γ(Y,U))
    (hn : relativeD f U x = (2*y) • Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y,U))) :
    relativeD g (E.hom ⁻¹ᵁ U) (E.hom.app U x) =
      (2 * E.hom.app U y) •
        Scheme.Modules.Hom.app (pulledCurveFrame f g E hE δ).hom _ (1 : Γ(X,E.hom ⁻¹ᵁ U)) := by
  rw [← differentialMap_D f g E.hom (by simpa using hE), hn,
    Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    pulledCurveFrame_one]
  congr 1
  exact (E.hom.app U).hom.map_mul 2 y |>.trans (by rw [map_ofNat])

lemma pulledCurveFrame_normalized_on
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) (x y : Γ(Y,U))
    (hn : relativeD f U x = (2*y) • Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y,U)))
    (V : X.Opens) (hV : V ≤ E.hom ⁻¹ᵁ U) :
    relativeD g V (E.hom.appLE U V hV x) =
      (2 * E.hom.appLE U V hV y) •
        Scheme.Modules.Hom.app (pulledCurveFrame f g E hE δ).hom V (1 : Γ(X,V)) := by
  have hh := GlobalNormalizedDifferential.relativeD_normalization_restrict g
    (E.hom ⁻¹ᵁ U) hV _ _ _ (pulledCurveFrame_normalized f g E hE δ U x y hn)
  erw [map_mul, map_ofNat, GlobalNormalizedDifferential.frame_section_restrict] at hh
  exact hh

variable (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of F) ⟶ Y)
    (hp : p ≫ E.hom = q)

/-- The canonical pointed comparison acts on every local differential section,
not only on exact differentials. -/
lemma pointed_iso_section (U : Y.Opens) (ω : Γ(f.kaehler, U))
    (V : (Spec (CommRingCat.of F)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap F F))) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h₂ : V ≤ p ⁻¹ᵁ (E.hom ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₁
      ((pointedDifferentialIso f g E.hom (iso_cartesian f g E hE) q p
        (by simpa using hp)).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap F F)))
          (Scheme.Modules.pullbackLocalSection q ω))) =
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection p
        ((differentialMap f g E.hom (by simpa using hE)).app _
          (Scheme.Modules.pullbackLocalSection E.hom ω))) := by
  exact pointed_section_general f g E.hom (iso_cartesian f g E hE) q p
    (by simpa using hp) U ω V h₁ h₂

lemma pointed_iso_curve_frame
    (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler)
    (U : Y.Opens) (V : (Spec (CommRingCat.of F)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap F F))) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h₂ : V ≤ p ⁻¹ᵁ (E.hom ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₁
      ((pointedDifferentialIso f g E.hom (iso_cartesian f g E hE) q p
        (by simpa using hp)).hom.app _
        (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap F F)))
          (Scheme.Modules.pullbackLocalSection q (Scheme.Modules.Hom.app δ.hom U (1 : Γ(Y,U)))))) =
    res ((Scheme.Modules.pullback p).obj g.kaehler) h₂
      (Scheme.Modules.pullbackLocalSection p
        (Scheme.Modules.Hom.app (pulledCurveFrame f g E hE δ).hom
          (E.hom ⁻¹ᵁ U) (1 : Γ(X,E.hom ⁻¹ᵁ U)))) := by
  rw [pointed_iso_section f g E hE p q hp, pulledCurveFrame_one f g E hE]

end FrameTransport

open NeronModelInfra WeierstrassProjModel
open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw in
lemma transported_schemeNsmul {F : Type} [CommRing F] {X Y : Scheme}
    {f : X ⟶ Spec (CommRingCat.of F)} {g : Y ⟶ Spec (CommRingCat.of F)}
    (E : X ≅ Y) (hE : E.hom ≫ g = f) (G : RelativeGroupLaw F g) (n : ℕ) :
    (transport E hE G).schemeNsmul n ≫ E.hom = E.hom ≫ G.schemeNsmul n := by
  have h := congrArg Subtype.val
    (ArithmeticThetaTateCuspsR0181.TateFullLevelMarking.transport_nsmul
      E hE G f n RelativeGroupLaw.idPoint)
  have hn := congrArg Subtype.val
    (G.nsmul_natural g f E.hom hE n RelativeGroupLaw.idPoint)
  exact h.trans (by simpa [pointsEquiv, WeierstrassProjModel.schemeHomOverComp, RelativeGroupLaw.schemeNsmul] using hn.symm)


open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential in
lemma chartSection_pullback {X Y : Scheme} {B : Type} [CommRing B]
    (f : X ⟶ Y) (i : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = i) (h : j ''ᵁ ⊤ ≤ f ⁻¹ᵁ (i ''ᵁ ⊤)) (a : B) :
    f.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) h ((chartRingEquiv i).symm a) =
      (chartRingEquiv j).symm a := by
  apply (chartRingEquiv j).injective
  rw [RingEquiv.apply_symm_apply]
  have hmaps : f.appLE (i ''ᵁ ⊤) (j ''ᵁ ⊤) h ≫ (j.appIso ⊤).hom =
      (i.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom',
      Scheme.Hom.appLE_comp_appLE]
    cases hj
    rfl
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((j.appIso ⊤).hom (f.appLE _ _ h ((chartRingEquiv i).symm a))) = a
  have hv := ConcreteCategory.congr_hom hmaps ((chartRingEquiv i).symm a)
  exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom hv).trans
    ((chartRingEquiv i).apply_symm_apply a)


variable (k : Type) [Field k] [CharZero k] (L : ℕ)
variable {D : LevelData k L}

open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential

/-- The affine normalization survives pullback along the SAME cubic isomorphism. -/
lemma normalized_pulled_tate_frame {X : Scheme}
    (f : X ⟶ Puncture k) (E : X ≅ projectiveCurve k L)
    (hE : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k L) = f)
    [SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k L))]
    (δ : CurveFrame k L) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ) :
    relativeD f (zOpen k L E)
        (zSection k L E (WeierstrassCurve.DrinfeldGlobal.xOverZ (TateCurve k L).toProjective)) =
      (2 * zSection k L E (WeierstrassCurve.DrinfeldGlobal.yOverZ (TateCurve k L).toProjective)) •
        Scheme.Modules.Hom.app
          (pulledCurveFrame (structureMap (LaurentSeries k) (TateCurve k L)) f E hE δ).hom
          (zOpen k L E) (1 : Γ(X,zOpen k L E)) := by
  let i := zLeg k L (Iso.refl (projectiveCurve k L))
  let j := zLeg k L E
  have hj : j ≫ E.hom = i := by simp [i, j, zLeg]
  have h : zOpen k L E ≤ E.hom ⁻¹ᵁ zOpen k L (Iso.refl (projectiveCurve k L)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (congrArg (fun q => q x) hj).symm⟩
  have hh := pulledCurveFrame_normalized_on
    (structureMap (LaurentSeries k) (TateCurve k L)) f E hE δ _ _ _ hδ _ h
  change relativeD f (zOpen k L E)
      (E.hom.appLE _ _ h ((chartRingEquiv i).symm _)) = _ at hh
  rw [chartSection_pullback E.hom i j hj h] at hh
  change _ = (2 * E.hom.appLE _ _ h ((chartRingEquiv i).symm _)) • _ at hh
  rw [chartSection_pullback E.hom i j hj h] at hh
  exact hh


/-- The normal-affine test is induced by the specified classifying map. -/
def affineTest (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D) :
    ArithmeticThetaOpenHodgeR0180.Test D.atlas.quotient.ring D.atlas.descent.family
      (LaurentSeries k) (TateCurve k L) T.level.law := by
  let ι : D.atlas.quotient.ring →+* LaurentSeries k :=
    (Spec.preimage (T.base ≫ D.quotient.inclusion)).hom
  have hmap : baseMap D.atlas.quotient.ring (LaurentSeries k) ι =
      T.base ≫ D.quotient.inclusion := Spec.map_preimage _
  exact { scalar := ι, map := T.map
          cartesian := by rw [hmap]; exact T.classifies.2.1
          origin_eq := by rw [hmap]; exact T.classifies.2.2.1
          nsmul_eq := T.nsmul_eq }

/-- Equality transport of the base map commutes with the canonical tensor
comparison. This applies to arbitrary sections, not just pure powers. -/
lemma tensorComparison_change_map {X Y : Scheme} (p q : X ⟶ Y) (h : p = q)
    (H : Y.Modules) (K : X.Modules)
    (e : (Scheme.Modules.pullback q).obj H ≅ K) (n : ℕ)
    (s : Γ(tensorPower Y H n, ⊤)) :
    res _ (V := ⊤) (by simp) ((tensorComparison p H K (pullbackEqIso h H ≪≫ e) n).hom.app _
      (Scheme.Modules.pullbackLocalSection p s)) =
    res _ (V := ⊤) (by simp) ((tensorComparison q H K e n).hom.app _
      (Scheme.Modules.pullbackLocalSection q s)) := by
  subst q
  rfl

lemma pullAmbientPower_eq_pullSection (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    (n : ℕ) (s : Γ(power D.atlas.descent.family n, ⊤)) :
    pullAmbientPower k L T n s = pullSection (affineTest k L T) n s := by
  exact tensorComparison_change_map _ _ (Spec.map_preimage _).symm _ _
    (comparison (affineTest k L T)) n s

/-- The pullback has the intrinsic initial-term characterization on the SAME
Tate cubic, for every normalized five-Kato function on that cubic. -/
lemma pullAmbientPower_represents (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    [IsIntegral (Curve (LaurentSeries k) (TateCurve k L))]
    [IsLocallyNoetherian (Curve (LaurentSeries k) (TateCurve k L))]
    [IsIntegral (GenericCurve (LaurentSeries k) (TateCurve k L))]
    [IsLocallyNoetherian (GenericCurve (LaurentSeries k) (TateCurve k L))]
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d)
    (g : (Curve (LaurentSeries k) (TateCurve k L)).functionField)
    (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized (LaurentSeries k) (TateCurve k L) T.level.law 5 g) :
    RepresentsInitial (LaurentSeries k) (TateCurve k L) T.level.law 5 g
      (pullAmbientPower k L T 24 d) := by
  letI := T.level.elliptic
  rw [pullAmbientPower_eq_pullSection]
  exact hd.2 (LaurentSeries k) (TateCurve k L) T.level.law T.level.originLaw
    (affineTest k L T) g hg

/-- The transported section is exactly the canonical intrinsic local section,
with no undetermined unit and independently of the full-level marking. -/
lemma pullAmbientPower_eq_localD (T : ArithmeticThetaBoundaryHodgeR0182.Test k L D)
    [IsIntegral (Curve (LaurentSeries k) (TateCurve k L))]
    [IsLocallyNoetherian (Curve (LaurentSeries k) (TateCurve k L))]
    [IsIntegral (GenericCurve (LaurentSeries k) (TateCurve k L))]
    [IsLocallyNoetherian (GenericCurve (LaurentSeries k) (TateCurve k L))]
    (d : Γ(power D.atlas.descent.family 24, ⊤)) (hd : IsD2 D.atlas.descent.family d) :
    letI := T.level.elliptic
    pullAmbientPower k L T 24 d =
      GlobalFamilyDiscriminantR0180.localD (LaurentSeries k) (TateCurve k L)
        T.level.law T.level.originLaw := by
  letI := T.level.elliptic
  apply (GlobalFamilyDiscriminantR0180.local_discriminant_exists
    (LaurentSeries k) (TateCurve k L) T.level.law T.level.originLaw).unique
  · constructor
    · rw [pullAmbientPower_eq_pullSection]
      exact GlobalFamilyDiscriminantR0180.pullSection_frame (affineTest k L T) 24 d hd.1
    · intro g hg
      exact pullAmbientPower_represents k L T d hd g hg
  · exact (GlobalFamilyDiscriminantR0180.local_discriminant_exists
      (LaurentSeries k) (TateCurve k L) T.level.law T.level.originLaw).exists.choose_spec

section ModelInitial
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaHodgeInitialR0163.OriginHodgeComparisonR0163
open ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149
attribute [local instance] ArithmeticThetaHodgeInitialR0163.sectionModule

variable {r : ℕ} {hr : 0 < r}
    {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
    (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (genericScheme k M)]

open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144

/-- Chart normalization of the pulled differential gives the global cleared
normalization required by the accepted Tate-model expansion theorem. -/
lemma model_pulled_frame_normalized (h3 : 3 ≤ r) (hM : IsModel k T M)
    (hsM : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) (hc : IsChartIso k r c)
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : IsCompactificationIso k M s hs a c E)
    [SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) (TateCurve k r))]
    (δ : CurveFrame k r) (hδ : ArithmeticThetaBoundaryHodgeR0182.Normalized k r δ) :
    IsGlobalDifferentialFrame k M s X Y
      (pulledCurveFrame (structureMap (LaurentSeries k) (TateCurve k r))
        (genericStructure k M) E hE.1 δ) := by
  let e := pulledCurveFrame (structureMap (LaurentSeries k) (TateCurve k r))
    (genericStructure k M) E hE.1 δ
  apply global_cleared k h3 M hM s hsM X Y e
  have hn := normalized_pulled_tate_frame k r (genericStructure k M) E hE.1 δ hδ
  have h := relativeD_normalization_restrict (genericStructure k M) (zOpen k r E)
    (complement_z_le k M s hs a c E hE) _ _ _ hn
  erw [map_mul, map_ofNat, frame_section_restrict (genericStructure k M) e (zOpen k r E)
    (complement k M s) (complement_z_le k M s hs a c E hE)] at h
  have hx := complement_chart_coordinate k M s hs X Y a ha c hc E hE false
  have hy := complement_chart_coordinate k M s hs X Y a ha c hc E hE true
  simp only [Bool.false_eq_true, ↓reduceIte, degree] at hx hy
  erw [hx,hy] at h
  exact h

/-- The accepted stalk-based initial tensor has the expected local-section
formula for every factorization, with the scalar evaluated at the actual origin. -/
lemma geometric_initial_local_formula
    (g : (genericScheme k M).functionField)
    (d : Γ(ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs 24, ⊤))
    (hd : ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs g d)
    (U : (genericScheme k M).Opens)
    (hx : genericPoint k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
    (u a : Γ(genericScheme k M, U))
    (ha : Scheme.stalkClosedPointTo (genericPoint k M s hs)
      ((genericScheme k M).presheaf.germ U _ hx a) = 0)
    (hf : letI : Nonempty U := ⟨⟨_, hx⟩⟩
      (5 : (genericScheme k M).functionField) * g =
        (genericScheme k M).germToFunctionField U (u * a ^ 24)) :
    res (ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs 24) le_top d =
      (genericPoint k M s hs).app U u •
        tensorPowerSection (Puncture k)
          (ArithmeticThetaHodgeFourTorsionR0147.Hodge k M s hs) 24
          (genericPoint k M s hs ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection (genericPoint k M s hs)
            (relativeD (genericStructure k M) U a)) := by
  letI : Algebra (LaurentSeries k) (OriginStalk k M s hs) :=
    (ArithmeticThetaConormalInitialR0162.originScalar k M s hs).toAlgebra
  letI : Module (LaurentSeries k) (OriginStalk k M s hs) :=
    @Algebra.toModule _ _ _ _
      (ArithmeticThetaConormalInitialR0162.originScalar k M s hs).toAlgebra
  letI : Nonempty U := ⟨⟨_, hx⟩⟩
  obtain ⟨ε, κ, c, e, v, b, hact, hc, he, hv, hb, hd⟩ := hd
  let germ := (genericScheme k M).presheaf.germ U _ hx
  have ha' : ε (germ a) = 0 := by
    change ε.toRingHom (germ a) = 0
    rw [hact.1]
    exact ha
  let ap : ideal ε := ⟨germ a, ha'⟩
  have hbf : b.1 = germ u * (germ a) ^ 24 := by
    apply IsFractionRing.injective (OriginStalk k M s hs) (genericScheme k M).functionField
    rw [hb, hf]
    change (genericScheme k M).germToFunctionField U (u * a ^ 24) =
      algebraMap (OriginStalk k M s hs) (genericScheme k M).functionField
        (germ.hom u * (germ.hom a) ^ 24)
    rw [← map_pow, ← map_mul]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := genericScheme k M)
      hx (u * a ^ 24)).symm
  have heq := differential_initial_factor ε 24 c hc (germ u) ap b hbf
  rw [hd, heq, map_smul, map_smul, PiTensorProduct.map_tprod, hv]
  change res _ le_top
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv (ε (germ u)) •
        tensorPowerSection _ _ 24 ⊤ (e (differentialClass ε (germ a)))) = _
  rw [InitialHodgeSection.res_smul]
  change _ • (ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs 24).presheaf.map
      (homOfLE le_top).op (tensorPowerSection _ _ 24 ⊤ _) = _
  rw [tensorPowerSection_restrict, he U hx a]
  congr 1
  have hscalar := evaluated_germ (genericPoint k M s hs) U hx u
  have heval : ε (germ u) = Scheme.stalkClosedPointTo (genericPoint k M s hs) (germ u) :=
    RingHom.congr_fun hact.1 (germ u)
  rw [heval, hscalar]
  exact restrict_topSection
    (L := (SheafOfModules.unit (Puncture k).ringCatSheaf : (Puncture k).Modules))
    (Scheme.preimage_eq_top_of_closedPoint_mem (genericPoint k M s hs) hx) _

open ArithmeticThetaGeometricNormR0150 ArithmeticThetaKatoExistenceR0151

/-- Pulling the normalized function through the actual projective model
isomorphism preserves its full divisor and every coprime multiplication norm. -/
lemma normalized_kato_to_model
    [IsLocallyNoetherian (genericScheme k M)]
    [SmoothOfRelativeDimension 1 (genericStructure k M)]
    (W : WeierstrassCurve (LaurentSeries k)) [W.IsElliptic]
    [IsIntegral (Curve (LaurentSeries k) W)]
    [IsLocallyNoetherian (Curve (LaurentSeries k) W)]
    [IsIntegral (GenericCurve (LaurentSeries k) W)]
    [IsLocallyNoetherian (GenericCurve (LaurentSeries k) W)]
    (H : ArithmeticThetaRelativeKatoR0169.Law (LaurentSeries k) W)
    (hH : ArithmeticThetaRelativeKatoR0169.IsOriginLaw (LaurentSeries k) W H)
    (G : ArithmeticThetaMarkedGroupLawR0146.Law k M)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) W)
    (hE : E.hom ≫ structureMap (LaurentSeries k) W = genericStructure k M)
    (hO : genericPoint k M s hs ≫ E.hom = origin (LaurentSeries k) W)
    (hN : ∀ n, G.schemeNsmul n ≫ E.hom = E.hom ≫ H.schemeNsmul n)
    (α : (Curve (LaurentSeries k) W).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap E.hom α) (c : ℕ) (hc : 0 < c)
    (g : (Curve (LaurentSeries k) W).functionField)
    (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized (LaurentSeries k) W H c g) :
    ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs G c (α g) := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  letI : SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) W) :=
    (relative_curve_geometry (LaurentSeries k) W).2.2.2.2.2.1
  have hg' := RelativeKatoFiberSpecialization.relative_isKato_over_field
    (LaurentSeries k) W H hH c hc g hg.1
  have hb : IsPullback E.hom (genericStructure k M) (structureMap (LaurentSeries k) W)
      (Spec.map (CommRingCat.ofHom (RingHom.id (LaurentSeries k)))) := by
    simp only [show CommRingCat.ofHom (RingHom.id (LaurentSeries k)) = 𝟙 _ from rfl,
      Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa using hE⟩
  have ho : ∀ x : genericScheme k M,
      E.hom x = ArithmeticThetaGeneralEllipticKatoR0168.originPoint (LaurentSeries k) W ↔
        x = identityPoint k M s hs := by
    intro x
    have he : E.hom (identityPoint k M s hs) =
        ArithmeticThetaGeneralEllipticKatoR0168.originPoint (LaurentSeries k) W :=
      congrArg (fun f => f (IsLocalRing.closedPoint (LaurentSeries k))) hO
    rw [← he]
    exact (Scheme.homeoOfIso E).injective.eq_iff
  refine ⟨⟨DivisorFieldBaseChange.map_ne_zero α hg'.1.1, ?_⟩, ?_⟩
  · intro x
    rw [DivisorFieldBaseChange.basechange_order
      (X := genericScheme k M) (Y := Curve (LaurentSeries k) W) (LaurentSeries k) (LaurentSeries k)
      (structureMap (LaurentSeries k) W) (genericStructure k M)
      (RingHom.id _) E.hom hb α hα g hg'.1.1 x, hg'.1.2]
    have hm : H.schemeNsmul c (E.hom x) = E.hom (G.schemeNsmul c x) :=
      (congrArg (fun f => f x) (hN c)).symm
    classical
    simp only [ArithmeticThetaGeneralEllipticKatoR0168.katoOrder,
      ArithmeticThetaGeometricNormR0150.katoOrder, hm, ho]
    rfl
  · intro n hn hcn φm hφm
    obtain ⟨hfinite, hetale, hsurj, _, φ, hφ, _⟩ :=
      ArithmeticThetaGeneralEllipticKatoR0168.general_multiplication_degree
        (LaurentSeries k) W H hH n hn
    letI := hfinite
    letI := hetale
    letI := hsurj
    have hcart : IsPullback E.hom (G.schemeNsmul n) (H.schemeNsmul n) E.hom :=
      ActualKatoFieldBaseChange.endomorphism_cartesian
        (structureMap (LaurentSeries k) W) (genericStructure k M) E.hom
        (Spec.map (CommRingCat.ofHom (RingHom.id (LaurentSeries k)))) hb
        (H.schemeNsmul n) (G.schemeNsmul n)
        (H.schemeNsmul_over n) (G.schemeNsmul_over n) (hN n)
    have hnorm := geometric_norm_base_change
      (Curve (LaurentSeries k) W) (Curve (LaurentSeries k) W)
      (genericScheme k M) (genericScheme k M) _ _ _ _ hcart
      φ φm α α hφ hφm hα hα g
    rw [hg'.2 n hn hcn φ hφ] at hnorm
    exact hnorm.symm

end ModelInitial

#print axioms differential_initial_factor
#print axioms pointed_section_general
#print axioms transportSection_injective
#print axioms pointed_iso_curve_frame
#print axioms transported_schemeNsmul
#print axioms model_pulled_frame_normalized
#print axioms geometric_initial_local_formula
#print axioms normalized_kato_to_model
#print axioms pullAmbientPower_eq_pullSection
#print axioms pullAmbientPower_represents
#print axioms pullAmbientPower_eq_localD

end ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

namespace ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaCompactifiedDifferentialR0145
section
variable {F : Type} [Field F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (E : X ≅ Y) (hE : E.hom ≫ f = g)
    [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of F) ⟶ Y)
    (hp : p ≫ E.hom = q)

abbrev pointedIso := pointedDifferentialIso f g E.hom (iso_cartesian f g E hE) q p (by simpa using hp)

lemma pointed_power_value (n : ℕ) (U : Y.Opens) (u a : Γ(Y,U))
    (V : (Spec (CommRingCat.of F)).Opens)
    (h₁ : V ≤ (Spec.map (CommRingCat.ofHom (algebraMap F F))) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h₂ : V ≤ p ⁻¹ᵁ (E.hom ⁻¹ᵁ U)) :
    res _ h₁ ((tensorComparison _ _ _ (pointedIso f g E hE p q hp) n).hom.app _
      (Scheme.Modules.pullbackLocalSection (Spec.map (CommRingCat.ofHom (algebraMap F F)))
        (q.app U u • tensorPowerSection _ _ n (q ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection q (relativeD f U a))))) =
    res _ h₂ ((p.app (E.hom ⁻¹ᵁ U) (E.hom.app U u)) •
      tensorPowerSection _ _ n (p ⁻¹ᵁ (E.hom ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection p (relativeD g (E.hom ⁻¹ᵁ U) (E.hom.app U a)))) := by
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul, InitialHodgeSection.res_smul, tensorComparison_section]
  congr 1
  · have he : q.appLE U (q ⁻¹ᵁ U) le_rfl ≫
        (Spec.map (CommRingCat.ofHom (algebraMap F F))).appLE (q ⁻¹ᵁ U) V h₁ =
        E.hom.appLE U (E.hom ⁻¹ᵁ U) le_rfl ≫ p.appLE (E.hom ⁻¹ᵁ U) V h₂ := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
        Category.id_comp, hp]
    simpa only [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE, ConcreteCategory.comp_apply, homOfLE_refl, op_id, (Spec (CommRingCat.of F)).presheaf.map_id, X.presheaf.map_id, ConcreteCategory.id_apply] using ConcreteCategory.congr_hom he u
  · change (tensorPower _ _ n).presheaf.map (homOfLE h₁).op _ =
      (tensorPower _ _ n).presheaf.map (homOfLE h₂).op _
    rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
    congr 1
    exact pointedDifferentialIso_D f g E.hom (iso_cartesian f g E hE) q p
      (by simpa using hp) U a V h₁ h₂
end
end ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

namespace ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaHodgeInitialR0163.OriginHodgeComparisonR0163
variable (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r}
    {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
    (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _)
    [IsIntegral (genericScheme k M)]
    (W : WeierstrassCurve (LaurentSeries k)) [W.IsElliptic]
    [IsIntegral (Curve (LaurentSeries k) W)]
    [IsLocallyNoetherian (Curve (LaurentSeries k) W)]
    [IsIntegral (GenericCurve (LaurentSeries k) W)]
    [IsLocallyNoetherian (GenericCurve (LaurentSeries k) W)]
    (H : Law (LaurentSeries k) W) (hH : IsOriginLaw (LaurentSeries k) W H)
    (E : genericScheme k M ≅ Curve (LaurentSeries k) W)
    (hE : E.hom ≫ structureMap (LaurentSeries k) W = genericStructure k M)
    (hO : genericPoint k M s hs ≫ E.hom = origin (LaurentSeries k) W)
    [SmoothOfRelativeDimension 1 (structureMap (LaurentSeries k) W)]
    (α : (Curve (LaurentSeries k) W).functionField →+* (genericScheme k M).functionField)
    (hα : IsFieldMap E.hom α)

include hH hα in
lemma initial_section_comparison
    (g : (Curve (LaurentSeries k) W).functionField)
    (d : Γ(HodgePower (LaurentSeries k) W 24,⊤))
    (hd : RepresentsInitial (LaurentSeries k) W H 5 g d)
    (dm : Γ(ArithmeticThetaHodgeInitialR0163.HodgePower k M s hs 24,⊤))
    (hm : ArithmeticThetaHodgeInitialR0163.RepresentsInitial k M s hs (α g) dm) :
    transportSection (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k))))
      _ _ (tensorComparison _ _ _ (pointedIso _ _ E hE _ _ hO) 24) d = dm := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨U,a,hx,ha⟩ := relative_identity_torsion_neighborhood
    (LaurentSeries k) W H hH 5 (by norm_num) (IsLocalRing.closedPoint (LaurentSeries k))
  letI : Nonempty U.1 := ⟨⟨_,hx⟩⟩
  have hx' : genericPoint k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ E.hom ⁻¹ᵁ U.1 := by
    change (genericPoint k M s hs ≫ E.hom) _ ∈ U.1
    rw [hO]
    exact hx
  letI : Nonempty (E.hom ⁻¹ᵁ U.1) := ⟨⟨_,hx'⟩⟩
  obtain ⟨u,hu,hdu⟩ := hd U a ha
  have hpoint : genericPoint k M s hs ⁻¹ᵁ (E.hom ⁻¹ᵁ U.1) = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem _ hx'
  have hv : (genericPoint k M s hs).app (E.hom ⁻¹ᵁ U.1) (E.hom.app U.1 a) = 0 := by
    have heq := InitialSectionNaturality.scalar_square
      (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k))))
      (origin (LaurentSeries k) W) (genericPoint k M s hs) E.hom (by simpa using hO)
      U.1 (E.hom ⁻¹ᵁ U.1) le_rfl
      (show genericPoint k M s hs ⁻¹ᵁ (E.hom ⁻¹ᵁ U.1) ≤
        _ ⁻¹ᵁ (origin (LaurentSeries k) W ⁻¹ᵁ U.1) from by
        simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
          Scheme.Hom.id_preimage]; intro x hx; change (genericPoint k M s hs ≫ E.hom) x ∈ U.1 at hx; rwa [hO] at hx) a
    rw [InitialHodgeSection.generator_vanishes (LaurentSeries k) W U a ha.2.1, map_zero] at heq
    simpa only [Scheme.Hom.appLE_eq_app] using heq.symm
  have hv' : Scheme.stalkClosedPointTo (genericPoint k M s hs)
      ((genericScheme k M).presheaf.germ _ _ hx' (E.hom.app U.1 a)) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv).1
    rw [evaluated_germ, hv, map_zero]
    exact (map_zero (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom).symm
  have hf : (5 : (genericScheme k M).functionField) * α g =
      (genericScheme k M).germToFunctionField (E.hom ⁻¹ᵁ U.1)
        (E.hom.app U.1 (u : _) * (E.hom.app U.1 a)^24) := by
    have heq := RelativeKatoArbitraryBaseChange.section_field_square E.hom α hα
      U.1 (E.hom ⁻¹ᵁ U.1) le_rfl ((u : _) * a^24)
    change _ = α ((Curve (LaurentSeries k) W).germToFunctionField U.1 ((u : _) * a^(5^2-1))) at heq
    rw [← hu] at heq
    simpa only [Scheme.Hom.appLE_eq_app, map_mul, map_pow, map_natCast, map_ofNat, Nat.cast_ofNat] using heq.symm
  have hdm := geometric_initial_local_formula k M s hs (α g) dm hm
    (E.hom ⁻¹ᵁ U.1) hx' (E.hom.app U.1 (u : _)) (E.hom.app U.1 a) hv' hf
  apply restrict_injective _ hpoint
  change res _ le_top _ = res _ le_top dm
  rw [hdm]
  have hle : genericPoint k M s hs ⁻¹ᵁ (E.hom ⁻¹ᵁ U.1) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k)))) ⁻¹ᵁ
        (origin (LaurentSeries k) W ⁻¹ᵁ U.1) := by
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Scheme.Hom.id_preimage]
    intro x hx
    change (genericPoint k M s hs ≫ E.hom) x ∈ U.1 at hx
    rwa [hO] at hx
  rw [transportSection_restrict _ _ _ _ d _ _ hle]
  change res (HodgePower (LaurentSeries k) W 24) le_top d = _ at hdu
  rw [hdu]
  exact (pointed_power_value _ _ E hE _ _ hO 24 U.1 (u : _) a _ hle le_rfl).trans
    (InitialHodgeSection.res_self _ _)
end ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

namespace ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaHodgeInitialR0163.OriginHodgeComparisonR0163
open ArithmeticThetaIntegralHodgeR0149.NormalizedIntegralHodgeFrameR0149
variable {F : Type} [Field F] {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of F)) (g : X ⟶ Spec (CommRingCat.of F))
    (E : X ≅ Y) (hE : E.hom ≫ f = g)
    [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of F) ⟶ X) (q : Spec (CommRingCat.of F) ⟶ Y)
    (hp : p ≫ E.hom = q)

def pointGenerator (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    Γ((Scheme.Modules.pullback q).obj f.kaehler,⊤) :=
  res _ (by simp) (Scheme.Modules.pullbackLocalSection q (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))))

lemma transport_pointGenerator (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    transportSection (Spec.map (CommRingCat.ofHom (algebraMap F F)))
      _ _ (pointedIso f g E hE p q hp) (pointGenerator f q δ) =
      pointGenerator g p (pulledCurveFrame f g E hE δ) := by
  have hg : pointGenerator f q δ = Scheme.Modules.pullbackLocalSection q
      (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))) := InitialHodgeSection.res_self _ _
  rw [hg]
  exact pointed_iso_curve_frame f g E hE p q hp δ ⊤ ⊤ (by simp) (by simp)

omit [SmoothOfRelativeDimension 1 f] in
lemma pointGenerator_frame (δ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ f.kaehler) :
    pointGenerator f q δ = frameSections (pointFrame f δ q) 1 := by
  have hg : pointGenerator f q δ = Scheme.Modules.pullbackLocalSection q
      (Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Y,⊤))) := InitialHodgeSection.res_self _ _
  rw [hg]
  change _ = Scheme.Modules.Hom.app (pointFrame f δ q).hom ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv 1)
  rw [map_one (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom]
  exact (pullFrame_one q δ.hom).symm
end ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

namespace ArithmeticThetaBoundaryHodgeR0182
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaGeometricNormR0150
open ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaOpenHodgeR0180 OpenDiscriminantFullTateExpansionR0182

/-- Exact full Tate expansion of the same intrinsic open discriminant under
 every enriched classifying map and its normalized differential. -/
theorem open_discriminant_full_tate_expansion :
    ∀ (k : Type) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L)
      (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L),
      ∀ (V : Test k L D) (d : (power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤)),
      IsD2 D.atlas.descent.family d → ExactD2 k L V d := by
  intro k _ _ L hL heven D V d hd
  letI := V.level.elliptic
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  have geom := relative_curve_geometry (LaurentSeries k) (TateCurve k L)
  letI := geom.1
  letI := geom.2.1
  letI := geom.2.2.2.1
  letI := geom.2.2.2.2.1
  letI := geom.2.2.2.2.2.1
  have hpos : 0 < L := by omega
  obtain ⟨T, M, hM⟩ := TateFullLevelMarking.model_exists k L hL hpos
  obtain ⟨s, hs, _⟩ := marked_section_algebraization k L hpos hL T M hM (zeroIndex L hpos) 1
  obtain ⟨X, hX, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs false
  obtain ⟨Y, hY, _⟩ := algebraic_tate_coordinates k L hpos hL T M hM s hs true
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k L hpos hL T heven M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k L
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k L hpos hL T heven M hM s hs X Y hX hY a ha c hc
  letI := GenericAffineCubicIsomorphismR0144.generic_integral k hL M hM
  letI := GenericAffineCubicIsomorphismR0144.generic_relative_one k hL M hM s hs
  letI : IsLocallyNoetherian (genericScheme k M) := LocallyOfFiniteType.isLocallyNoetherian (genericStructure k M)
  have hEs : E.hom ≫ structureMap (LaurentSeries k) (TateCurve k L) = genericStructure k M := hE.1
  have hOs : genericPoint k M s hs.1 ≫ E.hom = origin (LaurentSeries k) (TateCurve k L) := hE.2.2
  let G : ArithmeticThetaMarkedGroupLawR0146.Law k M := ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.transport E hEs V.level.law
  have hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G := by
    constructor
    · intro S t
      apply Subtype.ext
      change (V.level.law.one t).val ≫ E.inv = t ≫ genericPoint k M s hs.1
      rw [V.level.originLaw.1]
      change (t ≫ origin (LaurentSeries k) (TateCurve k L)) ≫ E.inv = _
      rw [← hOs]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro S t x y
      change (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (V.level.law.mul t _ _) =
        (ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw.pointsEquiv E hEs t).symm
        (V.level.law.mul t _ _)
      rw [V.level.originLaw.2]
  obtain ⟨α,hα⟩ := ActualMultiplicationFieldNorm.exists_fieldMap E.hom
  obtain ⟨g,hg⟩ := GlobalFamilyDiscriminantR0180.normalized_exists
    (LaurentSeries k) (TateCurve k L) V.level.law V.level.originLaw 5 (by norm_num) (by norm_num)
  have hgm := normalized_kato_to_model k M s hs.1 (TateCurve k L)
    V.level.law V.level.originLaw G E hEs hOs
    (fun n => transported_schemeNsmul E hEs V.level.law n) α hα 5 (by norm_num) g hg
  obtain ⟨dm,hm,_,hex⟩ := ArithmeticThetaHodgeInitialR0163.geometric_discriminant_hodge
    k L hpos hL heven T M hM s hs G hG X Y hX hY (α g) hgm
  let e := pointedIso _ _ E hEs (genericPoint k M s hs.1) _ hOs
  let p := Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries k) (LaurentSeries k)))
  letI : IsIso p := by
    dsimp only [p]
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  let δm : ArithmeticThetaHodgeFourTorsionR0147.Frame k M := pulledCurveFrame _ _ E hEs V.differential
  have hnorm := model_pulled_frame_normalized k M s hs.1 hL hM hs X Y a ha c hc E hE
    V.differential V.normalized
  have heq := initial_section_comparison k M s hs.1 (TateCurve k L) V.level.law V.level.originLaw
    E hEs hOs α hα g (pullAmbientPower k L V 24 d)
    (pullAmbientPower_represents k L V d hd g hg) dm hm
  unfold ExactD2
  apply transportSection_injective p _ _ (tensorComparison p _ _ e 24)
  change transportSection p _ _ (tensorComparison p _ _ e 24) (pullAmbientPower k L V 24 d) = _
  rw [heq]
  rw [transportSection_smul, transportSection_tensor]
  have hgen := (transport_pointGenerator _ _ E hEs (genericPoint k M s hs.1) _
    hOs V.differential).trans
      (pointGenerator_frame (genericStructure k M) (genericPoint k M s hs.1) δm)
  change transportSection p _ _ e (hodgeGenerator k L V.differential) =
    ArithmeticThetaHodgeFourTorsionR0147.hodgeSection k M s hs.1 δm 1 at hgen
  rw [hgen]
  have hscalar : p.appLE ⊤ ⊤ (by simp)
      (scalar (LaurentSeries k) (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv
        (ArithmeticThetaUnaryKatoPowerR0160.discriminant k L) := by
    have hp : p = 𝟙 _ := by
      dsimp only [p]
      simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [hp]
    erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
    rfl
  rw [hscalar]
  exact (hex δm hnorm).2

#print axioms open_discriminant_full_tate_expansion
end ArithmeticThetaBoundaryHodgeR0182
