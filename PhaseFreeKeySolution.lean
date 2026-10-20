module
public import PhaseFreeKeyNaturalityR0219
public import PhaseFreeAlphaDescentR0219
public import SchemeDiscriminantExistenceR0244
public import PhaseFreeMultiplierR0219
public import PhaseFreeMultiplierBaseChangeR0219
public import Mathlib
public import SchemeAlphaCharacterR0215
public import SchemeAlphaSectionR0215
public import AffineConormalHodgeNaturalityR0205
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ArithmeticThetaPalomarDifferential365
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens} (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s
section Differentials
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Base R)
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of R) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra R Γ(X, U) :=
  ((constToPresheaf f).app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (constToPresheaf f)
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (kaehlerPresheaf f)
def kaehlerToSections (U : X.Opens) : ((kaehlerPresheaf f).obj (op U) : Type u) → (Γ(kaehler f, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (kaehlerPresheaf f)).app (op U)).hom s
def relativeD (U : X.Opens) (a : Γ(X, U)) : Γ(kaehler f, U) :=
  letI : Algebra R Γ(X, U) := sectionsAlgebra f U
  kaehlerToSections f U (KaehlerDifferential.D R Γ(X, U) a)
end Differentials
end ArithmeticThetaPalomarDifferential365
section KaehlerProvider
open ArithmeticThetaCompactifiedDifferentialR0145
namespace ArithmeticThetaPointedComparison387
theorem kaehler_hom_ext {A : Type u} [CommRing A] {Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) {N : Y.Modules} {f g : gY.kaehler ⟶ N} (h : ∀ (U : Y.Opens) (a : Γ(Y,U)), f.app U (relativeD gY U a) = g.app U (relativeD gY U a)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv gY.kaehlerPresheaf N).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  letI := gY.sectionsAlgebra U.unop
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A Γ(Y,U.unop))
  intro a
  exact h U.unop a
end ArithmeticThetaPointedComparison387
end KaehlerProvider
namespace ArithmeticThetaPalomarGlobalFrame401
open ArithmeticThetaPalomarDifferential365
section Differential
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A))
    (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
def AllDerivationsCompatible (m : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX) : Prop :=
  ∀ (U : Y.Opens) (a : Γ(Y,U)),
    m.app (φ ⁻¹ᵁ U) (pullSection φ (relativeD gY U a)) =
      relativeD gX (φ ⁻¹ᵁ U) (φ.app U a)
theorem compatible_iff_original (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (m : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX) : AllDerivationsCompatible gY gX φ m ↔ m = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap gY gX φ hφ := by
  constructor
  · intro hm
    apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).injective
    apply ArithmeticThetaPointedComparison387.kaehler_hom_ext gY
    intro U a
    erw [← Scheme.Modules.app_pullbackLocalSection φ, ← Scheme.Modules.app_pullbackLocalSection φ]
    exact (hm U a).trans
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_D gY gX φ hφ U a).symm
  · rintro rfl
    exact ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_D gY gX φ hφ
theorem canonicalDifferentialMap (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) : ∃! m : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX, AllDerivationsCompatible gY gX φ m := by
  refine ⟨ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap gY gX φ hφ,
    (compatible_iff_original gY gX φ hφ _).mpr rfl, ?_⟩
  intro m hm
  exact (compatible_iff_original gY gX φ hφ m).mp hm
def differentialMap (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) : (Scheme.Modules.pullback φ).obj (kaehler gY) ⟶ kaehler gX :=
  (canonicalDifferentialMap gY gX φ hφ).exists.choose
end Differential
open ArithmeticThetaRelativeKatoR0169
abbrev ChartRing (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  WeierstrassCurve.DrinfeldGlobal.ZChartRing W.toProjective
def chartInclusion (R : Type u) [CommRing R] (W : WeierstrassCurve R) : Spec (CommRingCat.of (ChartRing R W)) ⟶ Curve R W :=
  WeierstrassCurve.DrinfeldGlobal.zChartι W.toProjective
def chartScalar (R : Type u) [CommRing R] (W : WeierstrassCurve R) : R →+* ChartRing R W :=
  (Spec.preimage (chartInclusion R W ≫ structureMap R W)).hom
abbrev CurveFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (SheafOfModules.unit (Curve R W).ringCatSheaf : (Curve R W).Modules) ≅ kaehler (structureMap R W)
def differentialSection (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) :=
  Scheme.Modules.Hom.app δ.hom ⊤ (1 : Γ(Curve R W, ⊤))
def NormalizedFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : Prop :=
  let j := chartInclusion R W
  let p := j ≫ structureMap R W
  let x := WeierstrassCurve.DrinfeldGlobal.xOverZ W.toProjective
  let y := WeierstrassCurve.DrinfeldGlobal.yOverZ W.toProjective
  let toGlobal := (Scheme.ΓSpecIso (CommRingCat.of (ChartRing R W))).inv
  relativeD p ⊤ (toGlobal x) =
    toGlobal (2*y + chartScalar R W W.a₁*x + chartScalar R W W.a₃) •
      (differentialMap (structureMap R W) p j (by simp [p])).app ⊤
        (pullSection j (differentialSection R W δ))
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
  (Scheme.Modules.pullback (origin R W)).obj (kaehler (structureMap R W))
def hodgeGenerator (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : Γ(Hodge R W,⊤) := pullSection (origin R W) (differentialSection R W δ)
def IsFrame {X : Scheme.{u}} (M : X.Modules) (s : Γ(M,⊤)) : Prop :=
  ∀ (U : X.Opens) (h : U ≤ ⊤), Function.Bijective (fun a : Γ(X,U) => a • M.presheaf.map (homOfLE h).op s)
theorem differentialMap_eq_original {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) : differentialMap gY gX φ hφ = ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap gY gX φ hφ :=
  (compatible_iff_original gY gX φ hφ _).mp (canonicalDifferentialMap gY gX φ hφ).exists.choose_spec
theorem normalizedFrame_iff_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : NormalizedFrame R W δ ↔ ArithmeticThetaGlobalFourTorsionR0190.NormalizedFrame R W δ := by
  unfold NormalizedFrame
  dsimp only
  erw [differentialMap_eq_original]
  rfl
theorem hodgeGenerator_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : hodgeGenerator R W δ = ArithmeticThetaGlobalFourTorsionR0190.hodgeGenerator R W δ := rfl
theorem normalizedFrameExists (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] : ∃ δ : CurveFrame R W, NormalizedFrame R W δ := by
  obtain ⟨δ,hδ⟩ := ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.normalized_frame_exists R W
  exact ⟨δ,(normalizedFrame_iff_original R W δ).mpr hδ⟩
theorem hodgeGeneratorFrame (R : Type u) [CommRing R] (W : WeierstrassCurve R) (δ : CurveFrame R W) : IsFrame (Hodge R W) (hodgeGenerator R W δ) := by
  exact ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.hodge_generator_frame R W δ
theorem normalizedFrameExistsUnique (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] : ∃! δ : CurveFrame R W, NormalizedFrame R W δ ∧ IsFrame (Hodge R W) (hodgeGenerator R W δ) := by
  obtain ⟨δ,hδ⟩ := normalizedFrameExists R W
  refine ⟨δ, ⟨hδ,hodgeGeneratorFrame R W δ⟩, ?_⟩
  intro δ' hδ'
  exact ArithmeticThetaGlobalFourTorsionR0190.RelativeNormalizedDifferential.normalized_frames_equal R W δ δ'
    ((normalizedFrame_iff_original R W δ).mp hδ) ((normalizedFrame_iff_original R W δ').mp hδ'.1)
theorem chartRing_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) : ChartRing R W = ArithmeticThetaLegendreComparisonR0177.ChartRing R W := rfl
theorem chartInclusion_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) : chartInclusion R W = ArithmeticThetaLegendreComparisonR0177.chartInclusion R W := rfl
theorem chartScalar_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) : chartScalar R W = ArithmeticThetaLegendreComparisonR0177.chartScalar R W := rfl
theorem curveFrame_eq_original (R : Type u) [CommRing R] (W : WeierstrassCurve R) : CurveFrame R W = ArithmeticThetaGlobalFourTorsionR0190.CurveFrame R W := rfl
end ArithmeticThetaPalomarGlobalFrame401
namespace ArithmeticThetaPalomarConormal436
open ArithmeticThetaPalomarDifferential365
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (e : S ⟶ X)
def Normalized (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Prop :=
  ∀ (U : X.Opens) (x : Γ(idealModule e.ker,U)),
    m.app (e ⁻¹ᵁ U) (pullSection e x) =
      pullSection e (relativeD c U ((idealInclusion e.ker).app U x))
theorem canonicalConormalMap : ∃! m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c), Normalized c e m := by
  let m := ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e
  refine ⟨m, ?_, ?_⟩
  · intro U x
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x
  · intro n hn
    apply Scheme.Modules.pullback_hom_ext e
    intro U x
    exact (hn U x).trans
      (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x).symm
def conormalMap : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c) :=
  (canonicalConormalMap c e).exists.choose
theorem normalized_iff_original (m : (Scheme.Modules.pullback e).obj (idealModule e.ker) ⟶ (Scheme.Modules.pullback e).obj (kaehler c)) : Normalized c e m ↔ m = ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e := by
  constructor
  · intro h
    apply Scheme.Modules.pullback_hom_ext e
    intro U x
    exact (h U x).trans
      (ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e U x).symm
  · rintro rfl
    exact ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap_pullback c e
theorem conormalMap_eq_original : conormalMap c e = ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap c e :=
  (normalized_iff_original c e _).mp (canonicalConormalMap c e).exists.choose_spec
end ArithmeticThetaPalomarConormal436
namespace ArithmeticThetaPalomarPullback437
def pullback_unit_iso (X Y : Scheme.{u}) (p : X ⟶ Y) : (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map p.base).Final := by
    apply (Monotone.final_functor_iff (OrderHomClass.monotone p.base.frameHom)).2
    intro U
    exact ⟨⊤, by simp⟩
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  exact e
def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def squarePullbackIso {A B X Y : Scheme.{u}} (a : A ⟶ B) (s : B ⟶ Y) (t : A ⟶ X) (b : X ⟶ Y) (h : a ≫ s = t ≫ b) (M : Y.Modules) : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback s).obj M) ≅ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback b).obj M) :=
  (Scheme.Modules.pullbackComp a s).app M ≪≫ pullbackEqIso h M ≪≫
    ((Scheme.Modules.pullbackComp t b).app M).symm
end ArithmeticThetaPalomarPullback437
namespace ArithmeticThetaPalomarAffineAlpha437
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (L : ℕ)
  (M : FullLevel R W G L (𝟙 (Base R)))
def RealizesAlpha [Algebra ℚ R] (a : Γ(Hodge R W, ⊤)) : Prop :=
  ∃ (e : Fin 3 → R) (x y g : R) (δ : ArithmeticThetaPalomarGlobalFrame401.CurveFrame R W),
    RootData R W G L M e x y g ∧ ArithmeticThetaPalomarGlobalFrame401.NormalizedFrame R W δ ∧
    a = ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator R W δ
end ArithmeticThetaPalomarAffineAlpha437
namespace ArithmeticThetaPalomarSchemeAlpha437
open NeronModelInfra ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaPalomarDifferential365 ArithmeticThetaPalomarPullback437
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)
def AffineIdealCompatible (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) : Prop :=
  i.hom ≫ (idealInclusion (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) =
    (Scheme.Modules.pullback P.comparison).map (idealInclusion E.zero.ker) ≫
      (ArithmeticThetaPalomarPullback437.pullback_unit_iso _ _ P.comparison).hom
def affineHodgeMap (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) : (Scheme.Modules.pullback P.base).obj (Cotangent E) ⟶ ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation :=
  (squarePullbackIso P.base E.zero
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation) P.comparison
    P.zero_eq.symm (idealModule E.zero.ker)).hom ≫
  (Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)).map i.hom ≫
  ArithmeticThetaPalomarConormal436.conormalMap
    (ArithmeticThetaRelativeKatoR0169.structureMap P.ring P.equation)
    (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)
def affineAlpha (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ (idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)) (a : Γ(Cotangent E, ⊤)) : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation, ⊤) :=
  (affineHodgeMap E M P i).app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection P.base (Cotangent E) a)
def RealizesAlpha (a : Γ(Cotangent E, ⊤)) : Prop :=
  ∀ P : AffineTest E M,
    (∃ i, AffineIdealCompatible E M P i) ∧
    ∀ i, AffineIdealCompatible E M P i →
      ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha
        P.ring P.equation P.law 4 P.level (affineAlpha E M P i a)
theorem affineAlpha_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) (G : ArithmeticThetaRelativeKatoR0169.Law R W) (L : ℕ) (N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R))) (a : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge R W, ⊤)) : ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha R W G L N a ↔ ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L N a := by
  simp only [ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha,
    ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha,
    ArithmeticThetaPalomarGlobalFrame401.normalizedFrame_iff_original,
    ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator_eq_original]
  rfl
theorem idealCompatible_iff (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) : AffineIdealCompatible E M P i ↔ ArithmeticThetaSchemeFourCharacterR0215.AffineIdealCompatible E M P i := Iff.rfl
theorem affineHodgeMap_eq (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) : affineHodgeMap E M P i = ArithmeticThetaSchemeFourCharacterR0215.affineHodgeMap E M P i := by
  unfold affineHodgeMap
  rw [ArithmeticThetaPalomarConormal436.conormalMap_eq_original]
  rfl
theorem affineAlpha_eq (P : AffineTest E M) (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) (a : Γ(Cotangent E, ⊤)) : affineAlpha E M P i a = ArithmeticThetaSchemeFourCharacterR0215.affineAlpha E M P i a := by
  unfold affineAlpha
  rw [affineHodgeMap_eq]
  rfl
theorem realizesAlpha_iff (a : Γ(Cotangent E, ⊤)) : RealizesAlpha E M a ↔ ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a := by
  simp only [RealizesAlpha, ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha,
    idealCompatible_iff, affineAlpha_iff, affineAlpha_eq]
  rfl
theorem alphaExists (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) (E : Family S) (M : FullLevel E 4) : ∃! a : Γ(Cotangent E, ⊤), RealizesAlpha E M a := by
  obtain ⟨a,ha,hu⟩ := (ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_section k S σ E M).1
  refine ⟨a,(realizesAlpha_iff E M a).mpr ha,?_⟩
  intro b hb
  exact hu b ((realizesAlpha_iff E M b).mp hb)
theorem schemeAlphaCharacter :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (a : (Cotangent E).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → RealizesAlpha E M a → ∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A ∧ ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z ∧ (∀ a' : (Cotangent E).presheaf.obj (Opposite.op ⊤), RealizesAlpha E M' a' → a' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val • a) := by
  intro k _ _ S σ E M z a hz ha A hA
  obtain ⟨N,hN,hzN,hchar⟩ := ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_character
    k S σ E M z a hz ((realizesAlpha_iff E M a).mp ha) A hA
  exact ⟨N,hN,hzN,fun a' ha' => hchar a' ((realizesAlpha_iff E N a').mp ha')⟩
theorem recover_original_052 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4), ∀ (z : S.presheaf.obj (Opposite.op ⊤)) (a : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M z → ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a → ∀ (A : ArithmeticThetaFourTorsion.Mat4), ArithmeticThetaFourTorsion.PreservesEven A → ∃ M' : ArithmeticThetaSchemeLevelR0204.FullLevel E 4, ArithmeticThetaSchemeFourCharacterR0215.Changes E M M' A ∧ ArithmeticThetaSchemeFourCharacterR0215.MillerPhase E M' z ∧ (∀ a' : (ArithmeticThetaSchemeHodgeR0205.Cotangent E).presheaf.obj (Opposite.op ⊤), ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M' a' → a' = z ^ (ArithmeticThetaFourTorsion.characterExponent A).val • a) := by
  intro k _ _ S σ E M z a hz ha A hA
  obtain ⟨N,hN,hzN,hchar⟩ := schemeAlphaCharacter k S σ E M z a hz
    ((realizesAlpha_iff E M a).mpr ha) A hA
  exact ⟨N,hN,hzN,fun a' ha' => hchar a' ((realizesAlpha_iff E N a').mpr ha')⟩
end ArithmeticThetaPalomarSchemeAlpha437
namespace ArithmeticThetaPalomarMultiplier450
theorem phaseFreeMultiplier :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∃ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m ∧ (∀ (K : S.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames E P K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P K n → ∃! v : CategoryTheory.Iso L K, ArithmeticThetaPhaseFreeKeyR0219.PreservesFrames E P m n v) := by
  exact ArithmeticThetaPhaseFreeKeyR0219.phase_free_multiplier
theorem recover_original_095 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∃ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m ∧ (∀ (K : S.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames E P K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P K n → ∃! v : CategoryTheory.Iso L K, ArithmeticThetaPhaseFreeKeyR0219.PreservesFrames E P m n v) := by
  exact phaseFreeMultiplier
end ArithmeticThetaPalomarMultiplier450
namespace ArithmeticThetaPalomarMultiplier450
theorem phaseFreeMultiplierBaseChange :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∃! v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K, ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v := by
  exact ArithmeticThetaPhaseFreeKeyR0219.phase_free_multiplier_base_change
theorem recover_original_097 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∃! v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K, ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v := by
  exact phaseFreeMultiplierBaseChange
end ArithmeticThetaPalomarMultiplier450
namespace ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaSheafTensor
def pullSection {X Y : Scheme.{u}} (f : X ⟶ Y) {H : Y.Modules} {U : Y.Opens} (s : Γ(H,U)) : Γ((Scheme.Modules.pullback f).obj H, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s
def Compatible {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(H,U)) (t : Γ(K,U)),
    q.hom.app (f ⁻¹ᵁ U) (pullSection f (tensorSection Y H K U s t)) =
      tensorSection X M N (f ⁻¹ᵁ U)
        (e.hom.app (f ⁻¹ᵁ U) (pullSection f s)) (d.hom.app (f ⁻¹ᵁ U) (pullSection f t))
theorem canonicalBinaryTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) : ∃! q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N, Compatible f H K M N e d q := by
  let q := ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
    ArithmeticThetaPullback.sheafTensorCongr X e d
  have hq : Compatible f H K M N e d q := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (pullSection f (tensorSection Y H K U s t))) = _
    rw [show pullSection f (tensorSection Y H K U s t) =
      Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t) from rfl]
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Iso.ext
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ArithmeticThetaSheafTensor.tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change q'.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t)) =
    q.hom.app (f ⁻¹ᵁ U.unop) (pullSection f (tensorSection Y H K U.unop s t))
  exact (hq' U.unop s t).trans (hq U.unop s t).symm
theorem compatible_iff_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) (q : (Scheme.Modules.pullback f).obj (sheafTensor Y H K) ≅ sheafTensor X M N) : Compatible f H K M N e d q ↔ q = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫ ArithmeticThetaPullback.sheafTensorCongr X e d := by
  have h : Compatible f H K M N e d (ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫
      ArithmeticThetaPullback.sheafTensorCongr X e d) := by
    intro U s t
    change (ArithmeticThetaPullback.sheafTensorCongr X e d).hom.app _
      ((ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K).hom.app _
        (Scheme.Modules.pullbackLocalSection f (tensorSection Y H K U s t))) = _
    rw [ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_sheafTensor_local_section,
      ArithmeticThetaPullback.sheafTensorCongr_section]
    rfl
  constructor
  · intro hq
    exact (canonicalBinaryTensor f H K M N e d).unique hq h
  · rintro rfl
    exact h
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPalomarIdentity357
open ArithmeticThetaLocalWeierstrassR0203
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)
def Compatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (f : F.curve ⟶ E.curve) (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) : Prop :=
  i.hom ≫ idealInclusion F.zero.ker =
    (Scheme.Modules.pullback f).map (idealInclusion E.zero.ker) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
def cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
def cotangentComparison {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (i : (Scheme.Modules.pullback f).obj (idealModule E.zero.ker) ≅ idealModule F.zero.ker) : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F :=
  ((Scheme.Modules.pullbackComp b E.zero).app (idealModule E.zero.ker) ≪≫
    pullbackEqIso hz.symm (idealModule E.zero.ker) ≪≫
    ((Scheme.Modules.pullbackComp F.zero f).app (idealModule E.zero.ker)).symm) ≪≫
    (Scheme.Modules.pullback F.zero).mapIso i
def CotangentCompatible {S T : Scheme.{u}} (E : Family S) (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) : Prop :=
  ∃ i, Compatible E F f i ∧ e = cotangentComparison E F b f hz i
end ArithmeticThetaPalomarIdentity357
namespace ArithmeticThetaPalomarAlphaDescent459
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaSheafTensor ArithmeticThetaPalomarIdentity357 ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaPalomarSchemeAlpha437
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def productLine (L : S.Modules) : S.Modules := sheafTensor S (cotangent E) L
def tensorComparison (L : S.Modules) (A : MarkedTest E P) (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) : (Scheme.Modules.pullback A.map).obj (productLine E L) ≅ sheafTensor A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) :=
  (canonicalBinaryTensor A.map (cotangent E) L (cotangent A.family)
    ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose
def Descends (L : S.Modules) (m : Frames E P L) (β : Γ(productLine E L, ⊤)) : Prop :=
  ∀ A : MarkedTest E P,
    (∃ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c) ∧
    (∃ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a) ∧
    ∀ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c →
      ∀ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a →
      (tensorComparison E P L A c).hom.app ⊤
        (ArithmeticThetaPullback.pullbackGlobalSection A.map (productLine E L) β) =
        tensorSection A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) ⊤ a (m A)
theorem cotangentCompatible_iff {T : Scheme.{u}} (F : Family T) (b : T ⟶ S) (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero) (e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) : CotangentCompatible E F b f hz e ↔ ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hz e := Iff.rfl
theorem tensorComparison_eq_original (L : S.Modules) (A : MarkedTest E P) (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) : tensorComparison E P L A c = ArithmeticThetaPullback.pullback_sheafTensor_iso A.base S A.map (ArithmeticThetaSchemeHodgeR0205.Cotangent E) L ≪≫ ArithmeticThetaPullback.sheafTensorCongr A.base c (Iso.refl _) := by
  exact (compatible_iff_original A.map (cotangent E) L (cotangent A.family)
    ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _) _).mp
      (canonicalBinaryTensor A.map (cotangent E) L (cotangent A.family)
        ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose_spec
theorem descends_iff (L : S.Modules) (m : Frames E P L) (β : Γ(productLine E L, ⊤)) : Descends E P L m β ↔ ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β := by
  simp only [Descends, ArithmeticThetaPhaseFreeKeyR0219.Descends, cotangentCompatible_iff,
    realizesAlpha_iff, tensorComparison_eq_original]
  rfl
theorem phaseFreeAlphaDescent :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → (∃! β : (productLine E L).presheaf.obj (Opposite.op ⊤), Descends E P L m β) ∧ (∀ β : (productLine E L).presheaf.obj (Opposite.op ⊤), Descends E P L m β → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (productLine E L) ⊤ β) := by
  intro k _ _ S σ E P L m hm
  have h := ArithmeticThetaPhaseFreeKeyR0219.phase_free_alpha_descent k S σ E P L m hm
  convert h using 1 <;> simp only [descends_iff] <;> rfl
theorem recover_original_096 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → (∃! β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β) ∧ (∀ β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ArithmeticThetaRelativeDiscriminantR0171.IsFrame (ArithmeticThetaMultiplierKeyR0217.productLine E L) ⊤ β) := by
  intro k _ _ S σ E P L m hm
  have h := phaseFreeAlphaDescent k S σ E P L m hm
  convert h using 1 <;> simp only [descends_iff] <;> rfl
end ArithmeticThetaPalomarAlphaDescent459
namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
def Compatible (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Prop :=
  ∀ (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens) (m : Γ(M, U)),
    (e t).app U m = ((ihom.ev M).app N).app U
      (Scheme.Modules.tensorSections m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t))
theorem canonicalGlobalSectionsEquiv : ∃! e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N), Compatible M N e := by
  let e := Scheme.Modules.ihomGlobalSectionsEquiv M N
  have he : Compatible M N e := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply AddEquiv.ext
  intro t
  ext U m
  exact (he' t U m).trans (he t U m).symm
def globalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (canonicalGlobalSectionsEquiv M N).exists.choose
end ArithmeticThetaPalomarDual465
namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
theorem compatible_iff_original (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Compatible M N e ↔ e = Scheme.Modules.ihomGlobalSectionsEquiv M N := by
  have he : Compatible M N (Scheme.Modules.ihomGlobalSectionsEquiv M N) := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  constructor
  · intro h
    exact (canonicalGlobalSectionsEquiv M N).unique h he
  · rintro rfl
    exact he
theorem globalSectionsEquiv_eq_original : globalSectionsEquiv M N = Scheme.Modules.ihomGlobalSectionsEquiv M N :=
  (compatible_iff_original M N _).mp (canonicalGlobalSectionsEquiv M N).exists.choose_spec
theorem evaluationSection_eq_original (φ : M ⟶ N) : (globalSectionsEquiv M N).symm φ = (Scheme.Modules.ihomGlobalSectionsEquiv M N).symm φ := by
  rw [globalSectionsEquiv_eq_original]
end ArithmeticThetaPalomarDual465
namespace ArithmeticThetaPalomarKey466
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaPalomarAlphaDescent459 ArithmeticThetaPalomarIdentity357
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def thetaIdeal : E.curve.IdealSheafData := P.point.val.ker
def thetaLine : E.curve.Modules := (thetaIdeal E P).invModule
def thetaMap : (𝟙_ E.curve.Modules) ⟶ thetaLine E P :=
  (thetaIdeal E P).invModuleSection
def pushforwardLine : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E P)
def generator : (𝟙_ S.Modules) ⟶ pushforwardLine E P :=
  E.p.unitToPushforwardUnit ≫ (Scheme.Modules.pushforward E.p).map (thetaMap E P)
def originGenerator : (𝟙_ S.Modules) ⟶ (Scheme.Modules.pullback E.zero).obj (thetaLine E P) :=
  (Scheme.Modules.pullbackUnitIso E.zero).inv ≫
    (Scheme.Modules.pullback E.zero).map (thetaMap E P)
def IsRigidification (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Prop := originGenerator E P ≫ e.hom = 𝟙 _
def evaluation (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : pushforwardLine E P ⟶ (𝟙_ S.Modules) :=
  (Scheme.Modules.pushforward E.p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction E.zero).unit.app (thetaLine E P) ≫
      (Scheme.Modules.pushforward E.zero).map e.hom) ≫
    (Scheme.Modules.pushforwardComp E.zero E.p).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (E.law.one (𝟙 S)).property).hom.app _ ≫
    (Scheme.Modules.pushforwardId S).hom.app _
def evaluationSection (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Γ(Scheme.Modules.dual (pushforwardLine E P), ⊤) :=
  (ArithmeticThetaPalomarDual465.globalSectionsEquiv (pushforwardLine E P)
    (𝟙_ S.Modules)).symm (evaluation E P e)
def inverseSquare : S.Modules := tensorPower S (Scheme.Modules.dual (pushforwardLine E P)) 2
def evaluationSquare (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : Γ(inverseSquare E P, ⊤) :=
  tensorPowerSection S (Scheme.Modules.dual (pushforwardLine E P)) 2 ⊤
    (evaluationSection E P e)
def IsKey (L : S.Modules) (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) (β : Γ(productLine E L, ⊤)) (κ : inverseSquare E P ≅ productLine E L) : Prop :=
  κ.hom.app ⊤ (evaluationSquare E P e) = β
variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F) (b : T ⟶ S)
def productComparison (L : S.Modules) (K : T.Modules) (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) (v : (Scheme.Modules.pullback b).obj L ≅ K) : (Scheme.Modules.pullback b).obj (productLine E L) ≅ productLine F K :=
  (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor b (cotangent E) L
    (cotangent F) K c v).exists.choose
def AlphaNatural (L : S.Modules) (K : T.Modules) (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) (v : (Scheme.Modules.pullback b).obj L ≅ K) (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤)) : Prop :=
  (productComparison E F b L K c v).hom.app ⊤
    (pullbackGlobalSection b (productLine E L) β) = γ
def EvaluationSquareCompatible (eS : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) (eT : (Scheme.Modules.pullback F.zero).obj (thetaLine F Q) ≅ (𝟙_ T.Modules)) (j : (Scheme.Modules.pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q) : Prop :=
  j.hom.app ⊤ (pullbackGlobalSection b (inverseSquare E P) (evaluationSquare E P eS)) =
    evaluationSquare F Q eT
theorem evaluationSection_eq_original (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : evaluationSection E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e := by
  exact ArithmeticThetaPalomarDual465.evaluationSection_eq_original _ _ _
theorem evaluationSquare_eq_original (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) : evaluationSquare E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSquare E P e := by
  unfold evaluationSquare ArithmeticThetaMultiplierKeyR0217.evaluationSquare
  rw [evaluationSection_eq_original]
  rfl
theorem isKey_iff (L : S.Modules) (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) (β : Γ(productLine E L, ⊤)) (κ : inverseSquare E P ≅ productLine E L) : IsKey E P L e β κ ↔ ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ := by
  unfold IsKey ArithmeticThetaMultiplierKeyR0217.IsKey
  rw [evaluationSquare_eq_original]
  rfl
theorem productComparison_eq_original (L : S.Modules) (K : T.Modules) (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) (v : (Scheme.Modules.pullback b).obj L ≅ K) : productComparison E F b L K c v = ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v :=
  (ArithmeticThetaPalomarBinaryTensor458.compatible_iff_original b (cotangent E) L
    (cotangent F) K c v _).mp
      (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor b (cotangent E) L
        (cotangent F) K c v).exists.choose_spec
theorem alphaNatural_iff (L : S.Modules) (K : T.Modules) (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) (v : (Scheme.Modules.pullback b).obj L ≅ K) (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤)) : AlphaNatural E F b L K c v β γ ↔ ArithmeticThetaMultiplierKeyR0217.AlphaNatural E F b L K c v β γ := by
  unfold AlphaNatural ArithmeticThetaMultiplierKeyR0217.AlphaNatural
  rw [productComparison_eq_original]
  rfl
theorem evaluationSquareCompatible_iff (eS : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) (eT : (Scheme.Modules.pullback F.zero).obj (thetaLine F Q) ≅ (𝟙_ T.Modules)) (j : (Scheme.Modules.pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q) : EvaluationSquareCompatible E P F Q b eS eT j ↔ ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j := by
  unfold EvaluationSquareCompatible ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible
  rw [evaluationSquare_eq_original, evaluationSquare_eq_original]
  rfl
theorem phaseFreeKey :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaPalomarAlphaDescent459.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPalomarAlphaDescent459.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarKey466.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaPalomarKey466.IsRigidification E P e → ∃! κ : CategoryTheory.Iso (ArithmeticThetaPalomarKey466.inverseSquare E P) (ArithmeticThetaPalomarAlphaDescent459.productLine E L), ArithmeticThetaPalomarKey466.IsKey E P L e β κ := by
  intro k _ _ S σ E P L m hm β hβ e he
  have h := ArithmeticThetaPhaseFreeKeyR0219.phase_free_key k S σ E P L m hm β ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hβ) e he
  convert h using 1 <;> (try simp only [ArithmeticThetaPalomarAlphaDescent459.descends_iff, isKey_iff, alphaNatural_iff, evaluationSquareCompatible_iff, productComparison_eq_original]) <;> rfl
theorem recover_original_053 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ∀ (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P e → ∃! κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L), ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ := by
  intro k _ _ S σ E P L m hm β hβ e he
  have h := phaseFreeKey k S σ E P L m hm β ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hβ) e he
  convert h using 1 <;> (try simp only [ArithmeticThetaPalomarAlphaDescent459.descends_iff, isKey_iff, alphaNatural_iff, evaluationSquareCompatible_iff, productComparison_eq_original]) <;> rfl
theorem phaseFreeKeyNaturality :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∀ (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaPalomarIdentity357.cotangent E)) (ArithmeticThetaPalomarIdentity357.cotangent F)), ArithmeticThetaPalomarIdentity357.CotangentCompatible E F b f hb.2.1 c → ∀ (v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K), ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v → ∀ (β : (ArithmeticThetaPalomarAlphaDescent459.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaPalomarAlphaDescent459.productLine F K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPalomarAlphaDescent459.Descends E P L m β → ArithmeticThetaPalomarAlphaDescent459.Descends F Q K n γ → ArithmeticThetaPalomarKey466.AlphaNatural E F b L K c v β γ ∧ (∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaPalomarKey466.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F.zero).obj (ArithmeticThetaPalomarKey466.thetaLine F Q)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaPalomarKey466.IsRigidification E P eS → ArithmeticThetaPalomarKey466.IsRigidification F Q eT → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaPalomarKey466.inverseSquare E P) (ArithmeticThetaPalomarAlphaDescent459.productLine E L)) (κT : CategoryTheory.Iso (ArithmeticThetaPalomarKey466.inverseSquare F Q) (ArithmeticThetaPalomarAlphaDescent459.productLine F K)), ArithmeticThetaPalomarKey466.IsKey E P L eS β κ → ArithmeticThetaPalomarKey466.IsKey F Q K eT γ κT → (∃! j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaPalomarKey466.inverseSquare E P)) (ArithmeticThetaPalomarKey466.inverseSquare F Q), ArithmeticThetaPalomarKey466.EvaluationSquareCompatible E P F Q b eS eT j) ∧ (∀ j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaPalomarKey466.inverseSquare E P)) (ArithmeticThetaPalomarKey466.inverseSquare F Q), ArithmeticThetaPalomarKey466.EvaluationSquareCompatible E P F Q b eS eT j → CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map κ.hom) (ArithmeticThetaPalomarKey466.productComparison E F b L K c v).hom = CategoryTheory.CategoryStruct.comp j.hom κT.hom)) := by
  intro k _ _ S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ hβ hγ
  have h := ArithmeticThetaPhaseFreeKeyR0219.phase_free_key_naturality k S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hβ) ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hγ)
  convert h using 1 <;> (try simp only [ArithmeticThetaPalomarAlphaDescent459.descends_iff, isKey_iff, alphaNatural_iff, evaluationSquareCompatible_iff, productComparison_eq_original]) <;> rfl
theorem recover_original_054 :
∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E), ∀ (L : S.Modules) (m : ArithmeticThetaPhaseFreeKeyR0219.Frames E P L), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier E P L m → ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (Q : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint F) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hb : ArithmeticThetaEvenMarkingTorsorR0216.Cartesian E F b f), CategoryTheory.CategoryStruct.comp Q.point.val f = CategoryTheory.CategoryStruct.comp b P.point.val → ∀ (K : T.Modules) (n : ArithmeticThetaPhaseFreeKeyR0219.Frames F Q K), ArithmeticThetaPhaseFreeKeyR0219.IsMultiplier F Q K n → ∀ (c : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaSchemeHodgeR0205.Cotangent E)) (ArithmeticThetaSchemeHodgeR0205.Cotangent F)), ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hb.2.1 c → ∀ (v : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj L) K), ArithmeticThetaPhaseFreeKeyR0219.Compatible E P F Q b f L K m n v → ∀ (β : (ArithmeticThetaMultiplierKeyR0217.productLine E L).presheaf.obj (Opposite.op ⊤)) (γ : (ArithmeticThetaMultiplierKeyR0217.productLine F K).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β → ArithmeticThetaPhaseFreeKeyR0219.Descends F Q K n γ → ArithmeticThetaMultiplierKeyR0217.AlphaNatural E F b L K c v β γ ∧ (∀ (eS : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback E.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine E P)) (SheafOfModules.unit S.ringCatSheaf)) (eT : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback F.zero).obj (ArithmeticThetaMultiplierKeyR0217.thetaLine F Q)) (SheafOfModules.unit T.ringCatSheaf)), ArithmeticThetaMultiplierKeyR0217.IsRigidification E P eS → ArithmeticThetaMultiplierKeyR0217.IsRigidification F Q eT → ∀ (κ : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P) (ArithmeticThetaMultiplierKeyR0217.productLine E L)) (κT : CategoryTheory.Iso (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q) (ArithmeticThetaMultiplierKeyR0217.productLine F K)), ArithmeticThetaMultiplierKeyR0217.IsKey E P L eS β κ → ArithmeticThetaMultiplierKeyR0217.IsKey F Q K eT γ κT → (∃! j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j) ∧ (∀ j : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback b).obj (ArithmeticThetaMultiplierKeyR0217.inverseSquare E P)) (ArithmeticThetaMultiplierKeyR0217.inverseSquare F Q), ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j → CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Modules.pullback b).map κ.hom) (ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v).hom = CategoryTheory.CategoryStruct.comp j.hom κT.hom)) := by
  intro k _ _ S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ hβ hγ
  have h := phaseFreeKeyNaturality k S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hβ) ((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hγ)
  convert h using 1 <;> (try simp only [ArithmeticThetaPalomarAlphaDescent459.descends_iff, isKey_iff, alphaNatural_iff, evaluationSquareCompatible_iff, productComparison_eq_original]) <;> rfl
end ArithmeticThetaPalomarKey466
