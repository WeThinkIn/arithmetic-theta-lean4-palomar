module

public import ThetaIdentityEvaluationR0212
public import ThetaLineBaseChangeR0212
public import NoetherianPoleFiltrationR0203
public import FramedFiniteTypeApproximationR0203
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
public import EvenThetaRigidificationR0212

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open ArithmeticThetaThetaEvaluationR0212
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

/-- The actual Weierstrass family supplies the framed geometry over any rational
algebra, including the zero ring. -/
def weierstrassFrame (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) : FramedCurve R where
  target := Curve R W
  structureMap := structureMap R W
  law := ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G
  geometry := ArithmeticThetaFullLevelCoverR0175.BaseChange.geometry R W G
  dimension := WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  hodge := by
    have hz : ((ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree.toGRJ G).one
        (𝟙 (Base R))).val = origin R W := by
      change (G.one (𝟙 (Base R))).val = origin R W
      simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))
    rw [hz]
    exact ArithmeticThetaRelativeCyclicQuotientR0173.FramedSchemeQuotientR0174.OriginHodge.source_hodge_trivial R W

lemma weierstrassFrame_zero (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) : (weierstrassFrame R W G hG).zero = origin R W := by
  change (G.one (𝟙 (Base R))).val = origin R W
  simpa only [Category.id_comp] using hG.1 (𝟙 (Base R))

#print axioms weierstrassFrame
#print axioms weierstrassFrame_zero
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

/-- Sections along an actual scheme isomorphism, with the structural R-action. -/
def sectionsPullbackIso {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (c : Y ⟶ Spec (.of R)) (d : X ⟶ Spec (.of R)) (e : X ≅ Y)
    (he : e.hom ≫ c = d) (M : Y.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom d
      ((Scheme.Modules.pullback e.hom).obj M) ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom d
    ((Scheme.Modules.pullback e.hom).obj M) ⊤
  let δ : M ≅ (Scheme.Modules.pushforward e.hom).obj
      ((Scheme.Modules.pushforward e.inv).obj M) :=
    ((Scheme.Modules.pushforwardId Y).app M).symm ≪≫
      ((Scheme.Modules.pushforwardCongr e.inv_hom_id).app M).symm ≪≫
      ((Scheme.Modules.pushforwardComp e.inv e.hom).app M).symm
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M) :=
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom).isIso_unit_app_of_iso δ
  let f : Γ(M, ⊤) →ₗ[R] Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) := {
    toFun := Scheme.Modules.pullbackLocalSection e.hom
    map_add' := Scheme.Modules.pullbackLocalSection_add e.hom
    map_smul' := by
      intro r x
      change Scheme.Modules.pullbackLocalSection e.hom
        (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ ⊤ le_top) r • x) =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ d.appLE ⊤ ⊤ le_top) r •
          (show Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) from
            Scheme.Modules.pullbackLocalSection e.hom x)
      have hc : c.appLE ⊤ ⊤ le_top = c.appTop := (Scheme.Hom.app_eq_appLE c).symm
      have hd : d.appLE ⊤ ⊤ le_top = d.appTop := (Scheme.Hom.app_eq_appLE d).symm
      rw [hc, hd, Scheme.Modules.pullbackLocalSection_smul]
      congr 1
      have h : (Scheme.ΓSpecIso (.of R)).inv ≫ c.appTop ≫ e.hom.appTop =
          (Scheme.ΓSpecIso (.of R)).inv ≫ d.appTop := by
        rw [← Scheme.Hom.comp_appTop, he]
      exact congrArg (fun k : CommRingCat.of R ⟶ Γ(X, ⊤) => k r) h }
  exact LinearEquiv.ofBijective f
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M).app ⊤))

/-- A Cartesian family square preserving sections is Cartesian on the sections. -/
lemma section_cartesian {S T X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ T)
    (f : X ⟶ Y) (b : S ⟶ T) (sq : IsPullback f p q b)
    (z : S ⟶ X) (w : T ⟶ Y) (hz : z ≫ p = 𝟙 _) (hw : w ≫ q = 𝟙 _)
    (hzw : z ≫ f = b ≫ w) : IsPullback z b f w := by
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hzw
    (fun s => s.fst ≫ p) (fun s => ?_) (fun s => ?_) (fun s m hm _ => ?_))
  · apply sq.hom_ext
    · rw [Category.assoc, hzw, Category.assoc, ← sq.w_assoc,
        ← Category.assoc s.fst f, s.condition]
      simp only [Category.assoc]
      rw [← Category.assoc w q, hw, Category.id_comp]
    · rw [Category.assoc, hz, Category.comp_id]
  · have h := congrArg (fun a => a ≫ q) s.condition
    simpa only [Category.assoc, sq.w, hw, Category.comp_id] using h
  · rw [← hm, Category.assoc, hz, Category.comp_id]

lemma section_ideal_comap {S T X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ T)
    (f : X ⟶ Y) (b : S ⟶ T) (sq : IsPullback f p q b)
    (z : S ⟶ X) (w : T ⟶ Y) (hz : z ≫ p = 𝟙 _) (hw : w ≫ q = 𝟙 _)
    (hzw : z ≫ f = b ≫ w) [IsClosedImmersion w] : w.ker.comap f = z.ker := by
  have hp := section_cartesian p q f b sq z w hz hw hzw
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

/-- Pullback of an invertible ideal's inverse is identified by its actual
canonical section and the pulled-back zero ideal. -/
lemma inverseIdeal_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (hI : I.IsInvertible)
    (hJ : J.IsInvertible) (hIJ : I.comap f = J) :
    Nonempty ((Scheme.Modules.pullback f).obj I.invModule ≅ J.invModule) := by
  let s := Scheme.Modules.pullbackSection f I.invModuleSection
  have hz : Scheme.Modules.zeroSchemeIdeal s = J := by
    rw [← hI.isInvertible_invModule.comap_zeroSchemeIdeal,
      hI.zeroSchemeIdeal_invModuleSection, hIJ]
  have hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible := hz ▸ hJ
  obtain ⟨e, -⟩ := (hI.isInvertible_invModule.pullback f).exists_iso_invModule_zeroSchemeIdeal s hZ
  rw [hz] at e
  exact ⟨e⟩

#print axioms sectionsPullbackIso
#print axioms section_ideal_comap
#print axioms inverseIdeal_pullback
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174
open ArithmeticThetaLocalWeierstrassR0203
open scoped TensorProduct

/-- Degree-one sections over an arbitrary rational algebra, obtained by actual
Cartesian finite-type approximation and the accepted arbitrary scalar extension. -/
lemma origin_sections_equiv (R : Type u) [CommRing R] [Algebra ℚ R]
    (Q : ArithmeticThetaLocalWeierstrassR0203.FramedCurve R) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap Q.zero.ker.invModule ⊤
    Nonempty (Γ(Q.zero.ker.invModule, ⊤) ≃ₗ[R] R) := by
  obtain ⟨D⟩ := framed_finite_type_approximation R Q
  letI := D.commRing
  letI := D.rational
  letI := D.finiteType
  letI : IsNoetherianRing D.ring := Algebra.FiniteType.isNoetherianRing ℚ D.ring
  letI : Algebra D.ring R := D.scalar.toRingHom.toAlgebra
  let L := (D.model.zero.ker ^ 1).invModule
  let b := Scheme.TwoAffineOpenCover.specMap D.ring R
  let P := pullback D.model.structureMap b
  let π : P ⟶ D.model.target := pullback.fst D.model.structureMap b
  let c : P ⟶ Spec (.of R) := pullback.snd D.model.structureMap b
  let Lp := (Scheme.Modules.pullback π).obj L
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom D.model.structureMap L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c Lp ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap Q.zero.ker.invModule ⊤
  have h₀ : Nonempty (Γ(L, ⊤) ≃ₗ[D.ring] D.ring) := by
    exact NoetherianPoleFiltration.origin_first_sections D.ring D.model
  obtain ⟨ε₀⟩ := h₀
  obtain ⟨ε, -⟩ :=
    (NoetherianPositiveCohomology.positive_sections_baseChange D.ring D.model 1 (by omega)).2 R
  let ε' : R ⊗[D.ring] Γ(L, ⊤) ≃ₗ[R] Γ(Lp, ⊤) := ε
  let e : Q.target ≅ P := D.cartesian.isoPullback
  have he : e.hom ≫ c = Q.structureMap := D.cartesian.isoPullback_hom_snd
  have hep : e.hom ≫ π = D.comparison := D.cartesian.isoPullback_hom_fst
  letI : IsProper D.model.structureMap := D.model.geometry.proper
  haveI : IsClosedImmersion (D.model.zero ≫ D.model.structureMap) := by
    rw [D.model.zero_over]; infer_instance
  haveI : IsClosedImmersion D.model.zero :=
    IsClosedImmersion.of_comp _ D.model.structureMap
  have hI : D.model.zero.ker.comap D.comparison = Q.zero.ker :=
    section_ideal_comap Q.structureMap D.model.structureMap D.comparison b D.cartesian
      Q.zero D.model.zero Q.zero_over D.model.zero_over D.zero_eq
  obtain ⟨δ⟩ := inverseIdeal_pullback D.comparison D.model.zero.ker Q.zero.ker
    D.model.zero_ideal_invertible Q.zero_ideal_invertible hI
  let η : (Scheme.Modules.pullback e.hom).obj Lp ≅ Q.zero.ker.invModule :=
    (Scheme.Modules.pullbackComp e.hom π).app L ≪≫
      (Scheme.Modules.pullbackCongr hep).app L ≪≫
      (Scheme.Modules.pullback D.comparison).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one D.model.zero.ker))) ≪≫ δ
  let ηs := sectionsPullbackIso c Q.structureMap e he Lp ≪≫ₗ
    FibreCohomology.sectionsIsoLinear Q.structureMap η ⊤
  exact ⟨ηs.symm ≪≫ₗ ε'.symm ≪≫ₗ ε₀.baseChange D.ring R _ _ ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid D.ring R R⟩

#print axioms origin_sections_equiv
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaThetaEvaluationR0212
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

/-- Translation identifies sections of the actual inverse ideal of any section
with those of the origin, retaining the same structural scalar map. -/
lemma point_sections_equiv (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (p : NeronModelInfra.SchemeHomOver (𝟙 (Base R)) (structureMap R W)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap R W) p.val.ker.invModule ⊤
    Nonempty (Γ(p.val.ker.invModule, ⊤) ≃ₗ[R] R) := by
  let c := structureMap R W
  let z := origin R W
  letI : IsProper c := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 c :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hz : z ≫ c = 𝟙 _ := (WeierstrassProjModel.kwZeroSect R W).property
  haveI : IsClosedImmersion (z ≫ c) := by rw [hz]; infer_instance
  haveI : IsClosedImmersion z := IsClosedImmersion.of_comp z c
  have hIz : z.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id z hz
  have hIp : p.val.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id p.val p.property
  obtain ⟨τ, hτ, hτmul⟩ := G.exists_iso_comp_eq_and_comp_hom_eq_mul p
  have hτz : z ≫ τ.hom = p.val := by
    have h := hτmul (𝟙 (Base R)) (G.one (𝟙 (Base R)))
    rw [G.one_mul] at h
    have hp : WeierstrassProjModel.schemeHomOverComp (𝟙 (Base R))
        (Category.comp_id _) p = p := Subtype.ext (Category.id_comp _)
    rw [hp] at h
    simpa only [hG.1, Category.id_comp] using h
  have hi : τ.inv ≫ c = c := by
    calc
      τ.inv ≫ c = τ.inv ≫ (τ.hom ≫ c) := by rw [hτ]
      _ = c := by simp
  have hpz : p.val ≫ τ.inv = z := by rw [← hτz]; simp
  have sq : IsPullback τ.inv c c (𝟙 (Base R)) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hi⟩
  have hI : z.ker.comap τ.inv = p.val.ker :=
    section_ideal_comap c c τ.inv (𝟙 (Base R)) sq p.val z p.property hz
      (by simpa using hpz)
  obtain ⟨δ⟩ := inverseIdeal_pullback τ.inv z.ker p.val.ker hIz hIp hI
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c z.ker.invModule ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c p.val.ker.invModule ⊤
  have hε : Nonempty (Γ(z.ker.invModule, ⊤) ≃ₗ[R] R) := by
    have h := origin_sections_equiv R (weierstrassFrame R W G hG)
    rw [weierstrassFrame_zero] at h
    exact h
  obtain ⟨ε⟩ := hε
  let η := sectionsPullbackIso c c τ.symm hi z.ker.invModule ≪≫ₗ
    FibreCohomology.sectionsIsoLinear c δ ⊤
  exact ⟨η.symm ≪≫ₗ ε⟩

lemma theta_sections_equiv (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 4 (𝟙 (Base R))) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap R W) (thetaLine R W G M) ⊤
    Nonempty (Γ(thetaLine R W G M, ⊤) ≃ₗ[R] R) :=
  point_sections_equiv R W G hG
    ⟨evenPoint R W G M, EvenThetaRigidification.evenPoint_over R W G M⟩

/-- The actual identity restriction is invertible because its zero scheme is
empty; this uses the full marking's geometric disjointness. -/
lemma originGenerator_isIso (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (M : FullLevel R W G 4 (𝟙 (Base R))) : IsIso (originGenerator R W G M) := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  haveI : IsClosedImmersion (evenPoint R W G M ≫ structureMap R W) := by
    rw [EvenThetaRigidification.evenPoint_over]; infer_instance
  haveI : IsClosedImmersion (evenPoint R W G M) :=
    IsClosedImmersion.of_comp _ (structureMap R W)
  have hI : (thetaIdeal R W G M).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (EvenThetaRigidification.evenPoint_over R W G M)
  have hL := hI.isInvertible_invModule
  have hz : Scheme.Modules.zeroSchemeIdeal (thetaMap R W G M) = thetaIdeal R W G M := by
    rw [EvenThetaRigidification.thetaMap_eq]; exact hI.zeroSchemeIdeal_invModuleSection
  have hd : Disjoint (Set.range (origin R W)) ((thetaIdeal R W G M).support : Set _) := by
    change Disjoint (Set.range (origin R W)) ((evenPoint R W G M).ker.support : Set (Curve R W))
    rw [Scheme.Hom.support_ker, (evenPoint R W G M).isClosedEmbedding.isClosed_range.closure_eq]
    exact (EvenThetaRigidification.evenPoint_disjoint R W G M).symm
  have ht := ((thetaIdeal R W G M).comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
    (origin R W) hd).1
  have hp : Scheme.Modules.zeroSchemeIdeal (originGenerator R W G M) = ⊤ := by
    change Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection (origin R W) (thetaMap R W G M)) = ⊤
    rw [← hL.comap_zeroSchemeIdeal, hz, ht]
  apply SectionFrames.isIso_of_frame_top
  apply (hL.pullback (origin R W)).isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
  rw [hp, Scheme.IdealSheafData.support_top]
  exact disjoint_bot_right

#print axioms point_sections_equiv
#print axioms theta_sections_equiv
#print axioms originGenerator_isIso
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaThetaEvaluationR0212
open ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174

/-- A sheaf functional on a structural pushforward is linear for the actual
base-ring action on global sections. -/
def pushforwardFunctional {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (L : X.Modules)
    (v : (Scheme.Modules.pushforward c).obj L ⟶ 𝟙_ (Spec (.of R)).Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L ⊤
    Γ(L, ⊤) →ₗ[R] R := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L ⊤
  refine {
    toFun := fun s => (Scheme.ΓSpecIso (.of R)).hom (v.app ⊤ s)
    map_add' := fun s t => by rw [map_add, map_add]
    map_smul' := ?_ }
  intro r s
  change (Scheme.ΓSpecIso (.of R)).hom
    (v.app ⊤ (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ ⊤ le_top) r • s)) =
      r * (Scheme.ΓSpecIso (.of R)).hom (v.app ⊤ s)
  have hc : c.appLE ⊤ ⊤ le_top = c.appTop := (Scheme.Hom.app_eq_appLE c).symm
  rw [hc]
  change (Scheme.ΓSpecIso (.of R)).hom
    (v.app ⊤ ((Scheme.ΓSpecIso (.of R)).inv r •
      (show Γ((Scheme.Modules.pushforward c).obj L, ⊤) from s))) = _
  rw [Scheme.Modules.Hom.app_smul]
  change (Scheme.ΓSpecIso (.of R)).hom
    ((Scheme.ΓSpecIso (.of R)).inv r * (show Γ(Spec (.of R), ⊤) from v.app ⊤ s)) = _
  rw [map_mul]
  have hr : (Scheme.ΓSpecIso (.of R)).hom ((Scheme.ΓSpecIso (.of R)).inv r) = r :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).inv_hom_id r
  rw [hr]

lemma scalar_generator_apply (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) (G : Law R W) (M : FullLevel R W G 4 (𝟙 (Base R)))
    (r : R) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap R W) (thetaLine R W G M) ⊤
    (generator R W G M).app ⊤ ((Scheme.ΓSpecIso (.of R)).inv r) = r • thetaSection R W G M := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap R W) (thetaLine R W G M) ⊤
  calc
    _ = GradedOAlgebra.baseScalar (structureMap R W) r • thetaSection R W G M :=
      PushforwardGenerator.fromSection_top_apply (thetaLine R W G M) (thetaSection R W G M)
        ((structureMap R W).app ⊤ ((Scheme.ΓSpecIso (.of R)).inv r))
    _ = _ := by rw [GeometricCubic.baseScalar_eq_const]; rfl

lemma generator_global_bijective (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 4 (𝟙 (Base R))) :
    Function.Bijective ((generator R W G M).app ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (structureMap R W) (thetaLine R W G M) ⊤
  obtain ⟨ε⟩ := theta_sections_equiv R W G hG M
  haveI := originGenerator_isIso R W G M
  let e := (asIso (originGenerator R W G M)).symm
  have he : IsRigidification R W G M e := IsIso.hom_inv_id _
  have h := IdentityEvaluation.generator_evaluation R W G M e he
  let v := pushforwardFunctional (structureMap R W) (thetaLine R W G M) (evaluation R W G M e)
  let s := thetaSection R W G M
  have hvs : v s = 1 := by
    have h₁ := congrArg (fun f => f.app ⊤ ((Scheme.ΓSpecIso (.of R)).inv (1 : R))) h
    change (evaluation R W G M e).app ⊤
      ((generator R W G M).app ⊤ ((Scheme.ΓSpecIso (.of R)).inv (1 : R))) =
        (Scheme.ΓSpecIso (.of R)).inv (1 : R) at h₁
    rw [scalar_generator_apply, one_smul] at h₁
    change (Scheme.ΓSpecIso (.of R)).hom ((evaluation R W G M e).app ⊤ s) = 1
    rw [h₁]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).inv_hom_id (1 : R)
  have hb : Function.Bijective (fun r : R => r • s) := by
    constructor
    · intro a b hab
      have hv := congrArg v hab
      simpa only [map_smul, hvs, smul_eq_mul, mul_one] using hv
    · intro x
      refine ⟨v x, ?_⟩
      have hx := ArithmeticThetaLocalWeierstrassR0203.NoetherianPoleFiltration.rank_one_interchange
        ε.symm v s x
      simpa only [hvs, one_smul] using hx.symm
  apply (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)).mp
  change Function.Bijective (fun r : R =>
    (generator R W G M).app ⊤ ((Scheme.ΓSpecIso (.of R)).inv r))
  constructor
  · intro a b hab
    apply hb.1
    exact (scalar_generator_apply R W G M a).symm.trans
      (hab.trans (scalar_generator_apply R W G M b))
  · intro x
    obtain ⟨r, hr⟩ := hb.2 x
    exact ⟨r, (scalar_generator_apply R W G M r).trans hr⟩

#print axioms pushforwardFunctional
#print axioms scalar_generator_apply
#print axioms generator_global_bijective
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaThetaEvaluationR0212

/-- Affine localization promotes the verified global generator to the specified
sheaf isomorphism, hence to bijectivity on every base open. -/
lemma generator_isIso (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (M : FullLevel R W G 4 (𝟙 (Base R))) : IsIso (generator R W G M) := by
  letI : IsProper (structureMap R W) := WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hI : (thetaIdeal R W G M).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (evenPoint R W G M)
      (EvenThetaRigidification.evenPoint_over R W G M)
  have hL := hI.isInvertible_invModule
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) (pushforwardLine R W G M)) :=
    Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial (A := R) (structureMap R W)
      (PushforwardGenerator.weierstrassTwoAffineCover R W) (thetaLine R W G M) hL.1
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) (𝟙_ (Base R).Modules)) :=
    Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial (R := CommRingCat.of R) _
      (fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩)
  exact PushforwardGenerator.isIso_of_bijective_global (A := CommRingCat.of R)
    (generator R W G M) (generator_global_bijective R W G hG M)

#print axioms generator_isIso
end ArithmeticThetaUniversalEvaluationR0213.ArbitraryGenerator

namespace ArithmeticThetaUniversalEvaluationR0213
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaThetaEvaluationR0212

/-- The specified theta generator is invertible over every rational algebra;
the actual adjunction-defined evaluation is its inverse and frames the dual. -/
theorem arbitrary_theta_generator_evaluation :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W), ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G → ∀ M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G 4 (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R)), CategoryTheory.IsIso (ArithmeticThetaThetaEvaluationR0212.generator R W G M) ∧ (∀ e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeKatoR0169.origin R W)).obj (ArithmeticThetaThetaEvaluationR0212.thetaLine R W G M)) ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)), ArithmeticThetaThetaEvaluationR0212.IsRigidification R W G M e → CategoryTheory.IsIso (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M e) ∧ CategoryTheory.CategoryStruct.comp (ArithmeticThetaThetaEvaluationR0212.generator R W G M) (ArithmeticThetaThetaEvaluationR0212.evaluation R W G M e) = CategoryTheory.CategoryStruct.id ((SheafOfModules.unit (ArithmeticThetaRelativeDiscriminantR0171.Base R).ringCatSheaf)) ∧ ArithmeticThetaRelativeDiscriminantR0171.IsFrame (AlgebraicGeometry.Scheme.Modules.dual (ArithmeticThetaThetaEvaluationR0212.pushforwardLine R W G M)) ⊤ (ArithmeticThetaThetaEvaluationR0212.evaluationSection R W G M e)) := by
  intro R _ _ W _ G hG M
  haveI := ArbitraryGenerator.generator_isIso R W G hG M
  refine ⟨inferInstance, ?_⟩
  intro e he
  have h := IdentityEvaluation.generator_evaluation R W G M e he
  have hv : evaluation R W G M e = inv (generator R W G M) := by
    apply (cancel_epi (generator R W G M)).mp
    exact h.trans (IsIso.hom_inv_id _).symm
  refine ⟨?_, h, ?_⟩
  · rw [hv]
    infer_instance
  · exact IdentityEvaluation.dual_frame (pushforwardLine R W G M)
      (generator R W G M) (evaluation R W G M e) h

#print axioms arbitrary_theta_generator_evaluation
end ArithmeticThetaUniversalEvaluationR0213
