import FullLevelCoverGeometryR0175
import EtaleNormality
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
namespace NormalAffineExtensionR0175
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeKatoNaturalityR0170

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R]

/-- An actual nonempty open-and-closed integral component of a finite étale cover. -/
lemma integral_component {X : Scheme.{u}} (f : X ⟶ Base R)
    [IsFinite f] [Etale f] [Surjective f] :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ IsIntegral U ∧
      Surjective (U.ι ≫ f) ∧ ∀ z, (U.ι ≫ f).finrank z ≤ f.finrank z := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsIntegrallyClosed Γ(Base R, ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hd (x : X) : IsDomain (X.presheaf.stalk x) :=
    (Smooth.isDomain_and_isIntegrallyClosed_stalk f x).1
  obtain ⟨x, hx⟩ := f.surjective (genericPoint (Base R))
  let U : X.Opens := ⟨irreducibleComponent x,
    (isOpen_irreducibleComponent_of_isDomain_stalk hd x).1⟩
  have hc : IsClosed (U : Set X) := isClosed_irreducibleComponent
  letI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
    (isIrreducible_irreducibleComponent (x := x))
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hc)
  letI : IsIntegral U :=
    isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk U
      (fun y => (Smooth.isDomain_and_isIntegrallyClosed_stalk (U.ι ≫ f) y).1)
  have hs : Surjective (U.ι ≫ f) := by
    constructor
    apply Set.range_eq_univ.mp
    apply IsClopen.eq_univ
    · exact ⟨(U.ι ≫ f).isClosedMap.isClosed_range,
        (U.ι ≫ f).isOpenMap.isOpen_range⟩
    · exact Set.range_nonempty _
  refine ⟨U, hc, inferInstance, hs, ?_⟩
  let V : X.Opens := ⟨(U : Set X)ᶜ, hc.isOpen_compl⟩
  have huv : U ⊔ V = ⊤ := by ext y; simp [V]
  have hdj : U ⊓ V = ⊥ := by ext y; simp [V]
  intro z
  have he := f.finrank_restrict_add_finrank_restrict_of_isCompl U V huv hdj z
  omega

/-- The coordinate ring and actual structural map of an integral cover component. -/
structure AffineComponent {X : Scheme.{u}} (f : X ⟶ Base R) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  inclusion : R →+* ring
  lift : Base ring ⟶ X
  commutes : lift ≫ f = baseMap R ring inclusion
  finite : IsFinite (baseMap R ring inclusion)
  etale : Etale (baseMap R ring inclusion)
  surjective : Surjective (baseMap R ring inclusion)
  degree : ∀ z, 0 < (baseMap R ring inclusion).finrank z ∧
    (baseMap R ring inclusion).finrank z ≤ f.finrank z

attribute [instance] AffineComponent.commRing AffineComponent.domain
  AffineComponent.noetherian AffineComponent.normal AffineComponent.rational

lemma affine_component {X : Scheme.{u}} (f : X ⟶ Base R)
    [IsFinite f] [Etale f] [Surjective f] : Nonempty (AffineComponent R f) := by
  obtain ⟨U, hc, hi, hs, hr⟩ := integral_component R f
  letI := hi
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hc)
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : IsAffine U := isAffine_of_isAffineHom U.ι
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let S := Γ(U, ⊤)
  letI : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  let q : Base S ⟶ X := (Scheme.isoSpec U).inv ≫ U.ι
  let ι : R →+* S := (Spec.preimage (q ≫ f)).hom
  have he : baseMap R S ι = q ≫ f := Spec.map_preimage _
  letI : Algebra R S := ι.toAlgebra
  letI : IsFinite (baseMap R S ι) := by rw [he]; dsimp [q]; infer_instance
  letI : Etale (baseMap R S ι) := by rw [he]; dsimp [q]; infer_instance
  letI : Surjective (U.ι ≫ f) := hs
  letI : Surjective (baseMap R S ι) := by
    rw [he]; change Surjective ((Scheme.isoSpec U).inv ≫ (U.ι ≫ f)); infer_instance
  letI : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp (show Etale (baseMap R S ι) from inferInstance))
  letI : IsIntegrallyClosed S := ArithmeticThetaSmoothNormality.etaleDomain_integrallyClosed R S
  letI : Algebra ℚ S := (ι.comp (algebraMap ℚ R)).toAlgebra
  refine ⟨{
    ring := S
    inclusion := ι
    lift := q
    commutes := he.symm
    finite := inferInstance
    etale := inferInstance
    surjective := inferInstance
    degree := ?_ }⟩
  intro z
  refine ⟨(baseMap R S ι).one_le_finrank_iff_surjective.mpr inferInstance z, ?_⟩
  rw [he]
  change ((Scheme.isoSpec U).inv ≫ (U.ι ≫ f)).finrank z ≤ _
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  exact hr z

lemma mul_val_congr (W : WeierstrassCurve R) (G : Law R W)
    {T : Scheme.{u}} {t t' : T ⟶ Base R} (ht : t = t')
    (x y : SchemeHomOver t (structureMap R W))
    (x' y' : SchemeHomOver t' (structureMap R W))
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    (G.mul t x y).val = (G.mul t' x' y').val := by
  subst t'
  have hx' : x = x' := Subtype.ext hx
  have hy' : y = y' := Subtype.ext hy
  subst x'
  subst y'
  rfl

/-- Transport a full marking along the actual pointed Cartesian curve comparison. -/
lemma change_ring (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (S : Type u) [CommRing S] [IsDomain S] (ι : R →+* S)
    (L : ℕ) (A : FullLevel R W G L (baseMap R S ι)) :
    ∃ (H : Law S (W.map ι)) (b : Curve S (W.map ι) ⟶ Curve R W),
      IsOriginLaw S (W.map ι) H ∧ IsBaseChange R W G S (W.map ι) H ι b ∧
      Nonempty (FullLevel S (W.map ι) H L (𝟙 (Base S))) := by
  letI : Algebra R S := ι.toAlgebra
  let Ws := W.map ι
  let fs := structureMap S Ws
  obtain ⟨α, hα⟩ := WeierstrassProjModel.projModel_isPullback_baseChange_ring W.toProjective S
  obtain ⟨b, hb, he⟩ := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.pointed_cartesian
    ι fs α hα G (WeierstrassProjModel.kwZeroSect S Ws)
  have he' : origin S Ws ≫ b = baseMap R S ι ≫ origin R W := he.trans (hG.1 _)
  obtain ⟨H, hm, ho⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
      ι (structureMap R W) fs b hb G
  have hH : IsOriginLaw S Ws H := by
    constructor
    · intro T t
      apply hb.hom_ext
      · simp only [ho, hG.1, Category.assoc, he', baseMap]
      · exact (H.one t).property.trans (by
          rw [Category.assoc]
          exact ((congrArg (fun z => t ≫ z)
            (WeierstrassProjModel.kwZeroSect S Ws).property).trans
            (Category.comp_id t)).symm)
    · intro T t x y
      apply Subtype.ext
      apply hb.hom_ext
      · rw [hm, hm, hG.2]
      · exact (H.mul t x y).property.trans (H.mul t y x).property.symm
  have hn := ArithmeticThetaGeneralEllipticKatoR0168.BaseChange.nsmul_comp ι fs b hb G H hm ho
  let push (x : SchemeHomOver (𝟙 (Base S)) fs) :
      SchemeHomOver (baseMap R S ι) (structureMap R W) :=
    ⟨x.val ≫ b, by
      have hw : b ≫ structureMap R W = fs ≫ baseMap R S ι := hb.w
      rw [Category.assoc, hw, ← Category.assoc, x.property, Category.id_comp]⟩
  have hp_inj : Function.Injective push := by
    intro x y h
    apply Subtype.ext
    apply hb.hom_ext
    · exact congrArg Subtype.val h
    · exact x.property.trans y.property.symm
  have hp_one : push (H.one (𝟙 _)) = G.one (baseMap R S ι) := by
    apply Subtype.ext
    change (H.one (𝟙 _)).val ≫ b = _
    rw [hH.1, Category.id_comp, he', hG.1]
  have hp_mul (x y : SchemeHomOver (𝟙 (Base S)) fs) :
      push (H.mul (𝟙 _) x y) = G.mul (baseMap R S ι) (push x) (push y) := by
    apply Subtype.ext
    exact (hm (𝟙 _) x y).trans
      (mul_val_congr R W G (Category.id_comp _) _ _ _ _ rfl rfl)
  have hp_nsmul (x : SchemeHomOver (𝟙 (Base S)) fs) (n : ℕ) :
      push (H.nsmul (𝟙 _) n x) = G.nsmul (baseMap R S ι) n (push x) := by
    induction n with
    | zero => exact hp_one
    | succ n ih => rw [H.nsmul_succ, hp_mul, ih, G.nsmul_succ]
  let lift (x : SchemeHomOver (baseMap R S ι) (structureMap R W)) :
      SchemeHomOver (𝟙 (Base S)) fs :=
    ⟨hb.lift x.val (𝟙 _) (by exact x.property.trans (Category.id_comp _).symm), hb.lift_snd _ _ _⟩
  have hp_lift (x : SchemeHomOver (baseMap R S ι) (structureMap R W)) :
      push (lift x) = x := Subtype.ext (hb.lift_fst _ _ _)
  refine ⟨H, b, hH, ⟨hb, he', hn⟩, ⟨{
    x := lift A.x
    y := lift A.y
    killed_x := ?_
    killed_y := ?_
    avoids := ?_ }⟩⟩
  · apply hp_inj
    rw [hp_nsmul, hp_lift, A.killed_x, hp_one]
  · apply hp_inj
    rw [hp_nsmul, hp_lift, A.killed_y, hp_one]
  · intro i j hij
    have hc : (H.mul (𝟙 _) (H.nsmul (𝟙 _) i.val (lift A.x))
        (H.nsmul (𝟙 _) j.val (lift A.y))).val ≫ b =
        (G.mul (baseMap R S ι) (G.nsmul (baseMap R S ι) i.val A.x)
          (G.nsmul (baseMap R S ι) j.val A.y)).val := by
      change (push _).val = _
      rw [hp_mul, hp_nsmul, hp_nsmul, hp_lift, hp_lift]
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ ⟨s,hs⟩
    apply Set.disjoint_left.mp (A.avoids i j hij)
    · exact ⟨t,rfl⟩
    · refine ⟨baseMap R S ι s, ?_⟩
      calc
        origin R W (baseMap R S ι s) = b (origin S Ws s) :=
          (congrArg (fun f => f s) he').symm
        _ = _ := (congrArg b hs).trans (congrArg (fun f => f t) hc)

end NormalAffineExtensionR0175
open NormalAffineExtensionR0175 CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171

/-- A normal integral affine splitting extension, extracted from the full GL cover. -/
theorem normal_affine_level_extension :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) , Nonempty (ArithmeticThetaFullLevelCoverR0175.LevelExtension R W G L) := by
  intro R _ _ _ _ _ W _ G hG L hL
  obtain ⟨Z,hZ⟩ := full_level_representability R W G hG L hL
  obtain ⟨hf,he,hs,hr⟩ := full_level_cover_geometry R W G hG L hL Z hZ
  letI := hf
  letI := he
  letI := hs
  obtain ⟨C⟩ := affine_component R Z.projection
  let A := CoverGeometryR0175.pullMark C.lift C.commutes Z.level
  obtain ⟨H,b,hH,hb,⟨B⟩⟩ := change_ring R W G hG C.ring C.inclusion L A
  exact ⟨{
    ring := C.ring
    inclusion := C.inclusion
    law := H
    originLaw := hH
    curveMap := b
    cartesian := hb
    finite := C.finite
    etale := C.etale
    surjective := C.surjective
    degree := fun z => ⟨(C.degree z).1, (C.degree z).2.trans_eq (hr z)⟩
    level := B }⟩

#print axioms normal_affine_level_extension
end ArithmeticThetaFullLevelCoverR0175
