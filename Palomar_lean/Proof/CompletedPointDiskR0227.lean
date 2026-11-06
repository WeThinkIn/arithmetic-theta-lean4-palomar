module

public import AmbientCompletedRootsDefinitionsR0227
public import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
public import Theorems.Thm_AlgebraicGeometry_exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one
public import CompletionUniformizer

@[expose] public section

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaAmbientCompletedRootsR0227
namespace CompletedPointDiskR0227
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Sections)
open ArithmeticThetaTateCuspsR0181 (Disk diskStructure genericInclusion)

lemma coordinate (k : Type) [Field k] [IsAlgClosed k] (X : Curve k)
    (x : X.space) (hx : IsClosed ({x} : Set X.space)) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.space.presheaf.stalk x))
        (X.space.presheaf.stalk x) ≃+* PowerSeries k,
      ∀ a : k, e (algebraMap _ _ ((X.space.presheaf.germ ⊤ x trivial).hom
        (X.map.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)))) =
          PowerSeries.C a := by
  letI := X.smooth
  letI : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  letI : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective (IsLocalRing.residue k)
      ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩)
  exact exists_adicCompletion_stalk_ringEquiv_powerSeries_of_smoothOfRelativeDimension_one
    k X.map x (Subsingleton.elim _ _) hx

lemma disk_frame (k : Type) [Field k] {Y : Scheme}
    (f : Disk k ⟶ Y) (J : Y.Modules) (hJ : Scheme.Modules.IsInvertible J) :
    ∃ h : Sections ((Scheme.Modules.pullback f).obj J),
      ArithmeticThetaRelativeDiscriminantR0171.IsFrame
        ((Scheme.Modules.pullback f).obj J) ⊤ h := by
  obtain ⟨U, s, hx, hs⟩ :=
    ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.local_frame_exists
      hJ (f (IsLocalRing.closedPoint (PowerSeries k)))
  have hU : (⊤ : (Disk k).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hx).ge
  exact ⟨_, ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.frame_restrict
    _ hU _ (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame
      f J s hs)⟩

lemma local_structure (k : Type) [Field k] (X : Curve k) (x : X.space)
    (φ : X.space.presheaf.stalk x →+* PowerSeries k)
    (hφ : ∀ a : k, φ ((X.space.presheaf.germ ⊤ x trivial).hom
      (X.map.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a))) =
        PowerSeries.C a) :
    (Spec.map (CommRingCat.ofHom φ) ≫ X.space.fromSpecStalk x) ≫ X.map =
      diskStructure k := by
  apply ext_to_Spec
  simp only [op_comp, Functor.map_comp, Category.assoc]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.map.appTop ≫
    (X.space.fromSpecStalk x).appTop ≫ (Spec.map (CommRingCat.ofHom φ)).appTop = _
  have h3 : (Spec (X.space.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.space.presheaf.stalk x)).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.fromSpecStalk_appTop, h3, Category.comp_id]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))).appTop ≫ _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact hφ a

lemma completed_disk (k : Type) [Field k] [IsAlgClosed k] (X : Curve k)
    (x : X.space) (hx : IsClosed ({x} : Set X.space)) :
    ∃ f : Disk k ⟶ X.space, IsCompletedDisk k X x f := by
  letI := X.smooth
  letI := X.geometricallyIntegral
  letI : IsIntegral X.space := GeometricallyIntegral.isIntegral_of_subsingleton X.map
  letI : IsDiscreteValuationRing (X.space.presheaf.stalk x) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed X.map x hx
  obtain ⟨e, he⟩ := coordinate k X x hx
  let φ : X.space.presheaf.stalk x →+* PowerSeries k :=
    e.toRingHom.comp (algebraMap _ _)
  letI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm⟩
  letI : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨f, hf⟩ := (SpecToEquivOfLocalRing X.space
    (CommRingCat.of (PowerSeries k))).surjective ⟨x, CommRingCat.ofHom φ, inferInstance⟩
  have hfac : f = Spec.map (CommRingCat.ofHom φ) ≫ X.space.fromSpecStalk x := by
    let E := SpecToEquivOfLocalRing X.space (CommRingCat.of (PowerSeries k))
    calc
      f = E.symm (E f) := (E.symm_apply_apply f).symm
      _ = E.symm ⟨x, CommRingCat.ofHom φ, inferInstance⟩ := congrArg E.symm hf
      _ = _ := rfl
  have hbase : f ≫ X.map = diskStructure k := by
    rw [hfac]
    exact local_structure k X x φ he
  have hi : Function.Injective φ :=
    ArithmeticThetaSectionCompletion.completion_expansion_injective _ k e
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hi]
    exact bot_le
  haveI : IsDominant (X.space.fromSpecStalk x) := by
    constructor
    apply Dense.mono (s₁ := {_root_.genericPoint X.space})
    · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X.space).specializes trivial
    · rw [dense_iff_closure_eq]
      exact genericPoint_spec X.space
  haveI : IsDominant (genericInclusion k) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      (algebraMap (PowerSeries k) (LaurentSeries k))).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))]
    exact bot_le
  have hdom : IsDominant (genericInclusion k ≫ f) := by
    rw [hfac]
    infer_instance
  obtain ⟨hc, hm⟩ := SpecToEquivOfLocalRing_eq_iff.mp hf
  change f (IsLocalRing.closedPoint (PowerSeries k)) = x at hc
  refine ⟨f, hbase, hc, hdom, ?_⟩
  cases hc
  refine ⟨e, ?_⟩
  intro a
  change e (algebraMap _ _ a) = (Scheme.stalkClosedPointTo f).hom a
  have hm' : Scheme.stalkClosedPointTo f = CommRingCat.ofHom φ := by
    change Scheme.stalkClosedPointTo f =
      (X.space.presheaf.stalkCongr (show Inseparable (f (IsLocalRing.closedPoint (PowerSeries k)))
        (f (IsLocalRing.closedPoint (PowerSeries k))) from Inseparable.refl _)).hom ≫ CommRingCat.ofHom φ at hm
    simpa using hm
  rw [hm']
  rfl

end CompletedPointDiskR0227
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaFiniteFieldModelsR0221 (Curve Sections)

theorem completed_point_disk (k : Type) [Field k] [IsAlgClosed k]
    (X : Curve k) (x : X.space) (hx : IsClosed ({x} : Set X.space))
    (J : X.space.Modules) (hJ : Scheme.Modules.IsInvertible J) :
    ∃ f : ArithmeticThetaTateCuspsR0181.Disk k ⟶ X.space,
      IsCompletedDisk k X x f ∧ ∃ h : Sections ((Scheme.Modules.pullback f).obj J),
        ArithmeticThetaRelativeDiscriminantR0171.IsFrame
          ((Scheme.Modules.pullback f).obj J) ⊤ h := by
  obtain ⟨f, hf⟩ := CompletedPointDiskR0227.completed_disk k X x hx
  exact ⟨f, hf, CompletedPointDiskR0227.disk_frame k f J hJ⟩

end ArithmeticThetaAmbientCompletedRootsR0227
#print axioms ArithmeticThetaAmbientCompletedRootsR0227.completed_point_disk
