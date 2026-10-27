import SchemeThetaNaturalityDefinitionsR0262
import SchemeCotangentCoherenceR0205
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
namespace ComparisonCoherence
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaPolygonCartierR0133 (unitPullback)
open ArithmeticThetaGenericEvaluationR0140.GenericDualLocalizationR0140

/-- Inclusion normalization determines composition for arbitrary Cartier ideals,
so it applies to every power, including the zeroth power. -/
theorem ideal_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hK : K.IsInvertible)
    (hf : I.comap f = J) (hg : J.comap g = K) (hgf : I.comap (g ≫ f) = K) :
    (Scheme.Modules.pullback g).map (idealPullbackIso f I J hI hJ hf).hom ≫
      (idealPullbackIso g J K hJ hK hg).hom =
    (Scheme.Modules.pullbackComp g f).hom.app I.module ≫
      (idealPullbackIso (g ≫ f) I K hI hK hgf).hom := by
  let : Mono K.moduleι := inferInstanceAs (Mono (kernel.ι _))
  apply (cancel_mono K.moduleι).mp
  rw [Category.assoc, idealPullbackIso_inclusion, ← Category.assoc,
    ← Functor.map_comp, idealPullbackIso_inclusion, Functor.map_comp,
    Category.assoc, Category.assoc, idealPullbackIso_inclusion]
  have hu := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom g f
  change (Scheme.Modules.pullbackComp g f).hom.app _ ≫ unitPullback (g ≫ f) =
    (Scheme.Modules.pullback g).map (unitPullback f) ≫ unitPullback g at hu
  rw [← hu, ← Category.assoc]
  exact congrArg (fun q ↦ q ≫ unitPullback (g ≫ f))
    ((Scheme.Modules.pullbackComp g f).hom.naturality I.moduleι)

abbrev ideal {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) :=
  idealPullbackIso f E.zero.ker F.zero.ker
    (CartesianIdentityIdeal.zero_ideal_invertible E)
    (CartesianIdentityIdeal.zero_ideal_invertible F)
    (CartesianIdentityIdeal.ideal_comap E F b f hc hz)

abbrev cotangent {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) :=
  cotangentComparison E F b f hz (ideal E F b f hc hz)

lemma cotangent_compatible {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) :
    CotangentCompatible E F b f hz (cotangent E F b f hc hz) := by
  refine ⟨ideal E F b f hc hz, ?_, rfl⟩
  exact idealPullbackIso_inclusion _ _ _ _ _ _

lemma cotangent_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (H : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
    (c : U ⟶ T) (g : H.curve ⟶ F.curve)
    (hd : IsPullback g H.p F.p c) (hw : H.zero ≫ g = c ≫ F.zero)
    (he : IsPullback (g ≫ f) H.p E.p (c ≫ b))
    (hv : H.zero ≫ (g ≫ f) = (c ≫ b) ≫ E.zero) :
    cotangent E H (c ≫ b) (g ≫ f) he hv =
      ((Scheme.Modules.pullbackComp c b).app (Cotangent E)).symm ≪≫
        (Scheme.Modules.pullback c).mapIso (cotangent E F b f hc hz) ≪≫
          cotangent F H c g hd hw := by
  apply Iso.ext
  apply (Iso.eq_inv_comp _).mpr
  exact (scheme_cotangent_coherence.2 S T U E F H b c f g hz hw hv _ _ _
    (cotangent_compatible E F b f hc hz)
    (cotangent_compatible F H c g hd hw)
    (cotangent_compatible E H (c ≫ b) (g ≫ f) he hv)).symm

/-- Tensoring the two prescribed comparisons commutes with successive pullback. -/
lemma tensor_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {M N : X.Modules} {M' N' : Y.Modules} {M'' N'' : Z.Modules}
    (i : (Scheme.Modules.pullback f).obj M ≅ M')
    (j : (Scheme.Modules.pullback f).obj N ≅ N')
    (i' : (Scheme.Modules.pullback g).obj M' ≅ M'')
    (j' : (Scheme.Modules.pullback g).obj N' ≅ N'') :
    Scheme.Modules.pullbackTensorObjIso (g ≫ f) M N ≪≫
      ((((Scheme.Modules.pullbackComp g f).app M).symm ≪≫
          (Scheme.Modules.pullback g).mapIso i ≪≫ i') ⊗ᵢ
       (((Scheme.Modules.pullbackComp g f).app N).symm ≪≫
          (Scheme.Modules.pullback g).mapIso j ≪≫ j')) =
    ((Scheme.Modules.pullbackComp g f).app (M ⊗ N)).symm ≪≫
      (Scheme.Modules.pullback g).mapIso
        (Scheme.Modules.pullbackTensorObjIso f M N ≪≫ (i ⊗ᵢ j)) ≪≫
      (Scheme.Modules.pullbackTensorObjIso g M' N' ≪≫ (i' ⊗ᵢ j')) := by
  have hp := congrArg Iso.inv (Scheme.Modules.pullbackComp_app_tensorObj g f M N)
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, tensorIso_inv,
    Iso.app_inv, Category.assoc] at hp
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [hp]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]
  have hn := (Functor.OplaxMonoidal.δ_natural (Scheme.Modules.pullback g) i.hom j.hom).symm
  change (Scheme.Modules.pullback g).map (i.hom ⊗ₘ j.hom) ≫
      (Scheme.Modules.pullbackTensorObjIso g M' N').hom =
    (Scheme.Modules.pullbackTensorObjIso g _ _).hom ≫
      ((Scheme.Modules.pullback g).map i.hom ⊗ₘ
        (Scheme.Modules.pullback g).map j.hom) at hn
  rw [← Category.assoc ((Scheme.Modules.pullback g).map (i.hom ⊗ₘ j.hom)), hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom]

/-- The dual comparison is characterized by the pulled-back evaluation pairing. -/
lemma dual_pairing {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) :
    (Scheme.Modules.pullbackTensorObjIso f M (Scheme.Modules.dual M)).hom ≫
      (e.hom ⊗ₘ (dualComparison f M ≫ (MonoidalClosed.pre e.inv).app (𝟙_ Y.Modules))) ≫
      (ihom.ev N).app (𝟙_ Y.Modules) =
    (Scheme.Modules.pullback f).map ((ihom.ev M).app (𝟙_ X.Modules)) ≫ unitPullback f := by
  have h : (e.hom ⊗ₘ (dualComparison f M ≫
      (MonoidalClosed.pre e.inv).app (𝟙_ Y.Modules))) ≫
        (ihom.ev N).app (𝟙_ Y.Modules) =
      MonoidalClosed.uncurry (dualComparison f M) := by
    rw [MonoidalCategory.tensorHom_def, Category.assoc,
      ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_pre_app,
      ← Category.assoc, ← comp_whiskerRight, e.hom_inv_id,
      id_whiskerRight, Category.id_comp]
  rw [h]
  simp only [dualComparison, MonoidalClosed.uncurry_curry, Iso.hom_inv_id_assoc]

lemma pairing_unique {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (q r : (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M) ⟶ Scheme.Modules.dual N)
    (h : (Scheme.Modules.pullbackTensorObjIso f M (Scheme.Modules.dual M)).hom ≫
        (e.hom ⊗ₘ q) ≫ (ihom.ev N).app (𝟙_ Y.Modules) =
      (Scheme.Modules.pullbackTensorObjIso f M (Scheme.Modules.dual M)).hom ≫
        (e.hom ⊗ₘ r) ≫ (ihom.ev N).app (𝟙_ Y.Modules)) : q = r := by
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (e.hom ▷ (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M))).mp
  simpa only [MonoidalClosed.uncurry_eq, ← Category.assoc,
    ← MonoidalCategory.tensorHom_def] using
      (cancel_epi (Scheme.Modules.pullbackTensorObjIso f M (Scheme.Modules.dual M)).hom).mp h

abbrev dualIso {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (hM : Scheme.Modules.IsInvertible M) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dual M) ≅ Scheme.Modules.dual N := by
  letI := dualComparison_isIso f M hM
  exact asIso (dualComparison f M) ≪≫
    ((MonoidalClosed.internalHom (C := Y.Modules)).mapIso e.symm.op).app (𝟙_ Y.Modules)

lemma dual_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (d : (Scheme.Modules.pullback g).obj N ≅ P)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) :
    dualIso (g ≫ f) (((Scheme.Modules.pullbackComp g f).app M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso e ≪≫ d) hM =
    ((Scheme.Modules.pullbackComp g f).app (Scheme.Modules.dual M)).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (dualIso f e hM) ≪≫ dualIso g d hN := by
  apply Iso.ext
  apply pairing_unique (g ≫ f)
    (((Scheme.Modules.pullbackComp g f).app M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso e ≪≫ d)
  change (Scheme.Modules.pullbackTensorObjIso (g ≫ f) M (Scheme.Modules.dual M)).hom ≫
    (_ ⊗ₘ (dualComparison (g ≫ f) M ≫ (MonoidalClosed.pre _).app _)) ≫ _ = _
  simp only [Iso.op_hom, Iso.symm_hom, Quiver.Hom.unop_op]
  rw [dual_pairing (g ≫ f) (((Scheme.Modules.pullbackComp g f).app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ d)]
  have ht := congrArg Iso.hom (tensor_comp f g e (dualIso f e hM) d (dualIso g d hN))
  simp only [Iso.trans_hom, tensorIso_hom] at ht
  rw [← Category.assoc]
  erw [ht]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change _ = (Scheme.Modules.pullbackComp g f).inv.app _ ≫
    (Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullbackTensorObjIso f M (Scheme.Modules.dual M)).hom ≫
        (e.hom ⊗ₘ (dualComparison f M ≫ (MonoidalClosed.pre e.inv).app _))) ≫
      (Scheme.Modules.pullbackTensorObjIso g N (Scheme.Modules.dual N)).hom ≫
        (d.hom ⊗ₘ (dualComparison g N ≫ (MonoidalClosed.pre d.inv).app _)) ≫ _
  rw [dual_pairing]
  rw [← Category.assoc ((Scheme.Modules.pullback g).map _), ← Functor.map_comp,
    Category.assoc, dual_pairing, Functor.map_comp]
  simp only [Category.assoc]
  have hu := Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom g f
  change (Scheme.Modules.pullbackComp g f).hom.app _ ≫ unitPullback (g ≫ f) =
    (Scheme.Modules.pullback g).map (unitPullback f) ≫ unitPullback g at hu
  rw [← hu, ← Category.assoc ((Scheme.Modules.pullback g).map _)]
  have hn := (Scheme.Modules.pullbackComp g f).hom.naturality
    ((ihom.ev M).app (𝟙_ X.Modules))
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Pasting the structural squares carries coherent base-line maps to the curves. -/
lemma square_comp {S T U X Y Z : Scheme.{u}}
    (a : U ⟶ T) (b : T ⟶ S) (r : U ⟶ Z) (s : T ⟶ Y) (t : S ⟶ X)
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (hg : r ≫ g = a ≫ s) (hf : s ≫ f = b ≫ t)
    (hgf : r ≫ (g ≫ f) = (a ≫ b) ≫ t)
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (d : (Scheme.Modules.pullback g).obj N ≅ P)
    (ed : (Scheme.Modules.pullback (g ≫ f)).obj M ≅ P)
    (hed : (Scheme.Modules.pullback g).map e.hom ≫ d.hom =
      (Scheme.Modules.pullbackComp g f).hom.app M ≫ ed.hom) :
    squarePullbackIso (a ≫ b) t r (g ≫ f) hgf.symm M ≪≫
        (Scheme.Modules.pullback r).mapIso ed =
      ((Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback t).obj M)).symm ≪≫
        (Scheme.Modules.pullback a).mapIso
          (squarePullbackIso b t s f hf.symm M ≪≫ (Scheme.Modules.pullback s).mapIso e) ≪≫
        (squarePullbackIso a s r g hg.symm N ≪≫ (Scheme.Modules.pullback r).mapIso d) := by
  apply Iso.ext
  apply (Iso.eq_inv_comp _).mpr
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback s).map e.hom)),
    CotangentCoherenceProof.square_naturality a s r g hg.symm e.hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hed, Functor.map_comp]
  exact (congrArg (fun q ↦ q ≫ (Scheme.Modules.pullback r).map ed.hom)
    (CotangentCoherenceProof.square_paste a b r s t g f hg hf hgf M)).symm.trans
      (by simp only [Category.assoc])

lemma origin_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (H : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
    (c : U ⟶ T) (g : H.curve ⟶ F.curve)
    (hd : IsPullback g H.p F.p c) (hw : H.zero ≫ g = c ≫ F.zero)
    (he : IsPullback (g ≫ f) H.p E.p (c ≫ b))
    (hv : H.zero ≫ (g ≫ f) = (c ≫ b) ≫ E.zero) (m : ℕ) :
    SchemeThetaSectionCohomology.originPowerComparison E H (c ≫ b) (g ≫ f) he hv m =
      ((Scheme.Modules.pullbackComp g f).app (Scheme.Modules.dual (E.zero.ker ^ m).module)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          (SchemeThetaSectionCohomology.originPowerComparison E F b f hc hz m) ≪≫
        SchemeThetaSectionCohomology.originPowerComparison F H c g hd hw m := by
  let hI := (CartesianIdentityIdeal.zero_ideal_invertible E).pow m
  let hJ := (CartesianIdentityIdeal.zero_ideal_invertible F).pow m
  let hK := (CartesianIdentityIdeal.zero_ideal_invertible H).pow m
  have hf : (E.zero.ker ^ m).comap f = F.zero.ker ^ m := by
    rw [comap_power, CartesianIdentityIdeal.ideal_comap E F b f hc hz]
  have hg : (F.zero.ker ^ m).comap g = H.zero.ker ^ m := by
    rw [comap_power, CartesianIdentityIdeal.ideal_comap F H c g hd hw]
  have hgf : (E.zero.ker ^ m).comap (g ≫ f) = H.zero.ker ^ m := by
    rw [comap_power, CartesianIdentityIdeal.ideal_comap E H (c ≫ b) (g ≫ f) he hv]
  have hi : idealPullbackIso (g ≫ f) _ _ hI hK hgf =
      ((Scheme.Modules.pullbackComp g f).app (E.zero.ker ^ m).module).symm ≪≫
        (Scheme.Modules.pullback g).mapIso (idealPullbackIso f _ _ hI hJ hf) ≪≫
        idealPullbackIso g _ _ hJ hK hg := by
    apply Iso.ext
    apply (Iso.eq_inv_comp _).mpr
    exact (ideal_comp f g _ _ _ hI hJ hK hf hg hgf).symm
  change dualIso (g ≫ f) (idealPullbackIso (g ≫ f) _ _ hI hK hgf) hI.isInvertible_module =
    ((Scheme.Modules.pullbackComp g f).app _).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (dualIso f (idealPullbackIso f _ _ hI hJ hf)
        hI.isInvertible_module) ≪≫
      dualIso g (idealPullbackIso g _ _ hJ hK hg) hJ.isInvertible_module
  rw [hi]
  exact dual_comp f g _ _ _ _

abbrev weight {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :=
  Scheme.Modules.pullbackTensorPowIso b (Cotangent E) m ≪≫
    Scheme.Modules.tensorPowMapIso (cotangent E F b f hc hz) m

lemma weight_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (H : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
    (c : U ⟶ T) (g : H.curve ⟶ F.curve)
    (hd : IsPullback g H.p F.p c) (hw : H.zero ≫ g = c ≫ F.zero)
    (he : IsPullback (g ≫ f) H.p E.p (c ≫ b))
    (hv : H.zero ≫ (g ≫ f) = (c ≫ b) ≫ E.zero) (m : ℕ) :
    weight E H (c ≫ b) (g ≫ f) he hv m =
      ((Scheme.Modules.pullbackComp c b).app ((Cotangent E).tensorPow m)).symm ≪≫
        (Scheme.Modules.pullback c).mapIso (weight E F b f hc hz m) ≪≫
          weight F H c g hd hw m := by
  unfold weight
  rw [cotangent_comp E F H b f hc hz c g hd hw he hv]
  exact Scheme.Modules.pullbackTensorPowIso_trans_tensorPowMapIso_comp b c _ _ _ _ _ m

abbrev baseFactor {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :=
  squarePullbackIso f E.p F.p b hc.w ((Cotangent E).tensorPow m) ≪≫
    (Scheme.Modules.pullback F.p).mapIso (weight E F b f hc hz m)

lemma baseFactor_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (H : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
    (c : U ⟶ T) (g : H.curve ⟶ F.curve)
    (hd : IsPullback g H.p F.p c) (hw : H.zero ≫ g = c ≫ F.zero)
    (he : IsPullback (g ≫ f) H.p E.p (c ≫ b))
    (hv : H.zero ≫ (g ≫ f) = (c ≫ b) ≫ E.zero) (m : ℕ) :
    baseFactor E H (c ≫ b) (g ≫ f) he hv m =
      ((Scheme.Modules.pullbackComp g f).app
        ((Scheme.Modules.pullback E.p).obj ((Cotangent E).tensorPow m))).symm ≪≫
        (Scheme.Modules.pullback g).mapIso (baseFactor E F b f hc hz m) ≪≫
          baseFactor F H c g hd hw m := by
  apply square_comp g f H.p F.p E.p c b hd.w.symm hc.w.symm he.w.symm
  have h := congrArg Iso.hom (weight_comp E F H b f hc hz c g hd hw he hv m)
  exact ((Iso.eq_inv_comp _).mp h).symm

lemma theta_eq {S T : Scheme.{u}} (E : Family S) (F : Family T)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero) (m : ℕ) :
    thetaComparison E F b f hc hz m =
      Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
        (SchemeThetaSectionCohomology.originPowerComparison E F b f hc hz m ⊗ᵢ
          baseFactor E F b f hc hz m) := by
  simp only [baseFactor, CotangentCoherenceProof.square_eq]
  rfl

lemma theta_comp {S T U : Scheme.{u}} (E : Family S) (F : Family T) (H : Family U)
    (b : T ⟶ S) (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)
    (c : U ⟶ T) (g : H.curve ⟶ F.curve)
    (hd : IsPullback g H.p F.p c) (hw : H.zero ≫ g = c ≫ F.zero)
    (he : IsPullback (g ≫ f) H.p E.p (c ≫ b))
    (hv : H.zero ≫ (g ≫ f) = (c ≫ b) ≫ E.zero) (m : ℕ) :
    thetaComparison E H (c ≫ b) (g ≫ f) he hv m =
      ((Scheme.Modules.pullbackComp g f).app (thetaLine E m)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso (thetaComparison E F b f hc hz m) ≪≫
          thetaComparison F H c g hd hw m := by
  rw [theta_eq, theta_eq, theta_eq,
    origin_comp E F H b f hc hz c g hd hw he hv,
    baseFactor_comp E F H b f hc hz c g hd hw he hv]
  exact tensor_comp f g _ _ _ _

/-- A composition-coherent comparison at the identity is forced to be the
pullback identity constraint; no separate choices of tensor-unit frames occur. -/
lemma theta_id {S : Scheme.{u}} (E : Family S) (m : ℕ)
    (hc : IsPullback (𝟙 E.curve) E.p E.p (𝟙 S))
    (hz : E.zero ≫ 𝟙 E.curve = 𝟙 S ≫ E.zero) :
    thetaComparison E E (𝟙 S) (𝟙 E.curve) hc hz m =
      (Scheme.Modules.pullbackId E.curve).app (thetaLine E m) := by
  let e := thetaComparison E E (𝟙 S) (𝟙 E.curve) hc hz m
  have he : IsPullback (𝟙 E.curve ≫ 𝟙 E.curve) E.p E.p (𝟙 S ≫ 𝟙 S) := by
    simpa only [Category.id_comp] using hc
  have hv : E.zero ≫ (𝟙 E.curve ≫ 𝟙 E.curve) = (𝟙 S ≫ 𝟙 S) ≫ E.zero := by
    simp
  have h : e = ((Scheme.Modules.pullbackComp (𝟙 E.curve) (𝟙 E.curve)).app
      (thetaLine E m)).symm ≪≫ (Scheme.Modules.pullback (𝟙 E.curve)).mapIso e ≪≫ e := by
    exact theta_comp E E E (𝟙 S) (𝟙 E.curve) hc hz (𝟙 S) (𝟙 E.curve) hc hz he hv m
  have h0 := congrArg (fun q ↦ q.hom ≫ e.inv) h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at h0
  have hu := congrArg (fun q ↦ q.app (thetaLine E m))
    (Scheme.Modules.pseudofunctor_left_unitality (𝟙 E.curve))
  simp only [NatTrans.comp_app] at hu
  dsimp at hu
  simp only [Category.comp_id] at hu
  let : (Scheme.Modules.pullback (𝟙 E.curve)).Faithful :=
    Functor.Faithful.of_iso (Scheme.Modules.pullbackId E.curve).symm
  apply Iso.ext
  apply (Scheme.Modules.pullback (𝟙 E.curve)).map_injective
  apply (cancel_epi ((Scheme.Modules.pullbackComp (𝟙 E.curve) (𝟙 E.curve)).app
    (thetaLine E m)).inv).mp
  exact h0.symm.trans hu.symm

end ComparisonCoherence
/-- Identity and composition coherence of the accepted Cartier/conormal theta comparison. -/
theorem scheme_theta_comparison_coherence :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ m : ℕ, (∀ (hc : CategoryTheory.IsPullback (CategoryTheory.CategoryStruct.id E.curve) E.p E.p (CategoryTheory.CategoryStruct.id S)) (hz : CategoryTheory.CategoryStruct.comp E.zero (CategoryTheory.CategoryStruct.id E.curve) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id S) E.zero), ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E E (CategoryTheory.CategoryStruct.id S) (CategoryTheory.CategoryStruct.id E.curve) hc hz m = (AlgebraicGeometry.Scheme.Modules.pullbackId E.curve).app (ArithmeticThetaSchemeThetaMarkingR0259.thetaLine E m)) ∧ (∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ (U : AlgebraicGeometry.Scheme.{u}) (H : ArithmeticThetaLocalWeierstrassR0203.Family U) (c : Quiver.Hom U T) (g : Quiver.Hom H.curve F.curve) (hd : CategoryTheory.IsPullback g H.p F.p c) (hw : CategoryTheory.CategoryStruct.comp H.zero g = CategoryTheory.CategoryStruct.comp c F.zero) (he : CategoryTheory.IsPullback (CategoryTheory.CategoryStruct.comp g f) H.p E.p (CategoryTheory.CategoryStruct.comp c b)) (hv : CategoryTheory.CategoryStruct.comp H.zero (CategoryTheory.CategoryStruct.comp g f) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp c b) E.zero), ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E H (CategoryTheory.CategoryStruct.comp c b) (CategoryTheory.CategoryStruct.comp g f) he hv m = CategoryTheory.Iso.trans ((AlgebraicGeometry.Scheme.Modules.pullbackComp g f).app (ArithmeticThetaSchemeThetaMarkingR0259.thetaLine E m)).symm (CategoryTheory.Iso.trans ((AlgebraicGeometry.Scheme.Modules.pullback g).mapIso (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison E F b f hc hz m)) (ArithmeticThetaSchemeThetaNaturalityR0262.thetaComparison F H c g hd hw m))) := by
  intro k _ _ S σ E m
  constructor
  · intro hc hz
    exact ComparisonCoherence.theta_id E m hc hz
  · intro T F b f hc hz U H c g hd hw he hv
    exact ComparisonCoherence.theta_comp E F H b f hc hz c g hd hw he hv m

#print axioms scheme_theta_comparison_coherence

end ArithmeticThetaSchemeThetaNaturalityR0262
