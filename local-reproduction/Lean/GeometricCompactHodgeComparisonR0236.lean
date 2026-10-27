import ArithmeticSectionsDefinitionsR0236

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaArithmeticSectionsR0236
namespace GeometricCompactHodgeComparison
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaBoundaryConstantsR0235
open ArithmeticThetaBoundaryConstantsR0235.CompactHodgeConstantComparison
open ArithmeticThetaBoundaryConstantsR0235.GeometricCanonicalHodgeDescent

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
  {L : ℕ} {ι : k →+* l}
  {D : LevelData k L} {E : LevelData l L}
  {X : Compactification k L D} {Y : Compactification l L E}

/-- The actual pullback extension has its tautological normalized comparison. -/
lemma pullback_compatible (C : Comparison k L ι D E X Y)
    (H : Extension k L D X) :
    CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H
      (pullbackExtension ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H)
      (Iso.refl _) := by
  apply (compatible_iff _ _ _ _ _ _ _ _).mpr
  simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Geometric canonicity is preserved by the specified compact coefficient
map, with its actual classifier and normalized open differential comparison. -/
lemma pullback_geometric (hL : 3 ≤ L) (heven : Even L)
    (C : Comparison k L ι D E X Y) (H : Extension k L D X)
    (hH : GeometricallyCanonical H) :
    GeometricallyCanonical
      (pullbackExtension ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H) := by
  let HC := pullbackExtension ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H
  apply (geometric_iff_pullback_canonical l L hL heven HC).mpr
  intro m _ _ _ κ V Z f F hf hF e he
  let B : CoefficientMap l L κ E V Y Z := ⟨f, F, hf, hF, e, he⟩
  let CB := coefficientComposite k L ι κ hL heven C B
  let HCB := pullbackExtension κ f F hF e HC
  let HD := pullbackExtension (κ.comp ι) CB.openMap CB.compactMap
    CB.extendsOpen CB.hodgeMap H
  have hD : Canonical m L HD :=
    (geometric_iff_pullback_canonical k L hL heven H).mp hH m (κ.comp ι)
      V Z CB.openMap CB.compactMap CB.classifies CB.extendsOpen CB.hodgeMap CB.normalized
  have hc := compactCompatible_composite k L ι κ hL heven C B H HC HCB
    (Iso.refl _) (Iso.refl _) (pullback_compatible C H) (pullback_compatible B HC)
  let a : HD.line ≅ HCB.line :=
    ((Scheme.Modules.pullbackComp B.compactMap C.compactMap).app H.line).symm ≪≫
      (Scheme.Modules.pullback B.compactMap).mapIso (Iso.refl HC.line) ≪≫ Iso.refl HCB.line
  exact canonical_of_open_iso m L HD HCB a
    ((compatible_iff (κ.comp ι) CB.openMap CB.compactMap CB.extendsOpen
      CB.hodgeMap H HCB a).mp hc) hD

/-- Uniqueness needs neither a rational cusp nor an algebraic-closure
hypothesis. It is rigidity of the specified open restriction. -/
lemma comparison_unique (C : Comparison k L ι D E X Y)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a b : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (ha : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J a)
    (hb : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J b) :
    a = b :=
  compact_comparison_unique ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J a b ha hb

open CategoryTheory.Limits Opposite

/-- Compatibility on the kernel pair gives the full family compatibility
required by the accepted fpqc morphism descent theorem. -/
lemma compatible_of_pair {S T : Scheme.{0}} (q : T ⟶ S)
    (P : (Over S)ᵒᵖ ⥤ Type) (a : P.obj (op (Over.mk q)))
    (h : P.map (Over.homMk (U := Over.mk (pullback.snd q q ≫ q)) (V := Over.mk q) (pullback.fst q q)
          (show pullback.fst q q ≫ q = pullback.snd q q ≫ q from pullback.condition)).op a =
        P.map (Over.homMk (U := Over.mk (pullback.snd q q ≫ q)) (V := Over.mk q) (pullback.snd q q) rfl).op a) :
    Presieve.Arrows.Compatible P
      (fun _ : Unit => Over.homMk (U := Over.mk q) (V := Over.mk (𝟙 S)) q)
      (fun _ => a) := by
  intro i j Z f g hfg
  let t : Z ⟶ Over.mk (pullback.snd q q ≫ q) :=
    Over.homMk (pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm))
      (by simpa only [Over.mk_hom, pullback.lift_snd_assoc] using Over.w g)
  have hf : t ≫ Over.homMk (U := Over.mk (pullback.snd q q ≫ q)) (V := Over.mk q) (pullback.fst q q) pullback.condition = f := by
    ext; exact pullback.lift_fst _ _ _
  have hg : t ≫ Over.homMk (U := Over.mk (pullback.snd q q ≫ q)) (V := Over.mk q) (pullback.snd q q) rfl = g := by
    ext; exact pullback.lift_snd _ _ _
  have hh := congrArg (fun z => P.map t.op z) h
  simpa only [← CategoryTheory.Functor.map_comp_apply, ← op_comp, hf, hg] using hh

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- Schematic density detects restriction of the presheaf of line morphisms. -/
lemma hom_presheaf_injective {S : Scheme.{0}} (M N : S.Modules)
    (hN : Scheme.Modules.IsInvertible N) {A B : Over S} (f : A ⟶ B)
    [IsSchemeTheoreticallyDominant f.left] [QuasiCompact f.left] :
    Function.Injective ((CanonicalDatum.MF.presheafHom M N).map f.op) := by
  intro a b hab
  apply hom_eq_of_pullback f.left (hN.pullback B.hom)
  change (Scheme.Modules.pullback f.left).map a = (Scheme.Modules.pullback f.left).map b
  change pullHom (F := CanonicalDatum.MF) a f.left A.hom A.hom (Over.w f) (Over.w f) =
    pullHom (F := CanonicalDatum.MF) b f.left A.hom A.hom (Over.w f) (Over.w f) at hab
  change (CanonicalDatum.MF.map f.left.op.toLoc).toFunctor.map a =
    (CanonicalDatum.MF.map f.left.op.toLoc).toFunctor.map b
  rw [map_eq_pullHom (F := CanonicalDatum.MF) a f.left A.hom A.hom (Over.w f) (Over.w f),
    map_eq_pullHom (F := CanonicalDatum.MF) b f.left A.hom A.hom (Over.w f) (Over.w f), hab]


def overFst {S A B : Scheme.{0}} (f : A ⟶ S) (g : B ⟶ S) :
    Over.mk (pullback.snd f g ≫ g) ⟶ Over.mk f :=
  Over.homMk (pullback.fst f g) pullback.condition

def overSnd {S A B : Scheme.{0}} (f : A ⟶ S) (g : B ⟶ S) :
    Over.mk (pullback.snd f g ≫ g) ⟶ Over.mk g :=
  Over.homMk (pullback.snd f g) rfl

/-- Agreement with a downstairs morphism on a schematically dense open
forces the kernel-pair equation for an upstairs morphism. -/
lemma pair_eq_of_overlap {S T U : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    [Flat q] [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (P : (Over S)ᵒᵖ ⥤ Type)
    (hP : ∀ {A B : Over S} (f : A ⟶ B),
      IsSchemeTheoreticallyDominant f.left → QuasiCompact f.left →
      Function.Injective (P.map f.op))
    (a : P.obj (op (Over.mk q))) (b : P.obj (op (Over.mk j)))
    (hab : P.map (overFst q j).op a =
      P.map (overSnd q j).op b) :
    P.map (overFst q q).op a =
      P.map (overSnd q q).op a := by
  let p := pullback.snd q q ≫ q
  let r := overFst p j
  let t₁ : Over.mk (pullback.snd p j ≫ j) ⟶ Over.mk (pullback.snd q j ≫ j) :=
    Over.homMk (pullback.lift (pullback.fst p j ≫ pullback.fst q q) (pullback.snd p j)
      (by rw [Category.assoc, pullback.condition]; exact pullback.condition))
      (by simp only [Over.mk_hom, pullback.lift_snd_assoc])
  let t₂ : Over.mk (pullback.snd p j ≫ j) ⟶ Over.mk (pullback.snd q j ≫ j) :=
    Over.homMk (pullback.lift (pullback.fst p j ≫ pullback.snd q q) (pullback.snd p j)
      (by rw [Category.assoc]; exact pullback.condition))
      (by simp only [Over.mk_hom, pullback.lift_snd_assoc])
  have h₁ : r ≫ overFst q q = t₁ ≫ overFst q j := by
    ext; exact (pullback.lift_fst _ _ _).symm
  have h₂ : r ≫ overSnd q q = t₂ ≫ overFst q j := by
    ext; exact (pullback.lift_fst _ _ _).symm
  have hv : t₁ ≫ overSnd q j = t₂ ≫ overSnd q j := by
    ext; exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  letI : Flat p := by dsimp [p]; infer_instance
  letI : IsSchemeTheoreticallyDominant r.left := by
    change IsSchemeTheoreticallyDominant (pullback.fst p j)
    infer_instance
  letI : QuasiCompact r.left := by
    change QuasiCompact (pullback.fst p j)
    infer_instance
  apply hP r inferInstance inferInstance
  change P.map r.op (P.map (overFst q q).op a) = P.map r.op (P.map (overSnd q q).op a)
  calc
    _ = P.map t₁.op (P.map (overFst q j).op a) := by
      exact (P.map_comp_apply (overFst q q).op r.op a).symm.trans
        ((congrArg (fun f => P.map f.op a) h₁).trans
          (P.map_comp_apply (overFst q j).op t₁.op a))
    _ = P.map t₁.op (P.map (overSnd q j).op b) := congrArg (fun z => P.map t₁.op z) hab
    _ = P.map t₂.op (P.map (overSnd q j).op b) := by
      simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp, hv]
    _ = P.map t₂.op (P.map (overFst q j).op a) := congrArg (fun z => P.map t₂.op z) hab.symm
    _ = _ := (P.map_comp_apply (overFst q j).op t₂.op a).symm.trans
      ((congrArg (fun f => P.map f.op a) h₂.symm).trans
        (P.map_comp_apply (overSnd q q).op r.op a))


/-- Apply the accepted fpqc descent of morphisms once the dense-open
normalization has supplied the compatibility equation. -/
lemma hom_descend_of_overlap {S T U : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    [Flat q] [QuasiCompact q] [Surjective q]
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (M N : S.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ⟶ (Scheme.Modules.pullback q).obj N)
    (b : (Scheme.Modules.pullback j).obj M ⟶ (Scheme.Modules.pullback j).obj N)
    (hab : (CanonicalDatum.MF.presheafHom M N).map (overFst q j).op a =
      (CanonicalDatum.MF.presheafHom M N).map (overSnd q j).op b) :
    ∃ c : M ⟶ N, (Scheme.Modules.pullback q).map c = a := by
  have hp := pair_eq_of_overlap q j (CanonicalDatum.MF.presheafHom M N)
    (fun f hf hq => @hom_presheaf_injective _ M N hN _ _ f hf hq) a b hab
  have hc := compatible_of_pair q (CanonicalDatum.MF.presheafHom M N) a hp
  let d := Pseudofunctor.DescentData.subtypeCompatibleHomEquiv CanonicalDatum.MF
    (fun _ : Unit => q) ⟨fun _ => a, hc⟩
  obtain ⟨c, he⟩ :=
    (ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective
      q M N hM hN).2 d
  exact ⟨c, congrArg (fun f => f.hom ()) he⟩

/-- The accepted full faithfulness also descends the inverse and both
inverse identities, so an overlap-compatible isomorphism descends. -/
lemma iso_descend_of_overlap {S T U : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    [Flat q] [QuasiCompact q] [Surjective q]
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (M N : S.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj N)
    (b : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
    (hab : (CanonicalDatum.MF.presheafHom M N).map (overFst q j).op a.hom =
      (CanonicalDatum.MF.presheafHom M N).map (overSnd q j).op b.hom) :
    ∃ c : M ≅ N, (Scheme.Modules.pullback q).mapIso c = a := by
  have hp := pair_eq_of_overlap q j (CanonicalDatum.MF.presheafHom M N)
    (fun f hf hq => @hom_presheaf_injective _ M N hN _ _ f hf hq) a.hom b.hom hab
  have hc := compatible_of_pair q (CanonicalDatum.MF.presheafHom M N) a.hom hp
  let d := Pseudofunctor.DescentData.subtypeCompatibleHomEquiv CanonicalDatum.MF
    (fun _ : Unit => q) ⟨fun _ => a.hom, hc⟩
  let F := CanonicalDatum.MF.toDescentData (fun _ : Unit => q)
  let e : F.obj M ≅ F.obj N := Pseudofunctor.DescentData.isoMk (fun _ => a) d.comm
  have hMN := ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q M N hM hN
  have hNM := ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q N M hN hM
  obtain ⟨c, hc⟩ := hMN.2 e.hom
  obtain ⟨d, hd⟩ := hNM.2 e.inv
  have hcd : c ≫ d = 𝟙 M := by
    apply (ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q M M hM hM).1
    change F.map (c ≫ d) = F.map (𝟙 M)
    rw [F.map_comp, F.map_id, hc, hd, e.hom_inv_id]
  have hdc : d ≫ c = 𝟙 N := by
    apply (ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.morphisms_bijective q N N hN hN).1
    change F.map (d ≫ c) = F.map (𝟙 N)
    rw [F.map_comp, F.map_id, hd, hc, e.inv_hom_id]
  refine ⟨⟨c, d, hcd, hdc⟩, ?_⟩
  apply Iso.ext
  exact congrArg (fun f => f.hom ()) hc

open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback.LDescDatumAux

/-- The presheaf restriction equation is the usual commutative square
for pullback morphisms, with the standard pullback associators retained. -/
lemma pullHom_eq_of_square {S T U V : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    (u : V ⟶ T) (v : V ⟶ U) (h : u ≫ q = v ≫ j)
    (M N : S.Modules)
    (a : (Scheme.Modules.pullback q).obj M ⟶ (Scheme.Modules.pullback q).obj N)
    (b : (Scheme.Modules.pullback j).obj M ⟶ (Scheme.Modules.pullback j).obj N)
    (hab : (Scheme.Modules.pullback u).map a ≫ (squarePullbackIso u q v j h N).hom =
      (squarePullbackIso u q v j h M).hom ≫ (Scheme.Modules.pullback v).map b) :
    pullHom (F := CanonicalDatum.MF) a u (v ≫ j) (v ≫ j) h h =
      pullHom (F := CanonicalDatum.MF) b v (v ≫ j) (v ≫ j) rfl rfl := by
  rw [pullHom_FF, pullHom_FF]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
  apply (cancel_epi (((Scheme.Modules.pullbackComp u q).app M).hom ≫
    (pullbackEqIso h M).hom)).mp
  apply (cancel_mono ((Scheme.Modules.pullbackComp v j).app N).inv).mp
  simpa only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    eqIso_congr, Scheme.Modules.pullbackCongr, ← Iso.app_hom, ← Iso.app_inv,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp] using hab


/-- A Cartesian presentation of the overlap may be used instead of the
chosen categorical pullback. -/
lemma overlap_of_square {S T U V : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    (u : V ⟶ T) (v : V ⟶ U) (h : IsPullback u v q j)
    (M N : S.Modules) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ⟶ (Scheme.Modules.pullback q).obj N)
    (b : (Scheme.Modules.pullback j).obj M ⟶ (Scheme.Modules.pullback j).obj N)
    (hab : (Scheme.Modules.pullback u).map a ≫ (squarePullbackIso u q v j h.w N).hom =
      (squarePullbackIso u q v j h.w M).hom ≫ (Scheme.Modules.pullback v).map b) :
    (CanonicalDatum.MF.presheafHom M N).map (overFst q j).op a =
      (CanonicalDatum.MF.presheafHom M N).map (overSnd q j).op b := by
  let P := CanonicalDatum.MF.presheafHom M N
  let t : Over.mk (v ≫ j) ⟶ Over.mk (pullback.snd q j ≫ j) :=
    Over.homMk h.isoPullback.hom (by
      change h.isoPullback.hom ≫ (pullback.snd q j ≫ j) = v ≫ j
      rw [← Category.assoc, h.isoPullback_hom_snd])
  letI : IsIso t.left := by change IsIso h.isoPullback.hom; infer_instance
  have ht₁ : t ≫ overFst q j = Over.homMk u h.w := by
    ext; exact h.isoPullback_hom_fst
  have ht₂ : t ≫ overSnd q j = Over.homMk v rfl := by
    ext; exact h.isoPullback_hom_snd
  apply hom_presheaf_injective M N hN t
  have h₁ := P.map_comp_apply (overFst q j).op t.op a
  have h₂ := P.map_comp_apply (overSnd q j).op t.op b
  rw [← op_comp, ht₁] at h₁
  rw [← op_comp, ht₂] at h₂
  exact h₁.symm.trans ((pullHom_eq_of_square q j u v h.w M N a b hab).trans h₂)

open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

/-- Descent preserves the prescribed open normalization. -/
lemma iso_descend_of_square {S T U V : Scheme.{0}} (q : T ⟶ S) (j : U ⟶ S)
    [Flat q] [QuasiCompact q] [Surjective q]
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (u : V ⟶ T) (v : V ⟶ U) (h : IsPullback u v q j)
    (M N : S.Modules) (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj N)
    (b : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback j).obj N)
    (hab : (Scheme.Modules.pullback u).map a.hom ≫ (squarePullbackIso u q v j h.w N).hom =
      (squarePullbackIso u q v j h.w M).hom ≫ (Scheme.Modules.pullback v).map b.hom) :
    ∃ c : M ≅ N, (Scheme.Modules.pullback q).mapIso c = a ∧
      (Scheme.Modules.pullback j).map c.hom = b.hom := by
  obtain ⟨c, hc⟩ := iso_descend_of_overlap q j M N hM hN a b
    (overlap_of_square q j u v h M N hN a.hom b.hom hab)
  have hch : (Scheme.Modules.pullback q).map c.hom = a.hom := congrArg Iso.hom hc
  letI : Flat v := MorphismProperty.of_isPullback h inferInstance
  letI : QuasiCompact v := MorphismProperty.of_isPullback h inferInstance
  letI : Surjective v := MorphismProperty.of_isPullback h inferInstance
  refine ⟨c, hc, ?_⟩
  apply ArithmeticThetaRootDescentR0197.FPQCRootMorphismsR0197.pullback_map_injective
    v _ _ (hM.pullback j) (hN.pullback j)
  apply (cancel_epi (squarePullbackIso u q v j h.w M).hom).mp
  rw [squarePullbackIso_naturality, hch, hab]

/-- The accepted compact comparison proves the flat and surjective
geometry for the specified map, including infinite coefficient extensions. -/
lemma coefficient_geometry (hL : 3 ≤ L) (heven : Even L)
    (C : Comparison k L ι D E X Y) :
    Flat C.compactMap ∧ QuasiCompact C.compactMap ∧ Surjective C.compactMap ∧
      IsPullback Y.inclusion C.openMap C.compactMap X.inclusion := by
  obtain ⟨hf, _⟩ := ArithmeticThetaLevelConstantsR0234.open_constant_cartesian
    k l ι L hL heven D E C.openMap C.classifies
  obtain ⟨F, hF, _⟩ := ArithmeticThetaLevelConstantsR0234.compact_constant_comparison
    k l ι L hL heven D E X Y C.openMap hf
  have heq : F = C.compactMap :=
    ArithmeticThetaLevelConstantsR0234.CompactComparison.extension_unique
      ι D E X Y C.openMap F C.compactMap hF.1 C.extendsOpen
  rw [heq] at hF
  exact ⟨MorphismProperty.of_isPullback hF.2.1.flip inferInstance,
    MorphismProperty.of_isPullback hF.2.1.flip inferInstance,
    MorphismProperty.of_isPullback hF.2.1.flip inferInstance, hF.2.2⟩

/-- Two normalized comparisons to a common lattice give the actual
commutative square for their quotient isomorphism. -/
lemma comparison_square (C : Comparison k L ι D E X Y)
    (H J : Extension k L D X) (K : Extension l L E Y)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ K.line)
    (b : (Scheme.Modules.pullback C.compactMap).obj J.line ≅ K.line)
    (ha : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H K a)
    (hb : CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap J K b) :
    (Scheme.Modules.pullback Y.inclusion).map (a ≪≫ b.symm).hom ≫
        (squarePullbackIso Y.inclusion C.compactMap C.openMap X.inclusion C.extendsOpen.2 J.line).hom =
      (squarePullbackIso Y.inclusion C.compactMap C.openMap X.inclusion C.extendsOpen.2 H.line).hom ≫
        (Scheme.Modules.pullback C.openMap).map (H.onOpen ≪≫ J.onOpen.symm).hom := by
  change (Scheme.Modules.pullback Y.inclusion).map a.hom ≫ K.onOpen.hom =
    (squarePullbackIso Y.inclusion C.compactMap C.openMap X.inclusion C.extendsOpen.2 H.line).hom ≫
      (Scheme.Modules.pullback C.openMap).map H.onOpen.hom ≫ C.hodgeMap.hom at ha
  change (Scheme.Modules.pullback Y.inclusion).map b.hom ≫ K.onOpen.hom =
    (squarePullbackIso Y.inclusion C.compactMap C.openMap X.inclusion C.extendsOpen.2 J.line).hom ≫
      (Scheme.Modules.pullback C.openMap).map J.onOpen.hom ≫ C.hodgeMap.hom at hb
  apply (cancel_mono ((Scheme.Modules.pullback C.openMap).map J.onOpen.hom ≫ C.hodgeMap.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hb]
  simpa only [Category.assoc, Iso.map_inv_hom_id_assoc] using ha


/-- Geometrically canonical extensions on the same compact base have a
unique open-normalized comparison, descended from an algebraic closure. -/
lemma same_field_exists (hL : 3 ≤ L) (heven : Even L)
    (H J : Extension k L D X) (hH : GeometricallyCanonical H)
    (hJ : GeometricallyCanonical J) :
    ∃ a : H.line ≅ J.line,
      (Scheme.Modules.pullback X.inclusion).map a.hom ≫ J.onOpen.hom = H.onOpen.hom := by
  let m := AlgebraicClosure k
  let κ : k →+* m := algebraMap k m
  obtain ⟨A⟩ := ArithmeticThetaLegendreAtlasR0176.legendre_level_family_construction m L hL
  obtain ⟨B, hB, V, Q, _⟩ :=
    ArithmeticThetaCompatibleLevelR0178.normal_affine_classifying_construction m L hL heven A
  let E : LevelData m L := ⟨A, B, hB, V, Q⟩
  obtain ⟨Y⟩ := smooth_projective_level_completion m L hL heven E
  let C := coefficientMap k L κ hL heven D E X Y
  obtain ⟨K, hK⟩ := compact_hodge_lattice_extension m L hL heven E Y
  obtain ⟨a, ha, _⟩ := hH m κ E Y C.openMap C.compactMap C.classifies
    C.extendsOpen C.hodgeMap C.normalized K hK
  obtain ⟨b, hb, _⟩ := hJ m κ E Y C.openMap C.compactMap C.classifies
    C.extendsOpen C.hodgeMap C.normalized K hK
  obtain ⟨hq, hqc, hs, hp⟩ := coefficient_geometry hL heven C
  letI := hq
  letI := hqc
  letI := hs
  letI := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.inclusion_schematic k L D X
  letI := compact_noetherian k L D X
  letI := X.openImmersion
  obtain ⟨c, _, hc⟩ := iso_descend_of_square C.compactMap X.inclusion
    Y.inclusion C.openMap hp H.line J.line H.invertible J.invertible
    (a ≪≫ b.symm) (H.onOpen ≪≫ J.onOpen.symm) (comparison_square C H J K a b ha hb)
  refine ⟨c, ?_⟩
  rw [hc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms coefficient_geometry
#print axioms comparison_square
#print axioms iso_descend_of_square
#print axioms iso_descend_of_overlap
#print axioms pullHom_eq_of_square
#print axioms hom_descend_of_overlap
#print axioms pullback_geometric
#print axioms comparison_unique

#print axioms same_field_exists

end GeometricCompactHodgeComparison

/-- The unique normalized compact Hodge comparison for every coefficient
embedding between geometrically canonical compact lattices. -/
theorem geometric_compact_hodge_comparison :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension l L E Y), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H → ArithmeticThetaBoundaryHodgeR0182.Canonical l L J → ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical J → ∃! a : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback C.compactMap).obj H.line) (J.line), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J a := by
  intro k l _ _ _ _ ι L hL heven D E X Y C H J _hH hgH _hJ hgJ
  let HC := ArithmeticThetaBoundaryConstantsR0235.CompactHodgeConstantComparison.pullbackExtension
    ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H
  obtain ⟨a, ha⟩ := GeometricCompactHodgeComparison.same_field_exists hL heven HC J
    (GeometricCompactHodgeComparison.pullback_geometric hL heven C H hgH) hgJ
  have hac := (ArithmeticThetaBoundaryConstantsR0235.CompactHodgeConstantComparison.compatible_iff
    ι C.openMap C.compactMap C.extendsOpen C.hodgeMap H J a).mpr ha
  exact ⟨a, hac, fun b hb => GeometricCompactHodgeComparison.comparison_unique C H J b a hb hac⟩

#print axioms geometric_compact_hodge_comparison
end ArithmeticThetaArithmeticSectionsR0236
