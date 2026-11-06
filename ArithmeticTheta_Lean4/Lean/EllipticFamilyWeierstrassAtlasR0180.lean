import OpenHodgeDescentDefinitionsR0180

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaOpenHodgeR0180
namespace EllipticFamilyWeierstrassAtlasR0180
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176

lemma hodge_invertible {S : Type u} [CommRing S] (E : EllipticFamily S) :
    Scheme.Modules.IsInvertible (hodge E) := by
  letI := E.smooth
  exact Scheme.Modules.IsInvertible.pullback (zero E)
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (E.projection.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1)

structure FramedChart (S : Type u) [CommRing S] (E : EllipticFamily S) (x : Base S) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  scalar : S →+* ring
  openImmersion : IsOpenImmersion (baseMap S ring scalar)
  contains : x ∈ Set.range (baseMap S ring scalar)
  frame : Nonempty ((Scheme.Modules.pullback (baseMap S ring scalar)).obj (hodge E) ≅
    SheafOfModules.unit (Base ring).ringCatSheaf)
attribute [instance] FramedChart.commRing FramedChart.domain FramedChart.noetherian
  FramedChart.normal FramedChart.rational

lemma framed_chart (k : Type u) [Field k] [CharZero k]
    (S : Type u) [CommRing S] [Algebra k S]
    (hS : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (E : EllipticFamily S) (x : Base S) : Nonempty (FramedChart S E x) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k S))
  letI : SmoothOfRelativeDimension 1 f := hS
  letI : IsLocallyNoetherian (Base S) := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsIntegrallyClosed Γ(Base k, ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have hd (z : Base S) : IsDomain ((Base S).presheaf.stalk z) :=
    (Smooth.isDomain_and_isIntegrallyClosed_stalk f z).1
  let C : (Base S).Opens := ⟨irreducibleComponent x,
    (isOpen_irreducibleComponent_of_isDomain_stalk hd x).1⟩
  letI : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp
    (isIrreducible_irreducibleComponent (x := x))
  letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian C.ι
  letI : IsIntegral C :=
    isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk C
      (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (C.ι ≫ f) z).1)
  let xc : C := ⟨x, mem_irreducibleComponent⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (Scheme.Modules.IsInvertible.pullback C.ι (hodge_invertible E)).1 xc
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  letI : Nonempty V := ⟨⟨xc, hxV⟩⟩
  letI : IsAffine V := hV
  let R := Γ(V, ⊤)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  let q : Base R ⟶ Base S := (Scheme.isoSpec V).inv ≫ V.ι ≫ C.ι
  let ρ : S →+* R := (Spec.preimage q).hom
  have hρ : baseMap S R ρ = q := Spec.map_preimage q
  let κ : k →+* R := ρ.comp (algebraMap k S)
  letI : Algebra k R := κ.toAlgebra
  have hκ : Spec.map (CommRingCat.ofHom κ) = q ≫ f := by
    rw [← hρ]; exact Spec.map_comp _ _
  letI : Smooth (Spec.map (CommRingCat.ofHom κ)) := by rw [hκ]; dsimp [q]; infer_instance
  letI : Algebra.Smooth k R := RingHom.smooth_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp (show Smooth (Spec.map (CommRingCat.ofHom κ)) from inferInstance))
  letI : IsIntegrallyClosed R := ArithmeticThetaSmoothNormality.smoothDomain_integrallyClosed k R
  letI : Algebra ℚ R := (κ.comp (algebraMap ℚ k)).toAlgebra
  refine ⟨⟨R, ρ, ?_, ?_, ?_⟩⟩
  · rw [hρ]; dsimp [q]; infer_instance
  · rw [hρ]
    refine ⟨(Scheme.isoSpec V).hom ⟨xc, hxV⟩, ?_⟩
    change ((Scheme.isoSpec V).hom ≫ (Scheme.isoSpec V).inv ≫ V.ι ≫ C.ι) _ = x
    simp [xc]
  · rw [hρ]
    let a : Base R ⟶ U := (Scheme.isoSpec V).inv ≫ (C : Scheme).homOfLE hVU
    have ha : a ≫ U.ι = (Scheme.isoSpec V).inv ≫ V.ι := by simp [a]
    exact ⟨((Scheme.Modules.pullbackComp ((Scheme.isoSpec V).inv ≫ V.ι) C.ι).app (hodge E)).symm ≪≫
      (Scheme.Modules.pullbackCongr ha.symm).app ((Scheme.Modules.pullback C.ι).obj (hodge E)) ≪≫
      ((Scheme.Modules.pullbackComp a U.ι).app ((Scheme.Modules.pullback C.ι).obj (hodge E))).symm ≪≫
      (Scheme.Modules.pullback a).mapIso eU ≪≫ Scheme.Modules.pullbackUnitIso a⟩

open ArithmeticThetaMarkedGroupLawR0146.ActualGenericGroupLaw
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- The same operations, expressed in the Weierstrass law interface. -/
def toWeierstrassLaw {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Base R} (G : GoodReductionJacobian.RelativeGroupLaw R p) :
    WeierstrassProjModel.RelativeGroupLaw R p where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := G.mul_natural

lemma transport_nsmul {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {p : X ⟶ Base R} {q : Y ⟶ Base R} (e : X ≅ Y)
    (he : e.hom ≫ q = p) (G : WeierstrassProjModel.RelativeGroupLaw R q)
    {T : Scheme.{u}} (t : T ⟶ Base R) (P : SchemeHomOver t p) (n : ℕ) :
    pointsEquiv e he t ((transport e he G).nsmul t n P) =
      G.nsmul t n (pointsEquiv e he t P) := by
  induction n with
  | zero => exact (pointsEquiv e he t).apply_symm_apply _
  | succ n ih =>
    change pointsEquiv e he t ((pointsEquiv e he t).symm (G.mul t _ _)) = _
    rw [Equiv.apply_symm_apply]
    exact congrArg (fun z => G.mul t z (pointsEquiv e he t P)) ih

lemma baseChange_nsmul {S R : Type u} [CommRing S] [CommRing R]
    {X : Scheme.{u}} {p : X ⟶ Base S} (G : GoodReductionJacobian.RelativeGroupLaw S p)
    (q : Base R ⟶ Base S) {T : Scheme.{u}} (t : T ⟶ Base R)
    (P : SchemeHomOver t (pullback.snd p q)) (n : ℕ) :
    GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q
      ((G.baseChange q).nsmul t n P) =
    G.nsmul (t ≫ q) n (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q P) := by
  induction n with
  | zero => exact GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_one q G t
  | succ n ih =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ,
      GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_mul, ih]
    rfl

lemma chart_of_frame {S : Type u} [CommRing S] (E : EllipticFamily S)
    (x : Base S) (C : FramedChart S E x) :
    ∃ D : Chart S E, x ∈ Set.range (baseMap S D.ring D.comparison.scalar) := by
  let R := C.ring
  let q := baseMap S R C.scalar
  letI : Algebra S R := C.scalar.toAlgebra
  letI := E.smooth
  letI := E.proper
  letI := E.connected
  let X := pullback E.projection q
  let p : X ⟶ Base R := pullback.snd E.projection q
  let H := E.law.baseChange q
  have hgeom : GoodReductionJacobian.AbelianSchemePropertyBundle R p := {
    smooth := inferInstance
    proper := inferInstance
    connectedFibres := fun z => p.isConnected_preimage_singleton z
    hasGroupLaw := ⟨H⟩ }
  have ho : (H.one (𝟙 _)).val ≫ pullback.fst E.projection q = q ≫ zero E := by
    change (pullback.lift (E.law.one (𝟙 _ ≫ q)).val (𝟙 _) _ ≫ pullback.fst E.projection q) = _
    rw [pullback.lift_fst]
    rw [Category.id_comp]
    exact (congrArg Subtype.val (E.law.one_natural (𝟙 _) q q (by simp))).symm
  obtain ⟨η⟩ := C.frame
  have hframe : Nonempty (SheafOfModules.unit (Base R).ringCatSheaf ≅
      (Scheme.Modules.pullback (H.one (𝟙 _)).val).obj p.kaehler) :=
    ⟨η.symm ≪≫ pointedDifferentialIso E.projection p (pullback.fst E.projection q)
      (IsPullback.of_hasPullback _ _) (zero E) (H.one (𝟙 _)).val ho⟩
  obtain ⟨W, hW, e, he, heo⟩ :=
    ArithmeticThetaCyclicPresentationR0174.relative_weierstrass_presentation
      R X p H hgeom inferInstance hframe
  letI := hW
  have hei : e.inv ≫ p = structureMap R W := by rw [← he, e.inv_hom_id_assoc]
  let G : Law R W := transport e.symm hei (toWeierstrassLaw H)
  have hG : IsOriginLaw R W G := by
    constructor
    · intro T t
      change (H.one t).val ≫ e.hom = t ≫ origin R W
      have ht := congrArg Subtype.val (H.one_natural (𝟙 _) t t (by simp))
      change t ≫ (H.one (𝟙 _)).val = (H.one t).val at ht
      rw [← ht, Category.assoc, heo]
    · intro T t P Q
      change (pointsEquiv e.symm hei t).symm (H.mul t _ _) =
        (pointsEquiv e.symm hei t).symm (H.mul t _ _)
      exact congrArg (pointsEquiv e.symm hei t).symm
        (GoodReductionJacobian.RelativeGroupLaw.IsCommutative.baseChange q E.commutative t _ _)
  let b := e.inv ≫ pullback.fst E.projection q
  have hc : IsPullback b (structureMap R W) E.projection q := by
    have comm : b ≫ E.projection = structureMap R W ≫ q := by
      dsimp [b]
      rw [Category.assoc, pullback.condition, ← Category.assoc, hei]
    exact IsPullback.of_iso_pullback ⟨comm⟩ e.symm rfl hei
  have hbzero : origin R W ≫ b = q ≫ zero E := by
    rw [← heo]
    simpa [b] using ho
  have hbn (n : ℕ) : G.schemeNsmul n ≫ b = b ≫ E.law.schemeNsmul n := by
    have ht := transport_nsmul e.symm hei (toWeierstrassLaw H) (structureMap R W)
      WeierstrassProjModel.RelativeGroupLaw.idPoint n
    have hb := baseChange_nsmul E.law q (structureMap R W)
      (pointsEquiv e.symm hei (structureMap R W) WeierstrassProjModel.RelativeGroupLaw.idPoint) n
    have htt := congrArg
      (fun P => (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase q P).val) ht
    have hnat := congrArg Subtype.val
      (E.law.nsmul_natural E.projection (structureMap R W ≫ q) b hc.w n
        GoodReductionJacobian.RelativeGroupLaw.idPoint)
    exact htt.trans ((congrArg Subtype.val hb).trans hnat.symm)
  exact ⟨⟨R, W, G, hG, ⟨C.scalar, b, hc, hbzero, hbn⟩, C.openImmersion⟩, C.contains⟩

end EllipticFamilyWeierstrassAtlasR0180
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaLegendreAtlasR0176
/-- Finite genuine pointed Weierstrass charts over every smooth affine base curve. -/
theorem elliptic_family_weierstrass_atlas
    (k : Type u) [Field k] [CharZero k] (S : Type u) [CommRing S] [Algebra k S]
    (hS : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (E : EllipticFamily S) : Nonempty (Atlas S E) := by
  classical
  have hlocal (x : Base S) :
      ∃ D : Chart S E, x ∈ Set.range (baseMap S D.ring D.comparison.scalar) :=
    EllipticFamilyWeierstrassAtlasR0180.chart_of_frame E x
      (Classical.choice (EllipticFamilyWeierstrassAtlasR0180.framed_chart k S hS E x))
  choose D hD using hlocal
  let U (x : Base S) := Set.range (baseMap S (D x).ring (D x).comparison.scalar)
  have hopen (x : Base S) : IsOpen (U x) := by
    letI := (D x).openImmersion
    exact IsOpenImmersion.isOpen_range _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hD x⟩)
  let e := Fintype.equivFin t
  refine ⟨⟨Fintype.card t, fun i => D (e.symm i).val, ?_⟩⟩
  intro x
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hy
  refine ⟨e ⟨y, hy⟩, ?_⟩
  change x ∈ U (e.symm (e ⟨y, hy⟩)).val
  rw [e.symm_apply_apply]
  exact hxy

#print axioms elliptic_family_weierstrass_atlas
end ArithmeticThetaOpenHodgeR0180
