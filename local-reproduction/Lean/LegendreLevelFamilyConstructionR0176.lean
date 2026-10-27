import LegendreFamilyGeometryR0176
import FullLevelAutomorphismRigidityR0176
import FullLevelFreeSignR0176
import AffineFreeSignQuotientR0176
import FullMarkingSignDescentR0176

/-! Construction of the Legendre atlas, including rigidity of its descended marking. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176
namespace LegendreLevelFamilyConstructionR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175

/-- Pull back an automorphism through its specified Cartesian square. -/
def cartesianIso {X Y B C : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ C} {q : B ⟶ C} (h : IsPullback a f g q)
    (e : Y ≅ Y) (he : e.hom ≫ g = g) : X ≅ X where
  hom := h.lift (a ≫ e.hom) f (by rw [Category.assoc, he]; exact h.w)
  inv := h.lift (a ≫ e.inv) f (by
    rw [← he, Category.assoc, Iso.inv_hom_id_assoc]; exact h.w)
  hom_inv_id := by
    apply h.hom_ext <;> simp [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]
  inv_hom_id := by
    apply h.hom_ext <;> simp [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]

lemma cartesian_rigidity (S : Type u) [CommRing S] [IsDomain S]
    [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    (W : WeierstrassCurve S) [W.IsElliptic] (H : Law S W) (hH : IsOriginLaw S W H)
    (L : ℕ) (hL : 3 ≤ L) (A : FullLevel S W H L (𝟙 (Base S)))
    {Y B : Scheme.{u}} {f : Y ⟶ B} {q : Base S ⟶ B} {a : Curve S W ⟶ Y}
    (h : IsPullback a (structureMap S W) f q)
    (o x y : B ⟶ Y)
    (ho : origin S W ≫ a = q ≫ o)
    (hx : A.x.val ≫ a = q ≫ x) (hy : A.y.val ≫ a = q ≫ y)
    (e : Y ≅ Y) (he : e.hom ≫ f = f)
    (heo : o ≫ e.hom = o) (hex : x ≫ e.hom = x) (hey : y ≫ e.hom = y) :
    a ≫ e.hom = a := by
  let v := cartesianIso h e he
  have hv : v.hom ≫ a = a ≫ e.hom := h.lift_fst _ _ _
  have hf : v.hom ≫ structureMap S W = structureMap S W := h.lift_snd _ _ _
  have hs {T : Scheme.{u}} (s : T ⟶ Curve S W) (t : T ⟶ B) (z : B ⟶ Y)
      (hz : s ≫ a = t ≫ z) (hze : z ≫ e.hom = z) : s ≫ v.hom = s := by
    apply h.hom_ext
    · rw [Category.assoc, hv, ← Category.assoc, hz, Category.assoc, hze]
    · rw [Category.assoc, hf]
  have hid := full_level_automorphism_rigidity S W H hH L hL A v hf
    (hs _ _ o ho heo) (hs _ _ x hx hex) (hs _ _ y hy hey)
  rw [← hv, hid, Category.id_comp]

structure NormalChart (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Base R) (x : X) where
  ring : Type u
  [commRing : CommRing ring]
  [domain : IsDomain ring]
  [noetherian : IsNoetherianRing ring]
  [normal : IsIntegrallyClosed ring]
  [rational : Algebra ℚ ring]
  inclusion : R →+* ring
  map : Base ring ⟶ X
  commutes : map ≫ f = baseMap R ring inclusion
  openImmersion : IsOpenImmersion map
  contains : x ∈ Set.range map

attribute [instance] NormalChart.commRing NormalChart.domain NormalChart.noetherian
  NormalChart.normal NormalChart.rational NormalChart.openImmersion

/-- Each component of the finite étale cover supplies its own normal domain;
no domain structure is imposed on the whole cover or the quotient. -/
lemma normal_chart (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    {X : Scheme.{u}} (f : X ⟶ Base R) [IsFinite f] [Etale f] (x : X) :
    Nonempty (NormalChart R f x) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsIntegrallyClosed Γ(Base R, ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hd (z : X) : IsDomain (X.presheaf.stalk z) :=
    (Smooth.isDomain_and_isIntegrallyClosed_stalk f z).1
  let U : X.Opens := ⟨irreducibleComponent x,
    (isOpen_irreducibleComponent_of_isDomain_stalk hd x).1⟩
  have hc : IsClosed (U : Set X) := isClosed_irreducibleComponent
  letI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
    (isIrreducible_irreducibleComponent (x := x))
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hc)
  letI : IsIntegral U :=
    isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk U
      (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (U.ι ≫ f) z).1)
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : IsAffine U := isAffine_of_isAffineHom U.ι
  letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let S := Γ(U, ⊤)
  letI : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  let q : Base S ⟶ X := (Scheme.isoSpec U).inv ≫ U.ι
  let ι : R →+* S := (Spec.preimage (q ≫ f)).hom
  have he : baseMap R S ι = q ≫ f := Spec.map_preimage _
  letI : Algebra R S := ι.toAlgebra
  letI : Etale (baseMap R S ι) := by rw [he]; dsimp [q]; infer_instance
  letI : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    (HasRingHomProperty.Spec_iff.mp (show Etale (baseMap R S ι) from inferInstance))
  letI : IsIntegrallyClosed S := ArithmeticThetaSmoothNormality.etaleDomain_integrallyClosed R S
  letI : Algebra ℚ S := (ι.comp (algebraMap ℚ R)).toAlgebra
  refine ⟨⟨S, ι, q, he.symm, inferInstance, ?_⟩⟩
  refine ⟨(Scheme.isoSpec U).hom ⟨x, mem_irreducibleComponent⟩, ?_⟩
  change ((Scheme.isoSpec U).hom ≫ (Scheme.isoSpec U).inv ≫ U.ι) _ = x
  simp

lemma descent_rigid (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] [Algebra k R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W) (hG : IsOriginLaw R W G)
    (L : ℕ) (hL : 3 ≤ L) (Z : LevelScheme R W G L) (hZ : Represents R W G Z)
    (σ : SignAction R W G Z)
    (Q : SignQuotient k (Z.projection ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) σ.map)
    (D : FamilyDescent k R W G Z σ Q) (M : FamilyLevel Q.ring D.family L)
    (hx : coverSection R W Z Z.level.x ≫ D.comparison = Q.q ≫ M.x.val)
    (hy : coverSection R W Z Z.level.y ≫ D.comparison = Q.q ≫ M.y.val) :
    FamilyRigid Q.ring D.family M := by
  classical
  intro e he ho hex hey
  obtain ⟨hf, ht, _, _⟩ := full_level_cover_geometry R W G hG L (by omega) Z hZ
  letI := hf
  letI := ht
  letI := Q.finite
  letI := Q.etale
  letI := Q.surjective
  letI : IsFinite D.comparison := MorphismProperty.of_isPullback D.cartesian.flip inferInstance
  letI : Etale D.comparison := MorphismProperty.of_isPullback D.cartesian.flip inferInstance
  letI : Surjective D.comparison := MorphismProperty.of_isPullback D.cartesian.flip inferInstance
  apply (cancel_epi D.comparison).mp
  rw [Category.comp_id]
  let C (z : Z.space) := Classical.choice (normal_chart R Z.projection z)
  let V : Z.space.OpenCover := {
    I₀ := Z.space
    X z := Base (C z).ring
    f z := (C z).map
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun z => ⟨z, (C z).contains⟩, fun z => (C z).openImmersion⟩ }
  apply (V.pullback₁ (coverToLevel R W Z)).hom_ext
  intro z
  let S := (C z).ring
  let ι := (C z).inclusion
  let q := (C z).map
  have hq : q ≫ Z.projection = baseMap R S ι := (C z).commutes
  let A₀ := BaseChange.restrict Z.level q
    (show q ≫ Z.projection = baseMap R S ι from (C z).commutes)
  obtain ⟨H, b, hH, hb, _⟩ := NormalAffineExtensionR0175.change_ring R W G hG S ι L A₀
  let Ws := W.map ι
  let A := BaseChange.up hb hG hH (BaseChange.restrict Z.level q
    (by simpa using (C z).commutes : q ≫ Z.projection = 𝟙 (Base S) ≫ baseMap R S ι))
  let c : Curve S Ws ⟶ coverCurve R W Z :=
    pullback.lift b (structureMap S Ws ≫ q) (by
      rw [Category.assoc, (C z).commutes]; exact hb.1.w)
  have hc : IsPullback c (structureMap S Ws) (coverToLevel R W Z) q := by
    have hout : IsPullback (c ≫ coverToCurve R W Z) (structureMap S Ws)
        (structureMap R W) (q ≫ Z.projection) := by
      simpa only [c, coverToCurve, pullback.lift_fst, hq, baseMap, Ws] using hb.1
    exact hout.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have hco : origin S Ws ≫ c = q ≫ coverSection R W Z (G.one Z.projection) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, c, pullback.lift_fst, coverSection]
      rw [hb.2.1, hG.1, ← Category.assoc, hq]
      rfl
    · simp only [Category.assoc, c, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, BaseChange.origin_over, Category.id_comp]
  have hcx : A.x.val ≫ c = q ≫ coverSection R W Z Z.level.x := by
    apply pullback.hom_ext
    · simp only [Category.assoc, c, pullback.lift_fst, coverSection]
      exact BaseChange.up_x hb hG hH _
    · simp only [Category.assoc, c, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, A.x.property, Category.id_comp]
  have hcy : A.y.val ≫ c = q ≫ coverSection R W Z Z.level.y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, c, pullback.lift_fst, coverSection]
      exact BaseChange.up_y hb hG hH _
    · simp only [Category.assoc, c, pullback.lift_snd, coverSection, Category.comp_id]
      rw [← Category.assoc, A.y.property, Category.id_comp]
  have hid := cartesian_rigidity S Ws H hH L hL A (hc.paste_horiz D.cartesian)
    (D.family.law.one (𝟙 _)).val M.x.val M.y.val
    (by rw [← Category.assoc, hco, Category.assoc, D.origin_eq, Category.assoc])
    (by rw [← Category.assoc, hcx, Category.assoc, hx, Category.assoc])
    (by rw [← Category.assoc, hcy, Category.assoc, hy, Category.assoc]) e he ho hex hey
  change pullback.fst (coverToLevel R W Z) q ≫ D.comparison ≫ e.hom =
    pullback.fst (coverToLevel R W Z) q ≫ D.comparison
  apply (cancel_epi hc.isoPullback.hom).mp
  simpa only [← Category.assoc, hc.isoPullback_hom_fst] using hid

end LegendreLevelFamilyConstructionR0176

open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaFullLevelCoverR0175

/-- The actual Legendre parameter family, with its descended full marking and rigidity. -/
theorem legendre_level_family_construction :
    ∀ (k : Type u) [Field k] [CharZero k] (L : ℕ) (hL : 3 ≤ L),
      Nonempty (LegendreAtlas k L) := by
  intro k _ _ L hL
  obtain ⟨hd, hn, hi, he, hs, G, hG⟩ := legendre_family_geometry k
  letI := hd
  letI := hn
  letI := hi
  letI := he
  letI := hs
  obtain ⟨Z, hZ⟩ := full_level_representability (LegendreRing k) (legendre k) G hG L (by omega)
  obtain ⟨hf, ht, _, _⟩ := full_level_cover_geometry (LegendreRing k) (legendre k) G hG L
    (by omega) Z hZ
  letI := hf
  letI := ht
  letI : IsAffine Z.space := isAffine_of_isAffineHom Z.projection
  letI : SmoothOfRelativeDimension 1 (Z.projection ≫ legendreBaseMap k) :=
    smoothOfRelativeDimension_comp 0 1 Z.projection (legendreBaseMap k)
  obtain ⟨σ⟩ := full_level_free_sign (LegendreRing k) (legendre k) G hG L hL Z hZ
  obtain ⟨Q⟩ := affine_free_sign_quotient k Z.space (Z.projection ≫ legendreBaseMap k)
    σ.map (by rw [← Category.assoc, σ.over_eq]) σ.square σ.free
  obtain ⟨D⟩ := elliptic_sign_descent k (LegendreRing k) (legendre k) G hG L hL Z hZ σ Q
  obtain ⟨M, hx, hy⟩ := full_marking_sign_descent k (LegendreRing k) (legendre k) G hG L hL Z hZ σ Q D
  exact ⟨⟨G, hG, Z, hZ, σ, Q, D, M,
    LegendreLevelFamilyConstructionR0176.descent_rigid k (LegendreRing k) (legendre k)
      G hG L hL Z hZ σ Q D M hx hy, hx, hy⟩⟩

#print axioms legendre_level_family_construction
end ArithmeticThetaLegendreAtlasR0176
