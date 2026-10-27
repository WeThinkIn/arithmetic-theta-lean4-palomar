import RelativeInversionNaturalityR0258

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaNaturalityR0258
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256
namespace MidpointNaturalityProof
open GoodReductionJacobian RelativeGroupLaw
open RelativePrimitiveThetaCommutator RelativeMidpointSymmetricThetaLift

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
variable (S : Type u) [CommRing S] [Algebra R S]

lemma point_square (P : point E) :
    (pointBaseChange E S P).val ≫ curveMap E S = baseMap (R := R) S ≫ P.val := by
  exact pullback.lift_fst _ _ _

lemma nsmul_square (P : point E) (n : ℕ) :
    ((family E S).law.nsmul (𝟙 _) n (pointBaseChange E S P)).val ≫ curveMap E S =
      baseMap (R := R) S ≫ (E.law.nsmul (𝟙 _) n P).val := by
  have h := ArithmeticThetaOpenHodgeR0180.EllipticFamilyWeierstrassAtlasR0180.baseChange_nsmul
    E.law (baseMap (R := R) S) (𝟙 _) (pointBaseChange E S P) n
  have hn := E.law.nsmul_natural (𝟙 _) ((𝟙 _) ≫ baseMap (R := R) S)
    (baseMap (R := R) S) (by simp) n P
  have hp : baseChangePointToBase (baseMap (R := R) S) (pointBaseChange E S P) =
      GoodReductionJacobian.schemeHomOverComp (baseMap (R := R) S) (by simp) P := by
    apply Subtype.ext
    exact point_square E S P
  rw [hp] at h
  exact (congrArg Subtype.val h).trans (congrArg Subtype.val hn).symm

lemma negative_square (P : point E) :
    baseMap (R := R) S ≫ negative E P = negative (family E S) (pointBaseChange E S P) ≫
      curveMap E S := by
  have hn := RelativeNormalizedThetaInversion.inverse_natural E (𝟙 _)
    ((𝟙 _) ≫ baseMap (R := R) S) (baseMap (R := R) S) (by simp) P
  change _ = (pullback.lift _ _ _) ≫ pullback.fst _ _
  rw [pullback.lift_fst]
  have hp : baseChangePointToBase (baseMap (R := R) S) (pointBaseChange E S P) =
      GoodReductionJacobian.schemeHomOverComp (baseMap (R := R) S) (by simp) P := by
    apply Subtype.ext
    exact point_square E S P
  rw [hp]
  exact congrArg Subtype.val hn

lemma translation_square (P : point E) :
    curveMap E S ≫ translation E P =
      translation (family E S) (pointBaseChange E S P) ≫ curveMap E S := by
  have h := point_translate E ((family E S).projection ≫ baseMap (R := R) S)
    ⟨curveMap E S, pullback.condition⟩ (E.law.nsmul (𝟙 _) 2 P)
  change _ ≫ E.law.translate _ = _ at h
  rw [show curveMap E S ≫ translation E P = _ from h]
  change _ = (pullback.lift _ _ _) ≫ pullback.fst _ _
  rw [pullback.lift_fst]
  congr 2
  apply Subtype.ext
  change ((family E S).projection ≫ baseMap (R := R) S) ≫ _ =
    ((family E S).projection ≫ _) ≫ curveMap E S
  rw [Category.assoc, Category.assoc, nsmul_square]

/-- Conjugation by a line isomorphism respects composition of lifts. -/
lemma conjugate_comp {X : Scheme.{u}} (f g : X ⟶ X) {L N : X.Modules}
    (e : L ≅ N) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    (Scheme.Modules.pullback (f ≫ g)).mapIso e.symm ≪≫
        PullbackLifts.compLift f g α β ≪≫ e =
      PullbackLifts.compLift f g
        ((Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e)
        ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ β ≪≫ e) := by
  have hn := (Scheme.Modules.pullbackComp f g).inv.naturality e.inv
  dsimp only [Functor.comp_map] at hn
  apply Iso.ext
  simp only [PullbackLifts.compLift, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.app_inv]
  have he : (Scheme.Modules.pullback f).map e.hom ≫
      (Scheme.Modules.pullback f).map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [reassoc_of% he, reassoc_of% hn]

/-- A fixed second lift can be cancelled from a composite lift. -/
lemma compLift_injective {X : Scheme.{u}} (f g : X ⟶ X) {L : X.Modules}
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    Function.Injective (fun α : (Scheme.Modules.pullback f).obj L ≅ L =>
      PullbackLifts.compLift f g α β) := by
  intro α α' h
  apply Iso.ext
  exact (cancel_epi (((Scheme.Modules.pullbackComp f g).app L).inv ≫
    ((Scheme.Modules.pullback f).mapIso β).hom)).mp
    (by simpa only [PullbackLifts.compLift, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      using congrArg Iso.hom h)

/-- The general conjugated pullback, instantiated below with thetaComparison. -/
def transport {X Y : Scheme.{u}} (c : Y ⟶ X) {L : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj L ≅ N) (f : X ⟶ X) (f' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (α : (Scheme.Modules.pullback f).obj L ≅ L) :
    (Scheme.Modules.pullback f').obj N ≅ N :=
  (Scheme.Modules.pullback f').mapIso e.symm ≪≫ PullbackLifts.lift c f f' hf α ≪≫ e

lemma transport_comp {X Y : Scheme.{u}} (c : Y ⟶ X) {L : X.Modules} {N : Y.Modules}
    (e : (Scheme.Modules.pullback c).obj L ≅ N)
    (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (hfg : c ≫ (f ≫ g) = (f' ≫ g') ≫ c)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    transport c e (f ≫ g) (f' ≫ g') hfg (PullbackLifts.compLift f g α β) =
      PullbackLifts.compLift f' g' (transport c e f f' hf α) (transport c e g g' hg β) := by
  unfold transport
  rw [PullbackLifts.lift_comp _ _ _ _ _ hf hg hfg, conjugate_comp]

/-- Transport and uniqueness of midpoint reflection, before geometric specialization. -/
lemma transport_midpoint {X Y B C : Scheme.{u}} (c : Y ⟶ X) (b : C ⟶ B)
    (o : B ⟶ X) (o' : C ⟶ Y) (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (hfg : c ≫ (f ≫ g) = (f' ≫ g') ≫ c) (ho : b ≫ o = o' ≫ c)
    (hfix : o ≫ (f ≫ g) = o) (hfix' : o' ≫ (f' ≫ g') = o')
    {L : X.Modules} {N : Y.Modules} (e : (Scheme.Modules.pullback c).obj L ≅ N)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L)
    (α' : (Scheme.Modules.pullback f').obj N ≅ N)
    (β' : (Scheme.Modules.pullback g').obj N ≅ N)
    (hβ : transport c e g g' hg β = β')
    (hα : (Scheme.Modules.pullback o).mapIso (PullbackLifts.compLift f g α β) =
      (Scheme.Modules.pullbackComp o (f ≫ g) ≪≫ Scheme.Modules.pullbackCongr hfix).app L)
    (hα' : (Scheme.Modules.pullback o').mapIso (PullbackLifts.compLift f' g' α' β') =
      (Scheme.Modules.pullbackComp o' (f' ≫ g') ≪≫ Scheme.Modules.pullbackCongr hfix').app N)
    (hu : ∀ ψ χ : (Scheme.Modules.pullback (f' ≫ g')).obj N ≅ N,
      (Scheme.Modules.pullback o').mapIso ψ =
        (Scheme.Modules.pullbackComp o' (f' ≫ g') ≪≫ Scheme.Modules.pullbackCongr hfix').app N →
      (Scheme.Modules.pullback o').mapIso χ =
        (Scheme.Modules.pullbackComp o' (f' ≫ g') ≪≫ Scheme.Modules.pullbackCongr hfix').app N →
      ψ = χ) : transport c e f f' hf α = α' := by
  have hbase := InversionNaturalityProof.lift_fixed c b o o' (f ≫ g) (f' ≫ g')
    hfg ho hfix hfix' L (PullbackLifts.compLift f g α β) hα
  have hconj := InversionNaturalityProof.conjugate_fixed o' (f' ≫ g') hfix' e
    (PullbackLifts.lift c (f ≫ g) (f' ≫ g') hfg (PullbackLifts.compLift f g α β)) hbase
  have he := hu _ _ hconj hα'
  have hc := transport_comp c e f g f' g' hf hg hfg α β
  have hh := hc.symm.trans he
  rw [hβ] at hh
  exact compLift_injective f' g' β' hh

#print axioms transport_midpoint

/-- Expose the normalization equation before specializing the family. -/
lemma midpoint_equation (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) (h : MidpointNormalized E m P ι α) :
    ∃ hf : negative E P ≫ (translation E P ≫ inverse E) = negative E P,
      (Scheme.Modules.pullback (negative E P)).mapIso
        (PullbackLifts.compLift (translation E P) (inverse E) α ι) =
      (Scheme.Modules.pullbackComp (negative E P) (translation E P ≫ inverse E) ≪≫
        Scheme.Modules.pullbackCongr hf).app (thetaLine E m) := by
  obtain ⟨hf, hh⟩ := h
  exact ⟨hf, hh⟩

/-- Whole-family reflection uniqueness in the same pullback presentation. -/
lemma reflection_unique (m : ℕ) (P : point E)
    (h : Nonempty (Lift E m (reflection E P)))
    (hf : negative E P ≫ (translation E P ≫ inverse E) = negative E P) :
    ∀ ψ χ : (Scheme.Modules.pullback (translation E P ≫ inverse E)).obj (thetaLine E m) ≅
      thetaLine E m,
      (Scheme.Modules.pullback (negative E P)).mapIso ψ =
        (Scheme.Modules.pullbackComp (negative E P) (translation E P ≫ inverse E) ≪≫
          Scheme.Modules.pullbackCongr hf).app (thetaLine E m) →
      (Scheme.Modules.pullback (negative E P)).mapIso χ =
        (Scheme.Modules.pullbackComp (negative E P) (translation E P ≫ inverse E) ≪≫
          Scheme.Modules.pullbackCongr hf).app (thetaLine E m) → ψ = χ := by
  obtain ⟨φ, hφ, hu⟩ := normalized_reflection E m P h
  intro ψ χ hψ hχ
  exact (hu ψ hψ).trans (hu χ hχ).symm

end MidpointNaturalityProof

/-- Midpoint-normalized translation lifts commute with the specified geometric base change. -/
theorem relative_midpoint_naturality :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : EllipticFamily R) (S : Type u) [CommRing S] [Algebra R S]
      [Algebra ℚ S] [IsScalarTower ℚ R S] [IsNoetherianRing S] (m : ℕ),
      0 < m → Even m → ∀ P : point E,
      CategoryTheory.CategoryStruct.comp P.val (E.law.schemeNsmul (2*m)) = zero E →
      MidpointNatural E S m P := by
  intro R _ _ _ E S _ _ _ _ _ m _ _ P _ ι ιS α αS hι hιS hα hαS
  let ht := MidpointNaturalityProof.translation_square E S P
  obtain ⟨hi, hιeq⟩ := relative_inversion_naturality R E S m ι ιS hι hιS
  have hr : curveMap E S ≫ reflection E P =
      reflection (family E S) (pointBaseChange E S P) ≫ curveMap E S := by
    dsimp only [reflection]
    rw [← Category.assoc, ht, Category.assoc, hi, Category.assoc]
  let PS := pointBaseChange E S P
  obtain ⟨hf, hnorm⟩ := MidpointNaturalityProof.midpoint_equation E m P ι α hα
  obtain ⟨hfS, hnormS⟩ := MidpointNaturalityProof.midpoint_equation
    (family E S) m PS ιS αS hαS
  have hu := MidpointNaturalityProof.reflection_unique (family E S) m PS
    ⟨reflectionLift (family E S) m PS ιS αS⟩ hfS
  have hgen := MidpointNaturalityProof.transport_midpoint
    (L := thetaLine E m) (N := thetaLine (family E S) m)
    (curveMap E S) (baseMap (R := R) S) (negative E P) (negative (family E S) PS)
    (translation E P) (inverse E) (translation (family E S) PS) (inverse (family E S))
    ht hi hr (MidpointNaturalityProof.negative_square E S P) hf hfS
    (thetaComparison E S m) α ι αS ιS
  have hgen1 := hgen hιeq
  have hgen2 := hgen1 hnorm
  have hgen3 := hgen2 hnormS
  have hresult := hgen3 hu
  exact ⟨ht, hresult⟩

#print axioms relative_midpoint_naturality
end ArithmeticThetaRelativeThetaNaturalityR0258
