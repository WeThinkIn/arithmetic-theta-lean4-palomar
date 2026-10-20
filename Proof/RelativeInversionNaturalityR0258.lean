module

public import RelativeThetaNaturalityDefinitionsR0258

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaRelativeThetaNaturalityR0258
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256

namespace InversionNaturalityProof
open RelativePrimitiveThetaCommutator

lemma inverse_square_baseChange {R : Type u} [CommRing R] (E : EllipticFamily R)
    (S : Type u) [CommRing S] [Algebra R S] :
    curveMap E S ≫ inverse E = inverse (family E S) ≫ curveMap E S := by
  have hn := RelativeNormalizedThetaInversion.inverse_natural E E.projection
    ((family E S).projection ≫ baseMap (R := R) S) (curveMap E S)
    (pullback.condition) ⟨𝟙 _, Category.id_comp _⟩
  change curveMap E S ≫ _ = (pullback.lift _ _ _) ≫ pullback.fst _ _
  rw [pullback.lift_fst]
  simpa only [inverse, curveMap, GoodReductionJacobian.schemeHomOverComp,
    GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase,
    Category.id_comp, Category.comp_id] using congrArg Subtype.val hn

/-- Pulling back a lift preserves its identity action along a fixed section. -/
lemma lift_fixed {X Y B C : Scheme.{u}} (c : Y ⟶ X) (b : C ⟶ B)
    (o : B ⟶ X) (o' : C ⟶ Y) (f : X ⟶ X) (f' : Y ⟶ Y)
    (hc : c ≫ f = f' ≫ c) (ho : b ≫ o = o' ≫ c)
    (hf : o ≫ f = o) (hf' : o' ≫ f' = o')
    (L : X.Modules) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (hα : (Scheme.Modules.pullback o).mapIso α =
      (Scheme.Modules.pullbackComp o f ≪≫ Scheme.Modules.pullbackCongr hf).app L) :
    (Scheme.Modules.pullback o').mapIso (PullbackLifts.lift c f f' hc α) =
      (Scheme.Modules.pullbackComp o' f' ≪≫ Scheme.Modules.pullbackCongr hf').app
        ((Scheme.Modules.pullback c).obj L) := by
  let A := Scheme.Modules.pullbackComp b o ≪≫ Scheme.Modules.pullbackCongr ho ≪≫
    (Scheme.Modules.pullbackComp o' c).symm
  have hp := Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    o f o hf b c c o' f' o' hf' ho hc ho L
  have hn := A.hom.naturality α.hom
  dsimp only [Functor.comp_map] at hn
  have ha := congrArg Iso.hom hα
  change (Scheme.Modules.pullback o).map α.hom = _ at ha
  rw [ha] at hn
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullback o').map
    ((PullbackLifts.squareNat c f f' hc).app L).inv)).mp
  apply (cancel_epi (A.hom.app ((Scheme.Modules.pullback f).obj L))).mp
  simp only [PullbackLifts.lift, Functor.mapIso_hom, Iso.trans_hom,
    Functor.map_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]
  exact hn.symm.trans hp.symm

lemma conjugate_fixed {Y C : Scheme.{u}} (o : C ⟶ Y) (f : Y ⟶ Y)
    (hf : o ≫ f = o) {L N : Y.Modules} (e : L ≅ N)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (hα : (Scheme.Modules.pullback o).mapIso α =
      (Scheme.Modules.pullbackComp o f ≪≫ Scheme.Modules.pullbackCongr hf).app L) :
    (Scheme.Modules.pullback o).mapIso
      ((Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e) =
        (Scheme.Modules.pullbackComp o f ≪≫ Scheme.Modules.pullbackCongr hf).app N := by
  let F := Scheme.Modules.pullbackComp o f ≪≫ Scheme.Modules.pullbackCongr hf
  have hn := F.hom.naturality e.inv
  dsimp only [Functor.comp_map] at hn
  rw [Functor.mapIso_trans, Functor.mapIso_trans, hα]
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  dsimp only [F, Iso.app_hom] at hn ⊢
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

end InversionNaturalityProof

/-- Normalized inversion commutes with the prescribed geometric comparison. -/
theorem relative_inversion_naturality :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : EllipticFamily R) (S : Type u) [CommRing S] [Algebra R S]
      [Algebra ℚ S] [IsScalarTower ℚ R S] [IsNoetherianRing S] (m : ℕ),
        InversionNatural E S m := by
  intro R _ _ _ E S _ _ _ _ _ m ι ιS hι hιS
  let hc := InversionNaturalityProof.inverse_square_baseChange E S
  refine ⟨hc, ?_⟩
  obtain ⟨φ, hφ, hu⟩ := RelativeNormalizedThetaInversion.unique_fixed_lift (family E S) m
  have ht : (Scheme.Modules.pullback (zero (family E S))).mapIso
      (transportedLift E S m (inverse E) (inverse (family E S)) hc ι) =
        fixedComparison (family E S) m (zero (family E S)) (inverse (family E S))
          (RelativeNormalizedThetaInversion.inverse_zero (family E S)) := by
    obtain ⟨hz, hnorm⟩ := hι.1
    exact InversionNaturalityProof.conjugate_fixed
      (zero (family E S)) (inverse (family E S))
      (RelativeNormalizedThetaInversion.inverse_zero (family E S)) (thetaComparison E S m)
      (RelativePrimitiveThetaCommutator.PullbackLifts.lift (curveMap E S)
        (inverse E) (inverse (family E S)) hc ι)
      (InversionNaturalityProof.lift_fixed (curveMap E S) (baseMap (R := R) S)
        (zero E) (zero (family E S)) (inverse E) (inverse (family E S)) hc
        (RelativePrimitiveThetaCommutator.baseChanged_zero E (baseMap (R := R) S)).symm
        hz (RelativeNormalizedThetaInversion.inverse_zero (family E S)) (thetaLine E m) ι hnorm)
  obtain ⟨hzS, hnormS⟩ := hιS.1
  exact (hu _ ht).trans (hu _ hnormS).symm

#print axioms relative_inversion_naturality
end ArithmeticThetaRelativeThetaNaturalityR0258
