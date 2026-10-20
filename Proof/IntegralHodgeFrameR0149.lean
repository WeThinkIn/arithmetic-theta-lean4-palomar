module

public import IntegralHodgeDefinitionsR0149
public import AlgebraizedEffectiveCartierR0136
public import Definitions.Def_AlgebraicGeometry_ModulesRestrictOpen
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible

@[expose] public section

/-! Triviality of the actual integral identity Hodge module.
The restriction comparison preserves the geometric base map. All construction
helpers are confined to this module's namespace. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
namespace ArithmeticThetaIntegralHodgeR0149.IntegralHodgeFrameR0149

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

lemma restrict_kaehlerPresheaf (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    (Scheme.Modules.restrictPresheaf U).obj f.kaehlerPresheaf =
      (U.ι ≫ f).kaehlerPresheaf := by
  change PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (whiskerLeft U.ι.opensFunctor.op f.constToPresheaf) = _
  congr 1
  ext V
  simp only [Scheme.Hom.constToPresheaf, whiskerLeft_app,
    Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
  rw [Scheme.Hom.appLE]

/-- Restriction uses the same base scalar map as the original morphism. -/
def restrictKaehlerIso (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    (Scheme.Modules.pullback U.ι).obj f.kaehler ≅ (U.ι ≫ f).kaehler :=
  (Scheme.Modules.sheafificationCompPullbackIso U).app f.kaehlerPresheaf ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (eqToIso (restrict_kaehlerPresheaf f U))

/-- An open neighborhood of the closed point contains the full local section. -/
lemma section_factors {R : Type u} [CommRing R] [IsLocalRing R]
    (s : Spec (CommRingCat.of R) ⟶ X) (U : X.Opens)
    (h : s (IsLocalRing.closedPoint R) ∈ U) :
    ∃ t : Spec (CommRingCat.of R) ⟶ U.toScheme, t ≫ U.ι = s := by
  have hU : Set.range s ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open U.isOpen h
  refine ⟨IsOpenImmersion.lift U.ι s ?_, ?_⟩
  · simpa only [Scheme.Opens.range_ι] using hU
  · exact IsOpenImmersion.lift_fac _ _ _

/-- A local frame around the closed section point pulls back to a global frame. -/
lemma frame_from_neighborhood {R : Type u} [CommRing R] [IsLocalRing R]
    (s : Spec (CommRingCat.of R) ⟶ X) (L : X.Modules)
    (U : X.Opens) (hU : s (IsLocalRing.closedPoint R) ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf ≅
      (Scheme.Modules.pullback s).obj L) := by
  obtain ⟨t, ht⟩ := section_factors s U hU
  exact ⟨((Scheme.Modules.pullbackCongr ht.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp t U.ι).app L).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso t).symm⟩

end ArithmeticThetaIntegralHodgeR0149.IntegralHodgeFrameR0149

namespace ArithmeticThetaIntegralHodgeR0149
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open IntegralHodgeFrameR0149

/-- The actual identity Hodge module is trivial over the power-series base. -/
theorem integral_hodge_frame :
    ∀ (k : Type u) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
    (T : Tower k r hr) (he : Even r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s),
      Nonempty (IntegralFrame k M s) := by
  intro k _ _ r hr h3 T _ M hM s hs
  obtain ⟨W, hx, hW⟩ := AlgebraizedEffectiveCartierR0136.section_relative_one
    k h3 M hM (zeroIndex r hr) 1 s hs
  obtain ⟨t, ht⟩ := section_factors s W hx
  let := hW
  have hΩ : Scheme.Modules.IsInvertible (W.ι ≫ M.p).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      (Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
        (W.ι ≫ M.p) 1).1
  obtain ⟨V, htV, ⟨e⟩⟩ := hΩ.exists_trivialization (t (IsLocalRing.closedPoint (PowerSeries k)))
  obtain ⟨E⟩ := frame_from_neighborhood t (W.ι ≫ M.p).kaehler V htV e
  exact ⟨E ≪≫ (Scheme.Modules.pullback t).mapIso (restrictKaehlerIso M.p W).symm ≪≫
    (Scheme.Modules.pullbackComp t W.ι).app M.p.kaehler ≪≫
    (Scheme.Modules.pullbackCongr ht).app M.p.kaehler⟩

end ArithmeticThetaIntegralHodgeR0149

#print axioms ArithmeticThetaIntegralHodgeR0149.integral_hodge_frame
