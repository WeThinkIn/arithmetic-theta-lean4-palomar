module

public import TateSchemeScalarLiftR0263
public import TateSchemeShiftLiftR0263
public import TateSchemeSectionEvaluationR0263
public import SchemePrimitiveThetaCommutatorR0259

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaTateSchemeMarkingR0263
namespace ExactCommutator
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTateCuspsR0181
open ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open ArithmeticThetaGeometricLiftsR0141.GeometricThetaRelationsR0141

variable (k : Type) [Field k] [CharZero k] {m : ℕ} {hm : 0 < m}
  (V : TateLevel k (2*m)) {ζ : kˣ}
  (Q : LocalTheta.MarkedModel k m hm V ζ) (he : Even m)

lemma act_scaled {S : Scheme.{0}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (d : ℕ) (g : E.curve ⟶ E.curve) (a : Lift E d g) (c : Γ(S, ⊤)ˣ)
    (v : Γ(thetaLine E d, ⊤)) :
    SectionAction.globalAct g (scaled E d c a) v =
      (scalar E c : Γ(E.curve, ⊤)) • SectionAction.globalAct g a v := by
  open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2 in
    change resTop (scalar E c : Γ(E.curve, ⊤)) ⊤ • SectionAction.globalAct g a v = _
    simp [resTop]

lemma compose_actions {S : Scheme.{0}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (d : ℕ) (gA gB : E.curve ⟶ E.curve) (a : Lift E d gA) (b : Lift E d gB)
    (c : Γ(S, ⊤)ˣ) (h : gA ≫ gB = gB ≫ gA)
    (hact : ∀ v : Γ(thetaLine E d, ⊤),
      SectionAction.globalAct gA a (SectionAction.globalAct gB b v) =
        (scalar E c : Γ(E.curve, ⊤)) •
          SectionAction.globalAct gB b (SectionAction.globalAct gA a v))
    (v : Γ(thetaLine E d, ⊤)) :
    SectionAction.globalAct (gA ≫ gB) (compose E d gA gB a b) v =
      SectionAction.globalAct (gA ≫ gB)
        (scaled E d c (changeMap E d h (compose E d gB gA b a))) v := by
  rw [act_scaled]
  unfold changeMap compose
  rw [ScalarLift.globalAct_changeMap]
  have hA := ScalarLift.globalAct_comp gA gB (N := thetaLine E d) a b v
  have hB := ScalarLift.globalAct_comp gB gA (N := thetaLine E d) b a v
  dsimp only [Midpoint.composeLift] at hA hB
  rw [hA, hB]
  exact hact v

lemma section_commutator (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointX k V)))
    (b : Lift (family k V) m (translation (family k V) (pointY k V)))
    (ha : scalarLiftFacts k V Q he hζ a) (hb : shiftLiftFacts k V Q he b)
    (v : Γ(thetaLine (family k V) m, ⊤)) :
    SectionAction.globalAct _ a (SectionAction.globalAct _ b v) =
      (scalar (family k V) (phase k (ζ := ζ)) : Γ((family k V).curve, ⊤)) •
        SectionAction.globalAct _ b (SectionAction.globalAct _ a v) := by
  have hc := (tate_scheme_section_evaluation k m hm he V ζ hζ Q).1
  apply (sectionEquiv k V Q he).injective
  change _ = LocalTheta.modelFunctional k Q.model Q.origin m Q.cubic _
    (modelComparison k V Q he)
    ((((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv ≫ (family k V).p.appTop)
      (algebraMap k (LaurentSeries k) ((ζ^2 : kˣ) : k))) • _)
  erw [LocalTheta.modelFunctional_smul k Q.model Q.origin m Q.cubic _
    (modelComparison k V Q he) (family k V).p Q.cubic_over]
  change sectionEquiv k V Q he _ = sc k Q.model Q.origin m _ (sectionEquiv k V Q he _)
  rw [hc _ _ a _ ha.1, hc _ _ b _ hb.1, hc _ _ b _ hb.1, hc _ _ a _ ha.1]
  have h := (scaled_iff k Q.model Q.origin m _ _ _).mp
    ((Q.canonical_relations he hζ).2.2.1 (sectionEquiv k V Q he v))
  simpa only [ArithmeticThetaGeometricLiftsR0141.phase, pow_one,
    RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
    PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C] using h

lemma sheaf_commutator (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (a : Lift (family k V) m (translation (family k V) (pointX k V)))
    (b : Lift (family k V) m (translation (family k V) (pointY k V)))
    (ha : scalarLiftFacts k V Q he hζ a) (hb : shiftLiftFacts k V Q he b) :
    Commutator (family k V) m (pointX k V) (pointY k V) a b (phase k (ζ := ζ)) := by
  let h := SchemePrimitiveThetaCommutator.translations_commute (family k V) (pointX k V) (pointY k V)
  refine ⟨h, ?_⟩
  let := ArithmeticThetaGeometricLiftsR0141.GeometricScalarLiftR0141.scalarMap_isIso
    k Q.model Q.rotation Q.scaling Q.inversion Q.actions (ζ^2)
  let := ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.shiftMap_isIso
    k Q.model Q.rotation Q.scaling Q.inversion Q.actions
  have hs : Q.cubic.hom ≫ (translation (family k V) (pointX k V) ≫
      translation (family k V) (pointY k V)) = (Q.mapA ≫ Q.mapB) ≫ Q.cubic.hom := by
    rw [← Category.assoc, ScalarLift.scalar_square k V Q, Category.assoc,
      ShiftLiftProof.shift_commutes k V Q, ← Category.assoc]
  let e : ArithmeticThetaGeometricLiftsR0141.Lift k Q.model Q.origin m (Q.mapA ≫ Q.mapB) :=
    Q.canonicalA he hζ ≪≫ (Scheme.Modules.pullback Q.mapA).mapIso (Q.canonicalB he) ≪≫
      ((Scheme.Modules.pullbackComp Q.mapA Q.mapB).app _)
  apply ShiftLiftProof.action_ext k V Q he _ (Q.mapA ≫ Q.mapB) hs e
  exact compose_actions (family k V) m _ _ a b (phase k (ζ := ζ)) h
    (section_commutator k V Q he hζ a b ha hb)

omit [CharZero k] in
lemma primitive_phase (hm : 0 < m) (hζ : IsPrimitiveRoot (ζ : k) (2*m)) :
    PrimitiveUnit (S := Puncture k) m (phase k (ζ := ζ)) := by
  let f : k →+* Γ(Puncture k, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv.hom.comp
      (algebraMap k (LaurentSeries k))
  have hr := LocalTheta.MarkedModel.root_half (hm := hm) hζ
  constructor
  · apply Units.ext
    change f (((ζ^2 : kˣ) : k)) ^ m = 1
    rw [← map_pow, hr.pow_eq_one, map_one]
  · intro i hi
    have hu : IsUnit ((((ζ^2 : kˣ) : k)) ^ i.val - 1) :=
      isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hr.pow_ne_one_of_pos_of_lt hi i.isLt))
    change IsUnit (f (((ζ^2 : kˣ) : k)) ^ i.val - 1)
    simpa only [map_sub, map_pow, map_one] using hu.map f

end ExactCommutator

open ArithmeticThetaTateCuspsR0181 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily

/-- The literal Tate lifts have exactly the prescribed structural phase, primitive
in the actual global base ring. Equality is an equality of sheaf isomorphisms. -/
theorem tate_scheme_exact_commutator :
    ∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m)
      (V : TateLevel k (2*m)) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
    ∀ Q : LocalTheta.MarkedModel k m hm V ζ,
    ∀ (a : Lift (family k V) m (translation (family k V) (pointX k V)))
      (b : Lift (family k V) m (translation (family k V) (pointY k V))),
      scalarLiftFacts k V Q he hζ a → shiftLiftFacts k V Q he b →
      Commutator (family k V) m (pointX k V) (pointY k V) a b (phase k (ζ := ζ)) ∧
      PrimitiveUnit (S := Puncture k) m (phase k (ζ := ζ)) := by
  intro k _ _ m hm he V ζ hζ Q a b ha hb
  exact ⟨ExactCommutator.sheaf_commutator k V Q he hζ a b ha hb,
    ExactCommutator.primitive_phase k hm hζ⟩

end ArithmeticThetaTateSchemeMarkingR0263

#print axioms ArithmeticThetaTateSchemeMarkingR0263.tate_scheme_exact_commutator
