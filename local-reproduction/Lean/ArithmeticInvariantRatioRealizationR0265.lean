import TateInvariantComponentRatiosR0265
import InvariantRatioFieldDescentR0265

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace ArithmeticThetaInvariantRatiosR0265
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262
open SchemeDoubledTorsionLift
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
namespace ArithmeticInvariantRatioRealization
open Arithmetic
open ArithmeticThetaSchemeLevelR0204
variable (k : Type) [Field k] [CharZero k] (m : ℕ)
  (D : LevelData k (2*m)) (X : Compactification k (2*m) D)
  (Vd : DiskTest k (2*m) D X)

lemma zero_eq : (family k m D X Vd).zero =
    ArithmeticFamily.origin k (2*m) D X (point k m D X Vd) :=
  ArithmeticFamily.groupLaw_origin k (2*m) D X (point k m D X Vd)

lemma test_exists : Nonempty (Test k m D X Vd) := by
  let E := family k m D X Vd
  let U := GlobalSchemeClassifier.universalFamily (2*m) D.atlas
  let q := ArithmeticFamily.base k (2*m) D X (point k m D X Vd)
  let g := ArithmeticFamily.map k (2*m) D X (point k m D X Vd)
  have hc : IsPullback g E.p U.p q := IsPullback.of_hasPullback _ _
  have hz : E.zero ≫ g = q ≫ U.zero := by
    rw [zero_eq]
    exact ArithmeticFamily.origin_map k (2*m) D X (point k m D X Vd)
  have hmul : Multiplicative U E q g :=
    pointed_cartesian_group_law k _ _
      (Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))) U E q g hc hz
  let M := CartesianFullMarking.up U E q g hc hz hmul (2*m)
    (SchemeFullLevelUniversal.universalLevel D.atlas)
  have hlabel (P : SchemeHomOver (𝟙 _) U.p) :
      (CartesianFullMarking.lift U E q g hc P).val =
        ArithmeticFamily.label k (2*m) D X (point k m D X Vd) P := by
    apply hc.hom_ext
    · exact (CartesianFullMarking.lift_comp U E q g hc P).trans
        (ArithmeticFamily.label_map k (2*m) D X (point k m D X Vd) P).symm
    · exact (CartesianFullMarking.lift U E q g hc P).property.trans
        (ArithmeticFamily.label_structure k (2*m) D X (point k m D X Vd) P).symm
  obtain ⟨d, θ, hd, hdom, hθ⟩ := component_field_factor k (2*m) D X Vd
  have hb := (component_field_map_over k (2*m) D X Vd d hd θ hθ).2
  let f := ArithmeticFamily.tateMap k (2*m) D X (point k m D X Vd) Vd θ hb
  have hzT : (tateFamily k m D X Vd).zero ≫ f = Spec.map (CommRingCat.ofHom θ) ≫ E.zero := by
    rw [zero_eq]
    change (ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level).zero ≫ f = _
    rw [ArithmeticThetaSchemeDiscriminantR0244.SchemeDiscriminantExistence.weierstrass_zero]
    exact ArithmeticFamily.tateMap_origin k (2*m) D X (point k m D X Vd) Vd θ hb
  have hmT : Multiplicative E (tateFamily k m D X Vd) (Spec.map (CommRingCat.ofHom θ)) f := by
    intro W t a b a' b' ha hb'
    have ea : a' = ⟨a.val ≫ f, by rw [← ha]; exact a'.property⟩ := Subtype.ext ha
    have eb : b' = ⟨b.val ≫ f, by rw [← hb']; exact b'.property⟩ := Subtype.ext hb'
    rw [ea, eb]
    exact (ArithmeticFamily.tateMap_mul k (2*m) D X (point k m D X Vd) Vd θ hb t a b).symm
  refine ⟨{
    disk := d
    disk_eq := hd
    dominant := hdom
    scalar := θ
    generic_eq := hθ
    base_eq := hb
    level := M
    x_eq := hlabel _
    y_eq := hlabel _
    cartesian := ArithmeticFamily.tateMap_cartesian k (2*m) D X (point k m D X Vd) Vd θ hb
    pointed := hzT
    multiplicative := hmT
    x_tate := ?_
    y_tate := ?_ }⟩
  · rw [show M.x.val = _ from hlabel D.atlas.marking.x]
    exact (ArithmeticFamily.full_labels_tate k (2*m) D X (point k m D X Vd) Vd θ hb).1
  · rw [show M.y.val = _ from hlabel D.atlas.marking.y]
    exact (ArithmeticFamily.full_labels_tate k (2*m) D X (point k m D X Vd) Vd θ hb).2

open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

lemma action_sign {S : Scheme} (E : Family S) (m : ℕ) (P : ArithmeticThetaSchemeThetaMarkingR0259.point E)
    (α : Lift E m (translation E P)) (ε : Bool) :
    ActionRelations.thetaAction E m P (scaled E m (signUnit S ε) α) =
      if ε then -ActionRelations.thetaAction E m P α else ActionRelations.thetaAction E m P α := by
  unfold ActionRelations.thetaAction scaled scalar
  rw [ActionRelations.action_scaled]
  have hn : unitAction (V E m) (-1) = -(1 : End (V E m)) := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change resTop (-1 : Γ(S, ⊤)) U • x = -x
    simp [resTop]
  cases ε <;> simp only [signUnit, Bool.false_eq_true, ↓reduceIte]
  · simp [unitAction, smulIso, smulHom_one]
  · rw [hn, neg_mul, one_mul]

lemma signed_power {S : Scheme} (σ : S ⟶ Base k) (E : Family S)
    (hm : 0 < m) (he : Even m)
    (ι : Lift E m (inverse E)) (hι : NormalizedInversion E m ι)
    (P : ArithmeticThetaSchemeThetaMarkingR0259.point E)
    (hP : ArithmeticThetaSchemeLevelR0204.multiple E (𝟙 S) (2*m) P = E.law.one (𝟙 S))
    (α : Lift E m (translation E P)) (hα : MidpointNormalized E m P ι α) (ε : Bool) :
    ActionRelations.thetaAction E m P (scaled E m (signUnit S ε) α) ^ m = 1 := by
  obtain ⟨F, hF, -⟩ := scheme_cyclic_theta_splitting k S σ E m hm he P hP ι hι
  have hp := ActionRelations.cyclic_order E m P ι α hα F hF
  rw [action_sign]
  cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte, he.neg_pow, hp]

lemma action_commutator {S : Scheme} (E : Family S) (m : ℕ)
    (P Q : ArithmeticThetaSchemeThetaMarkingR0259.point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (c : Γ(S, ⊤)ˣ) (hc : Commutator E m P Q α β c) :
    ActionRelations.thetaAction E m P α * ActionRelations.thetaAction E m Q β =
      unitAction (V E m) c * (ActionRelations.thetaAction E m Q β * ActionRelations.thetaAction E m P α) := by
  obtain ⟨h, hc⟩ := hc
  have ho : (translation E P ≫ translation E Q) ≫ E.p = E.p := by
    rw [Category.assoc, translation_over, translation_over]
  have ho' : (translation E Q ≫ translation E P) ≫ E.p = E.p := by
    rw [Category.assoc, translation_over, translation_over]
  have H := congrArg (fun δ => PushforwardAction.action E.p (thetaLine E m) _ ho δ) hc
  unfold compose scaled changeMap scalar at H
  rw [ActionRelations.action_comp, ActionRelations.action_scaled,
    ActionRelations.action_change _ _ h _ ho', ActionRelations.action_comp] at H
  exact H

end ArithmeticInvariantRatioRealization
open ArithmeticInvariantRatioRealization Arithmetic
open ArithmeticThetaSchemeLevelR0204

/-- The arithmetic component quotients and their complete expansions are obtained
through the original disk and the same canonical theta comparison. -/
theorem arithmetic_invariant_ratio_realization :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m : ℕ) (hm : 0 < m) (he : Even m) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level → ∃ T : ArithmeticThetaInvariantRatiosR0265.Arithmetic.Test k m D X Vd, ArithmeticThetaInvariantRatiosR0265.Arithmetic.Realization k m D X Vd T hm he ζ hζ := by
  intro k _ _ _ m hm he D X Vd ζ hζ hmark
  obtain ⟨T⟩ := test_exists k m D X Vd
  refine ⟨T, ?_⟩
  let E := Arithmetic.family k m D X Vd
  let F := tateFamily k m D X Vd
  let σ := ArithmeticFamily.base k (2*m) D X (Arithmetic.point k m D X Vd) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := baseMap k m D X Vd T
  let f := curveMap k m D X Vd T
  obtain ⟨Q, N, hNx, hNy, i, a, b, hi, ha, hb, hv, hcomm, hglobal⟩ :=
    ArithmeticThetaTateSchemeMarkingR0263.global_literal_tate_marking k m hm he Vd.level ζ hζ hmark
  obtain ⟨I, α₀, β₀, hI, hα₀, hβ₀, hsα₀, hsβ₀, signs, hsigns, -⟩ :=
    hglobal _ σ E T.level t f T.cartesian T.pointed T.multiplicative T.x_tate T.y_tate
  let α := scaled E m (signUnit _ signs.1) α₀
  let β := scaled E m (signUnit _ signs.2) β₀
  let A := ActionRelations.thetaAction E m T.level.x α
  let B := ActionRelations.thetaAction E m T.level.y β
  let A' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level) a
  let B' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level) b
  have hA : IsAction E m (translation E T.level.x) α A :=
    ⟨translation_over E T.level.x, PushforwardAction.formula _ _ _ _ _⟩
  have hB : IsAction E m (translation E T.level.y) β B :=
    ⟨translation_over E T.level.y, PushforwardAction.formula _ _ _ _ _⟩
  have hA' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hB' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hpA : A ^ m = 1 := signed_power k m σ E hm he I hI _ T.level.killed_x α₀ hα₀ signs.1
  have hpB : B ^ m = 1 := signed_power k m σ E hm he I hI _ T.level.killed_y β₀ hβ₀ signs.2
  obtain ⟨c, hc, -⟩ := scheme_primitive_theta_commutator k _ σ E m hm he T.level α β
  have hrel : Relations m A B c := ⟨hpA, hpB, action_commutator E m _ _ α β c hc.1⟩
  have hline := scheme_invariant_theta_line k _ σ E m hm A B c hrel hc.2
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  have hpush := scheme_pushforward_intertwining k _ σ E _ F t f T.cartesian T.pointed m hm
  have hAA := hpush.2 _ _ α a A A' hsigns.1 hA hA'
  have hBB := hpush.2 _ _ β b B B' hsigns.2 hB hB'
  have hcmp := scheme_invariant_component_naturality k _ σ E _ F t f T.cartesian T.pointed
    m hm A B A' B' hpA hAA hBB
  have hrat := tate_invariant_component_ratios k m hm he Vd.level ζ hζ Q a b ha hb A' B' hA' hB'
  obtain ⟨r, hr, -⟩ := invariant_ratio_field_descent _ _ T.scalar E F f T.cartesian T.pointed
    m hm A B A' B' hline hfiber hcmp (unaryRatio k m hm) hrat
  refine ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hsigns.1, hsigns.2, A, B, A', B', r, hA, hB, hA', hB', hcmp, hr.1, hrat, hr.2, ?_⟩
  intro j
  exact (rationalExpansion_iff k (componentScheme k m D X Vd) (genericInclusion k ≫ T.disk)
    T.scalar T.generic_eq (r j) (unaryRatio k m hm j)).mpr (hr.2 j)

#print axioms arithmetic_invariant_ratio_realization

end ArithmeticThetaInvariantRatiosR0265
