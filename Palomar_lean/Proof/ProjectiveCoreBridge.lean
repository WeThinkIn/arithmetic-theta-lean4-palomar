module

public import ProjectiveTransportBridge

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace PalomarProjective956
open ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaSchemeThetaMarkingR0259 ArithmeticThetaSchemeSchrodingerR0261
open ArithmeticThetaSchemeThetaNaturalityR0262 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaTateCuspsR0181 ArithmeticThetaComponentDegreeR0184
open ArithmeticThetaInvariantRatiosR0265
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194
open ArithmeticThetaGlobalProjectiveRatiosR0266.GlobalArithmeticProjectiveRatios
open Arithmetic


variable (k : Type) [Field k] [CharZero k] (m : ℕ)
  (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (Vd : DiskTest k (2*m) D X)
def GlobalThetaData (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m)) : Prop :=
  let E := globalFamily k m D
  let T := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let P := (globalLevel k m D).x
  let Q := (globalLevel k m D).y
  ∃ (model : ArithmeticFamily.LocalTheta.MarkedModel k m hm Vd.level ζ)
    (a : Lift T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)))
    (b : Lift T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)))
    (I : Lift E m (inverse E)) (α₀ : Lift E m (translation E P))
    (β₀ : Lift E m (translation E Q)) (signs : Bool × Bool),
    ArithmeticThetaTateSchemeMarkingR0263.scalarLiftFacts k Vd.level model he hζ a ∧
    ArithmeticThetaTateSchemeMarkingR0263.shiftLiftFacts k Vd.level model he b ∧
    NormalizedInversion E m I ∧ MidpointNormalized E m P I α₀ ∧
    MidpointNormalized E m Q I β₀ ∧ Symmetric E m P I α₀ ∧ Symmetric E m Q I β₀ ∧
    let α := scaled E m (signUnit (globalBase k m D) signs.1) α₀
    let β := scaled E m (signUnit (globalBase k m D) signs.2) β₀
    ∃ (hc : IsPullback Vd.map T.p E.p (tateBase k m D X Vd))
      (hz : T.zero ≫ Vd.map = tateBase k m D X Vd ≫ E.zero),
      LiftCorresponds E T (tateBase k m D X Vd) Vd.map hc hz m
        (translation E P) (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) α a ∧
      LiftCorresponds E T (tateBase k m D X Vd) Vd.map hc hz m
        (translation E Q) (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) β b ∧
      ∃ (A B : End (V E m)) (A' B' : End (V T m)) (c : Γ(globalBase k m D, ⊤)ˣ),
        IsAction E m (translation E P) α A ∧ IsAction E m (translation E Q) β B ∧
        IsAction T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' ∧
        IsAction T m (translation T (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' ∧
        Relations m A B c ∧ PrimitiveUnit (S := globalBase k m D) m c ∧
        Scheme.Modules.IsInvertible (fixed A) ∧ Orbit m A B c ∧
        Scheme.Modules.IsInvertible (commonValueLine E m A) ∧
        InvariantComponents E T (tateBase k m D X Vd) Vd.map hc hz m A B A' B' ∧
        ComponentRatios T m hm A' B' (unaryRatio k m hm)

open InvariantRatioFieldDescent ArithmeticInvariantRatioRealization SchemeDoubledTorsionLift
def GlobalThetaCore : Prop :=
 ∀ (k : Type) [Field k] [CharZero k] (m : ℕ)
 (D : LevelData k (2*m)) (X : Compactification k (2*m) D) (Vd : DiskTest k (2*m) D X)
 (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)),
 CanonicalMarking k (2*m) (ζ : k) Vd.level → GlobalThetaData k m D X Vd hm he ζ hζ

theorem global_theta_core : GlobalThetaCore := by
  intro k _ _ m D X Vd hm he ζ hζ hmark
  let E := globalFamily k m D
  let F := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let M := globalLevel k m D
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := tateBase k m D X Vd
  have hc : IsPullback Vd.map F.p E.p t := Vd.classifies.2.1
  have hz : F.zero ≫ Vd.map = t ≫ E.zero := tate_pointed k m D X Vd
  have hmul : Multiplicative E F t Vd.map :=
    pointed_cartesian_group_law k _ _ σ E F t Vd.map hc hz
  obtain ⟨Q, _, _, _, i, a, b, _, ha, hb, _, _, hglobal⟩ :=
    ArithmeticThetaTateSchemeMarkingR0263.global_literal_tate_marking k m hm he Vd.level ζ hζ hmark
  obtain ⟨I, α₀, β₀, hI, hα₀, hβ₀, hsα₀, hsβ₀, signs, hsigns, _⟩ :=
    hglobal _ σ E M t Vd.map hc hz hmul Vd.classifies.2.2.2.1 Vd.classifies.2.2.2.2
  let α := scaled E m (signUnit _ signs.1) α₀
  let β := scaled E m (signUnit _ signs.2) β₀
  let A := ActionRelations.thetaAction E m M.x α
  let B := ActionRelations.thetaAction E m M.y β
  let A' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level) a
  let B' := ActionRelations.thetaAction F m (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level) b
  have hA : IsAction E m (translation E M.x) α A :=
    ⟨translation_over E M.x, PushforwardAction.formula _ _ _ _ _⟩
  have hB : IsAction E m (translation E M.y) β B :=
    ⟨translation_over E M.y, PushforwardAction.formula _ _ _ _ _⟩
  have hA' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointX k Vd.level)) a A' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hB' : IsAction F m (translation F (ArithmeticThetaTateSchemeMarkingR0263.pointY k Vd.level)) b B' :=
    ⟨translation_over F _, PushforwardAction.formula _ _ _ _ _⟩
  have hpA : A ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_x α₀ hα₀ signs.1
  have hpB : B ^ m = 1 := signed_power k m σ E hm he I hI _ M.killed_y β₀ hβ₀ signs.2
  obtain ⟨c, hcmt, _⟩ := scheme_primitive_theta_commutator k _ σ E m hm he M α β
  have hrel : Relations m A B c := ⟨hpA, hpB, action_commutator E m _ _ α β c hcmt.1⟩
  have hline := scheme_invariant_theta_line k _ σ E m hm A B c hrel hcmt.2
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  have horbit := scheme_schrodinger_orbit k _ σ (V E m) m hm A B c hrel hcmt.2
  have hvalue : Scheme.Modules.IsInvertible (commonValueLine E m A) :=
    hline.dual.1.tensor_monoidalV2 hfiber
  have hpush := scheme_pushforward_intertwining k _ σ E _ F t Vd.map hc hz m hm
  have hAA := hpush.2 _ _ α a A A' hsigns.1 hA hA'
  have hBB := hpush.2 _ _ β b B B' hsigns.2 hB hB'
  have hcmp := scheme_invariant_component_naturality k _ σ E _ F t Vd.map hc hz
    m hm A B A' B' hpA hAA hBB
  have hrat := tate_invariant_component_ratios k m hm he Vd.level ζ hζ Q a b ha hb A' B' hA' hB'
  exact ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsigns.1, hsigns.2, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hcmt.2, hline, horbit, hvalue, hcmp, hrat⟩

theorem realization_from_components (hcore : GlobalThetaCore) (hq : PalomarProjective954.QuotientTransfer) (hm : 0 < m) (he : Even m) (ζ : kˣ)
    (hζ : IsPrimitiveRoot (ζ : k) (2*m))
    (hmark : CanonicalMarking k (2*m) (ζ : k) Vd.level) :
    GlobalRealization k m D X Vd hm he ζ hζ := by
  let E := globalFamily k m D
  let F := ArithmeticThetaTateSchemeMarkingR0263.family k Vd.level
  let M := globalLevel k m D
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring))
  let t := tateBase k m D X Vd
  obtain ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsignα, hsignβ, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hprim, hline, horbit, hvalue, hcmp, hrat⟩ := hcore k m D X Vd hm he ζ hζ hmark
  have hfiber := (SchemePrimitiveThetaCommutator.line_invertible E m).pullback E.zero
  obtain ⟨test⟩ := test_exists k m D X Vd
  let g := genericBase k m D X Vd
  have ht : Spec.map (CommRingCat.ofHom test.scalar) ≫ g = t := by
    change Spec.map (CommRingCat.ofHom test.scalar) ≫
      (GeometricComponentCuspBoundR0184.componentGenericOpen k (2*m) D X (Vd.disk (closedPoint k)) ≫
        D.quotient.inclusion) = _
    rw [← Category.assoc, test.base_eq]
  let P := Scheme.Modules.pullback t
  let z : Fin m := ⟨0, hm⟩
  let d := component E m A B z
  let d' := component F m A' B' z
  let eN := fiberComparison E F t Vd.map hc hz m
  have hcomparison := hcmp
  obtain ⟨e, heq, _⟩ := hcomparison
  have H (j : Fin m) : P.map (component E m A B j) ≫ eN.hom =
      e.hom ≫ component F m A' B' j := heq.2.2 j
  have hdT : IsIso (P.map d) := by
    letI : IsIso d' := hrat.1
    have hdEq : P.map d = e.hom ≫ d' ≫ eN.inv := by
      rw [← Category.assoc, ← H z, Category.assoc, eN.hom_inv_id, Category.comp_id]
    rw [hdEq]
    infer_instance
  have hsT (j : Fin m) : P.map (component E m A B j) =
      P.map d ≫ scalarEnd (P.obj ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)))
        (unaryRatio k m hm j) := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, scalar_natural, ← Category.assoc, H z, Category.assoc, ← hrat.2 j]
    exact H j
  obtain ⟨C, hC⟩ := interior_chart k m D X Vd
  obtain ⟨r, C', hr, hCC', hreg, himage⟩ := hq
    (compactComponent k m D X Vd) (globalBase k m D) g C
    (LaurentSeries k) test.scalar t ht
    (fixed A) ((Scheme.Modules.pullback E.zero).obj (thetaLine E m)) hline hfiber
    d m (fun j => component E m A B j) (unaryRatio k m hm) hdT hsT
  refine ⟨Q, a, b, I, α₀, β₀, signs, ha, hb, hI, hα₀, hβ₀, hsα₀, hsβ₀,
    hc, hz, hsignα, hsignβ, A, B, A', B', c, hA, hB, hA', hB',
    hrel, hprim, hline, horbit, hvalue, hcmp, hrat,
    C', r, test, interior_refines k m D X Vd hC hCC', hr, hreg, himage, ?_⟩
  intro j
  exact (rationalExpansion_iff k (compactComponent k m D X Vd) (genericInclusion k ≫ test.disk)
    test.scalar test.generic_eq (r j) (unaryRatio k m hm j)).mpr (himage j)

theorem recover_from_components (hcore : GlobalThetaCore) (hq : PalomarProjective954.QuotientTransfer) :
∀ (k : Type) [Field k] [CharZero k] (m : ℕ) (hm : 0 < m) (he : Even m) (ζ : kˣ) (hζ : IsPrimitiveRoot (ζ : k) (2*m)), ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (2*m)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (2*m) D) (Vd : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (2*m) D X), ArithmeticThetaTateCuspsR0181.CanonicalMarking k (2*m) (ζ : k) Vd.level ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.Arithmetic.GlobalRealization k m D X Vd hm he ζ hζ := by
  intro k _ _ m hm he ζ hζ
  obtain ⟨D, X, Vd, hmark⟩ := GlobalArithmeticProjectiveRatios.geometric_data k m hm he ζ hζ
  exact ⟨D, X, Vd, hmark, realization_from_components k m D X Vd hcore hq hm he ζ hζ hmark⟩


end PalomarProjective956
