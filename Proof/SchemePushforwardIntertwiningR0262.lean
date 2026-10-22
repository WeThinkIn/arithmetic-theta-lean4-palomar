module

public import SchemeThetaNaturalityDefinitionsR0262
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
public import SchemeThetaActionRelationsR0261
public import SchemeThetaPushforwardBaseChangeR0261

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeThetaMarkingR0259
open ArithmeticThetaSchemeSchrodingerR0261
namespace PushforwardIntertwining

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)

lemma map_eq (m : ℕ) :
    pushforwardMap E F b f hc hz m =
      Scheme.Modules.baseChangeHom hc.w (thetaLine E m) ≫
        (Scheme.Modules.pushforward F.p).map (thetaComparison E F b f hc hz m).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction F.p).homEquiv _ _).symm.injective
  rw [pushforwardMap, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_naturality_right_symm]
  rw [Adjunction.homEquiv_counit, Scheme.Modules.baseChangeHom_counit]
  rfl

lemma map_isIso (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
    (m : ℕ) (hm : 0 < m) : IsIso (pushforwardMap E F b f hc hz m) := by
  have H := SchemeThetaPushforwardBaseChange.baseChangeMap_isIso k σ E m hm b
  rw [SchemeThetaPushforwardBaseChange.baseChangeMap_eq] at H
  haveI := (Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
    (IsPullback.of_hasPullback E.p b) hc (thetaLine E m)).mp H
  rw [map_eq]
  infer_instance

open ActionRelations (transport transport_refl transport_trans)

variable {X Y Z : Scheme.{u}}

def sectionMap (a : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (Scheme.Modules.pullback a).obj L ⟶ M) {U : Y.Opens} (s : Γ(L,U)) :
    Γ(M, a ⁻¹ᵁ U) := e.app _ (Scheme.Modules.pullbackLocalSection a s)

lemma sectionMap_transport (a : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (Scheme.Modules.pullback a).obj L ⟶ M) {U W : Y.Opens}
    (h : U = W) (s : Γ(L,U)) :
    sectionMap a e (transport L h s) =
      transport M (congrArg (fun U => a ⁻¹ᵁ U) h) (sectionMap a e s) := by
  subst W; simp

lemma sectionMap_comp (a : X ⟶ Y) (c : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (e : (Scheme.Modules.pullback a).obj M ⟶ N)
    (d : (Scheme.Modules.pullback c).obj L ⟶ M) {U : Z.Opens} (s : Γ(L,U)) :
    sectionMap (a ≫ c) (((Scheme.Modules.pullbackComp a c).app L).inv ≫
      (Scheme.Modules.pullback a).map d ≫ e) s =
      sectionMap a e (sectionMap c d s) := by
  let q := (Scheme.Modules.pullbackComp a c).app L
  have h := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection a c L U s
  have he : q.inv.app _ (Scheme.Modules.pullbackLocalSection (a ≫ c) s) =
      Scheme.Modules.pullbackLocalSection a (Scheme.Modules.pullbackLocalSection c s) := by
    have hh := congrArg (fun v => q.inv.app _ v) h
    change (q.hom ≫ q.inv).app _ _ = _ at hh
    rw [q.hom_inv_id] at hh
    exact hh.symm
  simp only [sectionMap, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [he]
  exact congrArg (fun x => e.app _ x)
    (Scheme.Modules.pullbackLocalSection_app a d (Scheme.Modules.pullbackLocalSection c s)).symm

lemma sectionMap_congr {a c : X ⟶ Y} (h : a = c)
    {L : Y.Modules} {M : X.Modules} (e : (Scheme.Modules.pullback c).obj L ⟶ M)
    {U : Y.Opens} (s : Γ(L,U)) :
    transport M (congrArg (fun a => a ⁻¹ᵁ U) h)
      (sectionMap a (((Scheme.Modules.pullbackCongr h).app L).hom ≫ e) s) =
      sectionMap c e s := by
  subst c
  simp [sectionMap, Scheme.Modules.pullbackCongr]

lemma hom_transport {L M : X.Modules} (e : L ⟶ M) {U W : X.Opens}
    (h : U = W) (s : Γ(L,U)) :
    e.app W (transport L h s) = transport M h (e.app U s) := by
  subst W; simp

lemma map_section (m : ℕ) (U : S.Opens) (s : Γ(V E m,U)) :
    (pushforwardMap E F b f hc hz m).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b s) =
    transport (thetaLine F m) (congrArg (fun a => a ⁻¹ᵁ U) hc.w)
      (sectionMap f (thetaComparison E F b f hc hz m).hom s) := by
  have h := congrArg (fun t => t s)
    (Scheme.Modules.unit_app_app_comp_baseChangeHom_app E.p b F.p f hc.w (thetaLine E m) U)
  change (Scheme.Modules.baseChangeHom hc.w (thetaLine E m)).app (b ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection b s) =
    transport ((Scheme.Modules.pullback f).obj (thetaLine E m))
      (congrArg (fun a => a ⁻¹ᵁ U) hc.w) (Scheme.Modules.pullbackLocalSection f s) at h
  calc
    _ = (thetaComparison E F b f hc hz m).hom.app _
      ((Scheme.Modules.baseChangeHom hc.w (thetaLine E m)).app _
        (Scheme.Modules.pullbackLocalSection b s)) :=
      congrArg (fun t => t.app (b ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection b s))
        (map_eq E F b f hc hz m)
    _ = (thetaComparison E F b f hc hz m).hom.app _
      (transport ((Scheme.Modules.pullback f).obj (thetaLine E m))
        (congrArg (fun a => a ⁻¹ᵁ U) hc.w) (Scheme.Modules.pullbackLocalSection f s)) :=
      congrArg (fun t => (thetaComparison E F b f hc hz m).hom.app _ t) h
    _ = _ := hom_transport _ _ _

lemma lift_section (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (h : g' ≫ f = f ≫ g) (α : Lift E m g)
    (U : E.curve.Opens) (s : Γ(thetaLine E m,U)) :
    transport (thetaLine F m) (congrArg (fun a => a ⁻¹ᵁ U) h)
      (sectionMap g' (transportedLift E F b f hc hz m g g' h α).hom
        (sectionMap f (thetaComparison E F b f hc hz m).hom s)) =
    sectionMap f (thetaComparison E F b f hc hz m).hom (sectionMap g α.hom s) := by
  rw [← sectionMap_comp, ← sectionMap_comp]
  have he : ((Scheme.Modules.pullbackComp g' f).app (thetaLine E m)).inv ≫
      (Scheme.Modules.pullback g').map (thetaComparison E F b f hc hz m).hom ≫
      (transportedLift E F b f hc hz m g g' h α).hom =
    ((Scheme.Modules.pullbackCongr h).app (thetaLine E m)).hom ≫
      ((Scheme.Modules.pullbackComp f g).app (thetaLine E m)).inv ≫
      (Scheme.Modules.pullback f).map α.hom ≫ (thetaComparison E F b f hc hz m).hom := by
    simp [transportedLift, ← Functor.map_comp, Category.assoc]
  rw [he]
  exact sectionMap_congr h _ s

lemma action_section (m : ℕ) (g : E.curve ⟶ E.curve) (α : Lift E m g)
    (A : End (V E m)) (hg : g ≫ E.p = E.p)
    (ha : ∀ (U : S.Opens) (s : Γ(thetaLine E m, E.p ⁻¹ᵁ U)),
      α.hom.app (g ⁻¹ᵁ (E.p ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection g s) =
        (thetaLine E m).presheaf.map
          (eqToHom (congrArg (fun a : E.curve ⟶ S => a ⁻¹ᵁ U) hg)).op (A.app U s))
    (U : S.Opens) (s : Γ(V E m,U)) :
    A.app U s = transport (thetaLine E m) (congrArg (fun a => a ⁻¹ᵁ U) hg)
      (sectionMap g α.hom s) := by
  have h := ha U s
  change sectionMap g α.hom s = transport (thetaLine E m)
    (congrArg (fun a => a ⁻¹ᵁ U) hg).symm (A.app U s) at h
  rw [h, transport_trans]
  simp

lemma intertwines (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (α : Lift E m g) (α' : Lift F m g') (A : End (V E m)) (A' : End (V F m))
    (h : LiftCorresponds E F b f hc hz m g g' α α')
    (ha : IsAction E m g α A) (ha' : IsAction F m g' α' A') :
    Intertwines E F b f hc hz m A A' := by
  obtain ⟨h, rfl⟩ := h
  obtain ⟨hg, hA⟩ := ha
  obtain ⟨hg', hA'⟩ := ha'
  apply Scheme.Modules.pullback_hom_ext b
  intro U s
  change (pushforwardMap E F b f hc hz m).app _
    (((Scheme.Modules.pullback b).map A).app _ (Scheme.Modules.pullbackLocalSection b s)) =
    A'.app _ ((pushforwardMap E F b f hc hz m).app _ (Scheme.Modules.pullbackLocalSection b s))
  rw [← Scheme.Modules.pullbackLocalSection_app, map_section, map_section]
  rw [action_section E m g α A hg hA, action_section F m g' _ A' hg' hA']
  rw [sectionMap_transport, sectionMap_transport, transport_trans, transport_trans]
  rw [← lift_section E F b f hc hz m g g' h α]
  rw [transport_trans]

end PushforwardIntertwining

/-- The fixed adjoint-counit comparison is invertible in positive degree and
intertwines every pair of corresponding geometric lifts on every open. -/
theorem scheme_pushforward_intertwining :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S) (f : Quiver.Hom F.curve E.curve) (hc : CategoryTheory.IsPullback f F.p E.p b) (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), ∀ (m : ℕ), 0 < m → CategoryTheory.IsIso (ArithmeticThetaSchemeThetaNaturalityR0262.pushforwardMap E F b f hc hz m) ∧ ∀ (g : Quiver.Hom E.curve E.curve) (g' : Quiver.Hom F.curve F.curve) (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m g) (α' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m g') (A : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V E m)) (A' : CategoryTheory.End (ArithmeticThetaSchemeSchrodingerR0261.V F m)), ArithmeticThetaSchemeThetaNaturalityR0262.LiftCorresponds E F b f hc hz m g g' α α' → ArithmeticThetaSchemeSchrodingerR0261.IsAction E m g α A → ArithmeticThetaSchemeSchrodingerR0261.IsAction F m g' α' A' → ArithmeticThetaSchemeThetaNaturalityR0262.Intertwines E F b f hc hz m A A' := by
  intro k _ _ S σ E T F b f hc hz m hm
  refine ⟨PushforwardIntertwining.map_isIso E F b f hc hz k σ m hm, ?_⟩
  intro g g' α α' A A' h ha ha'
  exact PushforwardIntertwining.intertwines E F b f hc hz m g g' α α' A A' h ha ha'

#print axioms scheme_pushforward_intertwining
end ArithmeticThetaSchemeThetaNaturalityR0262
