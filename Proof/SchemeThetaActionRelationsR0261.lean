module

public import SchemeThetaPushforwardActionR0261

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeSchrodingerR0261
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeThetaMarkingR0259
namespace ActionRelations
variable {X S : Scheme.{u}} (L : X.Modules)

def transport {U W : X.Opens} (h : U = W) (s : Γ(L, U)) : Γ(L, W) :=
  L.presheaf.map (eqToHom h.symm).op s

@[simp] lemma transport_refl (U : X.Opens) (s : Γ(L,U)) : transport L rfl s = s := by
  simp [transport]

lemma transport_trans {U W Z : X.Opens} (h : U = W) (j : W = Z) (s : Γ(L,U)) :
    transport L j (transport L h s) = transport L (h.trans j) s := by
  subst W; subst Z; simp

def raw (f : X ⟶ X) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    {U : X.Opens} (s : Γ(L,U)) : Γ(L,f ⁻¹ᵁ U) :=
  α.hom.app _ (Scheme.Modules.pullbackLocalSection f s)

lemma raw_transport (f : X ⟶ X) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    {U W : X.Opens} (h : U = W) (s : Γ(L,U)) :
    raw L f α (transport L h s) =
      transport L (congrArg (fun U => f ⁻¹ᵁ U) h) (raw L f α s) := by
  subst W; simp

lemma raw_comp (f g : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) {U : X.Opens} (s : Γ(L,U)) :
    raw L (f ≫ g) (((Scheme.Modules.pullbackComp f g).app L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ α) s = raw L f α (raw L g β s) := by
  let e := (Scheme.Modules.pullbackComp f g).app L
  have h := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection f g L U s
  have he : e.inv.app _ (Scheme.Modules.pullbackLocalSection (f ≫ g) s) =
      Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s) := by
    have hh := congrArg (fun v => e.inv.app _ v) h
    change e.inv.app _ (e.hom.app _ _) = _ at hh
    change (e.hom ≫ e.inv).app _ _ = _ at hh
    rw [e.hom_inv_id] at hh
    exact hh.symm
  simp only [raw, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [he, Scheme.Modules.pullbackLocalSection_app]
  rfl

def onOpen (f : X ⟶ X) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    {U : X.Opens} (h : f ⁻¹ᵁ U = U) (s : Γ(L,U)) : Γ(L,U) :=
  transport L h (raw L f α s)

lemma onOpen_comp (f g : X ⟶ X)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) {U : X.Opens}
    (hf : f ⁻¹ᵁ U = U) (hg : g ⁻¹ᵁ U = U)
    (hfg : (f ≫ g) ⁻¹ᵁ U = U) (s : Γ(L,U)) :
    onOpen L (f ≫ g) (((Scheme.Modules.pullbackComp f g).app L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso β ≪≫ α) hfg s =
      onOpen L f α hf (onOpen L g β hg s) := by
  simp only [onOpen, raw_comp, raw_transport, transport_trans]

lemma action_app (p : X ⟶ S) (f : X ⟶ X) (hf : f ≫ p = p)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (U : S.Opens) (s : Γ(L,p ⁻¹ᵁ U)) :
    (PushforwardAction.action p L f hf α).app U s =
      onOpen L f α (U := p ⁻¹ᵁ U) (congrArg (fun g : X ⟶ S => g ⁻¹ᵁ U) hf) s := by
  have h := PushforwardAction.formula p L f hf α U s
  change raw L f α s = transport L (congrArg (fun g : X ⟶ S => g ⁻¹ᵁ U) hf).symm ((PushforwardAction.action p L f hf α).app U s) at h
  rw [onOpen, h, transport_trans]
  simp

lemma action_comp (p : X ⟶ S) (f g : X ⟶ X)
    (hf : f ≫ p = p) (hg : g ≫ p = p) (hfg : (f ≫ g) ≫ p = p)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) :
    PushforwardAction.action p L (f ≫ g) hfg
      (((Scheme.Modules.pullbackComp f g).app L).symm ≪≫
        (Scheme.Modules.pullback f).mapIso β ≪≫ α) =
      PushforwardAction.action p L f hf α * PushforwardAction.action p L g hg β := by
  apply Scheme.Modules.hom_ext
  intro U; ext s
  change _ = (PushforwardAction.action p L f hf α).app U
    ((PushforwardAction.action p L g hg β).app U s)
  simp only [action_app]
  exact onOpen_comp L f g α β _ _ _ s

lemma action_change (p : X ⟶ S) {f g : X ⟶ X} (h : f = g)
    (hf : f ≫ p = p) (hg : g ≫ p = p)
    (α : (Scheme.Modules.pullback g).obj L ≅ L) :
    PushforwardAction.action p L f hf ((Scheme.Modules.pullbackCongr h).app L ≪≫ α) =
      PushforwardAction.action p L g hg α := by
  subst g
  rfl

open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

lemma raw_id {U : X.Opens} (s : Γ(L,U)) :
    raw L (𝟙 X) ((Scheme.Modules.pullbackId X).app L) s = s := by
  have h := congrArg (fun t => t.app L) (Scheme.Modules.conjugateEquiv_pullbackId_hom X)
  have hh := congrArg (fun t => t.app U s) h
  simp [conjugateEquiv] at hh
  exact hh

lemma action_id (p : X ⟶ S) :
    PushforwardAction.action p L (𝟙 X) (Category.id_comp p)
      ((Scheme.Modules.pullbackId X).app L) = 1 := by
  apply Scheme.Modules.hom_ext
  intro U; ext s
  rw [action_app]
  simp [onOpen, raw_id]

lemma action_scaled (p : X ⟶ S) (f : X ⟶ X) (hf : f ≫ p = p)
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (c : Γ(S,⊤)ˣ) :
    PushforwardAction.action p L f hf
      (α ≪≫ smulIso (Units.map p.appTop.hom.toMonoidHom c) L) =
      unitAction ((Scheme.Modules.pushforward p).obj L) c *
        PushforwardAction.action p L f hf α := by
  have hs : p.appTop (c : Γ(S,⊤)) = f.appTop (p.appTop (c : Γ(S,⊤))) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf]
  have hsmul : (smulIso (Units.map p.appTop.hom.toMonoidHom c) L).hom =
      smulHom (f.appTop (p.appTop (c : Γ(S,⊤)))) L := by
    change smulHom (p.appTop (c : Γ(S,⊤))) L = _
    exact congrArg (fun s => smulHom s L) hs
  unfold PushforwardAction.action
  simp only [Iso.trans_hom, Adjunction.homEquiv_unit, Functor.map_comp]
  rw [hsmul, pushforward_map_smulHom, pushforward_map_smulHom]
  change _ = _ ≫ smulHom (c : Γ(S,⊤)) _
  simp only [Category.assoc, smulHom_comp]

variable (E : Family S)
open SchemeDoubledTorsionLift SchemeCyclicThetaSplitting

def thetaAction (m : ℕ) (P : point E) (α : Lift E m (translation E P)) : End (V E m) :=
  PushforwardAction.action E.p (thetaLine E m) _ (translation_over E P) α

lemma cyclic_order (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) (hα : MidpointNormalized E m P ι α)
    (F : ∀ n : ℕ, Lift E m (translation E (multiple E P n)))
    (hF : CyclicSystem E m P ι F) : thetaAction E m P α ^ m = 1 := by
  let D (n : ℕ) : End (V E m) := thetaAction E m (multiple E P n) (F n)
  have hz : D 0 = 1 := by
    obtain ⟨h, hh⟩ := hF.2.1
    dsimp [D, thetaAction]
    rw [hh]
    unfold changeMap identityLift
    rw [action_change _ _ h _ (Category.id_comp E.p), action_id]
    rfl
  have hadd (a b : ℕ) : D (a+b) = D a * D b := by
    obtain ⟨h, hh⟩ := hF.2.2.1 a b
    have ho : (translation E (multiple E P a) ≫ translation E (multiple E P b)) ≫ E.p = E.p := by
      rw [Category.assoc, translation_over, translation_over]
    have H := congrArg (fun δ => PushforwardAction.action E.p (thetaLine E m) _ ho δ) hh
    unfold compose changeMap at H
    rw [action_comp _ _ _ _ _ _ ho, action_change _ _ h] at H
    exact H.symm
  have hp' : D (0+m) = D 0 := by
    obtain ⟨h, hh⟩ := hF.2.2.2 0
    dsimp [D, thetaAction]
    rw [hh]
    unfold changeMap
    rw [action_change]
  have hp : D m = D 0 := by simpa only [Nat.zero_add] using hp'
  have hpow (n : ℕ) : D n = D 1 ^ n := by
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [hadd, ih, pow_succ]
  have hgen : D 1 = thetaAction E m P α := by
    have H : ∀ (Q : point E) (hQ : Q = P) (γ : Lift E m (translation E Q)),
        MidpointNormalized E m Q ι γ → thetaAction E m Q γ = thetaAction E m P α := by
      intro Q hQ γ hγ
      subst Q
      have heq := (SchemeMidpointThetaLift.midpoint_exists_unique E m P ι ⟨α⟩).unique
        ⟨hγ, symmetric_of_midpoint E m P ι γ hγ⟩
        ⟨hα, symmetric_of_midpoint E m P ι α hα⟩
      rw [heq]
    exact H _ (multiple_one E P) _ (hF.1 1).1
  rw [← hgen, ← hpow, hp, hz]

end ActionRelations
open ActionRelations SchemeDoubledTorsionLift

theorem scheme_theta_action_relations
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (σ : S ⟶ Base k)
    (E : Family S) (m : ℕ) (hm : 0 < m) (he : Even m)
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m))
    (ι : Lift E m (inverse E))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (hι : NormalizedInversion E m ι)
    (hα : MidpointNormalized E m M.x ι α) (hβ : MidpointNormalized E m M.y ι β)
    (A B : End (V E m)) (c : (S.presheaf.obj (Opposite.op ⊤))ˣ)
    (hc : Commutator E m M.x M.y α β c)
    (hA : IsAction E m (translation E M.x) α A)
    (hB : IsAction E m (translation E M.y) β B) : Relations m A B c := by
  have ha : A = thetaAction E m M.x α :=
    (scheme_theta_pushforward_action k S σ E m _ (translation_over E M.x) α).unique
      hA ⟨translation_over E M.x, PushforwardAction.formula _ _ _ _ _⟩
  have hb : B = thetaAction E m M.y β :=
    (scheme_theta_pushforward_action k S σ E m _ (translation_over E M.y) β).unique
      hB ⟨translation_over E M.y, PushforwardAction.formula _ _ _ _ _⟩
  rw [ha, hb]
  obtain ⟨F, hF, _⟩ := scheme_cyclic_theta_splitting k S σ E m hm he M.x M.killed_x ι hι
  obtain ⟨G, hG, _⟩ := scheme_cyclic_theta_splitting k S σ E m hm he M.y M.killed_y ι hι
  refine ⟨cyclic_order E m M.x ι α hα F hF, cyclic_order E m M.y ι β hβ G hG, ?_⟩
  obtain ⟨h, hc⟩ := hc
  have ho : (translation E M.x ≫ translation E M.y) ≫ E.p = E.p := by
    rw [Category.assoc, translation_over, translation_over]
  have ho' : (translation E M.y ≫ translation E M.x) ≫ E.p = E.p := by
    rw [Category.assoc, translation_over, translation_over]
  have H := congrArg (fun δ => PushforwardAction.action E.p (thetaLine E m) _ ho δ) hc
  unfold compose scaled changeMap scalar at H
  rw [action_comp, action_scaled, action_change _ _ h _ ho', action_comp] at H
  exact H

#print axioms scheme_theta_action_relations
end ArithmeticThetaSchemeSchrodingerR0261
