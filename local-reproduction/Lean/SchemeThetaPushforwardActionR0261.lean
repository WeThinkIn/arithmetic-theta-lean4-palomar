import SchemeSchrodingerDefinitionsR0261

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaSchemeSchrodingerR0261
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeThetaMarkingR0259

namespace PushforwardAction

variable {S X : Scheme.{u}} (p : X ⟶ S) (L : X.Modules)
  (f : X ⟶ X) (h : f ≫ p = p)
  (α : (Scheme.Modules.pullback f).obj L ≅ L)

/-- Push forward the adjoint of the lift, then identify the composite map with
the original structural map. This is a morphism of module sheaves. -/
def action : End ((Scheme.Modules.pushforward p).obj L) :=
  (Scheme.Modules.pushforward p).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ α.hom) ≫
  (Scheme.Modules.pushforwardComp f p).hom.app L ≫
  (Scheme.Modules.pushforwardCongr h).hom.app L

lemma formula (U : S.Opens) (w : Γ(L, p ⁻¹ᵁ U)) :
    α.hom.app (f ⁻¹ᵁ (p ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection f w) =
      L.presheaf.map (eqToHom (congrArg (fun g : X ⟶ S => g ⁻¹ᵁ U) h)).op
        ((action p L f h α).app U w) := by
  let e := (Scheme.Modules.pushforwardComp f p).app L ≪≫
    (Scheme.Modules.pushforwardCongr h).app L
  have he := congrArg (fun t => t.app U w)
    (show action p L f h α ≫ e.inv =
      (Scheme.Modules.pushforward p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ α.hom) by
      simp [action, e])
  rw [Scheme.Modules.app_pullbackLocalSection]
  dsimp only [e] at he
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Iso.trans_inv, Iso.app_inv, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app,
    Scheme.Modules.pushforward_map_app] at he
  exact he.symm

/-- The all-open construction recovers the accepted action on global sections. -/
lemma action_top (w : Γ(L, ⊤)) :
    (action p L f h α).app ⊤ w =
      ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.Sections.act
        f α w := by
  have he := formula p L f h α ⊤ w
  simpa [ArithmeticThetaRelativeThetaRelationsR0256.RelativePrimitiveThetaCommutator.Sections.act]
    using he.symm

end PushforwardAction

theorem scheme_theta_pushforward_action
    (k : Type u) [Field k] [CharZero k] (S : Scheme.{u}) (_σ : S ⟶ Base k)
    (E : Family S) (m : ℕ) (f : E.curve ⟶ E.curve) (h : f ≫ E.p = E.p)
    (α : Lift E m f) : ∃! A : End (V E m), IsAction E m f α A := by
  refine ⟨PushforwardAction.action E.p (thetaLine E m) f h α,
    ⟨h, PushforwardAction.formula E.p (thetaLine E m) f h α⟩, ?_⟩
  intro B hB
  obtain ⟨h', hB⟩ := hB
  apply Scheme.Modules.hom_ext
  intro U
  ext w
  have he := (hB U w).symm.trans
    (PushforwardAction.formula E.p (thetaLine E m) f h α U w)
  exact (ConcreteCategory.bijective_of_isIso
    ((thetaLine E m).presheaf.map
      (eqToHom (congrArg (fun g : E.curve ⟶ S => g ⁻¹ᵁ U) h)).op)).injective he

#print axioms scheme_theta_pushforward_action
end ArithmeticThetaSchemeSchrodingerR0261
