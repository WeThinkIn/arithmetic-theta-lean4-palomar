module

public import RelativeThetaNaturalityDefinitionsR0258
public import RelativeThetaSectionsCohomologyR0257

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaNaturalityR0258
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256 ArithmeticThetaRelativeSchrodingerR0257
open RelativePrimitiveThetaCommutator
open scoped TensorProduct
namespace SectionIntertwining

lemma comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (s : Γ(L, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app L).inv.app ⊤
      (Scheme.Modules.pullbackLocalSection (f ≫ g) s) =
    Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s) := by
  let e := (Scheme.Modules.pullbackComp f g).app L
  have h := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection f g L ⊤ s
  have hh := congrArg (fun v => e.inv.app ⊤ v) h
  change e.inv.app ⊤ (e.hom.app ⊤ _) = _ at hh
  change (e.hom ≫ e.inv).app ⊤ _ = _ at hh
  rw [e.hom_inv_id] at hh
  exact hh.symm

lemma congr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (L : Y.Modules) (s : Γ(L, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).app L).inv.app ⊤
      (Scheme.Modules.pullbackLocalSection g s) =
      Scheme.Modules.pullbackLocalSection f s := by
  subst g
  rfl

lemma square_section {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) (L : X.Modules) (s : Γ(L, ⊤)) :
    ((PullbackLifts.squareNat c f g h).app L).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.pullbackLocalSection c s)) =
    Scheme.Modules.pullbackLocalSection c (Scheme.Modules.pullbackLocalSection f s) := by
  change ((Scheme.Modules.pullbackComp c f).app L).inv.app ⊤
    (((Scheme.Modules.pullbackCongr h).app L).inv.app ⊤
      (((Scheme.Modules.pullbackComp g c).app L).hom.app ⊤
        (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.pullbackLocalSection c s)))) = _
  have h₁ := Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection g c L ⊤ s
  have h₂ := congr_inv h L s
  have h₃ := comp_inv c f L s
  exact (congrArg (fun x => ((Scheme.Modules.pullbackComp c f).app L).inv.app ⊤
    (((Scheme.Modules.pullbackCongr h).app L).inv.app ⊤ x)) h₁).trans
    ((congrArg (fun x => ((Scheme.Modules.pullbackComp c f).app L).inv.app ⊤ x) h₂).trans h₃)


lemma lift_section {X Y : Scheme.{u}} (c : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (h : c ≫ f = g ≫ c) {L : X.Modules}
    (α : (Scheme.Modules.pullback f).obj L ≅ L) (s : Γ(L, ⊤)) :
    Sections.act g (PullbackLifts.lift c f g h α)
      (Scheme.Modules.pullbackLocalSection c s) =
    Scheme.Modules.pullbackLocalSection c (Sections.act f α s) := by
  change ((Scheme.Modules.pullback c).map α.hom).app ⊤
    (((PullbackLifts.squareNat c f g h).app L).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.pullbackLocalSection c s))) = _
  exact (congrArg (fun x => ((Scheme.Modules.pullback c).map α.hom).app ⊤ x)
    (square_section c f g h L s)).trans
    (Scheme.Modules.pullbackLocalSection_app c α.hom (Scheme.Modules.pullbackLocalSection f s)).symm

lemma conjugate_section {Y : Scheme.{u}} (g : Y ⟶ Y) {L M : Y.Modules}
    (e : L ≅ M) (α : (Scheme.Modules.pullback g).obj L ≅ L) (s : Γ(L, ⊤)) :
    Sections.act g ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ α ≪≫ e)
      (e.hom.app ⊤ s) = e.hom.app ⊤ (Sections.act g α s) := by
  change e.hom.app ⊤ (α.hom.app ⊤
    (((Scheme.Modules.pullback g).map e.inv).app ⊤
      (Scheme.Modules.pullbackLocalSection g (e.hom.app ⊤ s)))) = _
  have h := Scheme.Modules.pullbackLocalSection_app g e.inv (e.hom.app ⊤ s)
  have hi : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
    change (e.hom ≫ e.inv).app ⊤ s = s
    rw [e.hom_inv_id]
    rfl
  rw [hi] at h
  exact congrArg (fun x => e.hom.app ⊤ (α.hom.app ⊤ x)) h.symm

def sectionsEquiv {S : Type u} [CommRing S] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of S)) {L M : X.Modules} (e : L ≅ M) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p M ⊤
    Γ(L, ⊤) ≃ₗ[S] Γ(M, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p L ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p M ⊤
  exact {
    toFun := fun x => e.hom.app ⊤ x
    invFun := fun x => e.inv.app ⊤ x
    left_inv := fun x => by
      change (e.hom ≫ e.inv).app ⊤ x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := fun x => by
      change (e.inv ≫ e.hom).app ⊤ x = x
      rw [e.inv_hom_id]
      rfl
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => Scheme.Modules.Hom.app_smul e.hom _ x }

lemma sectionPull_act {R : Type u} [CommRing R] (E : EllipticFamily R)
    (S : Type u) [CommRing S] [Algebra R S] (m : ℕ)
    (f : E.curve ⟶ E.curve) (g : (family E S).curve ⟶ (family E S).curve)
    (h : curveMap E S ≫ f = g ≫ curveMap E S) (α : Lift E m f)
    (w : sections E m) :
    Sections.act g (transportedLift E S m f g h α) (sectionPull E S m w) =
      sectionPull E S m (Sections.act f α w) := by
  exact (conjugate_section g (thetaComparison E S m)
    (PullbackLifts.lift (curveMap E S) f g h α)
    (Scheme.Modules.pullbackLocalSection (curveMap E S) w)).trans
    (congrArg (fun x => (thetaComparison E S m).hom.app ⊤ x)
      (lift_section (curveMap E S) f g h α w))

end SectionIntertwining

/-- The canonical geometric tensor comparison intertwines every corresponding lift. -/
theorem relative_section_intertwining :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : EllipticFamily R) (S : Type u) [CommRing S] [Algebra R S] (m : ℕ),
      0 < m → SectionsNatural E S m := by
  intro R _ _ _ E S _ _ m hm
  letI := sectionModule E m
  letI := sectionModule (family E S) m
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (family E S).projection
    ((Scheme.Modules.pullback (curveMap E S)).obj (thetaLine E m)) ⊤
  obtain ⟨e₀, he₀⟩ := (relative_theta_sections_cohomology R E m hm).2 S
  let e₁ := SectionIntertwining.sectionsEquiv (family E S).projection (thetaComparison E S m)
  let e : S ⊗[R] sections E m ≃ₗ[S] sections (family E S) m := e₀.trans e₁
  have he (s : S) (w : sections E m) : e (s ⊗ₜ[R] w) = s • sectionPull E S m w := by
    change e₁ (e₀ (s ⊗ₜ[R] w)) = _
    rw [he₀, map_smul]
    rfl
  refine ⟨e, he, ?_⟩
  intro P α αS h v
  obtain ⟨h, rfl⟩ := h
  have hw (w : sections E m) :
      sectionPull E S m (thetaAct E m P α w) =
      thetaAct (family E S) m (pointBaseChange E S P)
        (transportedLift E S m _ _ h α) (sectionPull E S m w) :=
    (SectionIntertwining.sectionPull_act E S m _ _ h α w).symm
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s w =>
      simp only [LinearMap.baseChange_tmul, he, map_smul, hw]
  | add v w hv hw => simp only [map_add, hv, hw]

#print axioms relative_section_intertwining
end ArithmeticThetaRelativeThetaNaturalityR0258
