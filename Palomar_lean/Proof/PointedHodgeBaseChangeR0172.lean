module

public import PointedHodgeFunctorialityR0172
public import RelativeInitialSectionNaturalityR0171

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
universe u
namespace ArithmeticThetaRelativeIsogenyHodgeR0172
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaTensorPower PointedHodgeFunctoriality
namespace PointedHodgeBaseChange

/-- Equal geometric composites give equal restricted local sections. -/
theorem section_square {X Y T : Scheme.{u}} (p : T ⟶ X) (N : T.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(N,p ⁻¹ᵁ U))
    (f g : X ⟶ Y) (h : f = g) (U : Y.Opens) (a : Γ(Y,U))
    (B : T.Opens) (hf : B ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U))
    (hg : B ≤ p ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    res N hf (d _ (f.app U a)) = res N hg (d _ (g.app U a)) := by
  subst g
  rfl

/-- Naturality for a commuting square, stated with nested section pullbacks so
specializing the lemma does not unfold concrete scheme presentations. -/
theorem sections_commuting_square {X Y Z Q T : Scheme.{u}}
    (p : T ⟶ X) (N : T.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(N,p ⁻¹ᵁ U))
    (f : X ⟶ Y) (g : Y ⟶ Q) (h : X ⟶ Z) (k : Z ⟶ Q)
    (hsq : f ≫ g = h ≫ k) (U : Q.Opens) (a : Γ(Q,U))
    (B : T.Opens) (hf : B ≤ p ⁻¹ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ U)))
    (hh : B ≤ p ⁻¹ᵁ (h ⁻¹ᵁ (k ⁻¹ᵁ U))) :
    res N hf (d _ (f.app _ (g.app U a))) =
      res N hh (d _ (h.app _ (k.app U a))) := by
  exact section_square p N d (f ≫ g) (h ≫ k) hsq U a B hf hh

end PointedHodgeBaseChange
open PointedHodgeBaseChange
attribute [local irreducible] origin structureMap

/-- The actual pointed differential tensor map commutes with arbitrary Cartesian
base change, as determined on covering local differential tensor frames. -/
theorem pointed_hodge_arbitrary_base_change :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (W : WeierstrassCurve R) [W.IsElliptic] (V : WeierstrassCurve R) [V.IsElliptic] (Ws : WeierstrassCurve S) [Ws.IsElliptic] (Vs : WeierstrassCurve S) [Vs.IsElliptic] (ι : R →+* S) (f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W V) (fs : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap S Ws Vs) (bW : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hbW : CategoryTheory.IsPullback bW (ArithmeticThetaRelativeKatoR0169.structureMap S Ws) (ArithmeticThetaRelativeKatoR0169.structureMap R W) (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)) (hpbW : CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin S Ws) bW = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (ArithmeticThetaRelativeKatoR0169.origin R W)) (bV : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Vs) (ArithmeticThetaRelativeKatoR0169.Curve R V)) (hbV : CategoryTheory.IsPullback bV (ArithmeticThetaRelativeKatoR0169.structureMap S Vs) (ArithmeticThetaRelativeKatoR0169.structureMap R V) (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)) (hpbV : CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeKatoR0169.origin S Vs) bV = CategoryTheory.CategoryStruct.comp (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι) (ArithmeticThetaRelativeKatoR0169.origin R V)) (hsquare : CategoryTheory.CategoryStruct.comp fs.map bV = CategoryTheory.CategoryStruct.comp bW f.map) (n : ℕ) (eW : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).obj (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n)) (ArithmeticThetaRelativeDiscriminantR0171.HodgePower S Ws n)) (heW : ArithmeticThetaRelativeDiscriminantR0171.IsPowerBaseChange R W S Ws ι bW n eW) (eV : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).obj (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R V n)) (ArithmeticThetaRelativeDiscriminantR0171.HodgePower S Vs n)) (heV : ArithmeticThetaRelativeDiscriminantR0171.IsPowerBaseChange R V S Vs ι bV n eV), ArithmeticThetaRelativeIsogenyHodgeR0172.PowerNatural W V Ws Vs ι f fs n eW eV := by
  intro R _ _ _ _ _ S _ _ _ _ _ W _ V _ Ws _ Vs _ ι f fs bW hbW hpbW bV hbV hpbV hsquare n eW heW eV heV
  unfold PowerNatural
  apply hom_ext_frames
  intro x
  let p := baseMap R S ι
  letI : SmoothOfRelativeDimension 1 (structureMap R V) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one V.toProjective
  obtain ⟨U, a, hxU, hU⟩ := exists_exact_differential_frame (structureMap R V)
    ((origin R V) (p x))
  let B := p ⁻¹ᵁ (origin R V ⁻¹ᵁ U)
  refine ⟨B, Scheme.Modules.pullbackLocalSection p (localPower R V n U a), hxU, ?_, ?_⟩
  · apply pullback_frame
    apply tensorPower_frame
    exact pullback_frame (origin R V) (structureMap R V).kaehler _ hU
  · have hf := pointed_preimage (origin R V) (origin R W) f.map f.origin_eq U
    have hpf : B ≤ p ⁻¹ᵁ (origin R W ⁻¹ᵁ (f.map ⁻¹ᵁ U)) := fun y hy => hf hy
    have hv : B ≤ origin S Vs ⁻¹ᵁ (bV ⁻¹ᵁ U) := by
      intro y hy
      change (origin S Vs ≫ bV) y ∈ U
      rw [hpbV]
      exact hy
    have hw : B ≤ origin S Ws ⁻¹ᵁ (bW ⁻¹ᵁ (f.map ⁻¹ᵁ U)) := by
      intro y hy
      change (origin S Ws ≫ bW) y ∈ f.map ⁻¹ᵁ U
      rw [hpbW]
      exact hpf hy
    have hfs : B ≤ origin S Ws ⁻¹ᵁ (fs.map ⁻¹ᵁ (bV ⁻¹ᵁ U)) :=
      hv.trans (pointed_preimage (origin S Vs) (origin S Ws) fs.map fs.origin_eq _)
    have hfval := pointed_hodge_local_formula R W V f n U a _ le_rfl hf
    rw [res_refl] at hfval
    change eW.hom.app B (((Scheme.Modules.pullback p).map (powerMap f n)).app B
      (Scheme.Modules.pullbackLocalSection p (localPower R V n U a))) =
      (powerMap fs n).app B (eV.hom.app B
        (Scheme.Modules.pullbackLocalSection p (localPower R V n U a)))
    rw [← Scheme.Modules.pullbackLocalSection_app, hfval,
      ← InitialSectionNaturality.pullback_res, ← hom_res]
    rw [heW (f.map ⁻¹ᵁ U) (f.map.app U a) B hpf hw]
    have hvval := heV U a B le_rfl hv
    rw [res_refl] at hvval
    rw [hvval, ← hom_res]
    rw [pointed_hodge_local_formula S Ws Vs fs n (bV ⁻¹ᵁ U) (bV.app U a) B hv hfs]
    exact sections_commuting_square (origin S Ws) (HodgePower S Ws n) (localPower S Ws n)
      bW f.map fs.map bV hsquare.symm U a B hw hfs

#print axioms pointed_hodge_arbitrary_base_change
end ArithmeticThetaRelativeIsogenyHodgeR0172
