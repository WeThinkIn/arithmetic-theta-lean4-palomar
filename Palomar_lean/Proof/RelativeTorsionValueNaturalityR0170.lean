module

public import RelativeKatoArbitraryBaseChangeR0170
public import RelativeTorsionUnitValueR0170

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
namespace TorsionValueNaturality
open CategoryTheory AlgebraicGeometry

/-- Evaluation of regular sections commutes with the actual point square. -/
lemma evaluation_square {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (ι : R →+* S) (b : Y ⟶ X)
    (P : Spec (CommRingCat.of R) ⟶ X) (Ps : Spec (CommRingCat.of S) ⟶ Y)
    (hpoint : Ps ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ P)
    (U : X.Opens) (V : Y.Opens) (e : V ≤ b ⁻¹ᵁ U)
    (eP : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U)
    (ePs : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ Ps ⁻¹ᵁ V)
    (a : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom (Ps.appLE V ⊤ ePs (b.appLE U V e a)) =
      ι ((Scheme.ΓSpecIso (CommRingCat.of R)).hom (P.appLE U ⊤ eP a)) := by
  let j := Spec.map (CommRingCat.ofHom ι)
  have ht : j.appLE ⊤ ⊤ le_top = j.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have he : b.appLE U V e ≫ Ps.appLE V ⊤ ePs = P.appLE U ⊤ eP ≫ j.appTop := by
    rw [← ht, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hpoint, j]
  have H := congrArg (fun f : Γ(X, U) ⟶ CommRingCat.of S => f a)
    (calc
      (b.appLE U V e ≫ Ps.appLE V ⊤ ePs) ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
          (P.appLE U ⊤ eP ≫ j.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := by rw [he]
      _ = P.appLE U ⊤ eP ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom ι := by
        rw [Category.assoc, Scheme.ΓSpecIso_naturality])
  exact H

end TorsionValueNaturality
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169

/-- The unique unit value at a nonidentity prime-to-c torsion section is
natural under every pointed Cartesian base change with the stated point square. -/
theorem relative_torsion_value_naturality :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (gs : (ArithmeticThetaRelativeKatoR0169.Curve S Ws).functionField) (hgs : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized S Ws Gs c gs) (P : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of R)) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hP : CategoryTheory.CategoryStruct.comp P (ArithmeticThetaRelativeKatoR0169.structureMap R W) = CategoryTheory.CategoryStruct.id _) (N : ℕ) (hN : 0 < N) (hNP : CategoryTheory.CategoryStruct.comp P (G.schemeNsmul N) = ArithmeticThetaRelativeKatoR0169.origin R W) (hne : P ≠ ArithmeticThetaRelativeKatoR0169.origin R W) (hcN : Nat.Coprime c N) (Ps : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of S)) (ArithmeticThetaRelativeKatoR0169.Curve S Ws)) (hPs : CategoryTheory.CategoryStruct.comp Ps (ArithmeticThetaRelativeKatoR0169.structureMap S Ws) = CategoryTheory.CategoryStruct.id _) (hpoint : CategoryTheory.CategoryStruct.comp Ps b = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ι)) P), ∃! v : R, IsUnit v ∧ ArithmeticThetaRelativeKatoNaturalityR0170.HasValue R W P g v ∧ IsUnit (ι v) ∧ ArithmeticThetaRelativeKatoNaturalityR0170.HasValue S Ws Ps gs (ι v) := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG S _ _ _ _ _ Ws _ _ _ _ _ Gs hGs
    ι b hb c hc hc6 g hg gs hgs P hP N hN hNP hne hcN Ps hPs hpoint
  obtain ⟨hav, v, hv, huniq⟩ := relative_torsion_unit_value R W G hG c hc hc6 g hg
    P hP N hN hNP hne hcN
  have hNPs : Ps ≫ Gs.schemeNsmul N = origin S Ws := by
    apply hb.1.hom_ext
    · rw [Category.assoc, hb.2.2, ← Category.assoc, hpoint, Category.assoc, hNP]
      exact hb.2.1.symm
    · rw [Category.assoc, Gs.schemeNsmul_over, hPs]
      exact (WeierstrassProjModel.kwZeroSect S Ws).property.symm
  have hnes : Ps ≠ origin S Ws := by
    intro he
    let j := Spec.map (CommRingCat.ofHom ι)
    have H : j ≫ P = j ≫ origin R W := by
      exact hpoint.symm.trans ((congrArg (fun f => f ≫ b) he).trans hb.2.1)
    let x := genericPoint (Spec (CommRingCat.of S))
    have hx : P (j x) = origin R W (j x) :=
      congrArg (fun f : Spec (CommRingCat.of S) ⟶ Curve R W => f x) H
    apply hav (j x)
    refine ⟨j x, ?_⟩
    rw [hx]
    exact (congrArg (fun f : Spec (CommRingCat.of R) ⟶ Curve R W => f (j x))
      (RelativeExistence.origin_fixed R W G hG c)).symm
  obtain ⟨_, w, hw, huniqS⟩ := relative_torsion_unit_value S Ws Gs hGs c hc hc6 gs hgs
    Ps hPs N hN hNPs hnes hcN
  have ho : origin R W ≫ structureMap R W = 𝟙 _ :=
    (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [ho]; infer_instance
  letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
  let U : (Curve R W).Opens := (G.schemeNsmul c) ⁻¹ᵁ
    ⟨(Set.range (origin R W))ᶜ, (origin R W).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have eP : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U := fun x _ => hav x
  letI : Nonempty U := ⟨⟨P (genericPoint (Spec (CommRingCat.of R))), eP trivial⟩⟩
  let V := b ⁻¹ᵁ U
  have ePs : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ Ps ⁻¹ᵁ V := by
    intro x hx
    change b (Ps x) ∈ U
    have H := congrArg (fun f : Spec (CommRingCat.of S) ⟶ Curve R W => f x) hpoint
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at H
    rw [H]
    exact eP trivial
  letI : Nonempty V := ⟨⟨Ps (genericPoint (Spec (CommRingCat.of S))), ePs trivial⟩⟩
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  have hu := (RelativeExistence.relative_of_generic R W G hG C c hc hc6 g (hg.2 C)).2
  obtain ⟨a, ⟨ha, hau⟩, _⟩ := hu U (fun x hx => hx)
  have heval : (Scheme.ΓSpecIso (CommRingCat.of R)).hom (P.appLE U ⊤ eP a) = v :=
    huniq _ ⟨(hau.map (P.appLE U ⊤ eP).hom).map
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, ⟨U, inferInstance, eP, a, hau, ha, rfl⟩⟩
  have hbc := relative_kato_arbitrary_base_change R W G hG S Ws Gs hGs ι b hb
    c hc hc6 g hg gs hgs U V le_rfl a (fun x hx => hx) ha
  have hvs : HasValue S Ws Ps gs (ι v) := by
    refine ⟨V, inferInstance, ePs, b.appLE U V le_rfl a, hbc.1, hbc.2, ?_⟩
    rw [TorsionValueNaturality.evaluation_square ι b P Ps hpoint U V le_rfl eP ePs a, heval]
  have heq : ι v = w := huniqS _ ⟨hv.1.map ι, hvs⟩
  have htarget : IsUnit (ι v) ∧ HasValue S Ws Ps gs (ι v) := heq ▸ hw
  refine ⟨v, ⟨hv.1, hv.2, htarget⟩, ?_⟩
  intro w hw
  exact huniq w ⟨hw.1, hw.2.1⟩

#print axioms relative_torsion_value_naturality
end ArithmeticThetaRelativeKatoNaturalityR0170
