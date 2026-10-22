module

public import RootDescentDefinitionsR0197
public import RootTestPullbackCoherenceR0196
public import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
public import CompactDiscriminantSectionR0182

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaRootDescentR0197
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192 ArithmeticThetaMetaplecticTestsR0196
namespace FPQCRootMorphismsR0197
open P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective.AlgebraicGeometry.Scheme.Modules.HomDescFF

theorem morphisms_bijective
    {Y Y' : Scheme.{0}} (q : Y' ⟶ Y) [QuasiCompact q] [Flat q] [Surjective q]
    (L₁ L₂ : Y.Modules) (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂) :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).map : (L₁ ⟶ L₂) → _) := by
  choose U₁ hU₁ e₁ using h₁.exists_trivialization
  choose U₂ hU₂ e₂ using h₂.exists_trivialization
  let W : Y → Y.Opens := fun y => U₁ y ⊓ U₂ y
  have hW : ∀ y : Y, ∃ i, y ∈ W i := fun y => ⟨y, hU₁ y, hU₂ y⟩
  have eW₁ : ∀ y, Nonempty ((Scheme.Modules.pullback (W y).ι).obj L₁ ≅
      SheafOfModules.unit (W y : Scheme.{0}).ringCatSheaf) := fun y =>
    ⟨trivOfFac (U₁ y).ι (W y).ι (Y.homOfLE inf_le_left) (Y.homOfLE_ι _) (e₁ y).some⟩
  have eW₂ : ∀ y, Nonempty ((Scheme.Modules.pullback (W y).ι).obj L₂ ≅
      SheafOfModules.unit (W y : Scheme.{0}).ringCatSheaf) := fun y =>
    ⟨trivOfFac (U₂ y).ι (W y).ι (Y.homOfLE inf_le_right) (Y.homOfLE_ι _) (e₂ y).some⟩
  rw [Pseudofunctor.bijective_toDescentData_map_iff, Presieve.isSheafFor_iff_generate]
  refine Presieve.isSheafFor_trans _
    (Sieve.generate (Presieve.ofArrows (fun y => Over.mk (W y).ι)
      (fun y => Over.homMk (U := Over.mk (W y).ι) (V := Over.mk (𝟙 Y)) (W y).ι))) _
    ?_ ?_ ?_
  · have hcov : ∀ y : Y, ∃ i, y ∈ Set.range ((W i).ι).base := fun y =>
      ⟨y, by simpa using (show y ∈ W y from ⟨hU₁ y, hU₂ y⟩)⟩
    have hZ := AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
      (fun y => (W y).ι) hcov L₁ L₂
    rw [Pseudofunctor.bijective_toDescentData_map_iff, Presieve.isSheafFor_iff_generate] at hZ
    exact hZ
  · intro Z f _
    exact isSeparatedFor_pullback_cover L₁ L₂ W hW Z f
  · rintro Z f ⟨Y₃, a, f', ⟨y⟩, rfl⟩
    have ha : a.left ≫ (W y).ι = Z.hom := Over.w a
    exact isSheafFor_pullback_of_trivial q L₁ L₂ Z _
      (trivOfFac (W y).ι Z.hom a.left ha (eW₁ y).some)
      (trivOfFac (W y).ι Z.hom a.left ha (eW₂ y).some)


open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182
open ArithmeticThetaMetaplecticTestsR0196.RootTestPullbackCoherenceR0196

lemma pullback_map_injective {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (M N : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) :
    Function.Injective ((Scheme.Modules.pullback q).map : (M ⟶ N) → _) := by
  intro a b hab
  apply (morphisms_bijective q M N hM hN).1
  apply CategoryTheory.Pseudofunctor.DescentData.hom_ext
  intro i
  exact hab

lemma root_iso_descent {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q]
    (W : B.Modules) (hW : Scheme.Modules.IsInvertible W) :
    RootIsoDescent W (fun _ : Unit => q) := by
  intro J K e he
  let F := descent (fun _ : Unit => q)
  obtain ⟨a, ha⟩ := (morphisms_bijective q J.line K.line J.invertible K.invertible).2 e.hom
  obtain ⟨b, hb⟩ := (morphisms_bijective q K.line J.line K.invertible J.invertible).2 e.inv
  have hab : a ≫ b = 𝟙 J.line := by
    apply (morphisms_bijective q J.line J.line J.invertible J.invertible).1
    change F.map (a ≫ b) = F.map (𝟙 _)
    rw [F.map_comp, F.map_id, ha, hb, e.hom_inv_id]
  have hba : b ≫ a = 𝟙 K.line := by
    apply (morphisms_bijective q K.line K.line K.invertible K.invertible).1
    change F.map (b ≫ a) = F.map (𝟙 _)
    rw [F.map_comp, F.map_id, hb, ha, e.inv_hom_id]
  let z : J.line ≅ K.line := ⟨a, b, hab, hba⟩
  have hs : tensorPowerMap z.hom 2 ≫ K.square.hom = J.square.hom := by
    apply pullback_map_injective q _ _ (tensorPower_invertible J.line J.invertible 2) hW
    have ha' : (Scheme.Modules.pullback q).map a = e.hom.hom () :=
      congrArg (fun f => f.hom ()) ha
    have hh := he ()
    rw [← ha'] at hh
    change tensorPowerMap ((Scheme.Modules.pullback q).map a) 2 ≫
      (pullback_tensorPower_iso Y B q K.line 2).inv ≫
        (Scheme.Modules.pullback q).map K.square.hom =
      (pullback_tensorPower_iso Y B q J.line 2).inv ≫
        (Scheme.Modules.pullback q).map J.square.hom at hh
    rw [← Category.assoc, power_natural_inv q J.invertible a 2,
      Category.assoc, ← Functor.map_comp] at hh
    exact (cancel_epi (pullback_tensorPower_iso Y B q J.line 2).inv).1 hh
  refine ⟨⟨z, hs⟩, ?_, ?_⟩
  · apply Iso.ext
    exact ha
  · intro w hw
    apply Subtype.ext
    apply Iso.ext
    apply (morphisms_bijective q J.line K.line J.invertible K.invertible).1
    exact (congrArg Iso.hom hw).trans ha.symm

lemma weight_section_descent {B Y : Scheme.{0}} (q : Y ⟶ B)
    [QuasiCompact q] [Flat q] [Surjective q] (W : B.Modules) :
    WeightSectionDescent W (fun _ : Unit => q) := by
  intro J n t
  have h := morphisms_bijective q (SheafOfModules.unit B.ringCatSheaf)
    (tensorPower B J.line n) (Scheme.Modules.isInvertible_unit B)
    (tensorPower_invertible J.line J.invertible n)
  obtain ⟨s, hs⟩ := h.2 t
  exact ⟨s, hs, fun s' hs' => h.1 (hs'.trans hs.symm)⟩

end FPQCRootMorphismsR0197

/-- Full faithfulness of fpqc descent for invertible modules, specified squares,
and actual sections of every nonnegative tensor power. -/
theorem fpqc_root_morphisms
    (B Y : Scheme.{0}) (q : Y ⟶ B)
    (hq : QuasiCompact q) (hf : Flat q) (hs : Surjective q)
    (W : B.Modules) (hW : Scheme.Modules.IsInvertible W) :
    (∀ (M N : B.Modules), Scheme.Modules.IsInvertible M →
      Scheme.Modules.IsInvertible N →
      Function.Bijective ((descent (fun _ : Unit => q)).map : (M ⟶ N) →
        ((descent (fun _ : Unit => q)).obj M ⟶ (descent (fun _ : Unit => q)).obj N))) ∧
    RootIsoDescent W (fun _ : Unit => q) ∧ WeightSectionDescent W (fun _ : Unit => q) := by
  let := hq
  let := hf
  let := hs
  exact ⟨FPQCRootMorphismsR0197.morphisms_bijective q,
    FPQCRootMorphismsR0197.root_iso_descent q W hW,
    FPQCRootMorphismsR0197.weight_section_descent q W⟩

#print axioms fpqc_root_morphisms
end ArithmeticThetaRootDescentR0197
