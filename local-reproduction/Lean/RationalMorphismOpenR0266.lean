import GlobalProjectiveRatioDefinitionsR0266

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInvariantRatiosR0265
open InvariantRatioFieldDescent
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
namespace RationalMorphismOpen

lemma regular_scalar {X : Scheme.{u}} {M N : X.Modules}
    (hN : Scheme.Modules.IsInvertible N) (d v : M ⟶ N) [IsIso d] :
    ∃ a : Γ(X, ⊤), v = d ≫ smulHom a N := by
  obtain ⟨a, ha, _⟩ := hN.existsUnique_app_eq_smul (inv d ≫ v)
  have hh : inv d ≫ v = smulHom a N := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    exact ha U x
  exact ⟨a, by rw [← hh, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]⟩

lemma generic_ratios_unique {Z S : Scheme.{u}} [IsIntegral Z]
    (g : Spec (CommRingCat.of Z.functionField) ⟶ S)
    (M N : S.Modules) (d : M ⟶ N) (n : ℕ) (v : Fin n → (M ⟶ N))
    (hN : Scheme.Modules.IsInvertible N)
    (hd : IsIso ((Scheme.Modules.pullback g).map d)) :
    ∃! r : Fin n → Z.functionField, GenericRatios g M N d v r := by
  let P := Scheme.Modules.pullback g
  letI := hd
  have hex (i : Fin n) : ∃ a : Z.functionField,
      P.map (v i) = P.map d ≫ scalarEnd (P.obj N) a := by
    obtain ⟨a, ha⟩ := scalar_exists (hN.pullback g) (inv (P.map d) ≫ P.map (v i))
    exact ⟨a, by rw [← ha, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]⟩
  choose r hr using hex
  refine ⟨r, ⟨hd, hr⟩, ?_⟩
  intro r' hr'
  funext i
  apply scalar_injective (hN.pullback g)
  apply (cancel_epi (P.map d)).mp
  exact (hr'.2 i).symm.trans (hr i)

lemma pullback_comp_iso {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    {M N : T.Modules} (d : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map d)) ↔
      IsIso ((Scheme.Modules.pullback (f ≫ g)).map d) :=
  NatIso.isIso_map_iff (Scheme.Modules.pullbackComp f g) d

lemma pullback_scalar_equation {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (d v : M ⟶ N) (a : Γ(Y, ⊤))
    (h : v = d ≫ smulHom a N) :
    (Scheme.Modules.pullback f).map v =
      (Scheme.Modules.pullback f).map d ≫
        smulHom (f.appTop a) ((Scheme.Modules.pullback f).obj N) := by
  rw [h, Functor.map_comp, pullback_map_smulHom]

lemma transport_scalar_equation {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) {M N : T.Modules} (d v : M ⟶ N)
    (a : Γ(X, ⊤))
    (h : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map v) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map d) ≫
        smulHom a ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))) :
    (Scheme.Modules.pullback (f ≫ g)).map v =
      (Scheme.Modules.pullback (f ≫ g)).map d ≫
        smulHom a ((Scheme.Modules.pullback (f ≫ g)).obj N) := by
  let e := Scheme.Modules.pullbackComp f g
  apply (cancel_epi (e.hom.app M)).mp
  rw [← e.hom.naturality v, ← Category.assoc, ← e.hom.naturality d]
  dsimp only [Functor.comp_map]
  rw [h, Category.assoc, smulHom_comp, Category.assoc]

lemma trivialize_smaller {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ unitModule U.toScheme) :
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ unitModule V.toScheme) := by
  exact ⟨(Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)⟩

lemma common_trivialization {X : Scheme.{u}} {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      (Scheme.Modules.pullback U.ι).obj N) := by
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM.exists_trivialization x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN.exists_trivialization x
  obtain ⟨a⟩ := trivialize_smaller (show U ⊓ V ≤ U from inf_le_left) eM
  obtain ⟨b⟩ := trivialize_smaller (show U ⊓ V ≤ V from inf_le_right) eN
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨a ≪≫ b.symm⟩⟩

lemma basicOpen_scalar_iso {X : Scheme.{u}} (a : Γ(X, ⊤)) (M : X.Modules) :
    IsIso ((Scheme.Modules.pullback (X.basicOpen a).ι).map (smulHom a M)) := by
  rw [pullback_map_smulHom]
  have hu : IsUnit ((X.basicOpen a).ι.appTop a) := by
    have h : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
      X.toRingedSpace.isUnit_res_basicOpen a
    convert h.map (X.basicOpen a).topIso.inv.hom using 1
    change X.presheaf.map _ a = X.presheaf.map _ (X.presheaf.map _ a)
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨z, hz⟩ := hu
  rw [← hz]
  exact (smulIso z _).isIso_hom

lemma field_range_in_open {F : Type u} [Field F] {X : Scheme.{u}}
    (f : Spec (CommRingCat.of F) ⟶ X) (U : X.Opens)
    (hx : f (Classical.arbitrary (Spec (CommRingCat.of F))) ∈ U) :
    Set.range f ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change f x ∈ U
  rw [Subsingleton.elim x (Classical.arbitrary (Spec (CommRingCat.of F)))]
  exact hx

lemma open_iso_near_field {F : Type u} [Field F] {X : Scheme.{u}}
    (f : Spec (CommRingCat.of F) ⟶ X) {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (d : M ⟶ N) (hd : IsIso ((Scheme.Modules.pullback f).map d)) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j)
      (f' : Spec (CommRingCat.of F) ⟶ Y),
      f' ≫ j = f ∧ IsIso ((Scheme.Modules.pullback j).map d) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := common_trivialization hM hN
    (f (Classical.arbitrary (Spec (CommRingCat.of F))))
  let fU := IsOpenImmersion.lift U.ι f (field_range_in_open f U hxU)
  have hfU : fU ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  let P := Scheme.Modules.pullback U.ι
  obtain ⟨a, ha⟩ := regular_scalar (hN.pullback U.ι) e.hom (P.map d)
  have hdi : IsIso ((Scheme.Modules.pullback fU).map (P.map d)) := by
    apply (pullback_comp_iso fU U.ι d).mpr
    rwa [hfU]
  have hscalar : IsIso (smulHom (fU.appTop a) ((Scheme.Modules.pullback fU).obj (P.obj N))) := by
    have hh := pullback_scalar_equation fU e.hom (P.map d) a ha
    rw [hh] at hdi
    letI := hdi
    exact (isIso_comp_left_iff ((Scheme.Modules.pullback fU).map e.hom) _).mp hdi
  have hu : IsUnit (fU.appTop a) := by
    let b := (Scheme.ΓSpecIso (.of F)).hom (fU.appTop a)
    have hb : b ≠ 0 := by
      intro hz
      have heq : smulHom (fU.appTop a) ((Scheme.Modules.pullback fU).obj (P.obj N)) =
          scalarEnd ((Scheme.Modules.pullback fU).obj (P.obj N)) b := by
        simp [scalarEnd, b]
      have hzero := scalar_zero ((Scheme.Modules.pullback fU).obj (P.obj N))
      letI := hscalar
      apply iso_ne_zero ((hN.pullback U.ι).pullback fU)
        (smulHom (fU.appTop a) ((Scheme.Modules.pullback fU).obj (P.obj N)))
      rw [heq, hz, hzero]
    have hunit := (isUnit_iff_ne_zero.mpr hb).map (Scheme.ΓSpecIso (.of F)).inv.hom
    simpa [b] using hunit
  let W := U.toScheme.basicOpen a
  have hrange : Set.range fU ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hp : fU ⁻¹ᵁ W = ⊤ := by
      rw [Scheme.Hom.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    change x ∈ fU ⁻¹ᵁ W
    rw [hp]
    trivial
  let fW := IsOpenImmersion.lift W.ι fU hrange
  have hfW : fW ≫ W.ι = fU := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W.toScheme, W.ι ≫ U.ι, inferInstance, fW, ?_, ?_⟩
  · rw [← Category.assoc, hfW, hfU]
  · apply (pullback_comp_iso W.ι U.ι d).mp
    change IsIso ((Scheme.Modules.pullback W.ι).map (P.map d))
    rw [ha, Functor.map_comp]
    letI := basicOpen_scalar_iso a (P.obj N)
    infer_instance

lemma refine_iso {Z S : Scheme.{u}} [IsIntegral Z]
    (g : Spec (CommRingCat.of Z.functionField) ⟶ S) (C : GenericChart Z S g)
    {M N : S.Modules} (d : M ⟶ N)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hd : IsIso ((Scheme.Modules.pullback g).map d)) :
    ∃ C' : GenericChart Z S g, Refines g C C' ∧
      IsIso ((Scheme.Modules.pullback C'.map).map d) := by
  have hi : IsIso ((Scheme.Modules.pullback C.generic).map
      ((Scheme.Modules.pullback C.map).map d)) := by
    apply (pullback_comp_iso C.generic C.map d).mpr
    rwa [C.map_eq]
  obtain ⟨Y, j, hj, f, hf, hdj⟩ := open_iso_near_field C.generic
    (hM.pullback C.map) (hN.pullback C.map) ((Scheme.Modules.pullback C.map).map d) hi
  letI := hj
  let J := j ≫ C.domain.ι
  let e := J.isoOpensRange
  let j' := e.inv ≫ j
  have hj' : j' ≫ C.domain.ι = J.opensRange.ι := by
    exact J.isoOpensRange_inv_comp
  have hf' : (f ≫ e.hom) ≫ j' = C.generic := by
    simp only [j', Category.assoc, e.hom_inv_id_assoc, hf]
  let C' : GenericChart Z S g := {
    domain := J.opensRange
    nonempty := ⟨(f ≫ e.hom) (Classical.arbitrary (Spec (CommRingCat.of Z.functionField)))⟩
    map := j' ≫ C.map
    generic := f ≫ e.hom
    generic_eq := by rw [← hj', ← Category.assoc, hf', C.generic_eq]
    map_eq := by rw [← Category.assoc, hf', C.map_eq] }
  refine ⟨C', ⟨j', inferInstance, hj', rfl, hf'⟩, ?_⟩
  change IsIso ((Scheme.Modules.pullback (j' ≫ C.map)).map d)
  apply (pullback_comp_iso j' C.map d).mp
  change IsIso ((Scheme.Modules.pullback (e.inv ≫ j)).map
    ((Scheme.Modules.pullback C.map).map d))
  apply (pullback_comp_iso e.inv j _).mp
  letI := hdj
  infer_instance

lemma ratios_on_iso_chart {Z S : Scheme.{u}} [IsIntegral Z]
    (g : Spec (CommRingCat.of Z.functionField) ⟶ S) (C : GenericChart Z S g)
    (M N : S.Modules) (d : M ⟶ N) (n : ℕ) (v : Fin n → (M ⟶ N))
    (hN : Scheme.Modules.IsInvertible N)
    (hd : IsIso ((Scheme.Modules.pullback C.map).map d)) :
    ∃ r : Fin n → Z.functionField,
      GenericRatios g M N d v r ∧ RegularRatios g M N d v C r := by
  let P := Scheme.Modules.pullback C.map
  letI := hd
  have hex (i : Fin n) : ∃ a : Γ(C.domain.toScheme, ⊤),
      P.map (v i) = P.map d ≫ smulHom a (P.obj N) :=
    regular_scalar (hN.pullback C.map) (P.map d) (P.map (v i))
  choose a ha using hex
  let r : Fin n → Z.functionField := fun i =>
    (Scheme.ΓSpecIso (.of Z.functionField)).hom (C.generic.appTop (a i))
  refine ⟨r, ⟨?_, ?_⟩, hd, a, fun i => ⟨ha i, rfl⟩⟩
  · have hi := (pullback_comp_iso C.generic C.map d).mp
      (show IsIso ((Scheme.Modules.pullback C.generic).map (P.map d)) from inferInstance)
    rwa [C.map_eq] at hi
  · intro i
    have hh := transport_scalar_equation C.generic C.map d (v i)
      (C.generic.appTop (a i))
      (pullback_scalar_equation C.generic (P.map d) (P.map (v i)) (a i) (ha i))
    rw [C.map_eq] at hh
    simpa [r, scalarEnd] using hh

end RationalMorphismOpen

/-- The unique generic quotients extend regularly on an open refinement of
exactly the original chart, with the actual generic-field images. -/
theorem rational_morphism_open :
∀ (Z S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral Z] (g : Quiver.Hom (AlgebraicGeometry.Spec (CommRingCat.of Z.functionField)) S) (C : ArithmeticThetaGlobalProjectiveRatiosR0266.GenericChart Z S g) (M N : S.Modules) (d : Quiver.Hom M N) (n : ℕ) (v : Fin n → Quiver.Hom M N), AlgebraicGeometry.Scheme.Modules.IsInvertible M → AlgebraicGeometry.Scheme.Modules.IsInvertible N → CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.Modules.pullback g).map d) → ∃! r : Fin n → Z.functionField, ArithmeticThetaGlobalProjectiveRatiosR0266.GenericRatios g M N d v r ∧ ∃ C' : ArithmeticThetaGlobalProjectiveRatiosR0266.GenericChart Z S g, ArithmeticThetaGlobalProjectiveRatiosR0266.Refines g C C' ∧ ArithmeticThetaGlobalProjectiveRatiosR0266.RegularRatios g M N d v C' r := by
  intro Z S _ g C M N d n v hM hN hd
  obtain ⟨C', hC', hd'⟩ := RationalMorphismOpen.refine_iso g C d hM hN hd
  obtain ⟨r, hr, hreg⟩ := RationalMorphismOpen.ratios_on_iso_chart g C' M N d n v hN hd'
  obtain ⟨r₀, _, hu⟩ := RationalMorphismOpen.generic_ratios_unique g M N d n v hN hd
  exact ⟨r, ⟨hr, C', hC', hreg⟩, fun r' hr' => (hu r' hr'.1).trans (hu r hr).symm⟩

#print axioms rational_morphism_open
end ArithmeticThetaGlobalProjectiveRatiosR0266
