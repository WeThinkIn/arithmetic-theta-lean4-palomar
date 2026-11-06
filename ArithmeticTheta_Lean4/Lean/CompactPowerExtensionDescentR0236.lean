import ArithmeticSectionsDefinitionsR0236
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace ArithmeticThetaArithmeticSectionsR0236.CompactPowerExtensionDescent
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaBoundaryHodgeR0182
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182

variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
  {ι : k →+* l} {L : ℕ} {D : LevelData k L} {E : LevelData l L}
  {X : Compactification k L D} {Y : Compactification l L E}

lemma comparison_square (C : Comparison k L ι D E X Y)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (ha : ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap
      C.compactMap C.extendsOpen C.hodgeMap H J a) :
    composeComparison C.compactMap Y.inclusion (Y.inclusion ≫ C.compactMap) rfl
      H.line J.line (openHodge l L E) a J.onOpen =
    composeComparison X.inclusion C.openMap (Y.inclusion ≫ C.compactMap)
      C.extendsOpen.2 H.line (openHodge k L D) (openHodge l L E) H.onOpen C.hodgeMap := by
  apply Iso.ext
  simp only [composeComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    pullbackEqIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  change (Scheme.Modules.pullbackComp Y.inclusion C.compactMap).inv.app H.line ≫
    ((Scheme.Modules.pullback Y.inclusion).map a.hom ≫ J.onOpen.hom) = _
  rw [ha]
  simp only [Iso.app_hom, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

lemma restrict_transport (C : Comparison k L ι D E X Y)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (ha : ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap
      C.compactMap C.extendsOpen C.hodgeMap H J a)
    (n : ℕ) (s : Γ(tensorPower X.space H.line n, ⊤)) :
    restrictPower l L J n (powerTransport C.compactMap H.line J.line a n s) =
      powerTransport C.openMap _ _ C.hodgeMap n (restrictPower k L H n s) := by
  change transportSection Y.inclusion _ _ _ (transportSection C.compactMap _ _ _ s) =
    transportSection C.openMap _ _ _ (transportSection X.inclusion _ _ _ s)
  rw [← transportSection_comp, ← tensorComparison_comp _ _ _ _ _ H.invertible,
    comparison_square C H J a ha,
    tensorComparison_comp_eq _ _ _ _ _ _ _ H.invertible, transportSection_comp_eq]
  rfl

lemma upstairs_extension_unique (C : Comparison k L ι D E X Y)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (ha : ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap
      C.compactMap C.extendsOpen C.hodgeMap H J a)
    (n : ℕ) (u : Γ(openPower k L D n, ⊤))
    (s : Γ(tensorPower X.space H.line n, ⊤)) (hs : restrictPower k L H n s = u)
    (t : Γ(tensorPower Y.space J.line n, ⊤))
    (ht : restrictPower l L J n t = powerTransport C.openMap _ _ C.hodgeMap n u) :
    powerTransport C.compactMap H.line J.line a n s = t := by
  apply restrictPower_injective l L J n
  rw [restrict_transport C H J a ha, hs, ht]

/-- The actual coefficient map is Cartesian both on the compact curve and
on its specified open subscheme. -/
lemma coefficient_cartesian (C : Comparison k L ι D E X Y)
    (hL : 3 ≤ L) (heven : Even L) :
    CategoryTheory.IsPullback C.compactMap Y.projection X.projection
      (ArithmeticThetaLevelConstantsR0234.constants ι) ∧
    CategoryTheory.IsPullback Y.inclusion C.openMap C.compactMap X.inclusion := by
  obtain ⟨ho, _⟩ := ArithmeticThetaLevelConstantsR0234.open_constant_cartesian
    k l ι L hL heven D E C.openMap C.classifies
  obtain ⟨F, hF, _⟩ := ArithmeticThetaLevelConstantsR0234.compact_constant_comparison
    k l ι L hL heven D E X Y C.openMap ho
  have heq : C.compactMap = F :=
    ArithmeticThetaLevelConstantsR0234.CompactComparison.extension_unique
      ι D E X Y C.openMap C.compactMap F C.extendsOpen hF.1
  rw [heq]
  exact hF.2

open scoped TensorProduct

/-- A vector lies in a linear-map image if its scalar extension does. This
uses a linear functional on the coefficient field taking 1 to 1; no finite
extension or finite-dimensional source module is required. -/
lemma linear_image_descends {K F V W : Type} [Field K] [Field F] [Algebra K F]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (r : V →ₗ[K] W) (u : W)
    (h : ∃ z : F ⊗[K] V, r.lTensor F z = (1 : F) ⊗ₜ[K] u) :
    ∃ v : V, r v = u := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : F) ≠ 0)
  let evV : F ⊗[K] V →ₗ[K] V :=
    (TensorProduct.lid K V).toLinearMap.comp (TensorProduct.map φ LinearMap.id)
  let evW : F ⊗[K] W →ₗ[K] W :=
    (TensorProduct.lid K W).toLinearMap.comp (TensorProduct.map φ LinearMap.id)
  have natural : ∀ z : F ⊗[K] V, r (evV z) = evW (r.lTensor F z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c v => simp [evV, evW]
    | add z w hz hw => simp only [map_add, hz, hw]
  obtain ⟨z, hz⟩ := h
  refine ⟨evV z, ?_⟩
  rw [natural, hz]
  simp [evW, hφ]

/-- The scalar action on sections is induced by the specified structural map. -/
abbrev sectionsModule {K : Type} [CommRing K] {S : Scheme.{0}}
    (p : S ⟶ Spec (CommRingCat.of K)) (M : S.Modules) : Module K Γ(M, ⊤) :=
  Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom

lemma scalar_natural {K : Type} [CommRing K] {S T : Scheme.{0}}
    (p : S ⟶ Spec (CommRingCat.of K)) (q : T ⟶ Spec (CommRingCat.of K))
    (f : T ⟶ S) (hf : f ≫ p = q) (c : K) :
    f.appTop (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) =
      q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) := by
  have hh := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hf)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hh

/-- Pullback and an actual line comparison are linear for their structural
field actions whenever the morphism is over that field. -/
def transportLinear {K : Type} [CommRing K] {S T : Scheme.{0}}
    (p : S ⟶ Spec (CommRingCat.of K)) (q : T ⟶ Spec (CommRingCat.of K))
    (f : T ⟶ S) (hf : f ≫ p = q) (M : S.Modules) (N : T.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) :
    letI := sectionsModule p M
    letI := sectionsModule q N
    Γ(M, ⊤) →ₗ[K] Γ(N, ⊤) := by
  letI := sectionsModule p M
  letI := sectionsModule q N
  refine { toFun := transportSection f M N e, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    simp only [transportSection, Scheme.Modules.pullbackLocalSection_add,
      ArithmeticThetaRelativeDiscriminantR0171.res, map_add]
  · intro c x
    change transportSection f M N e
      (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) • x) =
      q.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) • transportSection f M N e x
    rw [transportSection_smul]
    congr 1
    simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using scalar_natural p q f hf c

def sectionsIso {K : Type} [CommRing K] {S : Scheme.{0}}
    (p : S ⟶ Spec (CommRingCat.of K)) (M N : S.Modules) (e : M ≅ N) :
    letI := sectionsModule p M
    letI := sectionsModule p N
    Γ(M, ⊤) ≃ₗ[K] Γ(N, ⊤) := by
  letI := sectionsModule p M
  letI := sectionsModule p N
  let f : Γ(M, ⊤) →ₗ[K] Γ(N, ⊤) :=
    { toFun := e.hom.app ⊤
      map_add' := fun x y => map_add (e.hom.app ⊤).hom x y
      map_smul' := fun c x => Scheme.Modules.Hom.app_smul e.hom
        (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) x }
  exact LinearEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤))

/-- Flat base change for sections, with the chosen pullback comparison retained. -/
lemma sections_baseChange {K F : Type} [Field K] [Field F] [Algebra K F]
    {S T : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of K))
    [QuasiCompact p] [IsSeparated p]
    (q : T ⟶ Spec (CommRingCat.of F)) (f : T ⟶ S)
    (hf : CategoryTheory.IsPullback f q p (Spec.map (CommRingCat.ofHom (algebraMap K F))))
    (M : S.Modules) (hM : Scheme.Modules.IsInvertible M) (N : T.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ N) :
    letI := sectionsModule p M
    letI := sectionsModule q N
    ∃ β : F ⊗[K] Γ(M, ⊤) ≃ₗ[F] Γ(N, ⊤),
      ∀ s : Γ(M, ⊤), β ((1 : F) ⊗ₜ[K] s) = transportSection f M N e s := by
  letI : Algebra K Γ(S, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom.toAlgebra
  letI : Algebra F Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ q.appTop).hom.toAlgebra
  letI := sectionsModule p M
  letI := sectionsModule q ((Scheme.Modules.pullback f).obj M)
  letI := sectionsModule q N
  obtain ⟨β, hβ⟩ := Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    F p q f hf M hM
  refine ⟨β.trans (sectionsIso q _ N e), fun s => ?_⟩
  change (e.hom.app ⊤) (β (1 ⊗ₜ[K] s)) = _
  rw [hβ]
  simp only [transportSection, ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.res_self]
  rfl

lemma linear_square_descends {K F V W V' W' : Type}
    [Field K] [Field F] [Algebra K F]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']
    (r : V →ₗ[K] W) (r' : V' →ₗ[F] W')
    (β : F ⊗[K] V ≃ₗ[F] V') (γ : F ⊗[K] W ≃ₗ[F] W')
    (hc : ∀ v, r' (β ((1 : F) ⊗ₜ[K] v)) = γ ((1 : F) ⊗ₜ[K] r v))
    (u : W) (ht : ∃ t, r' t = γ ((1 : F) ⊗ₜ[K] u)) : ∃ v, r v = u := by
  apply linear_image_descends (F := F) r u
  have hn : ∀ z : F ⊗[K] V, r' (β z) = γ (r.lTensor F z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c v =>
      have hz : c ⊗ₜ[K] v = c • ((1 : F) ⊗ₜ[K] v) := by simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, hz, map_smul, map_smul, hc]
      rw [← map_smul]
      congr 1
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z w hz hw => simp only [map_add, hz, hw]
  obtain ⟨t, ht⟩ := ht
  refine ⟨β.symm t, γ.injective ?_⟩
  rw [← hn, β.apply_symm_apply, ht]

lemma extension_exists (C : Comparison k L ι D E X Y)
    (hL : 3 ≤ L) (heven : Even L)
    (H : Extension k L D X) (J : Extension l L E Y)
    (a : (Scheme.Modules.pullback C.compactMap).obj H.line ≅ J.line)
    (ha : ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap
      C.compactMap C.extendsOpen C.hodgeMap H J a)
    (n : ℕ) (u : Γ(openPower k L D n, ⊤))
    (ht : ∃ t : Γ(tensorPower Y.space J.line n, ⊤),
      restrictPower l L J n t = powerTransport C.openMap _ _ C.hodgeMap n u) :
    ∃ s : Γ(tensorPower X.space H.line n, ⊤), restrictPower k L H n s = u := by
  letI : Algebra k l := ι.toAlgebra
  letI := X.proper
  letI := Y.proper
  letI := X.openImmersion
  letI := Y.openImmersion
  letI := compact_noetherian k L D X
  letI := compact_noetherian l L E Y
  letI : QuasiCompact (openStructure k L D) := by rw [← X.over_eq]; infer_instance
  letI : IsSeparated (openStructure k L D) := by rw [← X.over_eq]; infer_instance
  letI := sectionsModule X.projection (tensorPower X.space H.line n)
  letI := sectionsModule Y.projection (tensorPower Y.space J.line n)
  letI := sectionsModule (openStructure k L D) (openPower k L D n)
  letI := sectionsModule (openStructure l L E) (openPower l L E n)
  obtain ⟨hc, _⟩ := coefficient_cartesian C hL heven
  obtain ⟨ho, _⟩ := ArithmeticThetaLevelConstantsR0234.open_constant_cartesian
    k l ι L hL heven D E C.openMap C.classifies
  obtain ⟨β, hβ⟩ := sections_baseChange X.projection Y.projection C.compactMap hc
    (tensorPower X.space H.line n) (tensorPower_invertible H.line H.invertible n)
    (tensorPower Y.space J.line n) (tensorComparison C.compactMap H.line J.line a n)
  obtain ⟨γ, hγ⟩ := sections_baseChange (openStructure k L D) (openStructure l L E)
    C.openMap ho (openPower k L D n)
    (tensorPower_invertible (openHodge k L D) (openHodge_invertible k L D) n)
    (openPower l L E n) (tensorComparison C.openMap _ _ C.hodgeMap n)
  let r := transportLinear X.projection (openStructure k L D) X.inclusion X.over_eq
    (tensorPower X.space H.line n) (openPower k L D n)
    (tensorComparison X.inclusion H.line (openHodge k L D) H.onOpen n)
  let r' := transportLinear Y.projection (openStructure l L E) Y.inclusion Y.over_eq
    (tensorPower Y.space J.line n) (openPower l L E n)
    (tensorComparison Y.inclusion J.line (openHodge l L E) J.onOpen n)
  apply linear_square_descends r r' β γ
  · intro s
    rw [hβ, hγ]
    exact restrict_transport C H J a ha n s
  · obtain ⟨t, ht⟩ := ht
    refine ⟨t, ?_⟩
    rw [hγ]
    exact ht

end ArithmeticThetaArithmeticSectionsR0236.CompactPowerExtensionDescent

namespace ArithmeticThetaArithmeticSectionsR0236
theorem compact_power_extension_descent :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀
      (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E :
      ArithmeticThetaLevelCompactificationR0179.LevelData l L) (X :
      ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y :
      ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (C :
      ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) (H :
      ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (J : ArithmeticThetaBoundaryHodgeR0182.Extension
      l L E Y) (a : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback C.compactMap).obj H.line)
      (J.line)), ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι C.openMap C.compactMap
      C.extendsOpen C.hodgeMap H J a → ∀ (n : ℕ) (u : (ArithmeticThetaBoundaryHodgeR0182.openPower k L D
      n).presheaf.obj (Opposite.op ⊤)), (∃ t : (ArithmeticThetaTensorPower.tensorPower Y.space J.line
      n).presheaf.obj (Opposite.op ⊤), ArithmeticThetaBoundaryHodgeR0182.restrictPower l L J n t =
      ArithmeticThetaArithmeticSectionsR0236.powerTransport C.openMap
      (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E) C.hodgeMap
      n (u)) → ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line n).presheaf.obj (Opposite.op
      ⊤), ArithmeticThetaBoundaryHodgeR0182.restrictPower k L H n s = u ∧ ∀ t :
      (ArithmeticThetaTensorPower.tensorPower Y.space J.line n).presheaf.obj (Opposite.op ⊤),
      ArithmeticThetaBoundaryHodgeR0182.restrictPower l L J n t =
      ArithmeticThetaArithmeticSectionsR0236.powerTransport C.openMap
      (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E) C.hodgeMap
      n (u) → ArithmeticThetaArithmeticSectionsR0236.powerTransport C.compactMap H.line J.line a n (s) = t := by
  intro k l _ _ _ _ ι L hL heven D E X Y C H J a ha n u ht
  obtain ⟨s, hs⟩ := CompactPowerExtensionDescent.extension_exists C hL heven H J a ha n u ht
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · intro t ht
    exact CompactPowerExtensionDescent.upstairs_extension_unique C H J a ha n u s hs t ht
  · intro z hz
    exact ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.restrictPower_injective
      k L H n (hz.1.trans hs.symm)

#print axioms compact_power_extension_descent
end ArithmeticThetaArithmeticSectionsR0236
