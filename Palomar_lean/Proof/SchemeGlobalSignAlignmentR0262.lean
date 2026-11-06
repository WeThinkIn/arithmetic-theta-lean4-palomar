module

public import SchemeNormalizationTransportR0262
public import SchemeSymmetricSignsR0259

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaNaturalityR0262
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259
namespace GlobalSignAlignmentProof
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

variable {S T : Scheme.{u}} (E : Family S) (F : Family T)
  (b : T ⟶ S) (f : F.curve ⟶ E.curve)
  (hc : IsPullback f F.p E.p b) (hz : F.zero ≫ f = b ≫ E.zero)

lemma transport_sign (m : ℕ) (g : E.curve ⟶ E.curve) (g' : F.curve ⟶ F.curve)
    (h : g' ≫ f = f ≫ g) (α : Lift E m g) (ε : Bool) :
    transportedLift E F b f hc hz m g g' h (scaled E m (signUnit S ε) α) =
      scaled F m (signUnit T ε) (transportedLift E F b f hc hz m g g' h α) := by
  have hs : Units.map f.appTop.hom.toMonoidHom (scalar E (signUnit S ε)) =
      scalar F (signUnit T ε) := by
    apply Units.ext
    cases ε <;> simp [scalar, signUnit]
  have hn : smulIso (scalar F (signUnit T ε))
      ((Scheme.Modules.pullback f).obj (thetaLine E m)) ≪≫
      thetaComparison E F b f hc hz m =
      thetaComparison E F b f hc hz m ≪≫ smulIso (scalar F (signUnit T ε)) (thetaLine F m) := by
    apply Iso.ext
    exact smulHom_comp _ _
  simp only [transportedLift, scaled, Functor.mapIso_trans,
    pullback_mapIso_smulIso, hs, Iso.trans_assoc, hn]

lemma sign_injective (k : Type u) [Field k] [CharZero k]
    (τ : T ⟶ Base k) (hT : Nonempty T) : Function.Injective (signUnit T) := by
  letI : Nonempty T := hT
  letI : Nontrivial Γ(T, ⊤) := (T.presheaf.germ ⊤ hT.some trivial).hom.domain_nontrivial
  let ρ : ℚ →+* Γ(T, ⊤) := τ.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp (algebraMap ℚ k))
  letI : CharZero Γ(T, ⊤) := charZero_of_injective_ringHom ρ.injective
  intro a d h
  have hv := congrArg Units.val h
  cases a <;> cases d <;> simp_all [signUnit]

lemma single_sign (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ Base k) (m : ℕ) (hm : Multiplicative E F b f)
    (P : point E) (Q : point F) (hq : Q.val ≫ f = b ≫ P.val)
    (ι : Lift E m (inverse E)) (ι' : Lift F m (inverse F))
    (hi : NormalizedInversion E m ι) (hi' : NormalizedInversion F m ι')
    (α : Lift E m (translation E P)) (α' : Lift F m (translation F Q))
    (ha : Symmetric E m P ι α) (ha' : Symmetric F m Q ι' α')
    (hT : _root_.IsPreconnected (Set.univ : Set T)) (hne : Nonempty T) :
    ∃! ε : Bool, LiftCorresponds E F b f hc hz m (translation E P) (translation F Q)
      (scaled E m (signUnit S ε) α) α' := by
  let h := NormalizationTransportProof.translation_commutes E F b f hc hm P Q hq
  let γ := transportedLift E F b f hc hz m (translation E P) (translation F Q) h α
  have hγ : LiftCorresponds E F b f hc hz m (translation E P) (translation F Q) α γ := ⟨h, rfl⟩
  have hs := (scheme_normalization_transport k S σ E T F b f hc hz m hm).2
    P Q hq ι ι' hi hi' α γ
  have hsym := (hs.1 hγ).2 ha
  obtain ⟨c, hc', _⟩ := scheme_symmetric_signs k T (b ≫ σ) F m Q ι' hi' γ α' hsym ha'
  obtain ⟨ε, he⟩ : ∃ ε : Bool, c = signUnit T ε := by
    rcases hc'.2.2 hT with h1 | hn
    · exact ⟨false, h1⟩
    · exact ⟨true, hn⟩
  have halign : α' = scaled F m (signUnit T ε) γ := by rw [← he]; exact hc'.2.1
  refine ⟨ε, ⟨h, halign.trans (transport_sign E F b f hc hz m _ _ h α ε).symm⟩, ?_⟩
  intro δ hd
  obtain ⟨hdmap, hd⟩ := hd
  rw [transport_sign] at hd
  have heq := SchemeSymmetricSigns.scaled_injective F m γ (hd.symm.trans halign)
  exact sign_injective k (b ≫ σ) hne heq

end GlobalSignAlignmentProof

/-- The unique pair of constant signs on the original base aligning the prescribed test lifts. -/
theorem scheme_global_sign_alignment :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S), 
    ∀ (T : AlgebraicGeometry.Scheme.{u})
      (F : ArithmeticThetaLocalWeierstrassR0203.Family T)
      (b : Quiver.Hom T S)
      (f : Quiver.Hom F.curve E.curve)
      (hc : CategoryTheory.IsPullback f F.p E.p b)
      (hz : CategoryTheory.CategoryStruct.comp F.zero f = CategoryTheory.CategoryStruct.comp b E.zero), 
    ∀ (m : ℕ), 0 < m →
    Even m →
    ArithmeticThetaSchemeLevelR0204.Multiplicative E F b f →
    
    ∀ (M : ArithmeticThetaSchemeLevelR0204.FullLevel E (2*m))
      (N : ArithmeticThetaSchemeLevelR0204.FullLevel F (2*m)), CategoryTheory.CategoryStruct.comp N.x.val f = CategoryTheory.CategoryStruct.comp b M.x.val →
    CategoryTheory.CategoryStruct.comp N.y.val f = CategoryTheory.CategoryStruct.comp b M.y.val →
    
    ∀ (ι : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.inverse E))
      (ι' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m (ArithmeticThetaSchemeThetaMarkingR0259.inverse F)), ArithmeticThetaSchemeThetaMarkingR0259.NormalizedInversion E m ι →
    ArithmeticThetaSchemeThetaMarkingR0259.NormalizedInversion F m ι' →
    
    ∀ (α : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.x))
      (β : ArithmeticThetaSchemeThetaMarkingR0259.Lift E m (ArithmeticThetaSchemeThetaMarkingR0259.translation E M.y))
      (α' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.x))
      (β' : ArithmeticThetaSchemeThetaMarkingR0259.Lift F m (ArithmeticThetaSchemeThetaMarkingR0259.translation F N.y)), ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.x ι α →
    ArithmeticThetaSchemeThetaMarkingR0259.Symmetric E m M.y ι β →
    ArithmeticThetaSchemeThetaMarkingR0259.Symmetric F m N.x ι' α' →
    ArithmeticThetaSchemeThetaMarkingR0259.Symmetric F m N.y ι' β' →
    _root_.IsPreconnected (Set.univ : Set T) →
    Nonempty T →
    ArithmeticThetaSchemeThetaNaturalityR0262.SignAlignment E F b f hc hz m M N α β α' β' := by
  intro k _ _ S σ E T F b f hc hz m _ _ hm M N hx hy ι ι' hi hi' α β α' β'
    hα hβ hα' hβ' hT hne
  obtain ⟨ε, hε, uε⟩ := GlobalSignAlignmentProof.single_sign E F b f hc hz
    k σ m hm M.x N.x hx ι ι' hi hi' α α' hα hα' hT hne
  obtain ⟨δ, hδ, uδ⟩ := GlobalSignAlignmentProof.single_sign E F b f hc hz
    k σ m hm M.y N.y hy ι ι' hi hi' β β' hβ hβ' hT hne
  refine ⟨(ε, δ), ⟨hε, hδ⟩, ?_⟩
  intro z hz
  exact Prod.ext (uε z.1 hz.1) (uδ z.2 hz.2)

#print axioms scheme_global_sign_alignment
end ArithmeticThetaSchemeThetaNaturalityR0262
