module

public import SchemeThetaMarkingDefinitionsR0259
public import RelativeSymmetricLiftSignsR0256

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeSymmetricSigns
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

variable {S : Scheme.{u}} (E : Family S)

lemma line_invertible (m : ℕ) : Scheme.Modules.IsInvertible (thetaLine E m) := by
  have h := ArithmeticThetaSchemeHodgeR0205.CartesianIdentityIdeal.zero_ideal_invertible E
  exact (h.pow m).isInvertible_module.dual.1.tensor_monoidalV2
    (((h.isInvertible_module.pullback E.zero).tensorPow m).pullback E.p)

lemma constants_bijective : Function.Bijective E.p.appTop :=
  ArithmeticThetaKatoCharacterizationR0254.GlobalUnitTwoThreeNormRigidity.structure_app_bijective E ⊤

lemma scalar_injective : Function.Injective (scalar E) := by
  intro c d h
  apply Units.ext
  exact (constants_bijective E).1 (congrArg Units.val h)

lemma scalar_surjective : Function.Surjective (scalar E) := by
  let e := RingEquiv.ofBijective E.p.appTop.hom (constants_bijective E)
  exact (Units.mapEquiv e.toMulEquiv).surjective

lemma scaled_injective (m : ℕ) {f : E.curve ⟶ E.curve} (α : Lift E m f) :
    Function.Injective (fun c => scaled E m c α) := by
  intro c d h
  apply scalar_injective E
  apply Units.ext
  apply smulHom_injective (line_invertible E m)
  exact (cancel_epi α.hom).mp (congrArg Iso.hom h)

lemma exists_scaled (m : ℕ) {f : E.curve ⟶ E.curve} (α β : Lift E m f) :
    ∃ c : Γ(S, ⊤)ˣ, β = scaled E m c α := by
  obtain ⟨s, hs⟩ := aut_scalar (line_invertible E m) (α.symm ≪≫ β)
  obtain ⟨c, hc⟩ := scalar_surjective E s
  refine ⟨c, ?_⟩
  simp [scaled, hc, hs]

lemma scalar_pullback (f : E.curve ⟶ E.curve) (hf : f ≫ E.p = E.p)
    (c : Γ(S, ⊤)ˣ) : f.appTop (scalar E c : Γ(E.curve, ⊤)) = (scalar E c : Γ(E.curve, ⊤)) := by
  have h := congrArg (fun g => g.appTop) hf
  change E.p.appTop ≫ f.appTop = E.p.appTop at h
  exact ConcreteCategory.congr_hom h (c : Γ(S, ⊤))

lemma square_constraint (m : ℕ) (f : E.curve ⟶ E.curve)
    (hf : f ≫ E.p = E.p) (φ : Lift E m f) (c : Γ(S, ⊤)ˣ)
    (h : (Scheme.Modules.pullback f).mapIso (scaled E m c φ) ≪≫ scaled E m c φ =
      (Scheme.Modules.pullback f).mapIso φ ≪≫ φ) : c ^ 2 = 1 := by
  have hh := congrArg Iso.hom h
  have hs := scalar_pullback E f hf c
  simp only [scaled, Functor.mapIso_trans, Iso.trans_hom, Functor.mapIso_hom,
    smulIso, pullback_map_smulHom] at hh
  rw [hs, Category.assoc, smulHom_comp_assoc] at hh
  have hx : smulHom (scalar E c : Γ(E.curve, ⊤)) (thetaLine E m) ≫
      smulHom (scalar E c : Γ(E.curve, ⊤)) (thetaLine E m) = 𝟙 _ := by
    apply (cancel_epi φ.hom).mp
    apply (cancel_epi ((Scheme.Modules.pullback f).map φ.hom)).mp
    simpa only [Category.assoc, Category.comp_id] using hh
  rw [← smulHom_mul, ← smulHom_one (thetaLine E m)] at hx
  have hv := smulHom_injective (line_invertible E m) hx
  apply scalar_injective E
  apply Units.ext
  simpa [scalar, pow_two, map_mul] using hv

lemma symmetric_scalar_square (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) (c : Γ(S, ⊤)ˣ)
    (hα : Symmetric E m P ι α) (hβ : Symmetric E m P ι (scaled E m c α)) : c ^ 2 = 1 := by
  obtain ⟨ha, hα⟩ := hα
  obtain ⟨hb, hβ⟩ := hβ
  have hr : reflectionLift E m P ι (scaled E m c α) =
      scaled E m c (reflectionLift E m P ι α) := by
    simp [reflectionLift, compose, scaled, Iso.trans_assoc]
  rw [hr] at hβ
  refine square_constraint E m (reflection E P) ?_ (reflectionLift E m P ι α) c ?_
  · change (translation E P ≫ inverse E) ≫ E.p = E.p
    have hi : inverse E ≫ E.p = E.p := (E.law.inv E.p ⟨𝟙 E.curve, Category.id_comp E.p⟩).property
    rw [Category.assoc, hi]
    exact (E.law.mul E.p ⟨𝟙 E.curve, Category.id_comp E.p⟩
      ⟨E.p ≫ (multiple E P 2).val, by rw [Category.assoc, (multiple E P 2).property, Category.comp_id]⟩).property
  · exact hβ.trans hα.symm

/-- Local inverses glue, with no quasi-compactness or reducedness assumption. -/
lemma unit_of_basicOpen_top (X : Scheme.{u}) (a : Γ(X, ⊤))
    (ha : X.basicOpen a = ⊤) : IsUnit a := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
  intro x hx
  apply (X.mem_basicOpen a x hx).mp
  rw [ha]
  trivial

/-- A clopen of the spectrum of global sections pulls back to a clopen of X.
Local invertibility detects whether its defining idempotent is zero or one. -/
lemma global_idempotent (X : Scheme.{u}) (hX : _root_.IsPreconnected (Set.univ : Set X))
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  letI : PreconnectedSpace X := ⟨hX⟩
  have hc : IsClopen (X.basicOpen e : Set X) := by
    have ht : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, ⊤))) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
    have hp := ht.preimage X.toSpecΓ.continuous
    simpa only [← Scheme.toSpecΓ_preimage_basicOpen, Scheme.Hom.coe_preimage] using hp
  rcases _root_.isClopen_iff.mp hc with h0 | h1
  · left
    have h0' : X.basicOpen e = ⊥ := SetLike.coe_injective h0
    have ht : X.basicOpen (1 - e) = ⊤ := by
      apply top_le_iff.mp
      calc
        ⊤ = X.basicOpen (e + (1 - e)) := by simp
        _ ≤ X.basicOpen e ⊔ X.basicOpen (1 - e) := X.basicOpen_add_le _ _
        _ = X.basicOpen (1 - e) := by rw [h0', bot_sup_eq]
    have hone := (IsIdempotentElem.iff_eq_one_of_isUnit (unit_of_basicOpen_top X _ ht)).mp he.one_sub
    exact sub_eq_self.mp hone
  · right
    have h1' : X.basicOpen e = ⊤ := SetLike.coe_injective h1
    exact (IsIdempotentElem.iff_eq_one_of_isUnit (unit_of_basicOpen_top X _ h1')).mp he

lemma global_spectrum_preconnected (X : Scheme.{u})
    (hX : _root_.IsPreconnected (Set.univ : Set X)) :
    _root_.IsPreconnected (Set.univ : Set (PrimeSpectrum Γ(X, ⊤))) := by
  apply preconnectedSpace_iff_univ.mp
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases global_idempotent X hX e he with rfl | rfl
  · left; simp
  · right; simp

lemma connected_sign (k : Type u) [Field k] [CharZero k]
    (σ : S ⟶ Base k) (c : Γ(S, ⊤)ˣ) (hc : c ^ 2 = 1)
    (hS : _root_.IsPreconnected (Set.univ : Set S)) : c = 1 ∨ c = -1 := by
  let ρ : ℚ →+* Γ(S, ⊤) := σ.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp (algebraMap ℚ k))
  letI : Algebra ℚ Γ(S, ⊤) := ρ.toAlgebra
  exact ArithmeticThetaRelativeThetaRelationsR0256.RelativeSymmetricLiftSigns.connected_sign
    c hc (global_spectrum_preconnected S hS)

end SchemeSymmetricSigns
open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203

theorem scheme_symmetric_signs :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k))
      (E : ArithmeticThetaLocalWeierstrassR0203.Family S),
    ∀ (m : ℕ) (P : point E), ∀ (ι : Lift E m (inverse E)),
    NormalizedInversion E m ι → ∀ (α β : Lift E m (translation E P)),
    Symmetric E m P ι α → Symmetric E m P ι β →
    ∃! c : (S.presheaf.obj (Opposite.op ⊤))ˣ,
      c^2 = 1 ∧ β = scaled E m c α ∧
        (_root_.IsPreconnected (Set.univ : Set S) → c = 1 ∨ c = -1) := by
  intro k _ _ S σ E m P ι _ α β hα hβ
  obtain ⟨c, hc⟩ := SchemeSymmetricSigns.exists_scaled E m α β
  have hc2 := SchemeSymmetricSigns.symmetric_scalar_square E m P ι α c hα (hc ▸ hβ)
  refine ⟨c, ⟨hc2, hc, SchemeSymmetricSigns.connected_sign k σ c hc2⟩, ?_⟩
  intro d hd
  exact SchemeSymmetricSigns.scaled_injective E m α (hd.2.1.symm.trans hc)

#print axioms scheme_symmetric_signs
end ArithmeticThetaSchemeThetaMarkingR0259
