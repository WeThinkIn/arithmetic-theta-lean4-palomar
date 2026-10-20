module

public import RelativeThetaRelationsDefinitionsR0256

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaRelationsR0256
namespace RelativeSymmetricLiftSigns
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaLiftsR0255.RelativeMidpointSymmetricThetaLift
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
variable {R : Type u} [CommRing R] (E : EllipticFamily R)

lemma scalar_injective : Function.Injective (scalar E) := by
  intro c d h
  apply Units.ext
  exact (RelativeNormalizedThetaInversion.constants_bijective E).1
    (congrArg Units.val h)

lemma scalar_surjective : Function.Surjective (scalar E) := by
  let e := RingEquiv.ofBijective
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ E.projection.appTop).hom)
    (RelativeNormalizedThetaInversion.constants_bijective E)
  exact (Units.mapEquiv e.toMulEquiv).surjective

lemma scaled_injective (m : ℕ) {f : E.curve ⟶ E.curve} (α : Lift E m f) :
    Function.Injective (fun c => scaled E m c α) := by
  intro c d h
  apply scalar_injective E
  apply Units.ext
  apply smulHom_injective (RelativeNormalizedThetaInversion.line_invertible E m)
  exact (cancel_epi α.hom).mp (congrArg Iso.hom h)

lemma exists_scaled (m : ℕ) {f : E.curve ⟶ E.curve} (α β : Lift E m f) :
    ∃ c : Rˣ, β = scaled E m c α := by
  obtain ⟨s, hs⟩ := aut_scalar (RelativeNormalizedThetaInversion.line_invertible E m)
    (α.symm ≪≫ β)
  obtain ⟨c, hc⟩ := scalar_surjective E s
  refine ⟨c, ?_⟩
  simp [scaled, hc, hs]

lemma scalar_pullback (f : E.curve ⟶ E.curve) (hf : f ≫ E.projection = E.projection)
    (c : Rˣ) : f.appTop (scalar E c : Γ(E.curve, ⊤)) = (scalar E c : Γ(E.curve, ⊤)) := by
  have h := congrArg (fun g => g.appTop) hf
  change E.projection.appTop ≫ f.appTop = E.projection.appTop at h
  exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (c : R))

lemma square_constraint (m : ℕ) (f : E.curve ⟶ E.curve)
    (hf : f ≫ E.projection = E.projection) (φ : Lift E m f) (c : Rˣ)
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
  have hv := smulHom_injective (RelativeNormalizedThetaInversion.line_invertible E m) hx
  apply scalar_injective E
  apply Units.ext
  simpa [scalar, pow_two, map_mul] using hv

lemma connected_sign [Algebra ℚ R] (c : Rˣ) (hc : c ^ 2 = 1)
    (hconn : _root_.IsPreconnected (Set.univ : Set (PrimeSpectrum R))) : c = 1 ∨ c = -1 := by
  let : PreconnectedSpace (PrimeSpectrum R) := ⟨hconn⟩
  let q : R := algebraMap ℚ R (1 / 2)
  have hq : (2 : R) * q = 1 := by
    dsimp [q]
    have h := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hc' : (c : R) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hc
  let e : R := ((c : R) + 1) * q
  have he : IsIdempotentElem e := by
    change e * e = e
    dsimp [e]
    linear_combination q^2 * hc' + q * ((c : R) + 1) * hq
  let k := PrimeSpectrum.isIdempotentElemEquivClopens (R := R) ⟨e, he⟩
  have hek : e = 0 ∨ e = 1 := by
    rcases isClopen_iff.mp k.isClopen with hk | hk
    · left
      have hk' : k = ⊥ := SetLike.coe_injective hk
      have hh := congrArg (fun z => (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm z) hk'
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] at hh
      exact congrArg Subtype.val ((PrimeSpectrum.isIdempotentElemEquivClopens.symm_apply_apply _).symm.trans hh)
    · right
      have hk' : k = ⊤ := SetLike.coe_injective hk
      have hh := congrArg (fun z => (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm z) hk'
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] at hh
      exact congrArg Subtype.val ((PrimeSpectrum.isIdempotentElemEquivClopens.symm_apply_apply _).symm.trans hh)
  rcases hek with he0 | he1
  · right
    apply Units.ext
    change (c : R) = -1
    dsimp [e] at he0
    linear_combination 2 * he0 - ((c : R) + 1) * hq
  · left
    apply Units.ext
    change (c : R) = 1
    dsimp [e] at he1
    linear_combination 2 * he1 - ((c : R) + 1) * hq

lemma symmetric_scalar_square (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (α : Lift E m (translation E P)) (c : Rˣ)
    (hα : Symmetric E m P ι α) (hβ : Symmetric E m P ι (scaled E m c α)) :
    c ^ 2 = 1 := by
  obtain ⟨ha, hα⟩ := hα
  obtain ⟨hb, hβ⟩ := hβ
  have hr : reflectionLift E m P ι (scaled E m c α) =
      scaled E m c (reflectionLift E m P ι α) := by
    simp [reflectionLift, scaled, Iso.trans_assoc]
  rw [hr] at hβ
  refine square_constraint E m (reflection E P) ?_ (reflectionLift E m P ι α) c ?_
  · change (translation E P ≫ inverse E) ≫ E.projection = E.projection
    rw [Category.assoc, RelativeNormalizedThetaInversion.inverse_over]
    exact E.law.translate_over _
  · exact hβ.trans hα.symm

end RelativeSymmetricLiftSigns
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255

/-- Two symmetric lifts differ by a unique square-one unit of the actual base.
On a preconnected base that unit is one constant sign. -/
theorem relative_symmetric_lift_signs :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R),
    ∀ (m : ℕ) (P : ArithmeticThetaRelativeThetaLiftsR0255.point E)
      (ι : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.inverse E)),
    ArithmeticThetaRelativeThetaLiftsR0255.NormalizedInversion E m ι →
    ∀ (α β : ArithmeticThetaRelativeThetaLiftsR0255.Lift E m (ArithmeticThetaRelativeThetaLiftsR0255.translation E P)),
    ArithmeticThetaRelativeThetaLiftsR0255.Symmetric E m P ι α →
    ArithmeticThetaRelativeThetaLiftsR0255.Symmetric E m P ι β →
    ∃! c : Rˣ, c^2 = 1 ∧ β = ArithmeticThetaRelativeThetaRelationsR0256.scaled E m c α ∧
      (_root_.IsPreconnected (Set.univ : Set (PrimeSpectrum R)) → c = 1 ∨ c = -1) := by
  intro R _ _ _ E m P ι _ α β hα hβ
  obtain ⟨c, hc⟩ := RelativeSymmetricLiftSigns.exists_scaled E m α β
  have hc2 := RelativeSymmetricLiftSigns.symmetric_scalar_square E m P ι α c hα (hc ▸ hβ)
  refine ⟨c, ⟨hc2, hc, RelativeSymmetricLiftSigns.connected_sign c hc2⟩, ?_⟩
  intro d hd
  exact RelativeSymmetricLiftSigns.scaled_injective E m α (hd.2.1.symm.trans hc)

#print axioms relative_symmetric_lift_signs
end ArithmeticThetaRelativeThetaRelationsR0256
