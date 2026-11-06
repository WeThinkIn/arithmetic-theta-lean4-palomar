module

public import RelativeNormalizedThetaInversionR0255
public import RelativeDoubledTorsionThetaLiftR0255

@[expose] public section

/-! Midpoint normalization over the entire base, without a frame of the fibre line. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaRelativeThetaLiftsR0255
namespace RelativeMidpointSymmetricThetaLift
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ArithmeticThetaLegendreAtlasR0176
open ArithmeticThetaSharpCoverR0194.FullLevelProjectiveRatiosR0194.ArithmeticFamily
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

/-- Scalars acting on an invertible sheaf are determined on all opens. -/
lemma smulHom_injective {X : Scheme.{u}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) :
    Function.Injective (fun s : Γ(X, ⊤) => smulHom s M) := by
  intro s t h
  change smulHom s M = smulHom t M at h
  obtain ⟨r, hr, hu⟩ := hM.existsUnique_app_eq_smul (smulHom s M)
  have hs : s = r := hu s (fun _ _ => rfl)
  have ht : t = r := hu t (by intro U x; rw [h]; rfl)
  exact hs.trans ht.symm

/-- Every automorphism of an invertible sheaf is a unique global unit. -/
lemma aut_scalar {X : Scheme.{u}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (δ : M ≅ M) :
    ∃ s : Γ(X, ⊤)ˣ, smulIso s M = δ := by
  obtain ⟨s, hs, _⟩ := hM.existsUnique_app_eq_smul δ.hom
  obtain ⟨t, ht, _⟩ := hM.existsUnique_app_eq_smul δ.inv
  have hs' : smulHom s M = δ.hom := by ext U x; exact (hs U x).symm
  have ht' : smulHom t M = δ.inv := by ext U x; exact (ht U x).symm
  have hst : s * t = 1 := smulHom_injective hM (by
    change smulHom (s * t) M = smulHom 1 M
    rw [smulHom_mul, hs', ht', δ.inv_hom_id, smulHom_one])
  refine ⟨⟨s, t, hst, (mul_comm t s).trans hst⟩, ?_⟩
  apply Iso.ext
  exact hs'

/-- A section detects all automorphisms, using the actual structure map. -/
lemma aut_eq_refl {S X : Scheme.{u}} (p : X ⟶ S)
    (hp : Function.Surjective p.appTop) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (δ : M ≅ M)
    (hδ : (Scheme.Modules.pullback e).mapIso δ = Iso.refl _) : δ = Iso.refl _ := by
  obtain ⟨s, hs⟩ := aut_scalar hM δ
  have hscalar : smulHom (e.appTop (s : Γ(X, ⊤))) ((Scheme.Modules.pullback e).obj M) =
      smulHom 1 ((Scheme.Modules.pullback e).obj M) := by
    rw [← pullback_map_smulHom, smulHom_one]
    rw [← hs] at hδ
    exact congrArg Iso.hom hδ
  have hs1 := smulHom_injective (hM.pullback e) hscalar
  obtain ⟨d, hd⟩ := hp (s : Γ(X, ⊤))
  have hd1 : d = 1 := by
    rw [← appTop_appTop_of_comp_eq_id e p he d, hd, hs1]
  have hval : (s : Γ(X, ⊤)) = 1 := by rw [← hd, hd1, map_one]
  apply Iso.ext
  rw [← hs]
  change smulHom (s : Γ(X, ⊤)) M = 𝟙 M
  rw [hval, smulHom_one]

/-- Prescribe an isomorphism on a section of two globally isomorphic lines.
The fibre line itself need not be trivial. -/
lemma existsUnique_fibreIso {S X : Scheme.{u}} (p : X ⟶ S)
    (hp : Function.Surjective p.appTop) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (M N : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (c : (Scheme.Modules.pullback e).obj M ≅ (Scheme.Modules.pullback e).obj N)
    (α₀ : M ≅ N) :
    ∃! α : M ≅ N, (Scheme.Modules.pullback e).mapIso α = c := by
  let δ := c ≪≫ ((Scheme.Modules.pullback e).mapIso α₀).symm
  obtain ⟨s, hs⟩ := aut_scalar (hM.pullback e) δ
  let t := Units.map p.appTop.hom.toMonoidHom s
  let θ := smulIso t M
  have hθ : (Scheme.Modules.pullback e).mapIso θ = δ := by
    rw [pullback_mapIso_smulIso]
    have hts : Units.map e.appTop.hom.toMonoidHom t = s := by
      apply Units.ext
      exact appTop_appTop_of_comp_eq_id e p he s
    rw [hts, hs]
  let α := θ ≪≫ α₀
  have hα : (Scheme.Modules.pullback e).mapIso α = c := by
    dsimp only [α]
    rw [Functor.mapIso_trans, hθ]
    simp [δ]
  refine ⟨α, hα, ?_⟩
  intro β hβ
  have hβα : β ≪≫ α.symm = Iso.refl M := aut_eq_refl p hp e he hM _ (by
    rw [Functor.mapIso_trans, Functor.mapIso_symm, hβ, hα]
    simp)
  have hh := congrArg Iso.hom hβα
  apply Iso.ext
  simpa using hh =≫ α.hom

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

lemma point_inverse {T : Scheme.{u}} (t : T ⟶ base (R := R))
    (a : SchemeHomOver t E.projection) :
    a.val ≫ inverse E = (E.law.inv t a).val := by
  have h := RelativeNormalizedThetaInversion.inverse_natural E E.projection t a.val a.property
    (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.projection E.projection)
  have ha : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨𝟙 E.curve, Category.id_comp _⟩ : SchemeHomOver E.projection E.projection) = a := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha] at h
  exact congrArg Subtype.val h

lemma point_translate {T : Scheme.{u}} (t : T ⟶ base (R := R))
    (a : SchemeHomOver t E.projection) (b : point E) :
    a.val ≫ E.law.translate b =
      (E.law.mul t a ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩).val := by
  have h := E.law.mul_natural E.projection t a.val a.property RelativeGroupLaw.idPoint
    ⟨E.projection ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩
  have h₁ : GoodReductionJacobian.schemeHomOverComp a.val a.property RelativeGroupLaw.idPoint = a := by
    apply Subtype.ext
    exact Category.comp_id _
  have h₂ : GoodReductionJacobian.schemeHomOverComp a.val a.property
      (⟨E.projection ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ :
        SchemeHomOver E.projection E.projection) =
      ⟨t ≫ b.val, by rw [Category.assoc, b.property, Category.comp_id]⟩ := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b.val) a.property)
  rw [h₁, h₂] at h
  exact congrArg Subtype.val h

lemma reflection_square (P : point E) : reflection E P ≫ reflection E P = 𝟙 E.curve := by
  let a := E.law.nsmul (𝟙 _) 2 P
  let ca : SchemeHomOver E.projection E.projection :=
    ⟨E.projection ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩
  let i : SchemeHomOver E.projection E.projection := ⟨𝟙 E.curve, Category.id_comp _⟩
  let b := E.law.inv E.projection (E.law.mul E.projection i ca)
  have h₁ : reflection E P = b.val := point_inverse E E.projection (E.law.mul E.projection i ca)
  have h₂ : b.val ≫ E.law.translate a = (E.law.mul E.projection b ca).val :=
    point_translate E E.projection b a
  conv_lhs => lhs; rw [h₁]
  change b.val ≫ (E.law.translate a ≫ inverse E) = _
  rw [← Category.assoc, h₂, point_inverse]
  change (E.law.inv E.projection (E.law.mul E.projection
    (E.law.inv E.projection (E.law.mul E.projection i ca)) ca)).val = i.val
  congr 1
  letI := E.law.pointGroup E.projection
  have hcomm (v w : SchemeHomOver E.projection E.projection) : v * w = w * v :=
    E.commutative E.projection v w
  change ((i * ca)⁻¹ * ca)⁻¹ = i
  rw [mul_inv_rev, inv_inv, hcomm i ca, ← mul_assoc, inv_mul_cancel, one_mul]

lemma reflection_fixed (P : point E) : negative E P ≫ reflection E P = negative E P := by
  let a := E.law.inv (𝟙 _) P
  have hInv : a.val ≫ inverse E = P.val := by
    rw [point_inverse]
    congr 1
    letI := E.law.pointGroup (𝟙 (base (R := R)))
    exact inv_inv P
  have hd : a.val ≫ translation E P = P.val := by
    rw [translation, point_translate]
    have hid : (⟨𝟙 _ ≫ (E.law.nsmul (𝟙 _) 2 P).val, by
        rw [Category.assoc, (E.law.nsmul (𝟙 _) 2 P).property, Category.comp_id]⟩ :
        point E) = E.law.nsmul (𝟙 _) 2 P := by
      apply Subtype.ext
      exact Category.id_comp _
    rw [hid]
    letI := E.law.pointGroup (𝟙 (base (R := R)))
    have htwo : E.law.nsmul (𝟙 _) 2 P = P * P := by
      rw [E.law.nsmul_succ, E.law.nsmul_succ]
      change (1 * P) * P = P * P
      rw [one_mul]
    rw [htwo]
    change (P⁻¹ * (P * P)).val = P.val
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  change a.val ≫ (translation E P ≫ inverse E) = a.val
  rw [← Category.assoc, hd, point_inverse]

lemma structure_surjective : Function.Surjective E.projection.appTop := by
  intro s
  obtain ⟨r, hr⟩ := (RelativeNormalizedThetaInversion.constants_bijective E).2 s
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv r, hr⟩

lemma normalized_reflection (m : ℕ) (P : point E)
    (h : Nonempty (Lift E m (reflection E P))) :
    ∃! φ : Lift E m (reflection E P),
      (Scheme.Modules.pullback (negative E P)).mapIso φ =
        fixedComparison E m (negative E P) (reflection E P) (reflection_fixed E P) := by
  obtain ⟨φ⟩ := h
  exact existsUnique_fibreIso E.projection (structure_surjective E) (negative E P)
    (E.law.inv (𝟙 _) P).property _ _
    ((RelativeNormalizedThetaInversion.line_invertible E m).pullback _) _ φ

lemma normalized_square (m : ℕ) (P : point E) (φ : Lift E m (reflection E P))
    (hφ : (Scheme.Modules.pullback (negative E P)).mapIso φ =
      fixedComparison E m (negative E P) (reflection E P) (reflection_fixed E P)) :
    (Scheme.Modules.pullback (reflection E P)).mapIso φ ≪≫ φ =
      squareComparison E m (reflection E P) (reflection_square E P) := by
  apply FixedPointPullback.square_of_rigidified (negative E P) (reflection E P)
    (reflection_fixed E P) (reflection_square E P) (thetaLine E m) _ (Iso.refl _) φ
  · simpa only [Iso.trans_refl, fixedComparison] using hφ
  · intro ψ hψ
    exact aut_eq_refl E.projection (structure_surjective E) (negative E P)
      (E.law.inv (𝟙 _) P).property (RelativeNormalizedThetaInversion.line_invertible E m)
      ψ (by simpa only [Iso.trans_refl] using hψ)

lemma midpoint_exists_unique (m : ℕ) (P : point E) (ι : Lift E m (inverse E))
    (h : Nonempty (Lift E m (translation E P))) :
    ∃! α : Lift E m (translation E P),
      MidpointNormalized E m P ι α ∧ Symmetric E m P ι α := by
  obtain ⟨α₀⟩ := h
  obtain ⟨φ, hφ, hu⟩ := normalized_reflection E m P ⟨reflectionLift E m P ι α₀⟩
  let α : Lift E m (translation E P) :=
    ((Scheme.Modules.pullback (translation E P)).mapIso ι).symm ≪≫
      (Scheme.Modules.pullbackComp (translation E P) (inverse E)).app _ ≪≫ φ
  have hα : reflectionLift E m P ι α = φ := by
    apply Iso.ext
    simp [reflectionLift, α]
  refine ⟨α, ⟨⟨reflection_fixed E P, ?_⟩, ⟨reflection_square E P, ?_⟩⟩, ?_⟩
  · rw [hα]
    exact hφ
  · rw [hα]
    exact normalized_square E m P φ hφ
  · intro β hβ
    obtain ⟨hb, hβ⟩ := hβ.1
    have he : reflectionLift E m P ι β = reflectionLift E m P ι α :=
      (hu _ hβ).trans hα.symm
    apply Iso.ext
    exact (cancel_epi (((Scheme.Modules.pullbackComp (translation E P) (inverse E)).app _).inv ≫
      ((Scheme.Modules.pullback (translation E P)).mapIso ι).hom)).mp
      (by simpa only [reflectionLift, Iso.trans_hom, Iso.symm_hom, Category.assoc] using congrArg Iso.hom he)

end RelativeMidpointSymmetricThetaLift

/-- The unique midpoint-normalized symmetric translation lift on the full family. -/
theorem relative_midpoint_symmetric_theta_lift :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : ArithmeticThetaLegendreAtlasR0176.EllipticFamily R),
    ∀ m : ℕ, 0 < m → Even m → ∀ (P : point E),
      CategoryTheory.CategoryStruct.comp P.val (E.law.schemeNsmul (2*m)) = zero E →
    ∀ ι : Lift E m (inverse E), NormalizedInversion E m ι →
      ∃! α : Lift E m (translation E P),
        MidpointNormalized E m P ι α ∧ Symmetric E m P ι α := by
  intro R _ _ _ E m hm he P hP ι _
  exact RelativeMidpointSymmetricThetaLift.midpoint_exists_unique E m P ι
    (relative_doubled_torsion_theta_lift R E m hm he P hP)

#print axioms relative_midpoint_symmetric_theta_lift
end ArithmeticThetaRelativeThetaLiftsR0255
