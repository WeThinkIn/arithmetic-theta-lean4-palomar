module

public import EtaleCompletedBranches
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
namespace ArithmeticThetaGlobalization

/-- The affine coordinate version, with the algebra structure induced by the map. -/
lemma affine_etale_disk_lift
    (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (B : CommRingCat.{u}) (a : CommRingCat.of R ⟶ B) [Etale (Spec.map a)]
    (b₀ : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec B)
    (hb₀ : b₀ ≫ Spec.map a = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃! b : Spec (CommRingCat.of R) ⟶ Spec B,
      b ≫ Spec.map a = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b = b₀ := by
  letI : Algebra R B := a.hom.toAlgebra
  haveI : Algebra.Etale R B :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp inferInstance
  have hc₀ : a ≫ Spec.preimage b₀ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    simpa using hb₀
  let c₀ : B →ₐ[R] R ⧸ I :=
    { toRingHom := (Spec.preimage b₀).hom
      commutes' := fun r => congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I) => k.hom r) hc₀ }
  obtain ⟨c, hc, huniq⟩ :=
    ArithmeticThetaGeometricPrerequisites.formally_etale_unique_adic_lift R B R I c₀
  have hac : a ≫ CommRingCat.ofHom c.toRingHom = 𝟙 _ := by
    ext r
    exact c.commutes r
  have hcc : CommRingCat.ofHom c.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
      Spec.preimage b₀ := by
    ext x
    exact AlgHom.congr_fun hc x
  refine ⟨Spec.map (CommRingCat.ofHom c.toRingHom), ⟨?_, ?_⟩, ?_⟩
  · rw [← Spec.map_comp, hac, Spec.map_id]
  · rw [← Spec.map_comp, hcc, Spec.map_preimage]
  · intro b hb
    have hab : a ≫ Spec.preimage b = 𝟙 _ := by
      apply Spec.map_injective
      simpa using hb.1
    let d : B →ₐ[R] R :=
      { toRingHom := (Spec.preimage b).hom
        commutes' := fun r => congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k.hom r) hab }
    have hd : (Ideal.Quotient.mkₐ R I).comp d = c₀ := by
      have h := congrArg Spec.preimage hb.2
      simp only [Spec.preimage_comp, Spec.preimage_map] at h
      ext x
      exact congrArg (fun k : B ⟶ CommRingCat.of (R ⧸ I) => k.hom x) h
    have he := huniq d hd
    have he' : Spec.preimage b = CommRingCat.ofHom c.toRingHom := by
      ext x
      exact AlgHom.congr_fun he x
    rw [← Spec.map_preimage b, he']

/-- Transport the coordinate lift along the canonical affine presentation. -/
lemma affine_scheme_etale_disk_lift
    (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (Z : Scheme.{u}) [IsAffine Z] (q : Z ⟶ Spec (CommRingCat.of R)) [Etale q]
    (s₀ : Spec (CommRingCat.of (R ⧸ I)) ⟶ Z)
    (hs₀ : s₀ ≫ q = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃! s : Spec (CommRingCat.of R) ⟶ Z,
      s ≫ q = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = s₀ := by
  let a := Spec.preimage (Z.isoSpec.inv ≫ q)
  have ha : Spec.map a = Z.isoSpec.inv ≫ q := Spec.map_preimage _
  haveI : Etale (Spec.map a) := by rw [ha]; infer_instance
  have hb₀ : (s₀ ≫ Z.isoSpec.hom) ≫ Spec.map a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    simpa [ha] using hs₀
  obtain ⟨b, hb, huniq⟩ := affine_etale_disk_lift R I _ a (s₀ ≫ Z.isoSpec.hom) hb₀
  refine ⟨b ≫ Z.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · simpa [ha] using hb.1
  · rw [← Category.assoc, hb.2, Category.assoc, Z.isoSpec.hom_inv_id, Category.comp_id]
  · intro s hs
    have h : s ≫ Z.isoSpec.hom = b := huniq _ ⟨by simpa [ha] using hs.1, by
      rw [← Category.assoc, hs.2]⟩
    rw [← h, Category.assoc, Z.isoSpec.hom_inv_id, Category.comp_id]

/-- A prescribed residual branch of a finite étale cover lifts uniquely over
an adically complete affine disk. Both equalities are equalities of scheme maps. -/
theorem finite_etale_formal_disk_lift :
    ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
      (X Y : Scheme.{u}) (p : Y ⟶ X) [IsFinite p] [Etale p]
      (f : Spec (CommRingCat.of R) ⟶ X)
      (g₀ : Spec (CommRingCat.of (R ⧸ I)) ⟶ Y),
      g₀ ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f →
      ∃! g : Spec (CommRingCat.of R) ⟶ Y,
        g ≫ p = f ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g = g₀ := by
  intro R _ I _ X Y p _ _ f g₀ hg₀
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let s₀ : Spec (CommRingCat.of (R ⧸ I)) ⟶ pullback p f :=
    pullback.lift g₀ j hg₀
  obtain ⟨s, hs, huniq⟩ := affine_scheme_etale_disk_lift R I (pullback p f)
    (pullback.snd p f) s₀ (by simp [s₀, j, pullback.lift_snd])
  refine ⟨s ≫ pullback.fst p f, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs.1, Category.id_comp]
  · rw [← Category.assoc, hs.2]
    simp [s₀, pullback.lift_fst]
  · intro g hg
    let t : Spec (CommRingCat.of R) ⟶ pullback p f :=
      pullback.lift g (𝟙 _) (by simpa using hg.1)
    have ht : t = s := huniq t ⟨by simp [t, pullback.lift_snd], by
      apply pullback.hom_ext
      · simpa [t, s₀, pullback.lift_fst] using hg.2
      · simp [t, s₀, j, pullback.lift_snd]⟩
    have h := congrArg (fun k => k ≫ pullback.fst p f) ht
    simpa [t, pullback.lift_fst] using h

end ArithmeticThetaGlobalization
