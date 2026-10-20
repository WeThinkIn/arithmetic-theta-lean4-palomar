module

public import CompactifiedCoordinateIsomorphismR0145
public import AffineDifferentialFrameR0145
public import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension

public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
public import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext

public import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup

public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaCompactifiedDifferentialR0145
namespace GlobalNormalizedDifferential
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaGenericEvaluationR0140

section DerivationIdentities
variable {F B N : Type u} [CommRing F] [CommRing B] [Algebra F B]
variable [AddCommGroup N] [Module B N] [Module F N] [IsScalarTower F B N]

/-- Clearing denominators requires only the product rule, including zero denominators. -/
lemma cleared_product_rule (D : Derivation F B N) (x y a b : B) (δ : N)
    (hx : D x = (2 * y) • δ) :
    b • (a • D (x * a) - (x * a) • D a) =
      (2 * (y * b) * a ^ 2) • δ := by
  rw [D.leibniz, hx]
  module

/-- The vector field on the chart X/Y=u, Z/Y=v has a unit coefficient at infinity. -/
def infinityCoefficient (a₂ a₄ a₆ u v : B) : B :=
  1 - a₂ * u ^ 2 - 2 * a₄ * u * v - 3 * a₆ * v ^ 2

def infinitySlope (a₂ a₄ : B) (u v : B) : B :=
  3 * u ^ 2 + 2 * a₂ * u * v + a₄ * v ^ 2

lemma infinity_euler (a₂ a₄ a₆ u v : B)
    (h : v = u ^ 3 + a₂ * u ^ 2 * v + a₄ * u * v ^ 2 + a₆ * v ^ 3) :
    u * infinitySlope a₂ a₄ u v - v * infinityCoefficient a₂ a₄ a₆ u v = 2 * v := by
  dsimp [infinityCoefficient, infinitySlope]
  linear_combination -3 * h

lemma infinity_coprime (a₂ a₄ a₆ u v : B)
    (h : v = u ^ 3 + a₂ * u ^ 2 * v + a₄ * u * v ^ 2 + a₆ * v ^ 3)
    (h2 : IsUnit (2 : B)) (h3 : IsUnit (3 : B)) :
    IsCoprime (infinityCoefficient a₂ a₄ a₆ u v) (infinitySlope a₂ a₄ u v) := by
  let p := infinityCoefficient a₂ a₄ a₆ u v
  let q := infinitySlope a₂ a₄ u v
  let I : Ideal B := Ideal.span {p} ⊔ Ideal.span {q}
  have hp : p ∈ I := (show Ideal.span {p} ≤ I from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
  have hq : q ∈ I := (show Ideal.span {q} ≤ I from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  have hv : v ∈ I := (I.unit_mul_mem_iff_mem h2).mp (by
    rw [← infinity_euler a₂ a₄ a₆ u v h]
    exact I.sub_mem (I.mul_mem_left _ hq) (I.mul_mem_left _ hp))
  have hu : u ^ 2 ∈ I := (I.unit_mul_mem_iff_mem h3).mp (by
    have he : 3 * u ^ 2 = q - (2 * a₂ * u + a₄ * v) * v := by
      dsimp [q, infinitySlope]
      ring
    rw [he]
    exact I.sub_mem hq (I.mul_mem_left _ hv))
  have hone : (1 : B) ∈ I := by
    have he : 1 = p + a₂ * u ^ 2 + (2 * a₄ * u + 3 * a₆ * v) * v := by
      dsimp [p, infinityCoefficient]
      ring
    rw [he]
    exact I.add_mem (I.add_mem hp (I.mul_mem_left _ hu)) (I.mul_mem_left _ hv)
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.eq_top_of_isUnit_mem I hone isUnit_one)

lemma infinity_coefficient_mod (a₂ a₄ a₆ u v : B) {C : Type u} [CommRing C]
    (f : B →+* C) (hu : f u = 0) (hv : f v = 0) :
    f (infinityCoefficient a₂ a₄ a₆ u v) = 1 := by
  simp [infinityCoefficient, hu, hv]

/-- The affine and infinity formulas agree after multiplication by Z/Y. -/
lemma infinity_transition (D : Derivation F B N) (a₂ a₄ a₆ u v : B) (δ : N)
    (h : v = u ^ 3 + a₂ * u ^ 2 * v + a₄ * u * v ^ 2 + a₆ * v ^ 3)
    (hu : D u = (-infinityCoefficient a₂ a₄ a₆ u v) • δ)
    (hv : D v = (-infinitySlope a₂ a₄ u v) • δ) :
    v • D u - u • D v = (2 * v) • δ := by
  rw [hu, hv]
  calc
    v • ((-infinityCoefficient a₂ a₄ a₆ u v) • δ) -
        u • ((-infinitySlope a₂ a₄ u v) • δ) =
        (u * infinitySlope a₂ a₄ u v - v * infinityCoefficient a₂ a₄ a₆ u v) • δ := by module
    _ = _ := by rw [infinity_euler a₂ a₄ a₆ u v h]
end DerivationIdentities

section RelativeDerivation
variable {F : Type u} [CommRing F] {C : Scheme.{u}}
variable (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens)

lemma relativeD_add (a b : Γ(C, U)) :
    relativeD f U (a + b) = relativeD f U a + relativeD f U b := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U (KaehlerDifferential.D F Γ(C, U) (a + b)) = _
  rw [map_add, map_add]
  rfl

lemma relativeD_mul (a b : Γ(C, U)) :
    relativeD f U (a * b) = a • relativeD f U b + b • relativeD f U a := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U (KaehlerDifferential.D F Γ(C, U) (a * b)) = _
  rw [Derivation.leibniz, map_add, map_smul, map_smul]
  rfl

lemma relativeD_zero : relativeD f U 0 = 0 := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U (KaehlerDifferential.D F Γ(C, U) 0) = 0
  rw [map_zero, map_zero]

lemma relativeD_one : relativeD f U 1 = 0 := by
  letI := f.sectionsAlgebra U
  change f.kaehlerToSectionsₗ U (KaehlerDifferential.D F Γ(C, U) 1) = 0
  rw [Derivation.map_one_eq_zero, map_zero]

lemma relativeD_cleared (x y a b : Γ(C, U)) (δ : Γ(f.kaehler, U))
    (hx : relativeD f U x = (2 * y) • δ) :
    b • (a • relativeD f U (x * a) - (x * a) • relativeD f U a) =
      (2 * (y * b) * a ^ 2) • δ := by
  rw [relativeD_mul, hx]
  module
lemma relativeD_restrict {V : C.Opens} (hVU : V ≤ U) (a : Γ(C, U)) :
    f.kaehler.presheaf.map (homOfLE hVU).op (relativeD f U a) =
      relativeD f V (C.presheaf.map (homOfLE hVU).op a) := by
  letI := f.sectionsAlgebra U
  letI := f.sectionsAlgebra V
  have hn := P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.T0aKS.res_toSh
    f hVU (KaehlerDifferential.D F Γ(C, U) a)
  refine hn.trans ?_
  apply congrArg (f.kaehlerToSections V)
  exact PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    f.constToPresheaf (homOfLE hVU).op a

lemma relativeD_normalization_restrict {V : C.Opens} (hVU : V ≤ U)
    (x p : Γ(C, U)) (δ : Γ(f.kaehler, U)) (h : relativeD f U x = p • δ) :
    relativeD f V (C.presheaf.map (homOfLE hVU).op x) =
      C.presheaf.map (homOfLE hVU).op p • f.kaehler.presheaf.map (homOfLE hVU).op δ := by
  rw [← relativeD_restrict, h, Scheme.Modules.map_smul]

lemma relativeD_overlap (x y u v a₂ a₄ a₆ : Γ(C, U)) (δ ε : Γ(f.kaehler, U))
    (h2 : IsUnit (2 : Γ(C, U))) (hv : IsUnit v)
    (hxu : x * v = u) (hyv : y * v = 1)
    (heq : v = u ^ 3 + a₂ * u ^ 2 * v + a₄ * u * v ^ 2 + a₆ * v ^ 3)
    (hδ : relativeD f U x = (2 * y) • δ)
    (hεu : relativeD f U u = (-infinityCoefficient a₂ a₄ a₆ u v) • ε)
    (hεv : relativeD f U v = (-infinitySlope a₂ a₄ u v) • ε) : δ = ε := by
  have hdu := congrArg (relativeD f U) hxu
  rw [relativeD_mul, hδ, hεu] at hdu
  have hcross : v • relativeD f U u - u • relativeD f U v = (2 * v) • ε := by
    rw [hεu, hεv]
    calc
      v • ((-infinityCoefficient a₂ a₄ a₆ u v) • ε) -
          u • ((-infinitySlope a₂ a₄ u v) • ε) =
          (u * infinitySlope a₂ a₄ u v - v * infinityCoefficient a₂ a₄ a₆ u v) • ε := by module
      _ = _ := by rw [infinity_euler a₂ a₄ a₆ u v heq]
  have he : (2 * v) • δ = (2 * v) • ε := by
    calc
      (2 * v) • δ = v • (v • ((2 * y) • δ)) := by
        simp only [smul_smul]
        congr 1
        calc
          2 * v = 2 * v * (y * v) := by rw [hyv, mul_one]
          _ = v * (v * (2 * y)) := by ring
      _ = v • relativeD f U u - u • relativeD f U v := by
        rw [← hxu, relativeD_mul, hδ]
        module
      _ = (2 * v) • ε := hcross
  obtain ⟨w, hw⟩ := h2.mul hv
  rw [← hw] at he
  have hh := congrArg (fun z => (↑w⁻¹ : Γ(C, U)) • z) he
  simpa only [smul_smul, Units.inv_mul, one_smul] using hh

end RelativeDerivation

/-- A two-generator universal differential module is framed by a coprime tangent field. -/
lemma frame_of_coprime {F B : Type u} [CommRing F] [CommRing B] [Algebra F B]
    (x y p q : B) (hcp : IsCoprime p q)
    (d : Derivation F B B) (dx : d x = p) (dy : d y = q)
    (hrel : p • KaehlerDifferential.D F B y = q • KaehlerDifferential.D F B x)
    (hext : ∀ d e : Derivation F B (KaehlerDifferential F B),
      d x = e x → d y = e y → d = e) :
    ∃! e : DifferentialFrame F B,
      KaehlerDifferential.D F B x = p • e 1 ∧ KaehlerDifferential.D F B y = q • e 1 := by
  let Ω := KaehlerDifferential F B
  let D := KaehlerDifferential.D F B
  obtain ⟨a, b, hab⟩ := hcp
  let δ : Ω := a • D x + b • D y
  obtain ⟨hx, hy⟩ := AffineFrame.bezout_pair a b p q (D x) (D y) hab hrel
  change p • δ = D x at hx
  change q • δ = D y at hy
  let L : Ω →ₗ[B] B := d.liftKaehlerDifferential
  have Lx : L (D x) = p := (d.liftKaehlerDifferential_comp_D x).trans dx
  have Ly : L (D y) = q := (d.liftKaehlerDifferential_comp_D y).trans dy
  have Lδ : L δ = 1 := by
    change L (a • D x + b • D y) = 1
    rw [map_add, map_smul, map_smul, Lx, Ly]
    exact hab
  let E : B →ₗ[B] Ω := LinearMap.toSpanSingleton B Ω δ
  have hLE : L.comp E = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change L (z • δ) = z
    rw [map_smul, Lδ, smul_eq_mul, mul_one]
  have hEL : E.comp L = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply hext
    · change E (L (D x)) = D x
      rw [Lx]
      exact hx
    · change E (L (D y)) = D y
      rw [Ly]
      exact hy
  let e : DifferentialFrame F B := LinearEquiv.ofLinearMap E L hEL hLE
  have he1 : e 1 = δ := one_smul B δ
  refine ⟨e, ?_, ?_⟩
  · change D x = p • e 1 ∧ D y = q • e 1
    rw [he1]
    exact ⟨hx.symm, hy.symm⟩
  · intro e' he'
    have hδ : δ = e' 1 := by
      change a • D x + b • D y = e' 1
      rw [he'.1, he'.2, smul_smul, smul_smul, ← add_smul, hab, one_smul]
    apply LinearEquiv.ext
    intro z
    calc
      e' z = z • e' 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      _ = z • δ := by rw [hδ]
      _ = e z := rfl

section DifferentialTransport
variable {F A B C : Type u} [CommRing F] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra F A] [Algebra F B] [Algebra F C]

def differentialMap (φ : A →ₐ[F] B) : KaehlerDifferential F A →ₗ[F] KaehlerDifferential F B :=
  KaehlerDifferential.mapOfRingHom (RingHom.id F) φ.toRingHom (by
    ext a
    exact φ.commutes a)

lemma differentialMap_D (φ : A →ₐ[F] B) (a : A) :
    differentialMap φ (KaehlerDifferential.D F A a) = KaehlerDifferential.D F B (φ a) :=
  KaehlerDifferential.mapOfRingHom_D _ _ _ _

lemma differentialMap_smul (φ : A →ₐ[F] B) (a : A) (ω : KaehlerDifferential F A) :
    differentialMap φ (a • ω) = φ a • differentialMap φ ω :=
  KaehlerDifferential.mapOfRingHom_smul _ _ _ _ _

lemma differentialMap_comp (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (ω : KaehlerDifferential F A) :
    differentialMap ψ (differentialMap φ ω) = differentialMap (ψ.comp φ) ω := by
  have h := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := (differentialMap ψ).toAddMonoidHom.comp (differentialMap φ).toAddMonoidHom)
    (g := (differentialMap (ψ.comp φ)).toAddMonoidHom) (fun a b => by
      change differentialMap ψ (differentialMap φ (a • KaehlerDifferential.D F A b)) =
        differentialMap (ψ.comp φ) (a • KaehlerDifferential.D F A b)
      simp only [differentialMap_smul, differentialMap_D, AlgHom.comp_apply])
  exact DFunLike.congr_fun h ω

lemma differentialMap_id (ω : KaehlerDifferential F A) : differentialMap (AlgHom.id F A) ω = ω :=
  KaehlerDifferential.mapOfRingHom_id _ ω

lemma differentialMap_bijective (φ : A ≃ₐ[F] B) : Function.Bijective (differentialMap φ.toAlgHom) := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨differentialMap φ.symm.toAlgHom, ?_, ?_⟩
  · intro ω
    rw [differentialMap_comp, φ.symm_comp, differentialMap_id]
  · intro ω
    rw [differentialMap_comp, φ.comp_symm, differentialMap_id]

def frameTransport (φ : A ≃ₐ[F] B) (e : DifferentialFrame F A) : DifferentialFrame F B :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton B (KaehlerDifferential F B)
    (differentialMap φ.toAlgHom (e 1))) (by
      have hfun : (fun b : B => b • differentialMap φ.toAlgHom (e 1)) =
          (differentialMap φ.toAlgHom) ∘ e ∘ φ.symm := by
        funext b
        dsimp only [Function.comp_apply]
        rw [show e (φ.symm b) = (φ.symm b) • e 1 by rw [← map_smul, smul_eq_mul, mul_one],
          differentialMap_smul]
        simp
      change Function.Bijective (fun b : B => b • differentialMap φ.toAlgHom (e 1))
      rw [hfun]
      exact (differentialMap_bijective φ).comp (e.bijective.comp φ.symm.bijective))

lemma frameTransport_one (φ : A ≃ₐ[F] B) (e : DifferentialFrame F A) :
    frameTransport φ e 1 = differentialMap φ.toAlgHom (e 1) := one_smul B _

lemma frameTransport_normalization (φ : A ≃ₐ[F] B) (e : DifferentialFrame F A) (x p : A)
    (h : KaehlerDifferential.D F A x = p • e 1) :
    KaehlerDifferential.D F B (φ x) = φ p • frameTransport φ e 1 := by
  have hh := congrArg (differentialMap φ.toAlgHom) h
  rw [differentialMap_D, differentialMap_smul] at hh
  rw [frameTransport_one]
  exact hh
end DifferentialTransport

section SheafFrames
variable {F B : Type u} [CommRing F] [CommRing B] [Algebra F B] {C : Scheme.{u}}
variable (f : C ⟶ Spec (CommRingCat.of F))

lemma affine_frame (U : C.Opens) (hU : IsAffineOpen U)
    (hΩ : Scheme.Modules.IsInvertible f.kaehler) :
    letI := f.sectionsAlgebra U
    ∀ e : DifferentialFrame F Γ(C, U),
      Scheme.Modules.IsFrameOn (f.kaehlerToSections U (e 1)) U := by
  letI := f.sectionsAlgebra U
  intro e
  apply hΩ.isFrameOn_of_isAffineOpen_of_span_singleton_eq_top hU
  apply top_unique
  intro ω _
  obtain ⟨v, rfl⟩ := (f.kaehlerToSections_bijective_of_isAffineOpen hU).surjective ω
  obtain ⟨a, rfl⟩ := e.surjective v
  have he : e a = a • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  rw [he]
  change (f.kaehlerToSectionsₗ U) (a • e 1) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))

lemma affine_frame_normalization (U : C.Opens) :
    letI := f.sectionsAlgebra U
    ∀ (e : DifferentialFrame F Γ(C, U)) (x p : Γ(C, U)),
      KaehlerDifferential.D F Γ(C, U) x = p • e 1 →
        relativeD f U x = p • f.kaehlerToSections U (e 1) := by
  letI := f.sectionsAlgebra U
  intro e x p h
  change (f.kaehlerToSectionsₗ U) (KaehlerDifferential.D F Γ(C, U) x) = _
  rw [h, map_smul]
  rfl

variable (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]

def chartRingEquiv : Γ(C, i ''ᵁ ⊤) ≃+* B :=
  ((i.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv

lemma chartRingEquiv_algebraMap (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F B))) :
    letI := f.sectionsAlgebra (i ''ᵁ ⊤)
    ∀ a : F, chartRingEquiv i (algebraMap F Γ(C, i ''ᵁ ⊤) a) = algebraMap F B a := by
  letI := f.sectionsAlgebra (i ''ᵁ ⊤)
  intro a
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom)
    (((i.appIso ⊤).hom).hom
      ((f.constToPresheaf.app (Opposite.op (i ''ᵁ ⊤))).hom a)) = _
  rw [Scheme.Hom.appIso_hom']
  change (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
    f.appLE ⊤ (i ''ᵁ ⊤) le_top ≫ i.appLE (i ''ᵁ ⊤) ⊤ (Scheme.Hom.preimage_image_eq i ⊤).ge ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom a) = _
  rw [← Category.assoc (f.appLE _ _ _) , Scheme.Hom.appLE_comp_appLE, hi]
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F B))
  have he : (Spec.map (CommRingCat.ofHom (algebraMap F B))).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap F B))).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [he, hn]
  simp

lemma chartRingEquiv_restrict {A : Type u} [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ C) [IsOpenImmersion j] (φ : B →+* A)
    (hj : j = Spec.map (CommRingCat.ofHom φ) ≫ i)
    (hji : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤) (a : Γ(C, i ''ᵁ ⊤)) :
    chartRingEquiv j (C.presheaf.map (homOfLE hji).op a) = φ (chartRingEquiv i a) := by
  have he : C.presheaf.map (homOfLE hji).op ≫ (j.appIso ⊤).hom =
      (i.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    subst j
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom']
    rw [Scheme.Hom.map_appLE]
    rw [show (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) by
        simp [Scheme.Hom.appLE, Scheme.Hom.appTop]]
    rw [Scheme.Hom.appLE_comp_appLE]
  have hh := congrArg (fun q : Γ(C, i ''ᵁ ⊤) ⟶ CommRingCat.of A => q.hom a)
    (show C.presheaf.map (homOfLE hji).op ≫ (j.appIso ⊤).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom =
      (i.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom φ by
      rw [← Category.assoc, he, Category.assoc, Scheme.ΓSpecIso_naturality])
  exact hh

lemma chartSection_restrict {A : Type u} [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ C) [IsOpenImmersion j] (φ : B →+* A)
    (hj : j = Spec.map (CommRingCat.ofHom φ) ≫ i)
    (hji : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤) (a : B) :
    C.presheaf.map (homOfLE hji).op ((chartRingEquiv i).symm a) =
      (chartRingEquiv j).symm (φ a) := by
  apply (chartRingEquiv j).injective
  rw [chartRingEquiv_restrict i j φ hj hji, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]

lemma chart_normalization_restrict {A : Type u} [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ C) [IsOpenImmersion j] (φ : B →+* A)
    (hj : j = Spec.map (CommRingCat.ofHom φ) ≫ i)
    (hji : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤) (x p : B) (δ : Γ(f.kaehler, i ''ᵁ ⊤))
    (h : relativeD f (i ''ᵁ ⊤) ((chartRingEquiv i).symm x) = (chartRingEquiv i).symm p • δ) :
    relativeD f (j ''ᵁ ⊤) ((chartRingEquiv j).symm (φ x)) =
      (chartRingEquiv j).symm (φ p) • f.kaehler.presheaf.map (homOfLE hji).op δ := by
  have hh := relativeD_normalization_restrict f (i ''ᵁ ⊤) hji _ _ δ h
  rw [chartSection_restrict i j φ hj hji, chartSection_restrict i j φ hj hji] at hh
  exact hh

def chartAlgEquiv (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F B))) :
    letI := f.sectionsAlgebra (i ''ᵁ ⊤)
    Γ(C, i ''ᵁ ⊤) ≃ₐ[F] B :=
  letI := f.sectionsAlgebra (i ''ᵁ ⊤)
  { chartRingEquiv i with commutes' := chartRingEquiv_algebraMap f i hi }

lemma frame_on_chart (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F B)))
    (hΩ : Scheme.Modules.IsInvertible f.kaehler) (e : DifferentialFrame F B) :
    ∃ δ : Γ(f.kaehler, i ''ᵁ ⊤), Scheme.Modules.IsFrameOn δ (i ''ᵁ ⊤) ∧
      ∀ x p : B, KaehlerDifferential.D F B x = p • e 1 →
        relativeD f (i ''ᵁ ⊤) ((chartRingEquiv i).symm x) =
          (chartRingEquiv i).symm p • δ := by
  letI := f.sectionsAlgebra (i ''ᵁ ⊤)
  let φ := (chartAlgEquiv f i hi).symm
  let E := frameTransport φ e
  refine ⟨f.kaehlerToSections (i ''ᵁ ⊤) (E 1), ?_, ?_⟩
  · apply affine_frame f _ _ hΩ E
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange i
  · intro x p h
    exact affine_frame_normalization f _ E _ _ (frameTransport_normalization φ e x p h)

lemma iso_of_global_frame {M : C.Modules} (δ : Γ(M, ⊤)) (hδ : Scheme.Modules.IsFrameOn δ ⊤) :
    ∃ e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ M,
      ∀ U : C.Opens, Scheme.Modules.Hom.app e.hom U (1 : Γ(C, U)) = M.presheaf.map (homOfLE le_top).op δ := by
  let t := ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection M δ
  have ht : IsIso t := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr (fun U => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hδ (W := U) le_top le_top)
  letI := ht
  refine ⟨asIso t, ?_⟩
  intro U
  have he := ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection_apply
    M δ U (1 : Γ(C, U))
  exact he.trans (one_smul _ _)

lemma glue_frames {M : C.Modules} {ι : Type u} (U : ι → C.Opens)
    (hcov : (⨆ i, U i) = ⊤) (δ : ∀ i, Γ(M, U i))
    (hδ : ∀ i, Scheme.Modules.IsFrameOn (δ i) (U i))
    (hcompat : ∀ i j,
      M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (δ i) =
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (δ j)) :
    ∃ e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ M,
      ∀ i, Scheme.Modules.Hom.app e.hom (U i) (1 : Γ(C, U i)) = δ i := by
  obtain ⟨s, hs⟩ := (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    M U ⊤ (fun _ => le_top) hcov.ge).2 δ hcompat
  have hsframe : Scheme.Modules.IsFrameOn s ⊤ := by
    suffices hh : Scheme.Modules.IsFrameOn s (⨆ i, U i) from hh.mono hcov.ge
    apply Scheme.Modules.IsFrameOn.of_iSup
    intro i V hVtop hVi
    have he : M.presheaf.map (homOfLE hVi).op (δ i) =
        M.presheaf.map (homOfLE hVtop).op s := by
      rw [← hs i, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [← he]
    exact hδ i hVi hVi
  obtain ⟨e, he⟩ := iso_of_global_frame s hsframe
  exact ⟨e, fun i => (he (U i)).trans (hs i)⟩

lemma glue_two_frames {M : C.Modules} (U V : C.Opens) (hcov : U ⊔ V = ⊤)
    (δ : Γ(M, U)) (ε : Γ(M, V))
    (hδ : Scheme.Modules.IsFrameOn δ U) (hε : Scheme.Modules.IsFrameOn ε V)
    (hcompat : M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op δ =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op ε) :
    ∃ e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ M,
      Scheme.Modules.Hom.app e.hom U (1 : Γ(C, U)) = δ ∧
      Scheme.Modules.Hom.app e.hom V (1 : Γ(C, V)) = ε := by
  let O : ULift.{u} Bool → C.Opens := fun b => if b.down then V else U
  let d : ∀ b, Γ(M, O b) := fun b => match b with
    | ⟨false⟩ => δ
    | ⟨true⟩ => ε
  have hO : (⨆ b, O b) = ⊤ := by
    change (⨆ b : ULift.{u} Bool, if b.down then V else U) = ⊤
    simpa only [iSup_ulift, iSup_bool_eq, Bool.false_eq_true, if_false, if_true, sup_comm V U] using hcov
  have hd : ∀ b, Scheme.Modules.IsFrameOn (d b) (O b) := by
    rintro ⟨b⟩
    cases b
    · exact hδ
    · exact hε
  have hc : ∀ a b, M.presheaf.map (homOfLE (inf_le_left : O a ⊓ O b ≤ O a)).op (d a) =
      M.presheaf.map (homOfLE (inf_le_right : O a ⊓ O b ≤ O b)).op (d b) := by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b
    · rfl
    · exact hcompat
    · have hh := congrArg (fun z => M.presheaf.map (eqToHom (inf_comm V U)).op z) hcompat.symm
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh
      convert hh using 1 <;> rfl
    · rfl
  obtain ⟨e, he⟩ := glue_frames O hO d hd hc
  exact ⟨e, he ⟨false⟩, he ⟨true⟩⟩

end SheafFrames

section OriginPresentation
open MvPolynomial WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
open HomogeneousLocalization
open P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
variable {F : Type u} [CommRing F] (W : WeierstrassCurve F)

abbrev OriginRing := OriginChartRing W.toProjective

def originScalar : F →+* OriginRing W :=
  (fromZeroRingHom (projModelGradingCR W.toProjective)
    (Submonoid.powers (coord W.toProjective 1))).comp
      (algebraMap F (projModelGradingCR W.toProjective 0))

local instance originAlgebra : Algebra F (OriginRing W) := (originScalar W).toAlgebra

lemma origin_structure : originChartι W.toProjective ≫ projModelStrCR W.toProjective =
    Spec.map (CommRingCat.ofHom (originScalar W)) := by
  rw [projModelStrCR, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

def originPolynomial : MvPolynomial (Fin 2) F :=
  X 1 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 ^ 2 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 * X 1 + C W.a₄ * X 0 * X 1 ^ 2 + C W.a₆ * X 1 ^ 3)

abbrev OriginQuotient := MvPolynomial (Fin 2) F ⧸ Ideal.span {originPolynomial W}

abbrev originQ : MvPolynomial (Fin 2) F →ₐ[F] OriginQuotient W := Ideal.Quotient.mkₐ _ _

lemma origin_relation :
    zOverY W + algebraMap F (OriginRing W) W.a₁ * xOverY W * zOverY W +
      algebraMap F (OriginRing W) W.a₃ * zOverY W ^ 2 =
    xOverY W ^ 3 + algebraMap F (OriginRing W) W.a₂ * xOverY W ^ 2 * zOverY W +
      algebraMap F (OriginRing W) W.a₄ * xOverY W * zOverY W ^ 2 +
      algebraMap F (OriginRing W) W.a₆ * zOverY W ^ 3 :=
  originChart_rel W (RingHom.id _) (fun _ => rfl)

lemma origin_aeval_relation :
    aeval ![xOverY W, zOverY W] (originPolynomial W) = 0 := by
  simpa only [originPolynomial, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using sub_eq_zero.mpr (origin_relation W)

def originFromQuotient : OriginQuotient W →ₐ[F] OriginRing W :=
  Ideal.Quotient.liftₐ _ (aeval ![xOverY W, zOverY W]) (by
    intro p hp
    exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (origin_aeval_relation W)) : Ideal.span {originPolynomial W} ≤
        RingHom.ker (aeval ![xOverY W, zOverY W]).toRingHom) hp)

lemma quotient_relation :
    originQ W (X 1) + algebraMap F (OriginQuotient W) W.a₁ * originQ W (X 0) * originQ W (X 1) +
      algebraMap F (OriginQuotient W) W.a₃ * originQ W (X 1) ^ 2 =
    originQ W (X 0) ^ 3 + algebraMap F (OriginQuotient W) W.a₂ * originQ W (X 0) ^ 2 * originQ W (X 1) +
      algebraMap F (OriginQuotient W) W.a₄ * originQ W (X 0) * originQ W (X 1) ^ 2 +
      algebraMap F (OriginQuotient W) W.a₆ * originQ W (X 1) ^ 3 := by
  have h : originQ W (originPolynomial W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  apply sub_eq_zero.mp
  simpa only [originPolynomial, map_sub, map_add, map_mul, map_pow,
    show ∀ a, originQ W (C a) = algebraMap F (OriginQuotient W) a from fun _ => rfl] using h

def originToQuotient : OriginRing W →ₐ[F] OriginQuotient W :=
  let f := ChartHomAux.chartMap
    W.toProjective (originQ W (X 0)) (originQ W (X 1)) (quotient_relation W)
  { toRingHom := f
    commutes' := by
      intro a
      exact ChartHomAux.chartMap_sc W.toProjective _ _ (quotient_relation W) a }

lemma originToQuotient_x : originToQuotient W (xOverY W) = originQ W (X 0) :=
  ChartHomAux.chartMap_xOverY _ _ _ _

lemma originToQuotient_v : originToQuotient W (zOverY W) = originQ W (X 1) :=
  ChartHomAux.chartMap_zOverY _ _ _ _

@[simp] lemma originFromQuotient_x : originFromQuotient W (originQ W (X 0)) = xOverY W := by
  change aeval ![xOverY W, zOverY W] (X 0) = _
  simp

@[simp] lemma originFromQuotient_v : originFromQuotient W (originQ W (X 1)) = zOverY W := by
  change aeval ![xOverY W, zOverY W] (X 1) = _
  simp

lemma originFromTo : (originFromQuotient W).comp (originToQuotient W) = AlgHom.id F (OriginRing W) := by
  apply AlgHom.coe_ringHom_injective
  apply ringHom_originChartRing_ext W
  · intro a
    change originFromQuotient W (originToQuotient W (algebraMap F (OriginRing W) a)) = _
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · change originFromQuotient W (originToQuotient W (xOverY W)) = xOverY W
    rw [originToQuotient_x, originFromQuotient_x]
  · change originFromQuotient W (originToQuotient W (zOverY W)) = zOverY W
    rw [originToQuotient_v, originFromQuotient_v]

lemma originToFrom : (originToQuotient W).comp (originFromQuotient W) = AlgHom.id F (OriginQuotient W) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change originToQuotient W (originFromQuotient W (originQ W (X 0))) = originQ W (X 0)
    rw [originFromQuotient_x, originToQuotient_x]
  · change originToQuotient W (originFromQuotient W (originQ W (X 1))) = originQ W (X 1)
    rw [originFromQuotient_v, originToQuotient_v]

/-- A presentation of the actual projective Y-chart with its structural scalar map. -/
def originEquiv : OriginRing W ≃ₐ[F] OriginQuotient W :=
  AlgEquiv.ofAlgHom (originToQuotient W) (originFromQuotient W)
    (originToFrom W) (originFromTo W)
def originPolyU : MvPolynomial (Fin 2) F :=
  -(1 + C W.a₁ * X 0 + 2 * C W.a₃ * X 1 - C W.a₂ * X 0 ^ 2 -
    2 * C W.a₄ * X 0 * X 1 - 3 * C W.a₆ * X 1 ^ 2)

def originPolyV : MvPolynomial (Fin 2) F :=
  C W.a₁ * X 1 - 3 * X 0 ^ 2 - 2 * C W.a₂ * X 0 * X 1 - C W.a₄ * X 1 ^ 2

def originPolyTangent : Derivation F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin 2) F) :=
  MvPolynomial.mkDerivation _ (fun i => if i = 0 then originPolyU W else originPolyV W)

lemma originPolyTangent_relation : originPolyTangent W (originPolynomial W) = 0 := by
  simp [originPolynomial, originPolyTangent, originPolyU, originPolyV,
    Derivation.leibniz, pow_succ, smul_eq_mul]
  ring

lemma originPolyTangent_preserves (p : MvPolynomial (Fin 2) F) (hp : originQ W p = 0) :
    originQ W (originPolyTangent W p) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have hz : originQ W (originPolynomial W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  simp [Derivation.leibniz, originPolyTangent_relation, smul_eq_mul]

def originTangent : Derivation F (OriginQuotient W) (OriginQuotient W) :=
  Derivation.liftOfSurjective (f := originQ W) Ideal.Quotient.mk_surjective
    (originPolyTangent_preserves W)

lemma originTangent_u : originTangent W (originQ W (X 0)) = originQ W (originPolyU W) := by
  rw [originTangent, Derivation.liftOfSurjective_apply]
  simp [originPolyTangent]

lemma originTangent_v : originTangent W (originQ W (X 1)) = originQ W (originPolyV W) := by
  rw [originTangent, Derivation.liftOfSurjective_apply]
  simp [originPolyTangent]

lemma origin_derivation_ext {N : Type u} [AddCommGroup N] [Module (OriginQuotient W) N]
    [Module F N] [IsScalarTower F (OriginQuotient W) N]
    (d e : Derivation F (OriginQuotient W) N)
    (hu : d (originQ W (X 0)) = e (originQ W (X 0)))
    (hv : d (originQ W (X 1)) = e (originQ W (X 1))) : d = e := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change d (originQ W p) = e (originQ W p)
  induction p using MvPolynomial.induction_on with
  | C c =>
    change d (algebraMap F (OriginQuotient W) c) = e (algebraMap F (OriginQuotient W) c)
    simp only [Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have hi : d (originQ W (X i)) = e (originQ W (X i)) := by
      fin_cases i
      · exact hu
      · exact hv
    simp only [map_mul, Derivation.leibniz, hp, hi]

lemma origin_differential_relation :
    originQ W (originPolyU W) • KaehlerDifferential.D F (OriginQuotient W) (originQ W (X 1)) =
      originQ W (originPolyV W) • KaehlerDifferential.D F (OriginQuotient W) (originQ W (X 0)) := by
  have h := congrArg (KaehlerDifferential.D F (OriginQuotient W)) (quotient_relation W)
  simp only [map_add, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    Derivation.leibniz_pow, smul_smul] at h
  simp only [originPolyU, originPolyV, map_neg, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  simp only [show ∀ a, originQ W (C a) = algebraMap F (OriginQuotient W) a from fun _ => rfl]
  linear_combination (norm := module) -h

end OriginPresentation

section OriginFrame
open MvPolynomial WeierstrassCurve.DrinfeldGlobal
variable {F : Type u} [Field F] [CharZero F] (W : WeierstrassCurve F)

lemma origin_coprime (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    IsCoprime (originQ W (originPolyU W)) (originQ W (originPolyV W)) := by
  let u := originQ W (X 0)
  let v := originQ W (X 1)
  let a₂ := algebraMap F (OriginQuotient W) W.a₂
  let a₄ := algebraMap F (OriginQuotient W) W.a₄
  let a₆ := algebraMap F (OriginQuotient W) W.a₆
  have he : v = u ^ 3 + a₂ * u ^ 2 * v + a₄ * u * v ^ 2 + a₆ * v ^ 3 := by
    simpa only [h₁, h₃, map_zero, zero_mul, add_zero] using quotient_relation W
  have h2 : IsUnit (2 : OriginQuotient W) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : F) ≠ 0)).map
      (algebraMap F (OriginQuotient W))
  have h3 : IsUnit (3 : OriginQuotient W) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (3 : F) ≠ 0)).map
      (algebraMap F (OriginQuotient W))
  have hp : originQ W (originPolyU W) = -infinityCoefficient a₂ a₄ a₆ u v := by
    simp [originPolyU, h₁, h₃, infinityCoefficient, a₂, a₄, a₆, u, v]
    rfl
  have hq : originQ W (originPolyV W) = -infinitySlope a₂ a₄ u v := by
    simp only [originPolyV, h₁, map_sub, map_mul, map_pow, map_ofNat, map_zero, zero_mul, zero_sub]
    change -(3 * u ^ 2) - 2 * a₂ * u * v - a₄ * v ^ 2 = -(3 * u ^ 2 + 2 * a₂ * u * v + a₄ * v ^ 2)
    ring
  rw [hp, hq]
  exact (infinity_coprime a₂ a₄ a₆ u v he h2 h3).neg_left.neg_right

/-- A regular generating differential on the complete Y-chart, including the origin. -/
lemma origin_quotient_frame (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    ∃! e : DifferentialFrame F (OriginQuotient W),
      KaehlerDifferential.D F (OriginQuotient W) (originQ W (X 0)) =
        originQ W (originPolyU W) • e 1 ∧
      KaehlerDifferential.D F (OriginQuotient W) (originQ W (X 1)) =
        originQ W (originPolyV W) • e 1 :=
  frame_of_coprime _ _ _ _ (origin_coprime W h₁ h₃) (originTangent W)
    (originTangent_u W) (originTangent_v W) (origin_differential_relation W)
    (origin_derivation_ext W)
attribute [local instance] originAlgebra

lemma origin_ring_frame (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    ∃ e : DifferentialFrame F (OriginRing W),
      KaehlerDifferential.D F (OriginRing W) (xOverY W) =
        (-infinityCoefficient (algebraMap F (OriginRing W) W.a₂)
          (algebraMap F (OriginRing W) W.a₄) (algebraMap F (OriginRing W) W.a₆)
          (xOverY W) (zOverY W)) • e 1 ∧
      KaehlerDifferential.D F (OriginRing W) (zOverY W) =
        (-infinitySlope (algebraMap F (OriginRing W) W.a₂)
          (algebraMap F (OriginRing W) W.a₄) (xOverY W) (zOverY W)) • e 1 := by
  obtain ⟨e, he, _⟩ := origin_quotient_frame W h₁ h₃
  let φ := (originEquiv W).symm
  refine ⟨frameTransport φ e, ?_, ?_⟩
  · have h := frameTransport_normalization φ e _ _ he.1
    have hu : φ (originQ W (X 0)) = xOverY W := originFromQuotient_x W
    rw [hu] at h
    convert h using 2
    change -infinityCoefficient _ _ _ _ _ =
      aeval ![xOverY W, zOverY W] (originPolyU W)
    simp [originPolyU, h₁, h₃, infinityCoefficient]
  · have h := frameTransport_normalization φ e _ _ he.2
    have hv : φ (originQ W (X 1)) = zOverY W := originFromQuotient_v W
    rw [hv] at h
    convert h using 2
    change -infinitySlope _ _ _ _ = aeval ![xOverY W, zOverY W] (originPolyV W)
    simp [originPolyV, h₁, infinitySlope]
    ring

end OriginFrame

section ProjectiveOverlap
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
variable {F : Type u} [CommRing F] (W : WeierstrassCurve F)

abbrev OverlapRing := Away (projModelGradingCR W.toProjective)
  (coord W.toProjective 1 * coord W.toProjective 2)

def fromOrigin : OriginRing W →+* OverlapRing W :=
  awayMap (projModelGradingCR W.toProjective) (coord_mem W.toProjective 2) rfl

def fromAffine : ZChartRing W.toProjective →+* OverlapRing W :=
  awayMap (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) (mul_comm _ _)

abbrev overlapInclusion : Spec (CommRingCat.of (OverlapRing W)) ⟶ projModelCR W.toProjective :=
  Proj.awayι (projModelGradingCR W.toProjective) _
    (SetLike.mul_mem_graded (coord_mem W.toProjective 1) (coord_mem W.toProjective 2)) (by decide)

lemma fromOrigin_inclusion : Spec.map (CommRingCat.ofHom (fromOrigin W)) ≫ originChartι W =
    overlapInclusion W := Proj.SpecMap_awayMap_awayι _ _ _ _ _

lemma fromAffine_inclusion : Spec.map (CommRingCat.ofHom (fromAffine W)) ≫ zChartι W.toProjective =
    overlapInclusion W := Proj.SpecMap_awayMap_awayι _ _ _ _ _

lemma overlap_opens : (overlapInclusion W).opensRange =
    (originChartι W).opensRange ⊓ (zChartι W.toProjective).opensRange := by
  simp only [overlapInclusion, originChartι, zChartι, Proj.opensRange_awayι, Proj.basicOpen_mul]

lemma overlap_x : fromAffine W (xOverZ W.toProjective) * fromOrigin W (zOverY W) =
    fromOrigin W (xOverY W) := by
  rw [fromAffine, fromOrigin, xOverZ, xOverY, zOverY]
  ext
  simp only [val_mul, awayMap_mk, Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
  ring

lemma overlap_y : fromAffine W (yOverZ W.toProjective) * fromOrigin W (zOverY W) = 1 := by
  rw [fromAffine, fromOrigin, yOverZ, zOverY]
  ext
  simp only [val_mul, val_one, awayMap_mk, Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, mul_one]
  ring

lemma overlap_v_unit : IsUnit (fromOrigin W (zOverY W)) :=
  isUnit_iff_exists_inv.mpr ⟨fromAffine W (yOverZ W.toProjective), by rw [mul_comm, overlap_y]⟩

lemma projective_cover : (originChartι W).opensRange ⊔ (zChartι W.toProjective).opensRange = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, hy⟩ :=
    P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one.WeierstrassProjModel.srd1_pmsCR_awayι_jointly_surjective W.toProjective x
  fin_cases i
  · exact Or.inl (Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩)
  · exact Or.inr (Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩)

lemma origin_coefficients_map {B : Type u} [CommRing B] (φ : OriginRing W →+* B)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    φ (zOverY W) = φ (xOverY W) ^ 3 +
      φ (originScalar W W.a₂) * φ (xOverY W) ^ 2 * φ (zOverY W) +
      φ (originScalar W W.a₄) * φ (xOverY W) * φ (zOverY W) ^ 2 +
      φ (originScalar W W.a₆) * φ (zOverY W) ^ 3 := by
  have h := congrArg φ (origin_relation W)
  simpa only [h₁, h₃, map_add, map_mul, map_pow, map_zero, zero_mul, add_zero,
    originAlgebra, RingHom.algebraMap_toAlgebra] using h

lemma overlap_frame_agreement {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens)
    (φ : OverlapRing W →+* Γ(C, U)) (δ ε : Γ(f.kaehler, U))
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h2 : IsUnit (2 : Γ(C, U)))
    (hδ : relativeD f U (φ (fromAffine W (xOverZ W.toProjective))) =
      (2 * φ (fromAffine W (yOverZ W.toProjective))) • δ)
    (hεu : relativeD f U (φ (fromOrigin W (xOverY W))) =
      (-infinityCoefficient (φ (fromOrigin W (originScalar W W.a₂)))
        (φ (fromOrigin W (originScalar W W.a₄))) (φ (fromOrigin W (originScalar W W.a₆)))
        (φ (fromOrigin W (xOverY W))) (φ (fromOrigin W (zOverY W)))) • ε)
    (hεv : relativeD f U (φ (fromOrigin W (zOverY W))) =
      (-infinitySlope (φ (fromOrigin W (originScalar W W.a₂)))
        (φ (fromOrigin W (originScalar W W.a₄)))
        (φ (fromOrigin W (xOverY W))) (φ (fromOrigin W (zOverY W)))) • ε) : δ = ε := by
  apply relativeD_overlap f U _ _ _ _ _ _ _ δ ε h2 ((overlap_v_unit W).map φ)
  · simpa only [map_mul] using congrArg φ (overlap_x W)
  · simpa only [map_mul, map_one] using congrArg φ (overlap_y W)
  · exact origin_coefficients_map W (φ.comp (fromOrigin W)) h₁ h₃
  · exact hδ
  · exact hεu
  · exact hεv

end ProjectiveOverlap

section OpenImages
variable {C D : Scheme.{u}} (i : C ⟶ D) [IsOpenImmersion i]

lemma image_inf (U V : C.Opens) : i ''ᵁ (U ⊓ V) = (i ''ᵁ U) ⊓ (i ''ᵁ V) := by
  apply TopologicalSpace.Opens.ext
  exact Set.image_inter i.isOpenEmbedding.injective

lemma image_sup (U V : C.Opens) : i ''ᵁ (U ⊔ V) = (i ''ᵁ U) ⊔ (i ''ᵁ V) := by
  apply TopologicalSpace.Opens.ext
  exact Set.image_union _ _ _
end OpenImages

section GenericCurve
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma generic_kaehler_rank_one (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s) :
    Scheme.Modules.IsLocallyFreeOfRank 1 (genericStructure k M).kaehler := by
  letI := ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.generic_relative_one
    k h3 M hM s hs
  exact ((genericStructure k M).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
local instance zchartAlgebra : Algebra (LaurentSeries k) (ChartRing k r) :=
  (ProjectiveCubicChart.chartScalar k r).toAlgebra

lemma zchart_frame (h3 : 3 ≤ r) (he : Even r) :
    ∃ e : DifferentialFrame (LaurentSeries k) (ChartRing k r),
      KaehlerDifferential.D (LaurentSeries k) (ChartRing k r)
          (WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective) =
        (2 * WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective) • e 1 := by
  obtain ⟨a, ha, hx, hy⟩ := ProjectiveCubicChart.exists_chartEquiv k r
  let φ : ChartRing k r ≃ₐ[LaurentSeries k] CubicRing k r :=
    { a with commutes' := ha }
  obtain ⟨e, he, _⟩ := affine_differential_frame k r h3 he
  refine ⟨frameTransport φ.symm e, ?_⟩
  have h := frameTransport_normalization φ.symm e _ _ he.1
  have hx' : φ.symm (cubicCoordinate k r false) =
      WeierstrassCurve.DrinfeldGlobal.xOverZ (curve k r).toProjective :=
    φ.symm_apply_eq.mpr hx.symm
  have hy' : φ.symm (cubicCoordinate k r true) =
      WeierstrassCurve.DrinfeldGlobal.yOverZ (curve k r).toProjective :=
    φ.symm_apply_eq.mpr hy.symm
  simpa only [map_mul, map_ofNat, hx', hy'] using h

end GenericCurve

section LiftedCharts
open WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (E : C ≅ projectiveCurve k r)

local instance chartInclusion_open : IsOpenImmersion (chartInclusion k r) :=
  CompactifiedCoordinateIsomorphism.chart_open k

abbrev zLeg := chartInclusion k r ≫ E.inv
abbrev yLeg := originChartι (curve k r) ≫ E.inv
abbrev oLeg := overlapInclusion (curve k r) ≫ E.inv

instance zLeg_open : IsOpenImmersion (zLeg k r E) := by
  dsimp [zLeg, chartInclusion]
  infer_instance

abbrev zOpen : C.Opens := zLeg k r E ''ᵁ ⊤
abbrev yOpen : C.Opens := yLeg k r E ''ᵁ ⊤
abbrev oOpen : C.Opens := oLeg k r E ''ᵁ ⊤

lemma lifted_overlap : oOpen k r E = yOpen k r E ⊓ zOpen k r E := by
  simp only [oOpen, yOpen, zOpen, oLeg, yLeg, zLeg, Scheme.Hom.comp_image,
    Scheme.Hom.image_top_eq_opensRange]
  rw [overlap_opens, image_inf]
  rfl

lemma lifted_cover : zOpen k r E ⊔ yOpen k r E = ⊤ := by
  simp only [zOpen, yOpen, zLeg, yLeg, Scheme.Hom.comp_image,
    Scheme.Hom.image_top_eq_opensRange]
  rw [← image_sup]
  have hc : (chartInclusion k r).opensRange ⊔ (originChartι (curve k r)).opensRange = ⊤ := by
    rw [sup_comm]
    exact projective_cover (curve k r)
  rw [hc, Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]

lemma lifted_fromOrigin : oLeg k r E =
    Spec.map (CommRingCat.ofHom (fromOrigin (curve k r))) ≫ yLeg k r E := by
  rw [yLeg, ← Category.assoc, fromOrigin_inclusion]

lemma lifted_fromAffine : oLeg k r E =
    Spec.map (CommRingCat.ofHom (fromAffine (curve k r))) ≫ zLeg k r E := by
  rw [zLeg, ← Category.assoc]
  change overlapInclusion (curve k r) ≫ E.inv =
    (Spec.map (CommRingCat.ofHom (fromAffine (curve k r))) ≫ zChartι (curve k r).toProjective) ≫ E.inv
  rw [fromAffine_inclusion]

lemma lifted_origin_structure (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ projectiveStructure k r = f) :
    yLeg k r E ≫ f = Spec.map (CommRingCat.ofHom (originScalar (curve k r))) := by
  rw [yLeg, ← hE, Category.assoc, E.inv_hom_id_assoc]
  exact origin_structure (curve k r)

lemma lifted_affine_structure (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ projectiveStructure k r = f) :
    zLeg k r E ≫ f = Spec.map (CommRingCat.ofHom (ProjectiveCubicChart.chartScalar k r)) := by
  rw [zLeg, ← hE, Category.assoc, E.inv_hom_id_assoc]
  exact ProjectiveCubicChart.chart_structure k r

abbrev zSection : ChartRing k r ≃+* Γ(C, zOpen k r E) := (chartRingEquiv (zLeg k r E)).symm
abbrev ySection : OriginRing (curve k r) ≃+* Γ(C, yOpen k r E) := (chartRingEquiv (yLeg k r E)).symm
abbrev oSection : OverlapRing (curve k r) ≃+* Γ(C, oOpen k r E) := (chartRingEquiv (oLeg k r E)).symm

local instance lifted_zAlgebra : Algebra (LaurentSeries k) (ChartRing k r) :=
  (ProjectiveCubicChart.chartScalar k r).toAlgebra
attribute [local instance] originAlgebra

lemma lifted_z_frame (h3 : 3 ≤ r) (he : Even r)
    (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ projectiveStructure k r = f) (hΩ : Scheme.Modules.IsInvertible f.kaehler) :
    ∃ δ : Γ(f.kaehler, zOpen k r E), Scheme.Modules.IsFrameOn δ (zOpen k r E) ∧
      relativeD f (zOpen k r E) (zSection k r E (xOverZ (curve k r).toProjective)) =
        (2 * zSection k r E (yOverZ (curve k r).toProjective)) • δ := by
  obtain ⟨e, he⟩ := zchart_frame k h3 he
  obtain ⟨δ, hδ, hn⟩ := frame_on_chart f (zLeg k r E) (lifted_affine_structure k r E f hE) hΩ e
  refine ⟨δ, hδ, ?_⟩
  simpa only [map_mul, map_ofNat] using hn _ _ he

lemma lifted_y_frame (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ projectiveStructure k r = f) (hΩ : Scheme.Modules.IsInvertible f.kaehler) :
    ∃ δ : Γ(f.kaehler, yOpen k r E), Scheme.Modules.IsFrameOn δ (yOpen k r E) ∧
      relativeD f (yOpen k r E) (ySection k r E (xOverY (curve k r))) =
        ySection k r E (-infinityCoefficient (originScalar (curve k r) (curve k r).a₂)
          (originScalar (curve k r) (curve k r).a₄) (originScalar (curve k r) (curve k r).a₆)
          (xOverY (curve k r)) (zOverY (curve k r))) • δ ∧
      relativeD f (yOpen k r E) (ySection k r E (zOverY (curve k r))) =
        ySection k r E (-infinitySlope (originScalar (curve k r) (curve k r).a₂)
          (originScalar (curve k r) (curve k r).a₄) (xOverY (curve k r)) (zOverY (curve k r))) • δ := by
  letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
  obtain ⟨e, heu, hev⟩ := origin_ring_frame (curve k r) rfl rfl
  obtain ⟨δ, hδ, hn⟩ := frame_on_chart f (yLeg k r E) (lifted_origin_structure k r E f hE) hΩ e
  exact ⟨δ, hδ, hn _ _ heu, hn _ _ hev⟩
lemma lifted_frames_agree (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (δ : Γ(f.kaehler, zOpen k r E)) (ε : Γ(f.kaehler, yOpen k r E))
    (hδ : relativeD f (zOpen k r E) (zSection k r E (xOverZ (curve k r).toProjective)) =
      (2 * zSection k r E (yOverZ (curve k r).toProjective)) • δ)
    (hεu : relativeD f (yOpen k r E) (ySection k r E (xOverY (curve k r))) =
      ySection k r E (-infinityCoefficient (originScalar (curve k r) (curve k r).a₂)
        (originScalar (curve k r) (curve k r).a₄) (originScalar (curve k r) (curve k r).a₆)
        (xOverY (curve k r)) (zOverY (curve k r))) • ε)
    (hεv : relativeD f (yOpen k r E) (ySection k r E (zOverY (curve k r))) =
      ySection k r E (-infinitySlope (originScalar (curve k r) (curve k r).a₂)
        (originScalar (curve k r) (curve k r).a₄) (xOverY (curve k r)) (zOverY (curve k r))) • ε) :
    f.kaehler.presheaf.map (homOfLE (inf_le_left : zOpen k r E ⊓ yOpen k r E ≤ zOpen k r E)).op δ =
    f.kaehler.presheaf.map (homOfLE (inf_le_right : zOpen k r E ⊓ yOpen k r E ≤ yOpen k r E)).op ε := by
  have hoz : oOpen k r E ≤ zOpen k r E := (lifted_overlap k r E).le.trans inf_le_right
  have hoy : oOpen k r E ≤ yOpen k r E := (lifted_overlap k r E).le.trans inf_le_left
  have hδ' : relativeD f (zOpen k r E) (zSection k r E (xOverZ (curve k r).toProjective)) =
      zSection k r E (2 * yOverZ (curve k r).toProjective) • δ := by
    simpa only [map_mul, map_ofNat] using hδ
  have hz := chart_normalization_restrict f (zLeg k r E) (oLeg k r E)
    (fromAffine (curve k r)) (lifted_fromAffine k r E) hoz _ _ δ hδ'
  have hyu := chart_normalization_restrict f (yLeg k r E) (oLeg k r E)
    (fromOrigin (curve k r)) (lifted_fromOrigin k r E) hoy _ _ ε hεu
  have hyv := chart_normalization_restrict f (yLeg k r E) (oLeg k r E)
    (fromOrigin (curve k r)) (lifted_fromOrigin k r E) hoy _ _ ε hεv
  let φ := (oSection k r E).toRingHom
  have h2 : IsUnit (2 : Γ(C, oOpen k r E)) := by
    letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
        ((φ.comp (fromOrigin (curve k r))).comp (originScalar (curve k r)))
  have hh := overlap_frame_agreement (curve k r) f (oOpen k r E) φ
    (f.kaehler.presheaf.map (homOfLE hoz).op δ)
    (f.kaehler.presheaf.map (homOfLE hoy).op ε) rfl rfl h2
    (by simpa only [φ, oSection, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul, map_ofNat] using hz)
    (by simpa only [φ, oSection, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, infinityCoefficient, map_neg, map_sub, map_mul, map_pow, map_one, map_ofNat] using hyu)
    (by simpa only [φ, oSection, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, infinitySlope, map_neg, map_add, map_mul, map_pow, map_ofNat] using hyv)
  have hO : zOpen k r E ⊓ yOpen k r E = oOpen k r E :=
    (inf_comm _ _).trans (lifted_overlap k r E).symm
  have ht := congrArg (fun z => f.kaehler.presheaf.map (eqToHom hO).op z) hh
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at ht
  convert ht using 1 <;> rfl

lemma lifted_global_frame (h3 : 3 ≤ r) (he : Even r)
    (f : C ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (hE : E.hom ≫ projectiveStructure k r = f) (hΩ : Scheme.Modules.IsInvertible f.kaehler) :
    ∃ e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ f.kaehler,
      relativeD f (zOpen k r E) (zSection k r E (xOverZ (curve k r).toProjective)) =
        (2 * zSection k r E (yOverZ (curve k r).toProjective)) •
          Scheme.Modules.Hom.app e.hom (zOpen k r E) (1 : Γ(C, zOpen k r E)) := by
  obtain ⟨δ, hδ, hδn⟩ := lifted_z_frame k r E h3 he f hE hΩ
  obtain ⟨ε, hε, hεu, hεv⟩ := lifted_y_frame k r E f hE hΩ
  obtain ⟨e, hez, hey⟩ := glue_two_frames (zOpen k r E) (yOpen k r E) (lifted_cover k r E)
    δ ε hδ hε (lifted_frames_agree k r E f δ ε hδn hεu hεv)
  exact ⟨e, by rw [hez]; exact hδn⟩
end LiftedCharts

section IdealSectionBridge
open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133
open ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionDescentR0134
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
variable {C D : Scheme.{u}}

lemma pulled_apply (f : D ⟶ C) {L : C.Modules}
    (j : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    (U : C.Opens) (v : Γ(L, U)) :
    (pulledInclusion f j).app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f v) =
      f.app U (j.app U v) := by
  rw [Scheme.Modules.app_pullbackLocalSection]
  change (adjoint f (pulledInclusion f j)).app U v = _
  rw [adjoint_pulled]
  rfl

lemma inclusion_app_bijective (U : C.Opens) {L : C.Modules}
    (j : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    [IsIso (pulledInclusion U.ι j)] : Function.Bijective (j.app U) := by
  have hp := (Scheme.Modules.bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff L U).1
  have hq := ConcreteCategory.bijective_of_isIso ((pulledInclusion U.ι j).app (U.ι ⁻¹ᵁ U))
  have hi : IsIso (U.ι.app U) := U.ι.isIso_app U (by rw [Scheme.Opens.opensRange_ι])
  letI := hi
  have hc := hq.comp hp
  have hcomp : (fun a : Γ(L, U) => (pulledInclusion U.ι j).app (U.ι ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection U.ι a)) = (fun a => U.ι.app U (j.app U a)) := by
    funext a
    exact pulled_apply U.ι j U a
  change Function.Bijective (fun a : Γ(L, U) => (pulledInclusion U.ι j).app (U.ι ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection U.ι a)) at hc
  rw [hcomp] at hc
  refine ⟨fun a b h => hc.1 (congrArg (U.ι.app U) h), ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hc.2 (U.ι.app U b)
  exact ⟨a, (ConcreteCategory.bijective_of_isIso (U.ι.app U)).1 ha⟩

lemma local_coordinate_scalar (U V : C.Opens) (hVU : V ≤ U) {L : C.Modules}
    (j q : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    [IsIso (pulledInclusion U.ι j)]
    (a : Γ(C, U))
    (ha : regularValue (pulledInclusion U.ι j) (pulledInclusion U.ι q) = U.topIso.inv a)
    (v : Γ(L, V)) :
    q.app V v = C.presheaf.map (homOfLE hVU).op a * (show Γ(C, V) from j.app V v) := by
  have hq : pulledInclusion U.ι q = pulledInclusion U.ι j ≫ unitScalar (U.topIso.inv a) := by
    apply Scheme.Modules.hom_ext
    intro W
    ext w
    rw [regularValue_spec (pulledInclusion U.ι j) (pulledInclusion U.ι q) W w, ha]
    change _ = Scheme.Modules.Hom.app (unitScalar (U.topIso.inv a)) W ((pulledInclusion U.ι j).app W w)
    rw [unitScalar, ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection_apply]
    exact mul_comm (show Γ(U.toScheme,W) from _ ) _
  have hV : V ≤ U.ι.opensRange := by simpa only [Scheme.Opens.opensRange_ι] using hVU
  calc
    q.app V v = localValue U.ι (pulledInclusion U.ι q) V hV v :=
      (localValue_pulled U.ι q V hV v).symm
    _ = localValue U.ι (pulledInclusion U.ι j ≫ unitScalar (U.topIso.inv a)) V hV v := by rw [hq]
    _ = _ := (localValue_open_scalar U V hVU (pulledInclusion U.ι j) a v).trans
      (congrArg (fun t : Γ(C,V) => C.presheaf.map (homOfLE hVU).op a * t)
        (localValue_pulled U.ι j V hV v))
lemma chart_section_on_open {B : Type u} [CommRing B]
    (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]
    (U : C.Opens) (b : U.toScheme ≅ Spec (CommRingCat.of B))
    (hb : b.hom ≫ i = U.ι) (hU : U ≤ i ''ᵁ ⊤) (x : B) :
    U.topIso.inv (C.presheaf.map (homOfLE hU).op ((chartRingEquiv i).symm x)) =
      b.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) := by
  have hmaps : C.presheaf.map (homOfLE hU).op ≫ U.topIso.inv =
      (i.appIso ⊤).hom ≫ b.hom.appTop := by
    rw [Scheme.Hom.appIso_hom']
    rw [show b.hom.appTop = b.hom.appLE ⊤ ⊤ (by simp) by
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Hom.preimage_top]
      change b.hom.app ⊤ = b.hom.app ⊤ ≫ U.toScheme.presheaf.map (𝟙 (Opposite.op ⊤))
      erw [CategoryTheory.Functor.map_id, Category.comp_id]]
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [hb, Scheme.Opens.ι_appLE]
    change C.presheaf.map _ ≫ C.presheaf.map _ = C.presheaf.map _
    rw [← Functor.map_comp]
    rfl
  have hv := ConcreteCategory.congr_hom hmaps ((chartRingEquiv i).symm x)
  change _ = b.hom.appTop ((i.appIso ⊤).hom ((chartRingEquiv i).symm x)) at hv
  refine hv.trans (congrArg b.hom.appTop ?_)
  change (i.appIso ⊤).hom ((i.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) = _
  exact ConcreteCategory.congr_hom (i.appIso ⊤).inv_hom_id _

lemma frame_section_restrict {F : Type u} [CommRing F]
    (f : C ⟶ Spec (CommRingCat.of F))
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ f.kaehler)
    (U V : C.Opens) (hVU : V ≤ U) :
    f.kaehler.presheaf.map (homOfLE hVU).op
      (Scheme.Modules.Hom.app e.hom U (1 : Γ(C,U))) =
      Scheme.Modules.Hom.app e.hom V (1 : Γ(C,V)) := by
  have h := ConcreteCategory.congr_hom (e.hom.val.naturality (homOfLE hVU).op) (1 : Γ(C,U))
  change Scheme.Modules.Hom.app e.hom V (C.presheaf.map (homOfLE hVU).op (1 : Γ(C,U))) =
    f.kaehler.presheaf.map (homOfLE hVU).op (Scheme.Modules.Hom.app e.hom U (1 : Γ(C,U))) at h
  simpa only [map_one] using h.symm

variable (k : Type u) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma coordinate_iso_value (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha : IsCoordinateIso k M s X Y a)
    (odd : Bool) :
    complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X) =
      a.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv
        (cubicCoordinate k r odd)) := by
  let j := pulledInclusion (complementInclusion k M s)
    (ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ degree odd))
  let φ : Dual k M s (degree odd) := match odd with | true => Y | false => X
  let q := pulledInclusion (complementInclusion k M s) φ
  letI : IsIso j := (ha.2 odd).1
  change regularValue j q = _
  apply regularValue_from_equation j q
  apply Scheme.Modules.hom_ext
  intro U
  ext v
  change q.app U v = Scheme.Modules.Hom.app (unitScalar _) U (j.app U v)
  rw [unitScalar, ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection_apply]
  refine ((ha.2 odd).2 U v).trans ?_
  change (_ : Γ(complementScheme k M s,U)) * _ = (show Γ(complementScheme k M s,U) from j.app U v) * _
  exact mul_comm _ _

lemma generic_coordinate_scalar (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (q : Dual k M s d) (V : (genericScheme k M).Opens) (hV : V ≤ complement k M s)
    (v : Γ(genericPower k M s d,V)) :
    (restrictDual k M s d q).app V v =
      (genericScheme k M).presheaf.map (homOfLE hV).op
        ((complement k M s).topIso.hom (complementCoordinate k M s d q)) *
        (show Γ(genericScheme k M,V) from (genericIdealInclusion k M s d).app V v) := by
  letI : IsIso (pulledInclusion (complement k M s).ι (genericIdealInclusion k M s d)) :=
    generic_complement_inclusion_isIso k M s d
  apply local_coordinate_scalar (complement k M s) V hV (genericIdealInclusion k M s d)
    (restrictDual k M s d q)
  change genericComplementValue k M s d (restrictDual k M s d q) = _
  rw [genericComplementValue_restrict]
  exact (ConcreteCategory.congr_hom (complement k M s).topIso.hom_inv_id _).symm

lemma hom_restrict {L P : C.Modules} (q : L ⟶ P)
    (U V : C.Opens) (hVU : V ≤ U) (v : Γ(L,U)) :
    P.presheaf.map (homOfLE hVU).op (q.app U v) =
      q.app V (L.presheaf.map (homOfLE hVU).op v) := by
  have h := ConcreteCategory.congr_hom (q.val.naturality (homOfLE hVU).op) v
  exact h.symm

lemma frame_restrict_injective [IsIntegral C] {L : C.Modules}
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ L)
    (U V : C.Opens) [Nonempty V] (hVU : V ≤ U) :
    Function.Injective (L.presheaf.map (homOfLE hVU).op) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv U)).1
  apply map_injective_of_isIntegral C (homOfLE hVU)
  exact (hom_restrict e.inv U V hVU x).trans
    ((congrArg (Scheme.Modules.Hom.app e.inv V) h).trans (hom_restrict e.inv U V hVU y).symm)

lemma frame_sections_subsingleton {L : C.Modules}
    (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ L)
    (U : C.Opens) (hU : ¬ Nonempty U) : Subsingleton Γ(L,U) := by
  have he : U = ⊥ := by
    ext x
    exact iff_false_intro (fun hx => hU ⟨⟨x,hx⟩⟩)
  haveI : Subsingleton Γ(C,U) := CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty he)
  letI : Subsingleton Γ((SheafOfModules.unit C.ringCatSheaf : C.Modules),U) :=
    ‹Subsingleton Γ(C,U)›
  exact Function.Injective.subsingleton
    (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv U)).1

lemma nonempty_inter [IsIntegral C] (U V : C.Opens) [Nonempty U] [Nonempty V] :
    Nonempty (U ⊓ V : C.Opens) := by
  have h := nonempty_preirreducible_inter U.isOpen V.isOpen
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U))
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty V))
  exact ⟨⟨h.choose, h.choose_spec⟩⟩

end IdealSectionBridge

section ActualCurveFrame
open WeierstrassCurve.DrinfeldGlobal
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The two local frames give a genuine global frame on the actual generic curve.
The ideal-section formulation of normalization is a subsequent bridge. -/
lemma actual_curve_global_frame (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ∃ (a : complementScheme k M s ≅ cubicScheme k r)
      (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
      (E : genericScheme k M ≅ projectiveCurve k r)
      (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler),
      IsCoordinateIso k M s X Y a ∧ IsChartIso k r c ∧
      IsCompactificationIso k M s hs.1 a c E ∧
      relativeD (genericStructure k M) (zOpen k r E)
          (zSection k r E (xOverZ (curve k r).toProjective)) =
        (2 * zSection k r E (yOverZ (curve k r).toProjective)) •
          Scheme.Modules.Hom.app e.hom (zOpen k r E)
            (1 : Γ(genericScheme k M, zOpen k r E)) := by
  obtain ⟨a, ha, _⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  obtain ⟨c, hc, _⟩ := projective_cubic_chart k r
  obtain ⟨E, hE, _⟩ := compactified_coordinate_isomorphism k r hr h3 T he M hM s hs X Y hX hY a ha c hc
  have hΩ := (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
    (generic_kaehler_rank_one k h3 M hM s hs)
  obtain ⟨e, he⟩ := lifted_global_frame k r E h3 he (genericStructure k M) hE.1 hΩ
  exact ⟨a, c, E, e, ha, hc, hE, he⟩
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

lemma complement_chart_factor (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k))
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : IsCompactificationIso k M s hs a c E) :
    (a ≪≫ c).hom ≫ zLeg k r E = (complement k M s).ι := by
  change (a.hom ≫ c.hom) ≫ chartInclusion k r ≫ E.inv = _
  rw [← Category.assoc, Category.assoc a.hom c.hom, ← hE.2.1, Category.assoc, E.hom_inv_id, Category.comp_id]

lemma complement_z_le (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k))
    (a : complementScheme k M s ≅ cubicScheme k r)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r)))
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : IsCompactificationIso k M s hs a c E) :
    complement k M s ≤ zOpen k r E := by
  have h := complement_chart_factor k M s hs a c E hE
  have hh : ((a ≪≫ c).hom ≫ zLeg k r E).opensRange = complement k M s := by
    simp only [h, Scheme.Opens.opensRange_ι]
  rw [Scheme.Hom.opensRange_comp_of_isIso] at hh
  exact (show complement k M s = zOpen k r E by
    simpa only [zOpen, Scheme.Hom.image_top_eq_opensRange] using hh.symm).le

lemma complement_chart_coordinate (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (X : Dual k M s 2) (Y : Dual k M s 3)
    (a : complementScheme k M s ≅ cubicScheme k r) (ha : IsCoordinateIso k M s X Y a)
    (c : cubicScheme k r ≅ Spec (CommRingCat.of (ChartRing k r))) (hc : IsChartIso k r c)
    (E : genericScheme k M ≅ projectiveCurve k r)
    (hE : IsCompactificationIso k M s hs a c E) (odd : Bool) :
    (genericScheme k M).presheaf.map (homOfLE (complement_z_le k M s hs a c E hE)).op
      (zSection k r E (if odd then yOverZ (curve k r).toProjective else xOverZ (curve k r).toProjective)) =
      (complement k M s).topIso.hom
        (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) := by
  apply (ConcreteCategory.bijective_of_isIso (complement k M s).topIso.inv).1
  rw [show (complement k M s).topIso.inv ((complement k M s).topIso.hom
    (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X))) =
    complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X) from
      ConcreteCategory.congr_hom (complement k M s).topIso.hom_inv_id _]
  rw [coordinate_iso_value k M s X Y a ha odd]
  have ht := chart_section_on_open (zLeg k r E) (complement k M s) (a ≪≫ c)
    (complement_chart_factor k M s hs a c E hE) (complement_z_le k M s hs a c E hE)
    (if odd then yOverZ (curve k r).toProjective else xOverZ (curve k r).toProjective)
  refine ht.trans ?_
  change (a.hom ≫ c.hom).appTop _ = _
  rw [Scheme.Hom.comp_appTop]
  change a.hom.appTop (c.hom.appTop _) = _
  rw [hc.2 odd]

lemma actual_complement_frame (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ∃ e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler,
      relativeD (genericStructure k M) (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X)) =
      (2 * (complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) •
        Scheme.Modules.Hom.app e.hom (complement k M s) (1 : Γ(genericScheme k M,complement k M s)) := by
  obtain ⟨a,c,E,e,ha,hc,hE,hn⟩ := actual_curve_global_frame k h3 he M hM s hs X Y hX hY
  refine ⟨e, ?_⟩
  have h := relativeD_normalization_restrict (genericStructure k M) (zOpen k r E)
    (complement_z_le k M s hs.1 a c E hE) _ _ _ hn
  erw [map_mul, map_ofNat, frame_section_restrict (genericStructure k M) e (zOpen k r E)
    (complement k M s) (complement_z_le k M s hs.1 a c E hE)] at h
  have hx := complement_chart_coordinate k M s hs.1 X Y a ha c hc E hE false
  have hy := complement_chart_coordinate k M s hs.1 X Y a ha c hc E hE true
  simp only [Bool.false_eq_true, ↓reduceIte, degree] at hx hy
  erw [hx,hy] at h
  exact h

lemma complement_cleared (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler)
    (hn : relativeD (genericStructure k M) (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X)) =
      (2 * (complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) •
        Scheme.Modules.Hom.app e.hom (complement k M s) (1 : Γ(genericScheme k M,complement k M s)))
    (V : (genericScheme k M).Opens) (hV : V ≤ complement k M s)
    (a : Γ(genericPower k M s 2,V)) (b : Γ(genericPower k M s 3,V)) :
    let ja : Γ(genericScheme k M,V) := (genericIdealInclusion k M s 2).app V a
    let jb : Γ(genericScheme k M,V) := (genericIdealInclusion k M s 3).app V b
    let xa : Γ(genericScheme k M,V) := (restrictDual k M s 2 X).app V a
    let yb : Γ(genericScheme k M,V) := (restrictDual k M s 3 Y).app V b
    jb • (ja • differentialAt k M V xa - xa • differentialAt k M V ja) =
      (2 * yb * ja ^ 2) • Scheme.Modules.Hom.app e.hom V (1 : Γ(genericScheme k M,V)) := by
  have h := relativeD_normalization_restrict (genericStructure k M) (complement k M s) hV _ _ _ hn
  erw [map_mul, map_ofNat, frame_section_restrict (genericStructure k M) e (complement k M s) V hV] at h
  have hx := generic_coordinate_scalar k M s 2 X V hV a
  have hy := generic_coordinate_scalar k M s 3 Y V hV b
  dsimp only [differentialAt]
  erw [hx,hy]
  exact relativeD_cleared (genericStructure k M) V _ _ _ _ _ h

lemma global_cleared (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler)
    (hn : relativeD (genericStructure k M) (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X)) =
      (2 * (complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) •
        Scheme.Modules.Hom.app e.hom (complement k M s) (1 : Γ(genericScheme k M,complement k M s))) :
    IsGlobalDifferentialFrame k M s X Y e := by
  letI := generic_integral k h3 M hM
  letI := complement_nonempty k h3 M hM s hs
  intro U a b
  dsimp only
  by_cases hU : Nonempty U
  · letI := hU
    let V := complement k M s ⊓ U
    letI : Nonempty V := nonempty_inter (complement k M s) U
    apply frame_restrict_injective e U V inf_le_right
    have h := complement_cleared k M s X Y e hn V inf_le_left
      ((genericPower k M s 2).presheaf.map (homOfLE (show V ≤ U from inf_le_right)).op a)
      ((genericPower k M s 3).presheaf.map (homOfLE (show V ≤ U from inf_le_right)).op b)
    dsimp only [differentialAt] at h ⊢
    simp only [Scheme.Modules.map_smul, map_sub, map_mul, map_pow, map_ofNat,
      relativeD_restrict, frame_section_restrict]
    have hj2 := hom_restrict (genericIdealInclusion k M s 2) U V inf_le_right a
    have hj3 := hom_restrict (genericIdealInclusion k M s 3) U V inf_le_right b
    have hq2 := hom_restrict (restrictDual k M s 2 X) U V inf_le_right a
    have hq3 := hom_restrict (restrictDual k M s 3 Y) U V inf_le_right b
    change (genericScheme k M).presheaf.map _ _ = _ at hj2 hj3 hq2 hq3
    erw [hj2,hj3,hq2,hq3]
    exact h
  · letI := frame_sections_subsingleton e U hU
    exact Subsingleton.elim _ _

lemma affine_y_nonzero (h3 : 3 ≤ r) (he : Even r) [Nontrivial (CubicRing k r)] :
    cubicCoordinate k r true ≠ 0 := by
  intro h
  have hd : cubicDerivative k r = 0 := by
    rw [← AffineFrame.tangent_y, h, map_zero]
  have hc := AffineFrame.coprime k r h3 he
  obtain ⟨a,b,hab⟩ := hc
  rw [h,hd,mul_zero,mul_zero,mul_zero,zero_add] at hab
  exact zero_ne_one hab

lemma complement_y_nonzero (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    (complement k M s).topIso.hom (complementCoordinate k M s 3 Y) ≠ 0 := by
  letI := generic_integral k h3 M hM
  letI := complement_nonempty k h3 M hM s hs
  obtain ⟨a,ha,_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  let φ : CubicRing k r →+* Γ(genericScheme k M,complement k M s) :=
    (complement k M s).topIso.hom.hom.comp
      (a.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv.hom)
  letI : Nontrivial (CubicRing k r) := φ.domain_nontrivial
  have hinj : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (complement k M s).topIso.hom).1.comp
      ((ConcreteCategory.bijective_of_isIso a.hom.appTop).1.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (CubicRing k r))).inv).1)
  have hv := coordinate_iso_value k M s X Y a ha true
  change complementCoordinate k M s 3 Y = _ at hv
  rw [hv]
  exact fun h => affine_y_nonzero k h3 he (hinj (h.trans φ.map_zero.symm))

open ArithmeticThetaPolygonCartierR0133.CanonicalCartierLineReductionR0133

lemma normalization_from_predicate (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler)
    (he : IsGlobalDifferentialFrame k M s X Y e) :
    relativeD (genericStructure k M) (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 2 X)) =
      (2 * (complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) •
        Scheme.Modules.Hom.app e.hom (complement k M s) (1 : Γ(genericScheme k M,complement k M s)) := by
  let U := complement k M s
  letI : IsIso (pulledInclusion U.ι (genericIdealInclusion k M s 2)) :=
    generic_complement_inclusion_isIso k M s 2
  letI : IsIso (pulledInclusion U.ι (genericIdealInclusion k M s 3)) :=
    generic_complement_inclusion_isIso k M s 3
  obtain ⟨a,ha⟩ := (inclusion_app_bijective U (genericIdealInclusion k M s 2)).2 (1 : Γ(genericScheme k M,U))
  obtain ⟨b,hb⟩ := (inclusion_app_bijective U (genericIdealInclusion k M s 3)).2 (1 : Γ(genericScheme k M,U))
  have hx := generic_coordinate_scalar k M s 2 X U le_rfl a
  have hy := generic_coordinate_scalar k M s 3 Y U le_rfl b
  have hid : (genericScheme k M).presheaf.map
      (homOfLE (show U ≤ U from le_rfl)).op = 𝟙 _ := by
    change (genericScheme k M).presheaf.map (𝟙 (Opposite.op U)) = 𝟙 _
    exact (genericScheme k M).presheaf.map_id (Opposite.op U)
  erw [ha,hid] at hx
  erw [hb,hid] at hy
  change (restrictDual k M s 2 X).app U a =
    U.topIso.hom (complementCoordinate k M s 2 X) * (1 : Γ(genericScheme k M,U)) at hx
  change (restrictDual k M s 3 Y).app U b =
    U.topIso.hom (complementCoordinate k M s 3 Y) * (1 : Γ(genericScheme k M,U)) at hy
  rw [mul_one] at hx hy
  have h := he U a b
  dsimp only [differentialAt] at h
  erw [ha,hb,hx,hy,relativeD_one] at h
  simpa only [one_smul,smul_zero,sub_zero,one_pow,mul_one,op_id,CategoryTheory.Functor.map_id,ConcreteCategory.id_apply] using h

lemma normalized_frame_unique (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (e e' : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
        (genericStructure k M).kaehler)
    (hn : IsGlobalDifferentialFrame k M s X Y e)
    (hn' : IsGlobalDifferentialFrame k M s X Y e') : e' = e := by
  letI := generic_integral k h3 M hM
  letI := complement_nonempty k h3 M hM s hs
  let U := complement k M s
  let y : Γ(genericScheme k M,U) := U.topIso.hom (complementCoordinate k M s 3 Y)
  have hy : y ≠ 0 := complement_y_nonzero k h3 he M hM s hs X Y hX hY
  have h2 : (2 : Γ(genericScheme k M,U)) ≠ 0 := by
    letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
    letI : Algebra (LaurentSeries k) Γ(genericScheme k M,U) := (genericStructure k M).sectionsAlgebra U
    have hi : IsUnit (2 : Γ(genericScheme k M,U)) := by
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
          (algebraMap (LaurentSeries k) Γ(genericScheme k M,U))
    exact hi.ne_zero
  have hmul : (2*y) • Scheme.Modules.Hom.app e'.hom U (1 : Γ(genericScheme k M,U)) =
      (2*y) • Scheme.Modules.Hom.app e.hom U (1 : Γ(genericScheme k M,U)) :=
    (normalization_from_predicate k M s X Y e' hn').symm.trans
      (normalization_from_predicate k M s X Y e hn)
  have hδ : Scheme.Modules.Hom.app e'.hom U (1 : Γ(genericScheme k M,U)) =
      Scheme.Modules.Hom.app e.hom U (1 : Γ(genericScheme k M,U)) := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv U)).1
    have hh := congrArg (Scheme.Modules.Hom.app e.inv U) hmul
    rw [Scheme.Modules.Hom.app_smul,Scheme.Modules.Hom.app_smul] at hh
    change (2*y) * (show Γ(genericScheme k M,U) from Scheme.Modules.Hom.app e.inv U _) =
      (2*y) * (show Γ(genericScheme k M,U) from Scheme.Modules.Hom.app e.inv U _) at hh
    exact @mul_left_cancel₀ Γ(genericScheme k M,U) _ _ _ (2*y)
      (show Γ(genericScheme k M,U) from Scheme.Modules.Hom.app e.inv U _)
      (show Γ(genericScheme k M,U) from Scheme.Modules.Hom.app e.inv U _) (mul_ne_zero h2 hy) hh
  apply Iso.ext
  apply unit_hom_ext
  apply frame_restrict_injective e ⊤ U le_top
  erw [frame_section_restrict (genericStructure k M) e' ⊤ U le_top,
    frame_section_restrict (genericStructure k M) e ⊤ U le_top]
  exact hδ

end ActualCurveFrame

end GlobalNormalizedDifferential
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaGenericEvaluationR0140

/-- The unique everywhere generating differential on the actual generic curve,
with the cleared normalization for every local section of the actual ideal powers. -/
theorem global_normalized_differential (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ∃! e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
      (genericStructure k M).kaehler, IsGlobalDifferentialFrame k M s X Y e := by
  obtain ⟨e,hn⟩ := GlobalNormalizedDifferential.actual_complement_frame k h3 he M hM s hs X Y hX hY
  have heN := GlobalNormalizedDifferential.global_cleared k h3 M hM s hs X Y e hn
  exact ⟨e,heN,fun e' he' => GlobalNormalizedDifferential.normalized_frame_unique
    k h3 he M hM s hs X Y hX hY e e' heN he'⟩

end ArithmeticThetaCompactifiedDifferentialR0145

#print axioms ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.origin_ring_frame
#print axioms ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.lifted_global_frame
#print axioms ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.actual_curve_global_frame

#print axioms ArithmeticThetaCompactifiedDifferentialR0145.global_normalized_differential
