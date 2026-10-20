module

public import PointedHodgeFunctorialityR0172
public import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
noncomputable section
universe u

namespace ArithmeticThetaRelativeIsogenyHodgeR0172
namespace RelativeMultiplicationHodgeWeight
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaTensorPower

/-- The actual multiplication morphism fixes the specified origin, including at zero. -/
theorem multiplication_origin (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G) (m : ℕ) :
    origin R W ≫ G.schemeNsmul m = origin R W := by
  have ho : (G.one (𝟙 _)).val = origin R W := by
    simpa only [Category.id_comp] using hG.1 (𝟙 _)
  rw [← ho, ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
    G.nsmul_unit]

/-- Pointed data constructed from the actual relative group multiplication. -/
def multiplicationPointed (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G) (m : ℕ) : PointedMap R W W where
  map := G.schemeNsmul m
  over_eq := G.schemeNsmul_over m
  origin_eq := multiplication_origin R W G hG m

theorem multiplicationPointed_map (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G) (m : ℕ) :
    (multiplicationPointed R W G hG m).map = G.schemeNsmul m := rfl

/-- Equality of actual scheme maps determines the pointed structure. -/
theorem pointedMap_ext {R : Type u} [CommRing R] {W V : WeierstrassCurve R}
    (f g : PointedMap R W V) (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The zeroth tensor power is the identity even for zero multiplication. -/
theorem power_weight_zero_exponent (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G) (m : ℕ)
    (U : (Base R).Opens) (s : Γ(HodgePower R W 0,U)) :
    (powerMap (multiplicationPointed R W G hG m) 0).app U s =
      (m : Γ(Base R,U))^0 • s := by
  rw [pow_zero, one_smul]
  rfl

/-- Multiplication by one has weight one on every actual tensor power. -/
theorem power_weight_one (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (n : ℕ) (U : (Base R).Opens) (s : Γ(HodgePower R W n,U)) :
    (powerMap (multiplicationPointed R W G hG 1) n).app U s =
      (1 : Γ(Base R,U))^n • s := by
  have hpoint : multiplicationPointed R W G hG 1 = PointedMap.identity R W := by
    apply pointedMap_ext
    change G.schemeNsmul 1 = 𝟙 _
    unfold WeierstrassProjModel.RelativeGroupLaw.schemeNsmul
    rw [G.nsmul_one_apply]
  rw [hpoint, (pointed_hodge_functoriality R W W W
    (PointedMap.identity R W) (PointedMap.identity R W) n).2, one_pow, one_smul]
  rfl

open ArithmeticThetaCompactifiedDifferentialR0145 (relativeD)
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange

/-- Relative differentiation over the base vanishes on every open of the base. -/
theorem base_relativeD_zero (R : Type u) [CommRing R]
    (U : (Base R).Opens) (a : Γ(Base R,U)) :
    relativeD (𝟙 (Base R)) U a = 0 := by
  apply ((𝟙 (Base R) : Base R ⟶ Base R).kaehler).isSheaf.section_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V ≤ U := hVU
  refine ⟨V, hle, hxV, ?_⟩
  rw [relativeD_restrict (𝟙 (Base R)) U hle a, map_zero]
  letI := (𝟙 (Base R) : Base R ⟶ Base R).sectionsAlgebra V
  letI := RelativeConormalHodgeGenerator.base_sections_unramified R V hV
  change (𝟙 (Base R) : Base R ⟶ Base R).kaehlerToSectionsₗ V (KaehlerDifferential.D R Γ(Base R,V) _) = 0
  rw [Subsingleton.elim (KaehlerDifferential.D R Γ(Base R,V) _) 0]
  exact map_zero ((𝟙 (Base R) : Base R ⟶ Base R).kaehlerToSectionsₗ V)

/-- A function pulled back from the base has zero relative differential. -/
theorem structure_relativeD_zero {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Base R) (U : (Base R).Opens) (a : Γ(Base R,U)) :
    relativeD p (p ⁻¹ᵁ U) (p.app U a) = 0 := by
  have h := differentialMap_D (𝟙 (Base R)) p p (by simp) U a
  rw [base_relativeD_zero, Scheme.Modules.pullbackLocalSection_zero, map_zero] at h
  exact h.symm

/-- Zero multiplication is the actual composite through the origin section. -/
theorem multiplicationPointed_zero_map (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G) :
    (multiplicationPointed R W G hG 0).map = structureMap R W ≫ origin R W := by
  change G.schemeNsmul 0 = _
  unfold WeierstrassProjModel.RelativeGroupLaw.schemeNsmul
  rw [G.nsmul_zero]
  exact hG.1 _

/-- The local differential of a pullback through the zero endomorphism vanishes. -/
theorem zero_localDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (G : Law R W) (hG : IsOriginLaw R W G)
    (U : (Curve R W).Opens) (a : Γ(Curve R W,U)) :
    localDifferential R W ((multiplicationPointed R W G hG 0).map ⁻¹ᵁ U)
      ((multiplicationPointed R W G hG 0).map.app U a) = 0 := by
  rw [multiplicationPointed_zero_map]
  change Scheme.Modules.pullbackLocalSection (origin R W)
    (relativeD (structureMap R W) ((structureMap R W) ⁻¹ᵁ ((origin R W) ⁻¹ᵁ U))
      ((structureMap R W).app _ ((origin R W).app U a))) = 0
  rw [structure_relativeD_zero, Scheme.Modules.pullbackLocalSection_zero]

attribute [local irreducible] origin structureMap in
/-- The specified Hodge differential map of zero multiplication is zero. -/
theorem hodgeMap_zero (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) :
    hodgeMap (multiplicationPointed R W G hG 0) = 0 := by
  apply hom_ext_frames
  intro x
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  obtain ⟨U,a,hx,hframe⟩ := exists_exact_differential_frame (structureMap R W) ((origin R W) x)
  refine ⟨origin R W ⁻¹ᵁ U, localDifferential R W U a, hx,
    pullback_frame (origin R W) (structureMap R W).kaehler (relativeD _ U a) hframe, ?_⟩
  have h := PointedHodgeFunctoriality.hodgeMap_D (multiplicationPointed R W G hG 0)
    U a (origin R W ⁻¹ᵁ U) le_rfl
    (PointedHodgeFunctoriality.pointed_preimage (origin R W) (origin R W)
      (multiplicationPointed R W G hG 0).map (multiplicationPointed R W G hG 0).origin_eq U)
  rw [res_refl, zero_localDifferential] at h
  simpa [res] using h

/-- Natural-number multiplication of a sheaf morphism evaluates sectionwise. -/
theorem nsmul_app {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (m : ℕ) (U : X.Opens) (s : Γ(M,U)) :
    (m • f).app U s = m • f.app U s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, Scheme.Modules.Hom.add_app]
    change (m • f).app U s + f.app U s = _
    rw [ih, succ_nsmul]

/-- Tensorization propagates a proved weight-one formula to every tensor exponent.
The differential formula remains a separate obligation; no scalar behavior is
included in the pointed-map definition. -/
theorem power_weight_of_hodge_weight
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (f : PointedMap R W W) (m : ℕ)
    (h : ∀ (U : (Base R).Opens) (s : Γ(Hodge R W,U)),
      (hodgeMap f).app U s = (m : Γ(Base R,U)) • s)
    (n : ℕ) (U : (Base R).Opens) (s : Γ(HodgePower R W n,U)) :
    (powerMap f n).app U s = (m : Γ(Base R,U))^n • s := by
  have heq : powerMap f n = (m^n) • 𝟙 (HodgePower R W n) := by
    apply PointedHodgeFunctoriality.power_ext R W n
    intro V a
    change (tensorMap (hodgeMap f) n).app _
      (tensorPowerSection (Base R) (Hodge R W) n _ (localDifferential R W V a)) = _
    rw [PointedHodgeFunctoriality.tensorMap_section, h]
    rw [InitialHodgeSection.tensor_smul, nsmul_app]
    change (m : Γ(Base R,origin R W ⁻¹ᵁ V))^n • _ = (m^n) • _
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rfl
  rw [heq, nsmul_app]
  change (m^n) • s = (m : Γ(Base R,U))^n • s
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- Zero multiplication has weight zero in positive degree and weight one in
degree zero, with the same formula on all opens, including the empty open. -/
theorem power_weight_zero (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (n : ℕ) (U : (Base R).Opens) (s : Γ(HodgePower R W n,U)) :
    (powerMap (multiplicationPointed R W G hG 0) n).app U s =
      (0 : Γ(Base R,U))^n • s := by
  apply power_weight_of_hodge_weight R W (multiplicationPointed R W G hG 0) 0
  intro V v
  rw [hodgeMap_zero]
  simp

/-- The actual local Hodge differential, as an additive map. -/
def localDifferentialAddHom (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) : Γ(Curve R W,U) →+ Γ(Hodge R W,origin R W ⁻¹ᵁ U) where
  toFun := localDifferential R W U
  map_zero' := by simp only [localDifferential, relativeD_zero,
    Scheme.Modules.pullbackLocalSection_zero]
  map_add' a b := by simp only [localDifferential, relativeD_add,
    Scheme.Modules.pullbackLocalSection_add]

/-- The Hodge differential kills the square of the actual origin kernel.
This compares the ring-theoretic first-order quotient with the specified sheaf
derivation, without choosing a coefficient or a frame. -/
theorem localDifferential_kerSquare (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (a : Γ(Curve R W,U))
    (ha : a ∈ (RingHom.ker ((origin R W).app U).hom)^2) :
    localDifferential R W U a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro a ha b hb
    have ha' := RingHom.mem_ker.mp ha
    have hb' := RingHom.mem_ker.mp hb
    simp only [localDifferential, relativeD_mul, Scheme.Modules.pullbackLocalSection_add,
      Scheme.Modules.pullbackLocalSection_smul, ha', hb', zero_smul, add_zero]
  · intro a b ha hb
    change localDifferentialAddHom R W U (a+b) = 0
    rw [map_add]
    change localDifferential R W U a + localDifferential R W U b = 0
    rw [ha, hb, add_zero]

/-- Congruent functions in the actual first-order neighborhood have the same
Hodge differential. -/
theorem localDifferential_congr_kerSquare (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) (U : (Curve R W).Opens) (a b : Γ(Curve R W,U))
    (h : a-b ∈ (RingHom.ker ((origin R W).app U).hom)^2) :
    localDifferential R W U a = localDifferential R W U b := by
  have H := localDifferential_kerSquare R W U (a-b) h
  change localDifferentialAddHom R W U (a-b) = 0 at H
  rw [map_sub, sub_eq_zero] at H
  exact H

/-- Projection from the actual first-order quotient to the section ring. -/
def squareKernelProjection {A S : Type u} [CommRing A] [CommRing S] (ε : A →+* S) :
    A ⧸ (RingHom.ker ε)^2 →+* S :=
  Ideal.Quotient.lift _ ε (fun a ha => RingHom.mem_ker.mp
    ((Ideal.pow_le_self (by omega : 2 ≠ 0)) ha))

theorem squareKernelProjection_surjective {A S : Type u} [CommRing A] [CommRing S]
    (ε : A →+* S) (hε : Function.Surjective ε) :
    Function.Surjective (squareKernelProjection ε) := by
  intro s
  obtain ⟨a, rfl⟩ := hε s
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem squareKernelProjection_ker_sq {A S : Type u} [CommRing A] [CommRing S]
    (ε : A →+* S) : RingHom.ker (squareKernelProjection ε)^2 = ⊥ := by
  rw [squareKernelProjection, Ideal.ker_quotient_lift, ← Ideal.map_pow,
    Ideal.map_quotient_self]

/-- The actual Hodge differential factors through the first-order origin
neighborhood because it annihilates the square of its kernel ideal. -/
def firstOrderDifferential (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) :
    Γ(Curve R W,U) ⧸ (RingHom.ker ((origin R W).app U).hom)^2 →+
      Γ(Hodge R W,origin R W ⁻¹ᵁ U) :=
  QuotientAddGroup.lift _ (localDifferentialAddHom R W U)
    (localDifferential_kerSquare R W U)

theorem firstOrderDifferential_mk (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (a : Γ(Curve R W,U)) :
    firstOrderDifferential R W U (Ideal.Quotient.mk _ a) = localDifferential R W U a := rfl

/-- The factorized differential kills genuine base scalars, with the scalar
structure induced by the given curve's structural morphism. -/
theorem firstOrderDifferential_base (R : Type u) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (r : R) :
    letI := (structureMap R W).sectionsAlgebra U
    firstOrderDifferential R W U
      (algebraMap R (Γ(Curve R W,U) ⧸ (RingHom.ker ((origin R W).app U).hom)^2) r) = 0 := by
  letI := (structureMap R W).sectionsAlgebra U
  change localDifferential R W U (algebraMap R Γ(Curve R W,U) r) = 0
  unfold localDifferential relativeD
  rw [Derivation.map_algebraMap]
  change Scheme.Modules.pullbackLocalSection (origin R W)
    ((structureMap R W).kaehlerToSectionsₗ U 0) = 0
  rw [map_zero, Scheme.Modules.pullbackLocalSection_zero]


open NeronModelInfra
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian.RelativeGroupLaw

set_option backward.isDefEq.respectTransparency false in
/-- The first-order weight of the actual multiplication map on an affine
neighborhood of the identity. The two ring maps are pinned to their scheme
maps; the additive readout kills base scalars, as does a square-zero component. -/
theorem square_zero_weight
    {R : Type u} [CommRing R] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    (G : GoodReductionJacobian.RelativeGroupLaw R p)
    (B : CommRingCat.{u}) [Algebra R B] (ι : Spec B ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (he : Set.range (G.one (𝟙 _)).val.base ⊆ Set.range ι.base)
    {C D : CommRingCat.{u}} (q : C ⟶ D) (hq : Function.Surjective q)
    (hq2 : RingHom.ker q.hom ^ 2 = ⊥)
    (t : Spec C ⟶ Spec (CommRingCat.of R)) [Algebra R C]
    (ht : algebraMap R C = (Spec.preimage t).hom)
    (k : SchemeHomOver t p)
    (hk : Spec.map q ≫ k.val = (G.one (Spec.map q ≫ t)).val)
    (m : ℕ) (κ κm : B ⟶ C)
    (hκ : Spec.map κ ≫ ι = k.val)
    (hκm : Spec.map κm ≫ ι = k.val ≫ G.schemeNsmul m)
    {M : Type u} [AddCommGroup M] (δ : C →+ M)
    (hδ : ∀ r : R, δ (algebraMap R C r) = 0) (b : B) :
    δ (κm.hom b) = m • δ (κ.hom b) := by
  have hk' : KwIsKerElt G q t k := Subtype.ext hk
  have hkm := kw_rglcktfm_isKerElt_nsmul G q t hk' m
  have ring_eq (l : SchemeHomOver t p) (hl : KwIsKerElt G q t l)
      (χ : B ⟶ C) (hχ : Spec.map χ ≫ ι = l.val) :
      χ = kwKerRing G B ι he q hq hq2 t l hl := by
    apply Spec.map_injective
    apply (cancel_mono ι).mp
    exact hχ.trans (kw_rglcktfm_map_kerRing G B ι he q hq hq2 t l hl).symm
  have hκ' := ring_eq k hk' κ hκ
  have hκm' := ring_eq (G.nsmul t m k) hkm κm
    (hκm.trans (nsmul_coe_eq_comp_schemeNsmul G m k).symm)
  have H := congrArg δ (kw_rglcktfm_kerAlg_nsmul_sub G B ι hι he q hq hq2 t ht k hk' m b)
  rw [kw_rglcktfm_kerAlg_one G B ι hι he q hq hq2 t ht] at H
  have hzero : δ (kwTrivLift (kwAug G B ι hι he) b) = 0 := by
    exact hδ _
  simp only [map_sub, map_nsmul, hzero, sub_zero] at H
  rw [hκ', hκm']
  exact H

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication acts by the natural-number scalar on every tangent vector
valued in any module over the base ring, read in the actual affine chart. -/
theorem tangent_weight
    {R : Type u} [CommRing R] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    (G : GoodReductionJacobian.RelativeGroupLaw R p)
    (B : CommRingCat.{u}) [Algebra R B] (ι : Spec B ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (ε : B →ₐ[R] R) (hε : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ ι = (G.one (𝟙 _)).val)
    (M : Type u) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (κ : B →ₐ[R] TrivSqZeroExt R M) (hκ : ∀ b, (κ b).fst = ε b)
    (m : ℕ) (κm : B →ₐ[R] TrivSqZeroExt R M)
    (hκm : Spec.map (CommRingCat.ofHom κm.toRingHom) ≫ ι =
      (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ ι) ≫ G.schemeNsmul m)
    (b : B) : (κm b).snd = m • (κ b).snd := by
  let C := CommRingCat.of (TrivSqZeroExt R M)
  let q : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom
  let t : Spec C ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R M)))
  have ht : algebraMap R C = (Spec.preimage t).hom := by
    rw [Spec.preimage_map]
    rfl
  let k : SchemeHomOver t p := ⟨Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ ι, by
    rw [Category.assoc, hι, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext κ.comp_algebraMap)⟩
  have he : Set.range (G.one (𝟙 _)).val.base ⊆ Set.range ι.base := by
    rw [← hε]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hq : Function.Surjective q := TrivSqZeroExt.fst_surjective
  have hq2 : RingHom.ker q.hom ^ 2 = ⊥ := TrivSqZeroExt.kerIdeal_sq R M
  have hqt : Spec.map q ≫ t = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    rfl
  have hk : Spec.map q ≫ k.val = (G.one (Spec.map q ≫ t)).val := by
    change Spec.map q ≫ (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ ι) = _
    rw [← Category.assoc, ← Spec.map_comp]
    have heq : CommRingCat.ofHom κ.toRingHom ≫ q = CommRingCat.ofHom ε.toRingHom := by
      ext a
      exact hκ a
    rw [heq, hε, hqt]
  exact square_zero_weight G B ι hι he q hq hq2 t ht k hk m
    (CommRingCat.ofHom κ.toRingHom) (CommRingCat.ofHom κm.toRingHom) rfl hκm
    (TrivSqZeroExt.sndHom R M).toAddMonoidHom (by intro r; rfl) b


open ArithmeticThetaDifferentialRecoveryR0148.AffineTranslationChainRule (affine_structural identity_appLE)

set_option backward.isDefEq.respectTransparency false in
/-- Affine-coordinate form of the multiplication weight on a first-order
origin neighborhood. All ring maps are restrictions of the actual maps. -/
theorem affine_first_order_weight
    {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Base R)
    (G : GoodReductionJacobian.RelativeGroupLaw R p)
    (e : Base R ⟶ X) [IsClosedImmersion e] (he : (G.one (𝟙 _)).val = e)
    (U V : X.affineOpens) (heU : Set.range e.base ⊆ U.1)
    (m : ℕ) (hVU : V.1 ≤ U.1) (hVm : V.1 ≤ G.schemeNsmul m ⁻¹ᵁ U.1)
    {M : Type u} [AddCommGroup M]
    (δ : Γ(X,V.1) ⧸ (RingHom.ker (e.app V.1).hom)^2 →+ M)
    (hδ : ∀ r : R, δ (Ideal.Quotient.mk _ ((p.constToPresheaf.app (op V.1)).hom r)) = 0)
    (a : Γ(X,U.1)) :
    δ (Ideal.Quotient.mk _ ((G.schemeNsmul m).appLE U.1 V.1 hVm a)) =
      m • δ (Ideal.Quotient.mk _ (X.presheaf.map (homOfLE hVU).op a)) := by
  letI := p.sectionsAlgebra U.1
  letI := p.sectionsAlgebra V.1
  let A := Γ(X,V.1)
  let ε : A →+* Γ(Base R,e ⁻¹ᵁ V.1) := (e.app V.1).hom
  let C := CommRingCat.of (A ⧸ (RingHom.ker ε)^2)
  let j : CommRingCat.of A ⟶ C := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let q : C ⟶ CommRingCat.of Γ(Base R,e ⁻¹ᵁ V.1) :=
    CommRingCat.ofHom (squareKernelProjection ε)
  let t : Spec C ⟶ Base R := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have ht : algebraMap R C = (Spec.preimage t).hom := by
    rw [Spec.preimage_map]
    rfl
  have hVstruct := affine_structural V.1 p V.2
  let k : SchemeHomOver t p := ⟨Spec.map j ≫ V.2.fromSpec, by
    rw [Category.assoc, hVstruct, ← Spec.map_comp]
    rfl⟩
  have hjq : j ≫ q = e.app V.1 := by ext b; rfl
  have heV : IsAffineOpen (e ⁻¹ᵁ V.1) := V.2.preimage e
  have hred : Spec.map q ≫ k.val = heV.fromSpec ≫ e := by
    change Spec.map q ≫ (Spec.map j ≫ V.2.fromSpec) = _
    rw [← Category.assoc, ← Spec.map_comp, hjq, e.app_eq_appLE]
    exact V.2.SpecMap_appLE_fromSpec e heV le_rfl
  have hep : e ≫ p = 𝟙 _ := by rw [← he]; exact (G.one (𝟙 _)).property
  have hbase : Spec.map q ≫ t = heV.fromSpec := by
    rw [← k.property, ← Category.assoc, hred, Category.assoc, hep, Category.comp_id]
  have hone {T : Scheme.{u}} (z : T ⟶ Base R) : (G.one z).val = z ≫ e := by
    have H := congrArg Subtype.val (G.one_natural (𝟙 _) z z (Category.comp_id z))
    change z ≫ (G.one (𝟙 _)).val = (G.one z).val at H
    exact H.symm.trans (congrArg (fun v => z ≫ v) he)
  have hk : Spec.map q ≫ k.val = (G.one (Spec.map q ≫ t)).val := by
    rw [hone, hbase]
    exact hred
  have he' : Set.range (G.one (𝟙 _)).val.base ⊆ Set.range U.2.fromSpec.base := by
    rw [he, U.2.range_fromSpec]
    exact heU
  let κ : Γ(X,U.1) ⟶ C := X.presheaf.map (homOfLE hVU).op ≫ j
  let κm : Γ(X,U.1) ⟶ C := (G.schemeNsmul m).appLE U.1 V.1 hVm ≫ j
  have hκ : Spec.map κ ≫ U.2.fromSpec = k.val := by
    change Spec.map (_ ≫ j) ≫ U.2.fromSpec = Spec.map j ≫ V.2.fromSpec
    rw [Spec.map_comp, Category.assoc]
    congr 1
    have H := U.2.SpecMap_appLE_fromSpec (𝟙 X) V.2 hVU
    simpa only [identity_appLE, Category.comp_id] using H
  have hκm : Spec.map κm ≫ U.2.fromSpec = k.val ≫ G.schemeNsmul m := by
    change Spec.map (_ ≫ j) ≫ U.2.fromSpec = (Spec.map j ≫ V.2.fromSpec) ≫ _
    rw [Spec.map_comp, Category.assoc, U.2.SpecMap_appLE_fromSpec _ V.2 hVm,
      Category.assoc]
  exact square_zero_weight G (CommRingCat.of Γ(X,U.1)) U.2.fromSpec
    (affine_structural U.1 p U.2) he' q
    (squareKernelProjection_surjective ε (e.app_surjective V.1 V.2))
    (squareKernelProjection_ker_sq ε) t ht k hk m κ κm hκ hκm δ hδ a


open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationFiniteEtaleDegree

attribute [local irreducible] origin structureMap in
/-- Actual local Hodge differentials have multiplication weight on every affine
subchart common to a fixed identity chart and its multiplication preimage. -/
theorem affine_localDifferential_weight (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (U V : (Curve R W).affineOpens) (heU : Set.range (origin R W).base ⊆ U.1)
    (m : ℕ) (hVU : V.1 ≤ U.1) (hVm : V.1 ≤ G.schemeNsmul m ⁻¹ᵁ U.1)
    (a : Γ(Curve R W,U.1)) :
    localDifferential R W V.1 ((G.schemeNsmul m).appLE U.1 V.1 hVm a) =
      m • localDifferential R W V.1 ((Curve R W).presheaf.map (homOfLE hVU).op a) := by
  letI : IsProper (structureMap R W) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hep : origin R W ≫ structureMap R W = 𝟙 _ := by
    unfold origin structureMap
    exact (WeierstrassProjModel.kwZeroSect R W).property
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by rw [hep]; infer_instance
  letI : IsClosedImmersion (origin R W) := IsClosedImmersion.of_comp _ (structureMap R W)
  have he : ((toGRJ G).one (𝟙 _)).val = origin R W := by
    change (G.one (𝟙 _)).val = origin R W
    simpa only [Category.id_comp] using hG.1 (𝟙 _)
  have hVm' : V.1 ≤ (toGRJ G).schemeNsmul m ⁻¹ᵁ U.1 := by rw [toGRJ_schemeNsmul]; exact hVm
  have H := affine_first_order_weight (structureMap R W) (toGRJ G) (origin R W) he
    U V heU m hVU hVm' (firstOrderDifferential R W V.1)
    (firstOrderDifferential_base R W V.1) a
  simp only [toGRJ_schemeNsmul] at H
  exact H


attribute [local irreducible] origin structureMap in
/-- The canonical Hodge map has the required weight on differentials of all
functions on any affine chart containing the identity section. -/
theorem hodgeMap_affine_generators (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (U : (Curve R W).affineOpens) (heU : Set.range (origin R W).base ⊆ U.1)
    (m : ℕ) (a : Γ(Curve R W,U.1)) :
    (hodgeMap (multiplicationPointed R W G hG m)).app (origin R W ⁻¹ᵁ U.1)
      (localDifferential R W U.1 a) = m • localDifferential R W U.1 a := by
  apply (Hodge R W).isSheaf.section_ext
  intro x hx
  have hx' : origin R W x ∈ U.1 ⊓ G.schemeNsmul m ⁻¹ᵁ U.1 := by
    refine ⟨hx, ?_⟩
    change (origin R W ≫ G.schemeNsmul m) x ∈ U.1
    rw [multiplication_origin R W G hG m]
    exact hx
  obtain ⟨V,hV,hxV,hsub⟩ := exists_isAffineOpen_mem_and_subset hx'
  have hVU : V ≤ U.1 := fun y hy => (hsub hy).1
  have hVm : V ≤ G.schemeNsmul m ⁻¹ᵁ U.1 := fun y hy => (hsub hy).2
  have hle : origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ U.1 := fun y hy => hVU hy
  have hle' : origin R W ⁻¹ᵁ V ≤ origin R W ⁻¹ᵁ (G.schemeNsmul m ⁻¹ᵁ U.1) := fun y hy => hVm hy
  refine ⟨origin R W ⁻¹ᵁ V, hle, hxV, ?_⟩
  have H := PointedHodgeFunctoriality.hodgeMap_D (multiplicationPointed R W G hG m)
    U.1 a (origin R W ⁻¹ᵁ V) hle hle'
  have hres := InitialHodgeSection.differential_res R W hVm ((G.schemeNsmul m).app U.1 a)
  have hfirst : res (Hodge R W) hle
      ((hodgeMap (multiplicationPointed R W G hG m)).app _ (localDifferential R W U.1 a)) =
      localDifferential R W V ((G.schemeNsmul m).appLE U.1 V hVm a) := H.trans hres
  change res (Hodge R W) hle _ = res (Hodge R W) hle _
  rw [hfirst, affine_localDifferential_weight R W G hG U ⟨V,hV⟩ heU m hVU hVm a]
  change m • localDifferential R W V _ = (Hodge R W).presheaf.map (homOfLE hle).op
    (m • localDifferential R W U.1 a)
  rw [map_nsmul]
  congr 1
  exact (InitialHodgeSection.differential_res R W hVU a).symm

open scoped TensorProduct

/-- Base-changed universal differentials determine linear maps, without any
finite generation or freeness assumption. -/
theorem tensor_differential_ext {R A B N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [AddCommGroup N] [Module B N]
    (F G : B ⊗[A] KaehlerDifferential R A →ₗ[B] N)
    (h : ∀ a : A, F (1 ⊗ₜ[A] KaehlerDifferential.D R A a) =
      G (1 ⊗ₜ[A] KaehlerDifferential.D R A a)) : F = G := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b ω
    obtain ⟨l,rfl⟩ := KaehlerDifferential.linearCombination_surjective R A ω
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ht : b ⊗ₜ[A] (l a • KaehlerDifferential.D R A a) =
        (algebraMap A B (l a) * b) • (1 ⊗ₜ[A] KaehlerDifferential.D R A a) := by
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, _root_.mul_one]
    rw [ht, map_smul, map_smul, h]
  · intro x y hx hy
    simp only [map_add, hx, hy]


set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] origin structureMap in
/-- Differentials from a single affine neighborhood of the whole identity
section determine a Hodge morphism. The proof uses the actual affine Kähler
module and its canonical pullback comparison on each affine base open. -/
theorem hodge_hom_ext_affine (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (U : (Curve R W).affineOpens) (heU : Set.range (origin R W).base ⊆ U.1)
    {N : (Base R).Modules} (F G : Hodge R W ⟶ N)
    (h : ∀ a : Γ(Curve R W,U.1), F.app (origin R W ⁻¹ᵁ U.1) (localDifferential R W U.1 a) =
      G.app (origin R W ⁻¹ᵁ U.1) (localDifferential R W U.1 a)) : F = G := by
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := by
    unfold structureMap
    exact WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  have hΩ : Scheme.Modules.IsInvertible (structureMap R W).kaehler :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
      ((structureMap R W).isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension 1).1
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨B,hB,hxB,hBV⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : B ≤ V := hBV
  refine ⟨B, hle, hxB, ?_⟩
  change res N hle (F.app V s) = res N hle (G.app V s)
  rw [hom_res, hom_res]
  have hBU : B ≤ origin R W ⁻¹ᵁ U.1 := fun y _ => heU (Set.mem_range_self y)
  letI := (structureMap R W).sectionsAlgebra U.1
  letI := ((origin R W).appLE U.1 B hBU).hom.toAlgebra
  let E : KaehlerDifferential R Γ(Curve R W,U.1) ≃ₗ[Γ(Curve R W,U.1)]
      Γ((structureMap R W).kaehler,U.1) :=
    LinearEquiv.ofBijective ((structureMap R W).kaehlerToSectionsₗ U.1)
    ((structureMap R W).kaehlerToSections_bijective_of_isAffineOpen U.2)
  obtain ⟨β,hβ⟩ := hΩ.exists_baseChange_sections_linearEquiv_pullback_of_le
    (origin R W) U.1 U.2 B hB hBU
  let β' := (LinearEquiv.baseChange Γ(Curve R W,U.1) Γ(Base R,B) _ _ E).trans β
  have HFG : ((F.val.app (op B)).hom.comp β'.toLinearMap) =
      ((G.val.app (op B)).hom.comp β'.toLinearMap) := by
    apply tensor_differential_ext (R := R)
    intro a
    change F.app B (β ((LinearEquiv.baseChange Γ(Curve R W,U.1) Γ(Base R,B) _ _ E)
      (1 ⊗ₜ[Γ(Curve R W,U.1)] KaehlerDifferential.D R Γ(Curve R W,U.1) a))) =
      G.app B (β ((LinearEquiv.baseChange Γ(Curve R W,U.1) Γ(Base R,B) _ _ E)
      (1 ⊗ₜ[Γ(Curve R W,U.1)] KaehlerDifferential.D R Γ(Curve R W,U.1) a)))
    rw [LinearEquiv.baseChange_tmul, hβ]
    change F.app B (res (Hodge R W) hBU (localDifferential R W U.1 a)) =
      G.app B (res (Hodge R W) hBU (localDifferential R W U.1 a))
    rw [← hom_res, ← hom_res, h]
  obtain ⟨z,hz⟩ := β'.surjective (res (Hodge R W) hle s)
  have HH := DFunLike.congr_fun HFG z
  change F.app B (β' z) = G.app B (β' z) at HH
  rwa [hz] at HH


/-- The standard Y-chart contains the whole actual Weierstrass origin section. -/
theorem exists_affine_origin_chart (R : Type u) [CommRing R] (W : WeierstrassCurve R) :
    ∃ U : (Curve R W).affineOpens, Set.range (origin R W).base ⊆ U.1 := by
  let ι := WeierstrassCurve.DrinfeldGlobal.originChartι W.toProjective
  refine ⟨⟨ι.opensRange, isAffineOpen_opensRange ι⟩, ?_⟩
  have he : origin R W = Spec.map (CommRingCat.ofHom (WeierstrassProjModel.kwYChartEval R W)) ≫ ι := rfl
  rintro _ ⟨x,rfl⟩
  change origin R W x ∈ Set.range ι.base
  rw [he]
  exact ⟨_,rfl⟩

attribute [local irreducible] origin structureMap in
/-- Scalar weight on every section of the actual relative Hodge sheaf. -/
theorem hodge_weight (R : Type u) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (m : ℕ)
    (B : (Base R).Opens) (s : Γ(Hodge R W,B)) :
    (hodgeMap (multiplicationPointed R W G hG m)).app B s = (m : Γ(Base R,B)) • s := by
  obtain ⟨U,heU⟩ := exists_affine_origin_chart R W
  have hmap : hodgeMap (multiplicationPointed R W G hG m) = m • 𝟙 (Hodge R W) := by
    apply hodge_hom_ext_affine R W U heU
    intro a
    rw [nsmul_app]
    exact hodgeMap_affine_generators R W G hG U heU m a
  rw [hmap, nsmul_app, Nat.cast_smul_eq_nsmul]
  rfl

end RelativeMultiplicationHodgeWeight
open RelativeMultiplicationHodgeWeight

/-- Multiplication by m induces weight m^n on all sections of the genuine nth
Hodge tensor power, including zero multiplication and the zeroth power. -/
theorem relative_multiplication_hodge_weight :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (m : ℕ), ∃ f : ArithmeticThetaRelativeIsogenyHodgeR0172.PointedMap R W W, f.map = G.schemeNsmul m ∧ ∀ (n : ℕ) (U : (ArithmeticThetaRelativeDiscriminantR0171.Base R).Opens) (s : (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W n).presheaf.obj (Opposite.op U)), (ArithmeticThetaRelativeIsogenyHodgeR0172.powerMap f n).app U s = ((m : (ArithmeticThetaRelativeDiscriminantR0171.Base R).presheaf.obj (Opposite.op U))^n) • s := by
  intro R _ _ _ _ _ W _ G hG m
  refine ⟨multiplicationPointed R W G hG m, rfl, ?_⟩
  exact power_weight_of_hodge_weight R W (multiplicationPointed R W G hG m) m
    (hodge_weight R W G hG m)

#print axioms relative_multiplication_hodge_weight
end ArithmeticThetaRelativeIsogenyHodgeR0172
