module

public import RelativeKatoCartierRatioR0170
public import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaRelativeKatoNaturalityR0170
namespace RelativeKatoFiberSpecialization
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169

/-- Rational restriction after a sheaf pullback is evaluation through the
actual stalk map at the target generic point. No dominance is needed. -/
lemma pullback_germ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)) :
    X.germToFunctionField V (f.appLE U V e a) =
      f.stalkMap (genericPoint X)
        (Y.presheaf.germ U (f (genericPoint X))
          (e (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
            (by simpa using (inferInstance : Nonempty V)))) a) := by
  rw [Scheme.Hom.appLE]
  change (f.app U ≫ X.presheaf.map (homOfLE e).op ≫
    X.presheaf.germ V (genericPoint X) _) a = _
  rw [X.presheaf.germ_res]
  exact (f.germ_stalkMap_apply U (genericPoint X) _ a).symm

/-- Two sections of the same rational function specialize equally wherever
both pullbacks are defined. This also applies to noninjective base maps. -/
lemma pullback_eq_of_rational_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (U U' : Y.Opens) (V V' : X.Opens)
    [Nonempty U] [Nonempty U'] [Nonempty V] [Nonempty V']
    (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    (a : Γ(Y, U)) (a' : Γ(Y, U'))
    (h : Y.germToFunctionField U a = Y.germToFunctionField U' a') :
    X.germToFunctionField V (f.appLE U V e a) =
      X.germToFunctionField V' (f.appLE U' V' e' a') := by
  rw [pullback_germ, pullback_germ]
  congr 1
  apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint X))) Y.functionField
  simpa only [Y.algebraMap_germ_eq_germToFunctionField] using h

/-- The already accepted relative normalization supplies units on the entire
complement, including non-affine opens. -/
lemma source_unit (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) (g : (Curve R W).functionField)
    (hg : Normalized R W G c g) : UnitOnComplement R W G c g := by
  obtain ⟨C⟩ := relative_generic_comparison R W G hG
  exact (RelativeExistence.relative_of_generic R W G hG C c hc hc6 g (hg.2 C)).2

/-- A regular section representing the normalized function on a torsion-free
open is itself a unit; its pullback is a unit under every scheme morphism. -/
lemma pulled_section_unit (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) (g : (Curve R W).functionField)
    (hg : Normalized R W G c g) {X : Scheme.{u}} (b : X ⟶ Curve R W)
    (U : (Curve R W).Opens) (V : X.Opens) [Nonempty U]
    (e : V ≤ b ⁻¹ᵁ U) (a : Γ(Curve R W, U))
    (hU : ∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W))
    (ha : (Curve R W).germToFunctionField U a = g) : IsUnit (b.appLE U V e a) := by
  obtain ⟨a', ha', _⟩ := source_unit R W G hG c hc hc6 g hg U hU
  have he : a = a' := (Curve R W).germToFunctionField_injective U (ha.trans ha'.1.symm)
  exact he ▸ ha'.2.map (b.appLE U V e).hom

/-- A single regular representative determines all pullbacks on all nonempty
opens. The outstanding mathematical content is identification of that value
with the normalized function on the fiber. -/
lemma unitPullback_of_one_section (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S)
    [IsIntegral (Curve S Ws)] (b : Curve S Ws ⟶ Curve R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (gs : (Curve S Ws).functionField)
    (U₀ : (Curve R W).Opens) (V₀ : (Curve S Ws).Opens)
    [Nonempty U₀] [Nonempty V₀] (e₀ : V₀ ≤ b ⁻¹ᵁ U₀)
    (a₀ : Γ(Curve R W, U₀))
    (ha₀ : (Curve R W).germToFunctionField U₀ a₀ = g)
    (hs₀ : (Curve S Ws).germToFunctionField V₀ (b.appLE U₀ V₀ e₀ a₀) = gs) :
    UnitPullback R W G S Ws b c g gs := by
  intro U V _ _ e a hU ha
  refine ⟨pulled_section_unit R W G hG c hc hc6 g hg b U V e a hU ha, ?_⟩
  exact (pullback_eq_of_rational_eq b U U₀ V V₀ e e₀ a a₀
    (ha.trans ha₀.symm)).trans hs₀

/-- An effective Cartier divisor on an integral scheme misses its generic point. -/
lemma generic_not_support {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I) :
    genericPoint X ∉ I.support := by
  obtain ⟨U, hx, a, ha, hIa⟩ := hI (genericPoint X)
  letI : Nonempty U.1 := ⟨⟨genericPoint X, hx⟩⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, hIa,
    X.zeroLocus_span, X.zeroLocus_singleton]
  intro h
  apply h
  apply (X.mem_basicOpen a (genericPoint X) hx).mpr
  apply isUnit_iff_ne_zero.mpr
  exact (map_ne_zero_iff _ (germ_injective_of_isIntegral X (genericPoint X) hx)).mpr
    (nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha))

open ArithmeticThetaGeometricNormR0150

/-- Finite étale norm charts can be chosen inside any prescribed open. -/
lemma exists_affineFree_subset {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f] (O : Y.Opens) (y : Y) (hyO : y ∈ O) :
    ∃ U : Y.Opens, y ∈ U ∧ U ≤ O ∧ IsAffineOpen U ∧ AffineFree f U := by
  obtain ⟨U, hU, hy, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  have hV := hU.preimage f
  letI := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  letI : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    have hf : (f.app U).hom.Flat := by
      simpa only [Scheme.Hom.appLE_eq_app] using f.flat_appLE hU hV le_rfl
    exact hf
  letI : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    have hf : (f.app U).hom.FinitePresentation := by
      simpa only [Scheme.Hom.appLE_eq_app] using f.finitePresentation_appLE hU hV le_rfl
    exact hf
  letI : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  let p := hU.primeIdealOf ⟨y, hy⟩
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U)) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ U))
    (Localization.AtPrime p.asIdeal)
  refine ⟨Y.basicOpen r, ?_, (Y.basicOpen_le r).trans hUO,
    hU.basicOpen r, LocalNorm.affineFree_basicOpen f U hU r hfree⟩
  have hp : p ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen r := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  change hU.fromSpec p ∈ Y.basicOpen r at hp
  simpa only [p, hU.fromSpec_primeIdealOf] using hp

lemma nsmul_pow {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of R)} (G : WeierstrassProjModel.RelativeGroupLaw R p)
    {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (z : NeronModelInfra.SchemeHomOver t p) :
    letI := G.pointGroup t
    G.nsmul t n z = z ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl

lemma multiplication_commutes {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of R)} (G : WeierstrassProjModel.RelativeGroupLaw R p)
    (c d : ℕ) : G.schemeNsmul c ≫ G.schemeNsmul d =
      G.schemeNsmul d ≫ G.schemeNsmul c := by
  have H (a b : ℕ) : G.schemeNsmul a ≫ G.schemeNsmul b = G.schemeNsmul (a*b) := by
    have hp : G.nsmul p b (G.nsmul p a ⟨𝟙 X, Category.id_comp p⟩) =
        G.nsmul p (a*b) ⟨𝟙 X, Category.id_comp p⟩ := by
      letI := G.pointGroup p
      simp only [nsmul_pow, pow_mul]
    simpa only [← ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential.comp_schemeNsmul,
      Category.id_comp] using congrArg Subtype.val hp
  rw [H, H, Nat.mul_comm]

/-- A rational product equation can be specialized on any chart on which its
factors are regular at the image of the target generic point. -/
lemma pullback_product_relation {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (U U₀ : Y.Opens) (V V₀ : X.Opens)
    [Nonempty U] [Nonempty U₀] [Nonempty V] [Nonempty V₀]
    (e : V ≤ f ⁻¹ᵁ U) (e₀ : V₀ ≤ f ⁻¹ᵁ U₀)
    (a₀ : Γ(Y, U₀)) (d r : Γ(Y, U))
    (h : Y.germToFunctionField U₀ a₀ * Y.germToFunctionField U d =
      Y.germToFunctionField U r) :
    X.germToFunctionField V₀ (f.appLE U₀ V₀ e₀ a₀) *
      X.germToFunctionField V (f.appLE U V e d) =
      X.germToFunctionField V (f.appLE U V e r) := by
  rw [pullback_germ, pullback_germ, pullback_germ, ← map_mul]
  congr 1
  apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint X))) Y.functionField
  simpa only [map_mul, Y.algebraMap_germ_eq_germToFunctionField] using h

/-- Two Cartier ideals have simultaneous regular generators on sufficiently
small affine neighborhoods. -/
lemma common_cartier_chart {X : Scheme.{u}} [IsIntegral X]
    (I J : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I)
    (hJ : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal J) (x : X) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧
      ∃ a b : Γ(X, U.1), IsRegular a ∧ IsRegular b ∧
        I.ideal U = Ideal.span {a} ∧ J.ideal U = Ideal.span {b} := by
  obtain ⟨U, hxU, a, ha, hIa⟩ := hI x
  obtain ⟨V, hxV, b, hb, hJb⟩ := hJ x
  obtain ⟨T, hT, hxT, he⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  have eU : T ≤ U.1 := he.trans inf_le_left
  have eV : T ≤ V.1 := he.trans inf_le_right
  letI : Nonempty T := ⟨⟨x, hxT⟩⟩
  letI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  letI : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let α := X.presheaf.map (homOfLE eU).op
  let β := X.presheaf.map (homOfLE eV).op
  refine ⟨⟨T, hT⟩, hxT, α a, β b, ?_, ?_, ?_, ?_⟩
  · exact IsRegular.of_ne_zero ((map_ne_zero_iff _ (map_injective_of_isIntegral X _)).mpr
      (nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp ha)))
  · exact IsRegular.of_ne_zero ((map_ne_zero_iff _ (map_injective_of_isIntegral X _)).mpr
      (nonZeroDivisors.ne_zero (isRegular_iff_mem_nonZeroDivisors.mp hb)))
  · rw [← I.map_ideal (U := ⟨T, hT⟩) eU, hIa, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← J.map_ideal (U := ⟨T, hT⟩) eV, hJb, Ideal.map_span, Set.image_singleton]
    rfl

/-- A generator of a divisor missing the generic point stays nonzero. -/
lemma generator_regular {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : genericPoint X ∉ I.support)
    (U : X.affineOpens) [Nonempty U.1] (a : Γ(X, U.1))
    (ha : I.ideal U = Ideal.span {a}) : IsRegular a := by
  apply IsRegular.of_ne_zero
  intro ha0
  apply hI
  have hx : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U.1))
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, ha, ha0,
    X.zeroLocus_span, X.zeroLocus_singleton]
  simp

variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsIntegral (Curve R W)] [IsLocallyNoetherian (Curve R W)]
    [IsIntegral (GenericCurve R W)] [IsLocallyNoetherian (GenericCurve R W)]
    (G : Law R W) (hG : IsOriginLaw R W G)
    (S : Type u) [CommRing S] [IsDomain S]
    [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S]
    (Ws : WeierstrassCurve S) [Ws.IsElliptic]
    [IsIntegral (Curve S Ws)] [IsLocallyNoetherian (Curve S Ws)]
    [IsIntegral (GenericCurve S Ws)] [IsLocallyNoetherian (GenericCurve S Ws)]
    (Gs : Law S Ws) (hGs : IsOriginLaw S Ws Gs)
    (ι : R →+* S) (b : Curve S Ws ⟶ Curve R W)
    (hb : IsBaseChange R W G S Ws Gs ι b)

lemma identity_support (x : Curve R W) :
    x ∈ (identityIdeal R W).support ↔ x ∈ Set.range (origin R W) := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  change x ∈ ((origin R W).ker.support : Set _) ↔ _
  rw [Scheme.Hom.support_ker, (origin R W).isClosedEmbedding.isClosed_range.closure_eq]

lemma torsion_support (c : ℕ) (x : Curve R W) :
    x ∈ (torsionIdeal R W G c).support ↔
      G.schemeNsmul c x ∈ Set.range (origin R W) := by
  change x ∈ ((identityIdeal R W).comap (G.schemeNsmul c)).support ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  exact identity_support R W _

include hb in
lemma origin_preimage (x : Curve S Ws) :
    b x ∈ Set.range (origin R W) ↔ x ∈ Set.range (origin S Ws) := by
  have hp := ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.section_pullback
    (structureMap R W) (structureMap S Ws) b (Spec.map (CommRingCat.ofHom ι))
    hb.1 (origin R W) (origin S Ws)
    (WeierstrassProjModel.kwZeroSect R W).property
    (WeierstrassProjModel.kwZeroSect S Ws).property hb.2.1
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback hp x s hs.symm
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom ι) t, ?_⟩
    exact (congrArg (fun f => f t) hb.2.1).symm

include hb in
lemma torsion_preimage (c : ℕ) (x : Curve S Ws) :
    G.schemeNsmul c (b x) ∈ Set.range (origin R W) ↔
      Gs.schemeNsmul c x ∈ Set.range (origin S Ws) := by
  have hm := congrArg (fun f : Curve S Ws ⟶ Curve R W => f x) (hb.2.2 c)
  change b (Gs.schemeNsmul c x) = G.schemeNsmul c (b x) at hm
  rw [← hm]
  exact origin_preimage R W G S Ws Gs ι b hb _

include hGs hb in
lemma generic_image_avoids (c : ℕ) (hc : 0 < c) :
    G.schemeNsmul c (b (genericPoint (Curve S Ws))) ∉ Set.range (origin R W) := by
  rw [torsion_preimage R W G S Ws Gs ι b hb c]
  rw [← torsion_support S Ws Gs c]
  exact generic_not_support (torsionIdeal S Ws Gs c)
    ((relative_torsion_cartier S Ws Gs hGs).2 c hc)

include hGs hb in
/-- There is a nonempty open on the source complement whose pullback is
nonempty. This holds for arbitrary, possibly noninjective, base maps. -/
lemma complement_chart (c : ℕ) (hc : 0 < c) :
    ∃ U : (Curve R W).Opens, Nonempty U ∧ Nonempty (b ⁻¹ᵁ U) ∧
      ∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W) := by
  let U := (torsionIdeal R W G c).support.compl
  have hx : b (genericPoint (Curve S Ws)) ∈ U := by
    exact fun h => generic_image_avoids R W G S Ws Gs hGs ι b hb c hc
      ((torsion_support R W G c _).mp h)
  exact ⟨U, ⟨⟨_, hx⟩⟩, ⟨⟨genericPoint (Curve S Ws), hx⟩⟩,
    fun x hx ht => hx ((torsion_support R W G c x).mpr ht)⟩

include hG hGs hb in
/-- The source normalized function has a unique rational specialization,
characterized by all its sheaf sections on the complement. Identifying this
specialization with the target normalized function is a separate step. -/
lemma exists_unique_specialized_function (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) (g : (Curve R W).functionField)
    (hg : Normalized R W G c g) :
    ∃! q : (Curve S Ws).functionField, UnitPullback R W G S Ws b c g q := by
  obtain ⟨U, hU, hV, hav⟩ := complement_chart R W G S Ws Gs hGs ι b hb c (by omega)
  letI := hU
  letI := hV
  obtain ⟨a, ha, _⟩ := source_unit R W G hG c hc hc6 g hg U hav
  let q := (Curve S Ws).germToFunctionField (b ⁻¹ᵁ U) (b.appLE U _ le_rfl a)
  refine ⟨q, unitPullback_of_one_section R W G hG S Ws b c hc hc6 g hg q
    U (b ⁻¹ᵁ U) le_rfl a ha.1 rfl, ?_⟩
  intro q' hq'
  exact (hq' U (b ⁻¹ᵁ U) le_rfl a hav ha.1).2.symm

include hG in
lemma multiplication_preserves_torsion (c d : ℕ) (x : Curve R W)
    (hx : G.schemeNsmul c x ∈ Set.range (origin R W)) :
    G.schemeNsmul c (G.schemeNsmul d x) ∈ Set.range (origin R W) := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, ?_⟩
  have hm := congrArg (fun f : Curve R W ⟶ Curve R W => f x)
    (multiplication_commutes G c d)
  change G.schemeNsmul d (G.schemeNsmul c x) =
    G.schemeNsmul c (G.schemeNsmul d x) at hm
  rw [← hm, ← hs]
  exact (congrArg (fun f => f s) (RelativeExistence.origin_fixed R W G hG d)).symm

include hG hGs hb in
/-- The determinant norm of the specialized function is normalized for every
positive multiplication coprime to c. Only affine section-ring pushouts are
used to cross the possibly non-dominant base change. -/
lemma specialized_norm (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (q : (Curve S Ws).functionField) (hq : UnitPullback R W G S Ws b c g q)
    (d : ℕ) (hd : 0 < d) (hcd : Nat.Coprime c d)
    (φs : (Curve S Ws).functionField →+* (Curve S Ws).functionField)
    (hφs : IsFieldMap (Gs.schemeNsmul d) φs) : fieldNorm φs q = q := by
  obtain ⟨hf, he, hs, _⟩ := relative_multiplication_degree R W G hG d hd
  letI := hf
  letI := he
  letI := hs
  obtain ⟨hfs, hes, hss, _⟩ := relative_multiplication_degree S Ws Gs hGs d hd
  letI := hfs
  letI := hes
  letI := hss
  obtain ⟨φ, hφ⟩ := ActualMultiplicationFieldNorm.exists_fieldMap (G.schemeNsmul d)
  obtain ⟨O, hO, hOb, hOc⟩ := complement_chart R W G S Ws Gs hGs ι b hb c (by omega)
  letI := hOb
  have hy : b (genericPoint (Curve S Ws)) ∈ O :=
    ((genericPoint_spec (Curve S Ws)).mem_open_set_iff (b ⁻¹ᵁ O).isOpen).mpr
      (by simpa using hOb)
  obtain ⟨U, hyU, hUO, hU, hfree⟩ := exists_affineFree_subset (G.schemeNsmul d) O _ hy
  obtain ⟨V, hV, hyV, e⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint (Curve S Ws) ∈ b ⁻¹ᵁ U from hyU)
  letI : Nonempty U := ⟨⟨_, hyU⟩⟩
  letI : Nonempty V := ⟨⟨_, hyV⟩⟩
  obtain ⟨x, hx⟩ := (G.schemeNsmul d).surjective (b (genericPoint (Curve S Ws)))
  letI : Nonempty (G.schemeNsmul d ⁻¹ᵁ U) := ⟨⟨x, by change G.schemeNsmul d x ∈ U; rwa [hx]⟩⟩
  obtain ⟨xs, hxs⟩ := (Gs.schemeNsmul d).surjective (genericPoint (Curve S Ws))
  letI : Nonempty (Gs.schemeNsmul d ⁻¹ᵁ V) := ⟨⟨xs, by change Gs.schemeNsmul d xs ∈ V; rwa [hxs]⟩⟩
  have hcU : ∀ x ∈ U, G.schemeNsmul c x ∉ Set.range (origin R W) :=
    fun x hx => hOc x (hUO hx)
  have hcpre : ∀ x ∈ G.schemeNsmul d ⁻¹ᵁ U,
      G.schemeNsmul c x ∉ Set.range (origin R W) := by
    intro x hx ht
    exact hcU _ hx (multiplication_preserves_torsion R W G hG c d x ht)
  obtain ⟨a, ha, _⟩ := source_unit R W G hG c hc hc6 g hg (G.schemeNsmul d ⁻¹ᵁ U) hcpre
  have hn := (LocalNorm.affine_field_data (G.schemeNsmul d) φ hφ U hU).2.2 hfree a
  rw [ha.1, hg.1.2.2 d hd hcd φ hφ] at hn
  have hcart := ArithmeticThetaKatoExistenceR0151.ActualKatoFieldBaseChange.endomorphism_cartesian
    (structureMap R W) (structureMap S Ws) b (Spec.map (CommRingCat.ofHom ι))
    hb.1 (G.schemeNsmul d) (Gs.schemeNsmul d)
    (G.schemeNsmul_over d) (Gs.schemeNsmul_over d) (hb.2.2 d)
  have e' : Gs.schemeNsmul d ⁻¹ᵁ V ≤ b ⁻¹ᵁ (G.schemeNsmul d ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hcart.w, Scheme.Hom.comp_preimage]
    exact (Gs.schemeNsmul d).preimage_mono e
  have hp := BaseChange.sections_pushout (G.schemeNsmul d) (Gs.schemeNsmul d) b b
    hcart U V hU hV e e'
  obtain ⟨hfree', hnorm⟩ := BaseChange.norm_of_pushout ((G.schemeNsmul d).app U)
    (b.appLE U V e) (b.appLE _ _ e') ((Gs.schemeNsmul d).app V) hp hfree
    ((G.schemeNsmul d).finite_app U hU)
  have hn' := (LocalNorm.affine_field_data (Gs.schemeNsmul d) φs hφs V hV).2.2 hfree'
    (b.appLE _ _ e' a)
  rw [(hq _ _ e' a hcpre ha.1).2] at hn'
  have H := congrArg ((Curve S Ws).germToFunctionField V) (hnorm a)
  change (Curve S Ws).germToFunctionField V
      (b.appLE U V e (affineNorm (G.schemeNsmul d) U a)) =
    (Curve S Ws).germToFunctionField V
      (affineNorm (Gs.schemeNsmul d) V (b.appLE _ _ e' a)) at H
  rw [(hq U V e _ hcU hn).2, hn'] at H
  exact H.symm

include hG hGs hb in
lemma specialized_ne_zero (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (q : (Curve S Ws).functionField) (hq : UnitPullback R W G S Ws b c g q) : q ≠ 0 := by
  obtain ⟨U, hU, hV, hav⟩ := complement_chart R W G S Ws Gs hGs ι b hb c (by omega)
  letI := hU
  letI := hV
  obtain ⟨a, ha, _⟩ := source_unit R W G hG c hc hc6 g hg U hav
  have H := hq U (b ⁻¹ᵁ U) le_rfl a hav ha.1
  exact H.2 ▸ (H.1.map ((Curve S Ws).germToFunctionField (b ⁻¹ᵁ U)).hom).ne_zero

include hb in
lemma identity_comap : (identityIdeal R W).comap b = identityIdeal S Ws := by
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  letI : IsClosedImmersion (origin R W ≫ structureMap R W) := by
    rw [show origin R W ≫ structureMap R W = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect R W).property]
    infer_instance
  letI : IsClosedImmersion (origin R W) :=
    IsClosedImmersion.of_comp (origin R W) (structureMap R W)
  have hp := ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.section_pullback
    (structureMap R W) (structureMap S Ws) b (Spec.map (CommRingCat.ofHom ι))
    hb.1 (origin R W) (origin S Ws)
    (WeierstrassProjModel.kwZeroSect R W).property
    (WeierstrassProjModel.kwZeroSect S Ws).property hb.2.1
  change (origin R W).ker.comap b = (origin S Ws).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hp.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

include hb in
lemma torsion_comap (c : ℕ) : (torsionIdeal R W G c).comap b = torsionIdeal S Ws Gs c := by
  unfold torsionIdeal
  rw [← Scheme.IdealSheafData.comap_comp, ← hb.2.2 c,
    Scheme.IdealSheafData.comap_comp, identity_comap R W G S Ws Gs ι b hb]

include hG hGs hb in
/-- The full Cartier equation specializes through ordinary section-ring maps.
The resulting scalar is a unit on the entire target affine chart. -/
lemma specialized_cartier_equation (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (q : (Curve S Ws).functionField) (hq : UnitPullback R W G S Ws b c g q)
    (U : (Curve R W).affineOpens) (V : (Curve S Ws).affineOpens)
    [Nonempty U.1] [Nonempty V.1] (e : V.1 ≤ b ⁻¹ᵁ U.1)
    (a d : Γ(Curve R W, U.1)) (ha : IsRegular a) (hd : IsRegular d)
    (hIa : (identityIdeal R W).ideal U = Ideal.span {a})
    (hId : (torsionIdeal R W G c).ideal U = Ideal.span {d}) :
    ∃ ε : Γ(Curve S Ws, V.1)ˣ,
      q * (Curve S Ws).germToFunctionField V.1 (b.appLE U.1 V.1 e d) =
        (Curve S Ws).germToFunctionField V.1
          ((ε : _) * (b.appLE U.1 V.1 e a)^(c^2)) := by
  obtain ⟨ε, hε⟩ := relative_kato_cartier_ratio R W G hG c hc hc6 g hg U a d ha hd hIa hId
  obtain ⟨O, hO, hOb, hOc⟩ := complement_chart R W G S Ws Gs hGs ι b hb c (by omega)
  letI := hO
  letI := hOb
  obtain ⟨a₀, ha₀, _⟩ := source_unit R W G hG c hc hc6 g hg O hOc
  have H := pullback_product_relation b U.1 O V.1 (b ⁻¹ᵁ O) e le_rfl a₀ d
    ((ε : _) * a^(c^2)) (by rwa [ha₀.1])
  rw [(hq O (b ⁻¹ᵁ O) le_rfl a₀ hOc ha₀.1).2] at H
  refine ⟨Units.map (b.appLE U.1 V.1 e).hom.toMonoidHom ε, ?_⟩
  change q * (Curve S Ws).germToFunctionField V.1 (b.appLE U.1 V.1 e d) =
    (Curve S Ws).germToFunctionField V.1
      (b.appLE U.1 V.1 e (ε : _) * (b.appLE U.1 V.1 e a)^(c^2))
  simpa only [map_mul, map_pow] using H

include hG hGs hb in
/-- The specialized Cartier equations yield the required orders on every
height-one point, including points on nongeneric fibers. -/
lemma specialized_orders (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (q : (Curve S Ws).functionField) (hq : UnitPullback R W G S Ws b c g q)
    (x : Curve S Ws) (hx : Order.coheight x = 1) :
    Scheme.ord q x = katoOrder S Ws Gs c x := by
  classical
  letI : IsProper (structureMap S Ws) :=
    WeierstrassProjModel.projModelStrCR_isProper Ws.toProjective
  letI : IsClosedImmersion (origin S Ws ≫ structureMap S Ws) := by
    rw [show origin S Ws ≫ structureMap S Ws = 𝟙 _ from
      (WeierstrassProjModel.kwZeroSect S Ws).property]
    infer_instance
  letI : IsClosedImmersion (origin S Ws) :=
    IsClosedImmersion.of_comp (origin S Ws) (structureMap S Ws)
  obtain ⟨hI, hT⟩ := relative_torsion_cartier R W G hG
  obtain ⟨U, hxU, a, d, ha, hd, hIa, hId⟩ := common_cartier_chart
    (identityIdeal R W) (torsionIdeal R W G c) hI (hT c (by omega)) (b x)
  obtain ⟨V, hV, hxV, e⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ b ⁻¹ᵁ U.1 from hxU)
  letI : Nonempty U.1 := ⟨⟨b x, hxU⟩⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A := b.appLE U.1 V e a
  let D := b.appLE U.1 V e d
  have hIA : (identityIdeal S Ws).ideal ⟨V, hV⟩ = Ideal.span {A} := by
    rw [← identity_comap R W G S Ws Gs ι b hb,
      Scheme.IdealSheafData.ideal_comap_of_le _ b U ⟨V, hV⟩ e,
      hIa, Ideal.map_span, Set.image_singleton]
  have hID : (torsionIdeal S Ws Gs c).ideal ⟨V, hV⟩ = Ideal.span {D} := by
    rw [← torsion_comap R W G S Ws Gs ι b hb c,
      Scheme.IdealSheafData.ideal_comap_of_le _ b U ⟨V, hV⟩ e,
      hId, Ideal.map_span, Set.image_singleton]
  obtain ⟨hIS, hTS⟩ := relative_torsion_cartier S Ws Gs hGs
  have hA : IsRegular A := generator_regular (identityIdeal S Ws)
    (generic_not_support _ hIS) ⟨V, hV⟩ A hIA
  have hD : IsRegular D := generator_regular (torsionIdeal S Ws Gs c)
    (generic_not_support _ (hTS c (by omega))) ⟨V, hV⟩ D hID
  obtain ⟨ε, hε⟩ := specialized_cartier_equation R W G hG S Ws Gs hGs ι b hb
    c hc hc6 g hg q hq U ⟨V, hV⟩ e a d ha hd hIa hId
  have hnormal := (relative_curve_geometry S Ws).2.2.1
  have hoa := RelativeKatoCartierRatio.generator_order hnormal (identityIdeal S Ws)
    ⟨V, hV⟩ A hA hIA (RelativeKatoCartierRatio.ker_radical (origin S Ws) ⟨V, hV⟩)
    x hxV hx
  have hod := RelativeKatoCartierRatio.generator_order hnormal (torsionIdeal S Ws Gs c)
    ⟨V, hV⟩ D hD hID
    (RelativeKatoCartierRatio.torsion_radical S Ws Gs hGs c (by omega) ⟨V, hV⟩)
    x hxV hx
  rw [identity_support S Ws] at hoa
  rw [torsion_support S Ws Gs] at hod
  have hq0 := specialized_ne_zero R W G hG S Ws Gs hGs ι b hb c hc hc6 g hg q hq
  have hAf : (Curve S Ws).germToFunctionField V A ≠ 0 :=
    (map_ne_zero_iff _ ((Curve S Ws).germToFunctionField_injective V)).mpr
      (isRegular_iff_ne_zero.mp hA)
  have hDf : (Curve S Ws).germToFunctionField V D ≠ 0 :=
    (map_ne_zero_iff _ ((Curve S Ws).germToFunctionField_injective V)).mpr
      (isRegular_iff_ne_zero.mp hD)
  have hεf : (Curve S Ws).germToFunctionField V (ε : _) ≠ 0 :=
    (ε.isUnit.map ((Curve S Ws).germToFunctionField V).hom).ne_zero
  have hoε : Scheme.ord ((Curve S Ws).germToFunctionField V (ε : _)) x = 0 := by
    rw [← (Curve S Ws).algebraMap_germ_eq_germToFunctionField hxV]
    exact ArithmeticThetaKatoExistenceR0151.DivisorFieldBaseChange.ord_stalk_unit x _
      (ε.isUnit.map ((Curve S Ws).presheaf.germ V x hxV).hom)
  have H := congrArg (fun z => Scheme.ord z x) hε
  change Scheme.ord (q * (Curve S Ws).germToFunctionField V D) x =
    Scheme.ord ((Curve S Ws).germToFunctionField V ((ε : _) * A^(c^2))) x at H
  rw [map_mul, map_pow, Scheme.ord_mul hq0 hDf,
    Scheme.ord_mul hεf (pow_ne_zero _ hAf), hoε, zero_add,
    RelativeKatoCartierRatio.order_pow _ hAf, hoa, hod] at H
  unfold ArithmeticThetaRelativeKatoR0169.katoOrder
  push_cast at H
  split_ifs at H ⊢ <;> omega

/-- Over a field the accepted height-one formulation gives exactly the
all-point Kato divisor; the sole remaining point is the generic point. -/
lemma relative_isKato_over_field (F : Type u) [Field F] [Algebra ℚ F]
    (Wf : WeierstrassCurve F) [Wf.IsElliptic]
    [IsIntegral (Curve F Wf)] [IsLocallyNoetherian (Curve F Wf)]
    [IsIntegral (GenericCurve F Wf)] [IsLocallyNoetherian (GenericCurve F Wf)]
    (Gf : Law F Wf) (hGf : IsOriginLaw F Wf Gf)
    (c : ℕ) (hc : 0 < c) (g : (Curve F Wf).functionField)
    (hg : IsRelativeKato F Wf Gf c g) :
    ArithmeticThetaGeneralEllipticKatoR0168.IsKatoFunction F Wf Gf c g := by
  letI : SmoothOfRelativeDimension 1 (structureMap F Wf) :=
    (relative_curve_geometry F Wf).2.2.2.2.2.1
  refine ⟨⟨hg.1, ?_⟩, hg.2.2⟩
  intro x
  have he (z : Curve F Wf) : z ∈ Set.range (origin F Wf) ↔
      z = ArithmeticThetaGeneralEllipticKatoR0168.originPoint F Wf := by
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (origin F Wf) (Subsingleton.elim a (IsLocalRing.closedPoint F))
    · intro h
      exact h ▸ Set.mem_range_self (IsLocalRing.closedPoint F)
  have ho : ArithmeticThetaRelativeKatoR0169.katoOrder F Wf Gf c x =
      ArithmeticThetaGeneralEllipticKatoR0168.katoOrder F Wf Gf c x := by
    unfold ArithmeticThetaRelativeKatoR0169.katoOrder
      ArithmeticThetaGeneralEllipticKatoR0168.katoOrder
    rw [he, he]
  rw [← ho]
  by_cases hx : x = genericPoint (Curve F Wf)
  · subst x
    obtain ⟨hI, hT⟩ := relative_torsion_cartier F Wf Gf hGf
    have hio : genericPoint (Curve F Wf) ∉ Set.range (origin F Wf) := by
      rw [← identity_support F Wf]
      exact generic_not_support _ hI
    have hto : Gf.schemeNsmul c (genericPoint (Curve F Wf)) ∉ Set.range (origin F Wf) := by
      rw [← torsion_support F Wf Gf]
      exact generic_not_support _ (hT c hc)
    rw [NormOrders.ord_generic]
    simp only [ArithmeticThetaRelativeKatoR0169.katoOrder, if_neg hio, if_neg hto, sub_self]
  · exact hg.2.1 x (NormOrders.smooth_coheight_one_of_ne_generic F (structureMap F Wf) x hx)

end RelativeKatoFiberSpecialization
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
open RelativeKatoFiberSpecialization

/-- The accepted relative Kato function specializes to the accepted normalized
function over every field base change, on all nonempty sheaf opens. -/
theorem relative_kato_fiber_specialization :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (F : Type u) [Field F] [Algebra ℚ F] (Wf : WeierstrassCurve F) [Wf.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve F Wf)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve F Wf)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve F Wf)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve F Wf)] (Gf : ArithmeticThetaRelativeKatoR0169.Law F Wf) (hGf : ArithmeticThetaRelativeKatoR0169.IsOriginLaw F Wf Gf) (ι : R →+* F) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve F Wf) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G F Wf Gf ι b) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (gf : (ArithmeticThetaRelativeKatoR0169.Curve F Wf).functionField) (hgf : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized F Wf Gf c gf), ArithmeticThetaRelativeKatoNaturalityR0170.UnitPullback R W G F Wf b c g gf := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG F _ _ Wf _ _ _ _ _ Gf hGf ι b hb c hc hc6 g hg gf hgf
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  obtain ⟨q, hq, _⟩ := exists_unique_specialized_function R W G hG F Wf Gf hGf ι b hb
    c hc hc6 g hg
  have hrel : IsRelativeKato F Wf Gf c q := by
    refine ⟨specialized_ne_zero R W G hG F Wf Gf hGf ι b hb c hc hc6 g hg q hq, ?_, ?_⟩
    · exact specialized_orders R W G hG F Wf Gf hGf ι b hb c hc hc6 g hg q hq
    · exact specialized_norm R W G hG F Wf Gf hGf ι b hb c hc hc6 g hg q hq
  have hqK := relative_isKato_over_field F Wf Gf hGf c (by omega) q hrel
  have hfK := relative_isKato_over_field F Wf Gf hGf c (by omega) gf hgf.1
  obtain ⟨f, _, huniq⟩ := ArithmeticThetaGeneralEllipticKatoR0168.general_kato_existence
    F Wf Gf hGf c hc hc6
  have heq : q = gf := (huniq q hqK).trans (huniq gf hfK).symm
  exact heq ▸ hq

#print axioms relative_kato_fiber_specialization

end ArithmeticThetaRelativeKatoNaturalityR0170
