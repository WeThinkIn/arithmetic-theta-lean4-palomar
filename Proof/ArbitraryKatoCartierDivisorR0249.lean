module

public import ArbitraryKatoUnitExistenceR0249
public import NormalModelUnitSpecializationR0249
public import NormalDiscriminantModelR0243

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace ArithmeticThetaArbitraryKatoUnitR0249
namespace ArbitraryKatoCartierDivisor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaArbitraryDiscriminantR0243

lemma restrict_trans {X : Scheme.{u}} (U V T : X.Opens) (e : V ≤ U) (e' : T ≤ V)
    (a : Γ(X, U)) : restrict V T e' (restrict U V e a) = restrict U T (e'.trans e) a := by
  change (X.presheaf.map (homOfLE e).op ≫ X.presheaf.map (homOfLE e').op) a = _
  rw [← Functor.map_comp]
  rfl

/-- A flat map preserves a regular element on affine charts. -/
lemma regular_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (U : X.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (a : Γ(X, U.1)) (ha : IsRegular a) : IsRegular (f.appLE U.1 V.1 e a) := by
  let φ := (f.appLE U.1 V.1 e).hom
  letI := φ.toAlgebra
  letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) := f.flat_appLE U.2 V.2 e
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := Γ(Y, V.1)) (isRegular_iff_mem_nonZeroDivisors.mp ha)
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply h
  change φ a * x = φ a * 0
  simpa only [φ, mul_zero, zero_mul, mul_comm] using hx

/-- Effective Cartier ideals pull back along flat maps. -/
lemma effective_comap_flat {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (I : X.IdealSheafData)
    (hI : ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal I) :
    ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (I.comap f) := by
  intro y
  obtain ⟨U, hy, a, ha, hIa⟩ := hI (f y)
  obtain ⟨V, hV, hyV, e⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ f ⁻¹ᵁ U.1 from hy)
  refine ⟨⟨V, hV⟩, hyV, f.appLE U.1 V e a,
    regular_appLE f U ⟨V, hV⟩ e a ha, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_le I f U ⟨V, hV⟩ e,
    hIa, Ideal.map_span, Set.image_singleton]

lemma identity_effective (R : Type u) [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (identityIdeal R W) := by
  letI : SmoothOfRelativeDimension 1 (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  letI : IsProper (structureMap R W) :=
    WeierstrassProjModel.projModelStrCR_isProper W.toProjective
  have hI := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := structureMap R W) (origin R W)
    (WeierstrassProjModel.kwZeroSect R W).property
  intro x
  obtain ⟨U, f, hx, a, ha, hIa⟩ := hI x
  exact ⟨(Curve R W).affineBasicOpen f, hx, a,
    isRegular_iff_mem_nonZeroDivisors.mpr ha, hIa⟩

/-- Multiplication is the base change of multiplication on any normal model. -/
lemma multiplication_etale (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) : Etale (G.schemeNsmul n) := by
  obtain ⟨M⟩ := normal_discriminant_model R W
  letI : Etale (M.law.schemeNsmul n) :=
    (relative_multiplication_degree M.ring M.equation M.law M.originLaw n hn).2.1
  have hp : IsPullback M.comparison.map
      (G.schemeNsmul n ≫ structureMap R W)
      (M.law.schemeNsmul n ≫ structureMap M.ring M.equation)
      (Spec.map (CommRingCat.ofHom M.scalar.toRingHom)) := by
    simpa only [WeierstrassProjModel.RelativeGroupLaw.schemeNsmul_over] using
      M.comparison.cartesian
  have hs : IsPullback M.comparison.map (G.schemeNsmul n)
      (M.law.schemeNsmul n) M.comparison.map :=
    hp.of_bot (NormalModelUnitSpecialization.comparison_nsmul
      M.comparison M.law M.originLaw G hG n).symm M.comparison.cartesian
  exact MorphismProperty.of_isPullback (P := @Etale) hs inferInstance

lemma torsion_effective (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (n : ℕ) (hn : 0 < n) :
    ArithmeticThetaPolygonCartierR0133.IsEffectiveCartierIdeal (torsionIdeal R W G n) := by
  letI := multiplication_etale R W G hG n hn
  exact effective_comap_flat (G.schemeNsmul n) (identityIdeal R W) (identity_effective R W)

/-- Restriction does not change the rational section on an integral source. -/
lemma rational_restrict {X : Scheme.{u}} [IsIntegral X]
    (U V : X.Opens) [Nonempty U] [Nonempty V] (e : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (restrict U V e a) = X.germToFunctionField U a := by
  change (X.presheaf.map (homOfLE e).op ≫ X.presheaf.germ V (genericPoint X) _) a = _
  rw [X.presheaf.germ_res]

/-- A rational identity on the integral source pulls back as a section identity
on an arbitrary target. No injectivity or reducedness is imposed on the target. -/
lemma product_pullback {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (U U₀ : Y.Opens) [Nonempty U] [Nonempty U₀]
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e₀ : V ≤ f ⁻¹ᵁ U₀)
    (a₀ : Γ(Y, U₀)) (b d : Γ(Y, U))
    (h : Y.germToFunctionField U₀ a₀ * Y.germToFunctionField U b =
      Y.germToFunctionField U d) :
    f.appLE U₀ V e₀ a₀ * f.appLE U V e b = f.appLE U V e d := by
  let T := U ⊓ U₀
  letI : Nonempty T := ⟨⟨genericPoint Y,
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U)),
    ((genericPoint_spec Y).mem_open_set_iff U₀.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U₀))⟩⟩
  have ht : restrict U₀ T inf_le_right a₀ * restrict U T inf_le_left b =
      restrict U T inf_le_left d := by
    apply Y.germToFunctionField_injective T
    rw [map_mul, rational_restrict, rational_restrict, rational_restrict]
    exact h
  have eT : V ≤ f ⁻¹ᵁ T := fun x hx => ⟨e hx, e₀ hx⟩
  have H := congrArg (f.appLE T V eT) ht
  simpa only [map_mul, restrict, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using H

/-- On a normal-model chart, the Cartier equation specializes to the complete
unit on the arbitrary target complement. -/
lemma model_chart_equation (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (v : UnitSection R W G c) (M : NormalModel R W)
    (hv : FromModel R W G M c v)
    (U : (Curve M.ring M.equation).affineOpens) [Nonempty U.1]
    (a b : Γ(Curve M.ring M.equation, U.1)) (ha : IsRegular a) (hb : IsRegular b)
    (hIa : (identityIdeal M.ring M.equation).ideal U = Ideal.span {a})
    (hIb : (torsionIdeal M.ring M.equation M.law c).ideal U = Ideal.span {b})
    (V : (Curve R W).Opens) (e : V ≤ M.comparison.map ⁻¹ᵁ U.1)
    (eC : V ≤ complement R W G c) :
    ∃ ε : (Γ(Curve M.ring M.equation, U.1))ˣ,
      restrict (complement R W G c) V eC (v : _) * M.comparison.map.appLE U.1 V e b =
        M.comparison.map.appLE U.1 V e ((ε : _) * a^(c^2)) := by
  obtain ⟨hU₀, g, hg, a₀, _, ha₀, e₀, hv⟩ := hv
  letI := hU₀
  obtain ⟨ε, hε⟩ := ArithmeticThetaRelativeKatoNaturalityR0170.relative_kato_cartier_ratio
    M.ring M.equation M.law M.originLaw c hc hc6 g hg U a b ha hb hIa hIb
  refine ⟨ε, ?_⟩
  have H := product_pullback M.comparison.map U.1
    (complement M.ring M.equation M.law c) V e (eC.trans e₀)
    a₀ b ((ε : _) * a^(c^2)) (ha₀ ▸ hε)
  rw [hv]
  simpa only [restrict, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] using H

/-- Two generators of the same principal ideal differ by a unit when one
of them is regular. This includes the zero ring. -/
lemma generator_unit {A : Type u} [CommRing A] (a a₀ : A) (ha : IsRegular a)
    (h : Ideal.span ({a₀} : Set A) = Ideal.span {a}) :
    ∃ e : Aˣ, a₀ = (e : A) * a := by
  obtain ⟨r, hr⟩ := Ideal.span_singleton_le_span_singleton.mp h.le
  obtain ⟨s, hs⟩ := Ideal.span_singleton_le_span_singleton.mp h.ge
  have hrs : r * s = 1 := ha.left (by change a * (r * s) = a * 1; rw [← mul_assoc, ← hr, ← hs, mul_one])
  refine ⟨⟨r, s, hrs, by rw [mul_comm, hrs]⟩, ?_⟩
  simpa only [Units.val_mk, mul_comm] using hr

/-- Changing both regular generators only changes the correcting unit on the
whole affine chart. -/
lemma change_generators {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a b a₀ b₀ : A) (ha : IsRegular a) (hb : IsRegular b)
    (hIa : Ideal.span ({a₀} : Set A) = Ideal.span {a})
    (hIb : Ideal.span ({b₀} : Set A) = Ideal.span {b})
    (z : B) (n : ℕ) (ε₀ : Aˣ) (he : z * φ b₀ = φ ((ε₀ : A) * a₀^n)) :
    ∃ ε : Aˣ, z * φ b = φ ((ε : A) * a^n) := by
  obtain ⟨ea, hea⟩ := generator_unit a a₀ ha hIa
  obtain ⟨eb, heb⟩ := generator_unit b b₀ hb hIb
  refine ⟨eb⁻¹ * ε₀ * ea^n, ?_⟩
  calc
    z * φ b = φ (↑(eb⁻¹) : A) * (z * φ b₀) := by
      rw [heb, map_mul]
      have hi : φ (↑(eb⁻¹) : A) * φ (eb : A) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc
        z * φ b = (φ (↑(eb⁻¹) : A) * φ (eb : A)) * (z * φ b) := by rw [hi, one_mul]
        _ = _ := by ring
    _ = φ ((↑(eb⁻¹) : A) * ((ε₀ : A) * a₀^n)) := by rw [he, ← map_mul]
    _ = φ ((↑(eb⁻¹ * ε₀ * ea^n) : A) * a^n) := by
      rw [hea]
      congr 1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
      ring

lemma regular_restrict {X : Scheme.{u}} (U V : X.affineOpens) (e : V.1 ≤ U.1)
    (a : Γ(X, U.1)) (ha : IsRegular a) : IsRegular (restrict U.1 V.1 e a) := by
  simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp, restrict] using
    regular_appLE (𝟙 X) U V e a ha

/-- At every target point, the normal-model equation yields a unit correcting
any specified pair of regular generators on a smaller affine neighborhood. -/
lemma local_equation (R : Type u) [CommRing R] [Algebra ℚ R]
    (W : WeierstrassCurve R) [W.IsElliptic] (G : Law R W)
    (hG : IsOriginLaw R W G) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (v : UnitSection R W G c) (hv : IsKatoUnit R W G c v)
    (U : (Curve R W).affineOpens) (a b : Γ(Curve R W, U.1))
    (ha : IsRegular a) (hb : IsRegular b)
    (hIa : (identityIdeal R W).ideal U = Ideal.span {a})
    (hIb : (torsionIdeal R W G c).ideal U = Ideal.span {b}) (x : U.1) :
    ∃ (V : (Curve R W).affineOpens) (e : V.1 ≤ U.1), x.1 ∈ V.1 ∧
      ∃ ε : (Γ(Curve R W, V.1))ˣ,
        restrict (complement R W G c) (V.1 ⊓ complement R W G c) inf_le_right (v : _) *
          restrict U.1 (V.1 ⊓ complement R W G c) (inf_le_left.trans e) b =
        restrict V.1 (V.1 ⊓ complement R W G c) inf_le_left
          ((ε : _) * (restrict U.1 V.1 e a)^(c^2)) := by
  obtain ⟨M⟩ := normal_discriminant_model R W
  have hcart := ArithmeticThetaRelativeKatoNaturalityR0170.relative_torsion_cartier
    M.ring M.equation M.law M.originLaw
  obtain ⟨T, hxT, a₀, b₀, ha₀, hb₀, hIa₀, hIb₀⟩ :=
    ArithmeticThetaRelativeKatoNaturalityR0170.RelativeKatoFiberSpecialization.common_cartier_chart
      (identityIdeal M.ring M.equation) (torsionIdeal M.ring M.equation M.law c)
      hcart.1 (hcart.2 c (by omega)) (M.comparison.map x.1)
  letI : Nonempty T.1 := ⟨⟨M.comparison.map x.1, hxT⟩⟩
  obtain ⟨V, hV, hxV, hVT⟩ := exists_isAffineOpen_mem_and_subset
    (show x.1 ∈ U.1 ⊓ M.comparison.map ⁻¹ᵁ T.1 from ⟨x.2, hxT⟩)
  let V' : (Curve R W).affineOpens := ⟨V, hV⟩
  have e : V ≤ U.1 := hVT.trans inf_le_left
  have eT : V ≤ M.comparison.map ⁻¹ᵁ T.1 := hVT.trans inf_le_right
  let φ := (M.comparison.map.appLE T.1 V eT).hom
  let ar := restrict U.1 V e a
  let br := restrict U.1 V e b
  have hA : Ideal.span ({φ a₀} : Set _) = Ideal.span {ar} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hIa₀,
      ← Scheme.IdealSheafData.ideal_comap_of_le _ _ T V' eT,
      NormalModelUnitSpecialization.identity_comap M.comparison,
      ← Scheme.IdealSheafData.map_ideal _ (U := V') e, hIa,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hB : Ideal.span ({φ b₀} : Set _) = Ideal.span {br} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hIb₀,
      ← Scheme.IdealSheafData.ideal_comap_of_le _ _ T V' eT,
      NormalModelUnitSpecialization.torsion_comap M.comparison M.law M.originLaw G hG c,
      ← Scheme.IdealSheafData.map_ideal _ (U := V') e, hIb,
      Ideal.map_span, Set.image_singleton]
    rfl
  let D := V ⊓ complement R W G c
  let ψ := ((Curve R W).presheaf.map (homOfLE (show D ≤ V from inf_le_left)).op).hom
  obtain ⟨ε₀, he₀⟩ := model_chart_equation R W G c hc hc6 v M (hv M)
    T a₀ b₀ ha₀ hb₀ hIa₀ hIb₀ D (inf_le_left.trans eT) inf_le_right
  have he : restrict (complement R W G c) D inf_le_right (v : _) * ψ (φ b₀) =
      ψ ((Units.map φ.toMonoidHom ε₀ : _) * (φ a₀)^(c^2)) := by
    change restrict (complement R W G c) D inf_le_right (v : _) *
      (Curve R W).presheaf.map (homOfLE inf_le_left).op
        (M.comparison.map.appLE T.1 V eT b₀) =
      (Curve R W).presheaf.map (homOfLE inf_le_left).op
        (M.comparison.map.appLE T.1 V eT (ε₀ : _) *
          (M.comparison.map.appLE T.1 V eT a₀)^(c^2))
    simpa only [map_mul, map_pow, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map] using he₀
  obtain ⟨ε, hε⟩ := change_generators ψ ar br (φ a₀) (φ b₀)
    (regular_restrict U V' e a ha) (regular_restrict U V' e b hb) hA hB
    (restrict (complement R W G c) D inf_le_right (v : _)) (c^2)
    (Units.map φ.toMonoidHom ε₀) he
  refine ⟨V', e, hxV, ε, ?_⟩
  change restrict (complement R W G c) D inf_le_right (v : _) *
    restrict V D inf_le_left (restrict U.1 V e b) =
    restrict V D inf_le_left ((ε : _) * ar^(c^2)) at hε
  rw [restrict_trans] at hε
  exact hε

lemma complement_inter_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (b : Γ(X, U.1)) (hb : I.ideal U = Ideal.span {b}) :
    U.1 ⊓ I.support.compl = X.basicOpen b := by
  ext x
  constructor
  · intro hx
    have he : x ∈ I.support ↔ x ∉ X.basicOpen b := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx.1, hb,
        X.zeroLocus_span, X.zeroLocus_singleton]
      rfl
    exact not_not.mp (fun hn => hx.2 (he.mpr hn))
  · intro hx
    have hxU := X.basicOpen_le b hx
    refine ⟨hxU, ?_⟩
    change x ∉ I.support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, hb,
      X.zeroLocus_span, X.zeroLocus_singleton]
    exact fun h => h hx

/-- Restriction away from a regular principal divisor is injective, even on a
nonreduced affine scheme. -/
lemma complement_restrict_injective {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (b : Γ(X, U.1)) (hb : IsRegular b)
    (hIb : I.ideal U = Ideal.span {b}) :
    Function.Injective (restrict U.1 (U.1 ⊓ I.support.compl) inf_le_left) := by
  let φ := (X.presheaf.map (homOfLE (show U.1 ⊓ I.support.compl ≤ U.1 from inf_le_left)).op).hom
  letI := φ.toAlgebra
  letI := U.2.isLocalization_of_eq_basicOpen b (homOfLE inf_le_left)
    (complement_inter_basicOpen I U b hIb)
  exact IsLocalization.injectiveₛ (M := Submonoid.powers b)
    (Γ(X, U.1 ⊓ I.support.compl)) (fun m hm => by
      obtain ⟨n, rfl⟩ := hm
      exact hb.pow n)

/-- An equation for a section on the complement, expressed on a subopen. -/
def Equation {X : Scheme.{u}} (C U : X.Opens) (v : Γ(X, C)) (a b : Γ(X, U))
    (n : ℕ) (V : X.Opens) (e : V ≤ U) (s : Γ(X, V)) : Prop :=
  restrict C (V ⊓ C) inf_le_right v * restrict U (V ⊓ C) (inf_le_left.trans e) b =
    restrict V (V ⊓ C) inf_le_left (s * (restrict U V e a)^n)

lemma restrict_mul {X : Scheme.{u}} (U V : X.Opens) (e : V ≤ U) (a b : Γ(X, U)) :
    restrict U V e (a*b) = restrict U V e a * restrict U V e b := map_mul _ _ _

lemma restrict_pow {X : Scheme.{u}} (U V : X.Opens) (e : V ≤ U) (a : Γ(X, U)) (n : ℕ) :
    restrict U V e (a^n) = (restrict U V e a)^n := map_pow _ _ _

lemma equation_restrict {X : Scheme.{u}} (C U : X.Opens) (v : Γ(X, C)) (a b : Γ(X, U))
    (n : ℕ) (V T : X.Opens) (e : V ≤ U) (eT : T ≤ V) (s : Γ(X, V))
    (h : Equation C U v a b n V e s) :
    Equation C U v a b n T (eT.trans e) (restrict V T eT s) := by
  have hh := congrArg (restrict (V ⊓ C) (T ⊓ C) (inf_le_inf eT le_rfl)) h
  dsimp only [Equation] at h ⊢
  change restrict (V ⊓ C) (T ⊓ C) _
    (restrict C (V ⊓ C) _ v * restrict U (V ⊓ C) _ b) =
    restrict (V ⊓ C) (T ⊓ C) _ (restrict V (V ⊓ C) _ (s * (restrict U V e a)^n)) at hh
  simpa only [restrict_mul, restrict_pow, restrict_trans] using hh

lemma equation_unique {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (v : Γ(X, I.support.compl)) (a b : Γ(X, U.1))
    (ha : IsRegular a) (hb : IsRegular b) (hIb : I.ideal U = Ideal.span {b})
    (n : ℕ) (V : X.affineOpens) (e : V.1 ≤ U.1) (s t : Γ(X, V.1))
    (hs : Equation I.support.compl U.1 v a b n V.1 e s)
    (ht : Equation I.support.compl U.1 v a b n V.1 e t) : s = t := by
  have hbV : I.ideal V = Ideal.span {restrict U.1 V.1 e b} := by
    rw [← I.map_ideal e, hIb, Ideal.map_span, Set.image_singleton]
    rfl
  have hi := complement_restrict_injective I V (restrict U.1 V.1 e b)
    (regular_restrict U V e b hb) hbV
  have he : s * (restrict U.1 V.1 e a)^n = t * (restrict U.1 V.1 e a)^n :=
    hi (hs.symm.trans ht)
  exact ((regular_restrict U V e a ha).pow n).right he

lemma equation_unique_open {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (v : Γ(X, I.support.compl)) (a b : Γ(X, U.1))
    (ha : IsRegular a) (hb : IsRegular b) (hIb : I.ideal U = Ideal.span {b})
    (n : ℕ) (V : X.Opens) (e : V ≤ U.1) (s t : Γ(X, V))
    (hs : Equation I.support.compl U.1 v a b n V e s)
    (ht : Equation I.support.compl U.1 v a b n V e t) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf V s t
  intro x hx
  change X.presheaf.germ V x hx s = X.presheaf.germ V x hx t
  obtain ⟨T, hT, hxT, eT⟩ := exists_isAffineOpen_mem_and_subset hx
  have he := equation_unique I U v a b ha hb hIb n ⟨T, hT⟩ (eT.trans e)
    (restrict V T eT s) (restrict V T eT t)
    (equation_restrict _ _ _ _ _ _ V T e eT s hs)
    (equation_restrict _ _ _ _ _ _ V T e eT t ht)
  have H := congrArg (X.presheaf.germ T x hxT) he
  simpa only [restrict, TopCat.Presheaf.germ_res_apply] using H

/-- The unique local correcting units glue on the full affine open. -/
lemma glue_equation {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (v : Γ(X, I.support.compl)) (a b : Γ(X, U.1))
    (ha : IsRegular a) (hb : IsRegular b) (hIb : I.ideal U = Ideal.span {b}) (n : ℕ)
    (h : ∀ x : U.1, ∃ (V : X.affineOpens) (e : V.1 ≤ U.1), x.1 ∈ V.1 ∧
      ∃ ε : (Γ(X, V.1))ˣ, Equation I.support.compl U.1 v a b n V.1 e (ε : _)) :
    ∃ ε : (Γ(X, U.1))ˣ,
      restrict I.support.compl (U.1 ⊓ I.support.compl) inf_le_right v *
        restrict U.1 (U.1 ⊓ I.support.compl) inf_le_left b =
      restrict U.1 (U.1 ⊓ I.support.compl) inf_le_left ((ε : _) * a^n) := by
  classical
  choose V e hx ε hε using h
  have hcover : U.1 ≤ ⨆ x : U.1, (V x).1 := by
    intro x hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun x => (V x).1)
      (fun x => (ε x : Γ(X, (V x).1))) := by
    intro i j
    exact equation_unique_open I U v a b ha hb hIb n ((V i).1 ⊓ (V j).1)
      (inf_le_left.trans (e i)) _ _
      (equation_restrict _ _ _ _ _ _ _ _ (e i) inf_le_left _ (hε i))
      (equation_restrict _ _ _ _ _ _ _ _ (e j) inf_le_right _ (hε j))
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' (fun x => (V x).1) U.1
    (fun x => homOfLE (e x)) hcover (fun x => (ε x : Γ(X, (V x).1))) hcompat
  change ∀ i, X.presheaf.map (homOfLE (e i)).op s = (ε i : _) at hs
  have hu : IsUnit s := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ U.1 s
    intro x hxU
    change IsUnit (X.presheaf.germ U.1 x hxU s)
    let y : U.1 := ⟨x, hxU⟩
    have H := (ε y).isUnit.map (X.presheaf.germ (V y).1 x (hx y)).hom
    rw [← hs y] at H
    change IsUnit (X.presheaf.germ (V y).1 x (hx y)
      (X.presheaf.map (homOfLE (e y)).op s)) at H
    simpa only [TopCat.Presheaf.germ_res_apply] using H
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  apply TopCat.Presheaf.section_ext X.sheaf (U.1 ⊓ I.support.compl)
  intro x hxU
  change X.presheaf.germ (U.1 ⊓ I.support.compl) x hxU _ =
    X.presheaf.germ (U.1 ⊓ I.support.compl) x hxU _
  let y : U.1 := ⟨x, hxU.1⟩
  have H := hε y
  change Equation I.support.compl U.1 v a b n (V y).1 (e y) (ε y : _) at H
  rw [← hs y] at H
  have H' := congrArg (X.presheaf.germ ((V y).1 ⊓ I.support.compl) x ⟨hx y, hxU.2⟩) H
  simpa only [Equation, restrict, map_mul, map_pow,
    TopCat.Presheaf.germ_res_apply] using H'

end ArbitraryKatoCartierDivisor
open ArithmeticThetaRelativeKatoR0169

/-- The canonical complete Kato unit has the exact Cartier divisor on every
rational-algebra elliptic Weierstrass base, including nonreduced and empty bases. -/
theorem arbitrary_kato_cartier_divisor :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
      [W.IsElliptic] (G : Law R W), IsOriginLaw R W G →
      ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : UnitSection R W G c,
      IsKatoUnit R W G c v → HasCartierDivisor R W G c v := by
  intro R _ _ W _ G hG c hc hc6 v hv
  refine ⟨ArbitraryKatoCartierDivisor.identity_effective R W,
    ArbitraryKatoCartierDivisor.torsion_effective R W G hG c (by omega), ?_⟩
  intro U a b ha hb hIa hIb
  apply ArbitraryKatoCartierDivisor.glue_equation (torsionIdeal R W G c)
    U v.val a b ha hb hIb (c^2)
  exact ArbitraryKatoCartierDivisor.local_equation R W G hG c hc hc6 v hv U a b ha hb hIa hIb

end ArithmeticThetaArbitraryKatoUnitR0249

#print axioms ArithmeticThetaArbitraryKatoUnitR0249.ArbitraryKatoCartierDivisor.torsion_effective

#print axioms ArithmeticThetaArbitraryKatoUnitR0249.arbitrary_kato_cartier_divisor
