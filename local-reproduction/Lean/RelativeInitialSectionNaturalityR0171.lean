import RelativeInitialHodgeSectionR0171
import RelativeHodgePowerBaseChangeR0171

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaRelativeDiscriminantR0171
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
namespace InitialSectionNaturality
open InitialHodgeSection RelativeKatoFiberSpecialization

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

include hGs hb in
/-- Identity charts pull back to identity charts on every nonempty affine
subopen. Regularity follows from the target Cartier divisor, without flatness. -/
lemma chart_pullback (c : ℕ) (U : (Curve R W).affineOpens)
    (V : (Curve S Ws).affineOpens) [Nonempty V.1]
    (h : V.1 ≤ b ⁻¹ᵁ U.1) (a : Γ(Curve R W,U.1))
    (ha : IdentityChart R W G c U a) :
    IdentityChart S Ws Gs c V (b.appLE U.1 V.1 h a) := by
  have hI : (identityIdeal S Ws).ideal V = Ideal.span {b.appLE U.1 V.1 h a} := by
    rw [← identity_comap R W G S Ws Gs ι b hb,
      Scheme.IdealSheafData.ideal_comap_of_le _ b U V h,
      ha.2.1, Ideal.map_span, Set.image_singleton]
  refine ⟨generator_regular (identityIdeal S Ws)
    (generic_not_support _ (relative_torsion_cartier S Ws Gs hGs).1) V _ hI, hI, ?_⟩
  rw [← torsion_comap R W G S Ws Gs ι b hb,
    ← identity_comap R W G S Ws Gs ι b hb,
    Scheme.IdealSheafData.ideal_comap_of_le _ b U V h,
    Scheme.IdealSheafData.ideal_comap_of_le _ b U V h, ha.2.2]

include hG hGs hb in
/-- The exact scaled initial product specializes through ordinary sheaf maps. -/
lemma scaled_product_pullback (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (gs : (Curve S Ws).functionField) (hgs : Normalized S Ws Gs c gs)
    (U : (Curve R W).Opens) (V : (Curve S Ws).Opens)
    [Nonempty U] [Nonempty V] (h : V ≤ b ⁻¹ᵁ U)
    (r : Γ(Curve R W,U)) (hr : (c : (Curve R W).functionField)*g =
      (Curve R W).germToFunctionField U r) :
    (c : (Curve S Ws).functionField)*gs =
      (Curve S Ws).germToFunctionField V (b.appLE U V h r) := by
  obtain ⟨O,hO,hOb,hOc⟩ := complement_chart R W G S Ws Gs hGs ι b hb c (by omega)
  letI := hO
  letI := hOb
  obtain ⟨a₀,ha₀,_⟩ := source_unit R W G hG c hc hc6 g hg O hOc
  have H := pullback_product_relation b U O V (b ⁻¹ᵁ O) h le_rfl a₀
    (c : Γ(Curve R W,U)) r (by rw [ha₀.1, map_natCast, mul_comm]; exact hr)
  rw [(relative_kato_arbitrary_base_change R W G hG S Ws Gs hGs ι b hb
    c hc hc6 g hg gs hgs O (b ⁻¹ᵁ O) le_rfl a₀ hOc ha₀.1).2,
    map_natCast, map_natCast, mul_comm] at H
  exact H


/-- Evaluation through a pointed square commutes with restriction to a
possibly smaller open on the target curve. -/
lemma scalar_square {X Y A B : Scheme.{u}} (p : B ⟶ A) (s : A ⟶ Y)
    (t : B ⟶ X) (f : X ⟶ Y) (hs : t ≫ f = p ≫ s)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (hp : t ⁻¹ᵁ V ≤ p ⁻¹ᵁ (s ⁻¹ᵁ U)) (r : Γ(Y,U)) :
    p.appLE (s ⁻¹ᵁ U) (t ⁻¹ᵁ V) hp (s.app U r) =
      t.app V (f.appLE U V h r) := by
  have H : s.appLE U (s ⁻¹ᵁ U) le_rfl ≫ p.appLE (s ⁻¹ᵁ U) (t ⁻¹ᵁ V) hp =
      f.appLE U V h ≫ t.appLE V (t ⁻¹ᵁ V) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hs]
  simpa only [Scheme.Hom.appLE_eq_app, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom H r

include hb in
lemma value_pullback (n : ℕ)
    (e : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W n) ≅ HodgePower S Ws n)
    (he : IsPowerBaseChange R W S Ws ι b n e)
    (U : (Curve R W).Opens) (V : (Curve S Ws).Opens)
    (h : V ≤ b ⁻¹ᵁ U)
    (hp : origin S Ws ⁻¹ᵁ V ≤ baseMap R S ι ⁻¹ᵁ (origin R W ⁻¹ᵁ U))
    (r a : Γ(Curve R W,U)) :
    res (HodgePower S Ws n) hp
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection (baseMap R S ι)
        ((origin R W).app U r • localPower R W n U a))) =
    (origin S Ws).app V (b.appLE U V h r) •
      localPower S Ws n V (b.appLE U V h a) := by
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, res_smul]
  rw [he U a (origin S Ws ⁻¹ᵁ V) hp (fun _ hx => h hx)]
  rw [power_res S Ws n h]
  congr 1
  exact scalar_square (baseMap R S ι) (origin R W) (origin S Ws) b hb.2.1 U V h hp r

lemma pullback_res {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : V ≤ U) (s : Γ(M,U)) :
    res ((Scheme.Modules.pullback p).obj M) (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => h hx)
      (Scheme.Modules.pullbackLocalSection p s) =
      Scheme.Modules.pullbackLocalSection p (res M h s) := by
  exact Scheme.Modules.map_homOfLE_pullbackLocalSection p h s


include hG hGs hb in
/-- The two global tensors agree on the identity preimage of each affine
subchart of a pulled-back identity chart. -/
lemma local_eq (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6)
    (g : (Curve R W).functionField) (hg : Normalized R W G c g)
    (gs : (Curve S Ws).functionField) (hgs : Normalized S Ws Gs c gs)
    (d : Γ(HodgePower R W (c^2-1),⊤)) (hd : RepresentsInitial R W G c g d)
    (ds : Γ(HodgePower S Ws (c^2-1),⊤)) (hds : RepresentsInitial S Ws Gs c gs ds)
    (e : (Scheme.Modules.pullback (baseMap R S ι)).obj (HodgePower R W (c^2-1)) ≅
      HodgePower S Ws (c^2-1))
    (he : IsPowerBaseChange R W S Ws ι b (c^2-1) e)
    (U : (Curve R W).affineOpens) (V : (Curve S Ws).affineOpens)
    [Nonempty U.1] [Nonempty V.1] (h : V.1 ≤ b ⁻¹ᵁ U.1)
    (a : Γ(Curve R W,U.1)) (ha : IdentityChart R W G c U a) :
    res (HodgePower S Ws (c^2-1)) le_top
      (e.hom.app _ (Scheme.Modules.pullbackLocalSection (baseMap R S ι) d)) =
    res (HodgePower S Ws (c^2-1))
      (show origin S Ws ⁻¹ᵁ V.1 ≤ ⊤ from le_top) ds := by
  have hp : origin S Ws ⁻¹ᵁ V.1 ≤ baseMap R S ι ⁻¹ᵁ (origin R W ⁻¹ᵁ U.1) := by
    intro x hx
    change (baseMap R S ι ≫ origin R W) x ∈ U.1
    rw [baseMap, ← hb.2.1]
    exact h hx
  have hA := chart_pullback R W G S Ws Gs hGs ι b hb c U V h a ha
  obtain ⟨ε,hε,hde⟩ := hd U a ha
  obtain ⟨εs,hεs,hdse⟩ := hds V (b.appLE U.1 V.1 h a) hA
  let εb : Γ(Curve S Ws,V.1)ˣ := ε.map (b.appLE U.1 V.1 h).hom.toMonoidHom
  have hprod : (c : (Curve S Ws).functionField)*gs =
      (Curve S Ws).germToFunctionField V.1
        ((εb : _) * (b.appLE U.1 V.1 h a)^(c^2-1)) := by
    have H := scaled_product_pullback R W G hG S Ws Gs hGs ι b hb
      c hc hc6 g hg gs hgs U.1 V.1 h ((ε : _) * a^(c^2-1)) hε
    change (c : (Curve S Ws).functionField)*gs =
      (Curve S Ws).germToFunctionField V.1
        (b.appLE U.1 V.1 h (ε : _) * (b.appLE U.1 V.1 h a)^(c^2-1))
    simpa only [map_mul, map_pow] using H
  have hεeq : εb = εs :=
    (relative_initial_unit S Ws Gs hGs c hc hc6 gs hgs V _ hA).unique hprod hεs
  calc
    _ = res (HodgePower S Ws (c^2-1)) hp
        (e.hom.app _ (Scheme.Modules.pullbackLocalSection (baseMap R S ι)
          (res (HodgePower R W (c^2-1)) le_top d))) := by
      rw [← pullback_res, ← HodgeBaseChange.hom_res, res_res]
      rfl
    _ = (origin S Ws).app V.1 (b.appLE U.1 V.1 h (ε : _)) •
        localPower S Ws (c^2-1) V.1 (b.appLE U.1 V.1 h a) := by
      rw [hde]
      exact value_pullback R W G S Ws Gs ι b hb (c^2-1) e he U.1 V.1 h hp (ε : _) a
    _ = res (HodgePower S Ws (c^2-1)) le_top ds := by
      rw [hdse]
      change (origin S Ws).app V.1 (εb : _) • _ = _
      rw [hεeq]

end InitialSectionNaturality
open InitialSectionNaturality InitialHodgeSection

/-- Intrinsic initial Hodge sections commute with every pointed Cartesian
base change, using sheaf pullbacks even when no function-field map exists. -/
theorem relative_initial_section_naturality :
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve R W)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve R W)] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra ℚ S] (Ws : WeierstrassCurve S) [Ws.IsElliptic] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.Curve S Ws)] [AlgebraicGeometry.IsIntegral (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaRelativeKatoR0169.GenericCurve S Ws)] (Gs : ArithmeticThetaRelativeKatoR0169.Law S Ws) (hGs : ArithmeticThetaRelativeKatoR0169.IsOriginLaw S Ws Gs) (ι : R →+* S) (b : Quiver.Hom (ArithmeticThetaRelativeKatoR0169.Curve S Ws) (ArithmeticThetaRelativeKatoR0169.Curve R W)) (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b) (c : ℕ) (hc : 1 < c) (hc6 : Nat.Coprime c 6) (g : (ArithmeticThetaRelativeKatoR0169.Curve R W).functionField) (hg : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized R W G c g) (gs : (ArithmeticThetaRelativeKatoR0169.Curve S Ws).functionField) (hgs : ArithmeticThetaRelativeKatoNaturalityR0170.Normalized S Ws Gs c gs) (d : (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W (c^2-1)).presheaf.obj (Opposite.op ⊤)) (hd : ArithmeticThetaRelativeDiscriminantR0171.RepresentsInitial R W G c g d) (ds : (ArithmeticThetaRelativeDiscriminantR0171.HodgePower S Ws (c^2-1)).presheaf.obj (Opposite.op ⊤)) (hds : ArithmeticThetaRelativeDiscriminantR0171.RepresentsInitial S Ws Gs c gs ds) (e : CategoryTheory.Iso ((AlgebraicGeometry.Scheme.Modules.pullback (ArithmeticThetaRelativeDiscriminantR0171.baseMap R S ι)).obj (ArithmeticThetaRelativeDiscriminantR0171.HodgePower R W (c^2-1))) (ArithmeticThetaRelativeDiscriminantR0171.HodgePower S Ws (c^2-1))) (he : ArithmeticThetaRelativeDiscriminantR0171.IsPowerBaseChange R W S Ws ι b (c^2-1) e), ArithmeticThetaRelativeDiscriminantR0171.InitialBaseChange R W S Ws ι (c^2-1) e d ds := by
  intro R _ _ _ _ _ W _ _ _ _ _ G hG S _ _ _ _ _ Ws _ _ _ _ _ Gs hGs
    ι b hb c hc hc6 g hg gs hgs d hd ds hds e he
  classical
  have hcharts (x : Base S) : ∃ (U : (Curve R W).affineOpens)
      (a : Γ(Curve R W,U.1)), origin R W (baseMap R S ι x) ∈ U.1 ∧
        IdentityChart R W G c U a :=
    relative_identity_torsion_neighborhood R W G hG c (by omega) _
  choose U a hxU ha using hcharts
  have htargets (x : Base S) : ∃ V : (Curve S Ws).affineOpens,
      origin S Ws x ∈ V.1 ∧ V.1 ≤ b ⁻¹ᵁ (U x).1 := by
    have hx : origin S Ws x ∈ b ⁻¹ᵁ (U x).1 := by
      change (origin S Ws ≫ b) x ∈ (U x).1
      rw [hb.2.1]
      exact hxU x
    obtain ⟨V,hV,hxV,hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨⟨V,hV⟩,hxV,hVU⟩
  choose V hxV hVU using htargets
  unfold InitialBaseChange
  change e.hom.app ⊤ (Scheme.Modules.pullbackLocalSection (baseMap R S ι) d) =
    res (HodgePower S Ws (c^2-1)) le_rfl ds
  rw [res_self]
  apply TopCat.Sheaf.eq_of_locally_eq'
    ⟨(HodgePower S Ws (c^2-1)).presheaf, (HodgePower S Ws (c^2-1)).isSheaf⟩
    (fun x => origin S Ws ⁻¹ᵁ (V x).1) ⊤ (fun _ => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x,hxV x⟩)
  intro x
  letI : Nonempty (U x).1 := ⟨⟨_,hxU x⟩⟩
  letI : Nonempty (V x).1 := ⟨⟨_,hxV x⟩⟩
  exact local_eq R W G hG S Ws Gs hGs ι b hb c hc hc6 g hg gs hgs
    d hd ds hds e he (U x) (V x) (hVU x) (a x) (ha x)

#print axioms relative_initial_section_naturality
end ArithmeticThetaRelativeDiscriminantR0171
