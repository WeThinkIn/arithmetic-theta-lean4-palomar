module

public import ArithmeticSectionsDefinitionsR0236

@[expose] public section

/-! Naturality of the intrinsic discriminant through the actual coefficient
classifier and its normalized Hodge comparison. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticSectionsR0236
namespace OpenDiscriminantConstantNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaLocalWeierstrassR0203 hiding Base
open ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaLevelConstantsR0234
open ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182

/-- The general-scheme family, on an affine base, retains exactly its law. -/
def affineFamily {R : Type} [CommRing R] (F : Family (Base R)) : EllipticFamily R where
  curve := F.curve
  projection := F.p
  law := { mul := F.law.mul, one := F.law.one, inv := F.law.inv
           mul_assoc := F.law.mul_assoc, one_mul := F.law.one_mul
           mul_one := F.law.mul_one, inv_mul_cancel := F.law.inv_mul_cancel
           mul_natural := F.law.mul_natural }
  commutative := F.law.mul_comm
  proper := F.proper
  smooth := F.dimension
  connected := F.connected

lemma pullbackEqIso_natural {X Y : Scheme} {p q : X ⟶ Y} (h : p = q)
    {M N : Y.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pullback p).map f ≫ (pullbackEqIso h N).hom =
      (pullbackEqIso h M).hom ≫ (Scheme.Modules.pullback q).map f := by
  subst q
  simp [pullbackEqIso]

lemma cotangent_change_base {S T : Scheme} (E : Family S) (F : Family T)
    (f : F.curve ⟶ E.curve) {b c : T ⟶ S} (h : b = c)
    (hb : F.zero ≫ f = b ≫ E.zero) (hc : F.zero ≫ f = c ≫ E.zero)
    (i : (Scheme.Modules.pullback f).obj E.zero.ker.module ≅ F.zero.ker.module) :
    (cotangentComparison E F b f hb i).hom =
      (pullbackEqIso h (Cotangent E)).hom ≫ (cotangentComparison E F c f hc i).hom := by
  subst c
  simp [pullbackEqIso]

/-- Naturality of the conormal derivative with an intermediate base map. -/
lemma conormal_differential_square {A R : Type} [CommRing A] [CommRing R]
    {Z : Scheme} (U : Family (Base A)) (F : Family (Base R))
    (j : Z ⟶ Base A) (b : Base R ⟶ Z) (f : F.curve ⟶ U.curve)
    (ρ : A →+* R) (hρ : Spec.map (CommRingCat.ofHom ρ) = b ≫ j)
    (hc : IsPullback f F.p U.p (Spec.map (CommRingCat.ofHom ρ)))
    (hz : F.zero ≫ f = Spec.map (CommRingCat.ofHom ρ) ≫ U.zero)
    (hz' : F.zero ≫ f = (b ≫ j) ≫ U.zero)
    (i : (Scheme.Modules.pullback f).obj U.zero.ker.module ≅ F.zero.ker.module)
    (hi : IdealCompatible U F f i)
    (e : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback U.zero).obj U.p.kaehler)) ≅ Cotangent F)
    (he : (Scheme.Modules.pullback b).map
      ((Scheme.Modules.pullback j).map (affineDifferential U)) ≫ e.hom =
      (Scheme.Modules.pullbackComp b j).hom.app (Cotangent U) ≫
        (cotangentComparison U F (b ≫ j) f hz' i).hom) :
    e.hom ≫ affineDifferential F =
      (Scheme.Modules.pullbackComp b j).hom.app
        ((Scheme.Modules.pullback U.zero).obj U.p.kaehler) ≫
      (pullbackEqIso hρ.symm ((Scheme.Modules.pullback U.zero).obj U.p.kaehler)).hom ≫
      (affineHodgeComparison U F ρ f hc hz).hom := by
  letI := AffineConormalHodgeNaturality.differential_isIso U
  apply (cancel_epi ((Scheme.Modules.pullback b).map
    ((Scheme.Modules.pullback j).map (affineDifferential U)))).mp
  rw [← Category.assoc _ e.hom, he]
  have hn := (affine_conormal_hodge_naturality A R U F ρ f hc hz).2.2 i hi
  have hnatural := (Scheme.Modules.pullbackComp b j).hom.naturality (affineDifferential U)
  simp only [Functor.comp_map] at hnatural
  rw [← Category.assoc _ ((Scheme.Modules.pullbackComp b j).hom.app _), hnatural]
  have heq : (Scheme.Modules.pullback (b ≫ j)).map (affineDifferential U) ≫
      (pullbackEqIso hρ.symm ((Scheme.Modules.pullback U.zero).obj U.p.kaehler)).hom =
      (pullbackEqIso hρ.symm (Cotangent U)).hom ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ρ))).map (affineDifferential U) := by
    exact pullbackEqIso_natural hρ.symm (affineDifferential U)
  have hcot : (cotangentComparison U F (b ≫ j) f hz' i).hom =
      (pullbackEqIso hρ.symm (Cotangent U)).hom ≫
        (cotangentComparison U F (Spec.map (CommRingCat.ofHom ρ)) f hz i).hom :=
    cotangent_change_base U F f hρ.symm hz' hz i
  simp only [Category.assoc]
  rw [hcot]
  simp only [Category.assoc]
  rw [← hn, ← Category.assoc ((Scheme.Modules.pullback (b ≫ j)).map (affineDifferential U)), heq]
  simp only [Category.assoc]


/-- On an affine classified family the normalized conormal comparison is the
canonical differential comparison, after the actual conormal derivative. -/
lemma classifier_differential {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : LevelData k L) (F : Family (Base R))
    (b : Base R ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve)
    (ρ : D.atlas.quotient.ring →+* R)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = b ≫ D.quotient.inclusion)
    (hc : IsPullback f F.p D.atlas.descent.family.projection (Spec.map (CommRingCat.ofHom ρ)))
    (hz : F.zero ≫ f = Spec.map (CommRingCat.ofHom ρ) ≫ zero D.atlas.descent.family)
    (e : (Scheme.Modules.pullback b).obj (weight D) ≅ Cotangent F)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b f e) :
    e.hom ≫ affineDifferential F =
      (Scheme.Modules.pullbackComp b D.quotient.inclusion).hom.app
        (hodge D.atlas.descent.family) ≫
      (pullbackEqIso hρ.symm (hodge D.atlas.descent.family)).hom ≫
      (affineHodgeComparison (universalFamily k L D.atlas) F ρ f hc hz).hom := by
  obtain ⟨hz', i, hi, he⟩ := he
  exact conormal_differential_square (universalFamily k L D.atlas) F
    D.quotient.inclusion b f ρ hρ hc hz hz' i hi e he


/-- Actual pointed Cartesian comparison between the two affine families. -/
structure FamilyMap {S T : Type} [CommRing S] [CommRing T]
    (E : EllipticFamily S) (F : EllipticFamily T) where
  scalar : S →+* T
  map : F.curve ⟶ E.curve
  cartesian : IsPullback map F.projection E.projection (baseMap S T scalar)
  origin_eq : zero F ≫ map = baseMap S T scalar ≫ zero E
  nsmul_eq : ∀ n, F.law.schemeNsmul n ≫ map = map ≫ E.law.schemeNsmul n

def familyIso {S T : Type} [CommRing S] [CommRing T]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F) :
    (Scheme.Modules.pullback (baseMap S T B.scalar)).obj (hodge E) ≅ hodge F := by
  letI : Algebra S T := B.scalar.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso E.projection F.projection B.map B.cartesian
    (zero E) (zero F) B.origin_eq

def compTest {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G) :
    ArithmeticThetaOpenHodgeR0180.Test S E R W G where
  scalar := C.scalar.comp B.scalar
  map := C.map ≫ B.map
  cartesian := by
    simpa only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp] using
      C.cartesian.paste_horiz B.cartesian
  origin_eq := by
    rw [← Category.assoc, C.origin_eq, Category.assoc, B.origin_eq, ← Category.assoc]
    simp only [baseMap, CommRingCat.ofHom_comp, Spec.map_comp]
  nsmul_eq := by
    intro n
    rw [← Category.assoc, C.nsmul_eq, Category.assoc, B.nsmul_eq, Category.assoc]


lemma compTest_scalar {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G) :
    (compTest B C).scalar = C.scalar.comp B.scalar := rfl

lemma familyIso_localPower {S T : Type} [CommRing S] [CommRing T]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    (n : ℕ) (U : E.curve.Opens) (a : Γ(E.curve, U)) (V : (Base T).Opens)
    (h₁ : V ≤ baseMap S T B.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ zero F ⁻¹ᵁ (B.map ⁻¹ᵁ U)) :
    res (power F n) h₁
      ((tensorComparison (baseMap S T B.scalar) (hodge E) (hodge F)
        (familyIso B) n).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap S T B.scalar)
          (familyLocalPower E n U a))) =
      res (power F n) h₂ (familyLocalPower F n (B.map ⁻¹ᵁ U) (B.map.app U a)) := by
  letI : Algebra S T := B.scalar.toAlgebra
  letI := E.smooth
  unfold familyLocalPower
  rw [tensorComparison_section]
  change (tensorPower (Base T) (hodge F) n).presheaf.map (homOfLE h₁).op
    (tensorPowerSection _ _ n _ _) =
      (tensorPower (Base T) (hodge F) n).presheaf.map (homOfLE h₂).op
        (tensorPowerSection _ _ n _ _)
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection (Base T) (hodge F) n V)
    (pointedDifferentialIso_D E.projection F.projection B.map B.cartesian
      (zero E) (zero F) B.origin_eq U a V h₁ h₂)

def familyDiff {S : Type} [CommRing S] (E : EllipticFamily S)
    (U : E.curve.Opens) (a : Γ(E.curve, U)) : Γ(hodge E, zero E ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection (zero E)
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD E.projection U a)

def testDiff (R : Type) [CommRing R] (W : WeierstrassCurve R)
    (U : (Curve R W).Opens) (a : Γ(Curve R W, U)) :
    Γ(Hodge R W, origin R W ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection (origin R W)
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD (structureMap R W) U a)

lemma familyIso_diff {S T : Type} [CommRing S] [CommRing T]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    (U : E.curve.Opens) (a : Γ(E.curve, U)) (V : (Base T).Opens)
    (h₁ : V ≤ baseMap S T B.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ zero F ⁻¹ᵁ (B.map ⁻¹ᵁ U)) :
    res (hodge F) h₁ ((familyIso B).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S T B.scalar) (familyDiff E U a))) =
    res (hodge F) h₂ (familyDiff F (B.map ⁻¹ᵁ U) (B.map.app U a)) := by
  letI : Algebra S T := B.scalar.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso_D E.projection F.projection B.map B.cartesian
    (zero E) (zero F) B.origin_eq U a V h₁ h₂

lemma testDiff_map_congr {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {X : Scheme} (f g : Curve R W ⟶ X) (h : f = g)
    (U : X.Opens) (a : Γ(X, U)) (V : (Base R).Opens)
    (hf : V ≤ origin R W ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : V ≤ origin R W ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    res (Hodge R W) hf (testDiff R W (f ⁻¹ᵁ U) (f.app U a)) =
    res (Hodge R W) hg (testDiff R W (g ⁻¹ᵁ U) (g.app U a)) := by
  subst g
  rfl

lemma composeComparison_section_of_local {X Y Z : Scheme}
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) (hr : r = q ≫ p)
    (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (U : X.Opens) (s : Γ(M, U)) (W : Y.Opens) (t : Γ(N, W))
    (hN : p ⁻¹ᵁ U ≤ W)
    (hs : e.hom.app _ (Scheme.Modules.pullbackLocalSection p s) = res N hN t)
    (V : Z.Opens) (h₁ : V ≤ r ⁻¹ᵁ U) (h₂ : V ≤ q ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    res P h₁ ((composeComparison p q r hr M N P e f).hom.app _
      (Scheme.Modules.pullbackLocalSection r s)) =
    res P (show V ≤ q ⁻¹ᵁ W from fun z hz => hN (h₂ hz))
      (f.hom.app _ (Scheme.Modules.pullbackLocalSection q t)) := by
  rw [composeComparison_section p q r hr M N P e f U s V h₁ h₂, hs,
    ← InitialSectionNaturality.pullback_res, ← hom_res, InitialHodgeSection.res_res]

lemma double_pullback_iso_ext {X Y Z : Scheme} (p : Z ⟶ Y) (q : Y ⟶ X)
    (M : X.Modules) (N : Z.Modules)
    (e f : (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M) ≅ N)
    (h : ∀ z : Z, ∃ (U : X.Opens) (s : Γ(M, U)),
      q (p z) ∈ U ∧ IsFrame M U s ∧
      res N le_rfl (e.hom.app (p ⁻¹ᵁ (q ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q s))) =
      res N le_rfl (f.hom.app (p ⁻¹ᵁ (q ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q s)))) :
    e = f := by
  apply Iso.ext
  apply hom_ext_frames
  intro z
  obtain ⟨U, s, hz, hs, heq⟩ := h z
  refine ⟨p ⁻¹ᵁ (q ⁻¹ᵁ U),
    Scheme.Modules.pullbackLocalSection p (Scheme.Modules.pullbackLocalSection q s),
    hz, pullback_frame p _ _ (pullback_frame q M _ hs), ?_⟩
  exact (res_bijective N (U := p ⁻¹ᵁ (q ⁻¹ᵁ U))
    (V := p ⁻¹ᵁ (q ⁻¹ᵁ U)) le_rfl le_rfl).1 heq

lemma family_iso_ext {S : Type} [CommRing S] (E : EllipticFamily S)
    {Z : Scheme} (p : Z ⟶ Base S) (N : Z.Modules)
    (e f : (Scheme.Modules.pullback p).obj (hodge E) ≅ N)
    (h : ∀ (U : E.curve.Opens) (a : Γ(E.curve, U)),
      res N le_rfl (e.hom.app (p ⁻¹ᵁ (zero E ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection p (familyDiff E U a))) =
      res N le_rfl (f.hom.app (p ⁻¹ᵁ (zero E ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection p (familyDiff E U a)))) : e = f := by
  apply double_pullback_iso_ext p (zero E) E.projection.kaehler N e f
  intro x
  letI := E.smooth
  obtain ⟨U, a, hx, hf⟩ := exists_exact_differential_frame E.projection (zero E (p x))
  exact ⟨U, ArithmeticThetaCompactifiedDifferentialR0145.relativeD E.projection U a,
    hx, hf, h U a⟩

lemma family_iso_ext_implicit_indices {S : Type} [CommRing S] (E : EllipticFamily S)
    {Z : Scheme} (p : Z ⟶ Base S) (N : Z.Modules)
    (e f : (Scheme.Modules.pullback p).obj (hodge E) ≅ N)
    (Q : E.curve.Opens → Z.Opens)
    (hQ : ∀ U, p ⁻¹ᵁ (zero E ⁻¹ᵁ U) ≤ Q U)
    (h : ∀ (U : E.curve.Opens) (a : Γ(E.curve, U)) (V : Z.Opens)
      (h₁ : V ≤ p ⁻¹ᵁ (zero E ⁻¹ᵁ U)) (_ : V ≤ Q U),
      res N h₁ (e.hom.app _
        (Scheme.Modules.pullbackLocalSection p (familyDiff E U a))) =
      res N h₁ (f.hom.app _
        (Scheme.Modules.pullbackLocalSection p (familyDiff E U a)))) : e = f := by
  apply family_iso_ext E p N e f
  exact fun U a => h U a _ le_rfl (hQ U)

lemma pointed_preimage_inclusion {X Y A B : Scheme}
    (p : B ⟶ A) (s : A ⟶ Y) (t : B ⟶ X) (f : X ⟶ Y)
    (h : t ≫ f = p ≫ s) (U : Y.Opens) :
    p ⁻¹ᵁ (s ⁻¹ᵁ U) ≤ t ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro y hy
  change (t ≫ f) y ∈ U
  rw [h]
  exact hy

def testBase {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G) :
    Spec (CommRingCat.of R) ⟶ Base S := baseMap S R C.scalar

lemma testBase_eq {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G) :
    testBase C = baseMap S R C.scalar := rfl

def testComparison {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G) :
    (Scheme.Modules.pullback (testBase C)).obj (hodge E) ≅ Hodge R W := comparison C

lemma testComparison_eq {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G) :
    testComparison C = comparison C := rfl

lemma testComparison_diff {S R : Type} [CommRing S] [CommRing R]
    {E : EllipticFamily S} {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (U : E.curve.Opens) (a : Γ(E.curve, U)) (V : (Base R).Opens)
    (h₁ : V ≤ testBase C ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    res (Hodge R W) h₁ ((testComparison C).hom.app _
      (Scheme.Modules.pullbackLocalSection (testBase C) (familyDiff E U a))) =
    res (Hodge R W) h₂ (testDiff R W (C.map ⁻¹ᵁ U) (C.map.app U a)) := by
  letI : Algebra S R := C.scalar.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso_D E.projection (structureMap R W) C.map C.cartesian
    (zero E) (origin R W) C.origin_eq U a V h₁ h₂

lemma typed_family_line_local {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G)
    (D : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (hm : C.map ≫ B.map = D.map)
    (hbase : testBase D = testBase C ≫ baseMap S T B.scalar)
    (U : E.curve.Opens) (a : Γ(E.curve, U)) (V : (Spec (CommRingCat.of R)).Opens)
    (h₁ : V ≤ testBase D ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (hD : V ≤ origin R W ⁻¹ᵁ (D.map ⁻¹ᵁ U)) :
    res (Hodge R W) h₁ ((testComparison D).hom.app _
      (Scheme.Modules.pullbackLocalSection (testBase D) (familyDiff E U a))) =
    res (Hodge R W) h₁
      ((composeComparison (baseMap S T B.scalar) (testBase C)
        (testBase D) hbase (hodge E) (hodge F) (Hodge R W)
        (familyIso B) (testComparison C)).hom.app _
          (Scheme.Modules.pullbackLocalSection (testBase D) (familyDiff E U a))) := by
  have hV : V ≤ testBase C ⁻¹ᵁ
      (baseMap S T B.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U)) := by
    intro y hy
    change (testBase C ≫ baseMap S T B.scalar) y ∈ zero E ⁻¹ᵁ U
    rw [← hbase]
    exact h₁ hy
  have hB : baseMap S T B.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U) ≤
      zero F ⁻¹ᵁ (B.map ⁻¹ᵁ U) := by
    intro y hy
    change (zero F ≫ B.map) y ∈ U
    rw [B.origin_eq]
    exact hy
  have hC : V ≤ origin R W ⁻¹ᵁ (C.map ⁻¹ᵁ (B.map ⁻¹ᵁ U)) := by
    intro y hy
    change (origin R W ≫ C.map ≫ B.map) y ∈ U
    rw [hm]
    exact hD hy
  have hleft := testComparison_diff D U a V h₁ hD
  have hinner := familyIso_diff B U a
    (baseMap S T B.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U)) le_rfl hB
  have hinner' : (familyIso B).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap S T B.scalar) (familyDiff E U a)) =
      res (hodge F) hB (familyDiff F (B.map ⁻¹ᵁ U) (B.map.app U a)) :=
    (res_refl _ _).symm.trans hinner
  have hcomp := composeComparison_section_of_local
    (baseMap S T B.scalar) (testBase C) (testBase D) hbase
    (hodge E) (hodge F) (Hodge R W) (familyIso B) (testComparison C)
    (zero E ⁻¹ᵁ U) (familyDiff E U a)
    (zero F ⁻¹ᵁ (B.map ⁻¹ᵁ U)) (familyDiff F (B.map ⁻¹ᵁ U) (B.map.app U a))
    hB hinner' V h₁ hV
  have hlast := testComparison_diff C (B.map ⁻¹ᵁ U) (B.map.app U a)
    V (fun y hy => hB (hV hy)) hC
  have hvalue : res (Hodge R W) hC
      (testDiff R W (C.map ⁻¹ᵁ (B.map ⁻¹ᵁ U)) (C.map.app _ (B.map.app U a))) =
      res (Hodge R W) hD (testDiff R W (D.map ⁻¹ᵁ U) (D.map.app U a)) :=
    testDiff_map_congr W (C.map ≫ B.map) D.map hm U a V hC hD
  exact hleft.trans (hcomp.trans (hlast.trans hvalue)).symm

lemma typed_family_line_refinement {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G)
    (D : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (hm : C.map ≫ B.map = D.map)
    (hbase : testBase D = testBase C ≫ baseMap S T B.scalar)
    :
    testComparison D =
      composeComparison (baseMap S T B.scalar) (testBase C)
        (testBase D) hbase
        (hodge E) (hodge F) (Hodge R W)
        (familyIso B)
        (testComparison C) := by
  exact family_iso_ext_implicit_indices (Z := Spec (CommRingCat.of R)) E (testBase D) (Hodge R W)
    (testComparison D)
    (composeComparison (baseMap S T B.scalar) (testBase C)
      (testBase D) hbase (hodge E) (hodge F) (Hodge R W)
      (familyIso B) (testComparison C))
    (fun U => origin R W ⁻¹ᵁ (D.map ⁻¹ᵁ U))
    (fun U => pointed_preimage_inclusion (testBase D) (zero E) (origin R W) D.map D.origin_eq U) (typed_family_line_local B C D hm hbase)

lemma family_power_refinement_of_line {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G)
    (D : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (hm : C.map ≫ B.map = D.map)
    (hbase : baseMap S R D.scalar = baseMap T R C.scalar ≫ baseMap S T B.scalar)
    (hline : comparison D =
      composeComparison (baseMap S T B.scalar) (baseMap T R C.scalar)
        (baseMap S R D.scalar) hbase (hodge E) (hodge F) (Hodge R W)
        (familyIso B) (comparison C))
    (n : ℕ) :
    powerComparison D n =
      composeComparison (baseMap S T B.scalar) (baseMap T R C.scalar)
        (baseMap S R D.scalar) hbase
        (power E n) (power F n) (HodgePower R W n)
        (tensorComparison (baseMap S T B.scalar) (hodge E) (hodge F) (familyIso B) n)
        (powerComparison C n) := by
  unfold powerComparison
  rw [hline]
  exact ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorComparison_comp_eq
    (baseMap S T B.scalar) (baseMap T R C.scalar) (baseMap S R D.scalar) hbase
    (hodge E) (hodge F) (Hodge R W)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible E) (familyIso B) (comparison C) n

lemma family_comparison_refinement {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G)
    (D : ArithmeticThetaOpenHodgeR0180.Test S E R W G)
    (hm : C.map ≫ B.map = D.map)
    (hbase : baseMap S R D.scalar = baseMap T R C.scalar ≫ baseMap S T B.scalar)
    (n : ℕ) :
    powerComparison D n =
      composeComparison (baseMap S T B.scalar) (baseMap T R C.scalar)
        (baseMap S R D.scalar) hbase
        (power E n) (power F n) (HodgePower R W n)
        (tensorComparison (baseMap S T B.scalar) (hodge E) (hodge F) (familyIso B) n)
        (powerComparison C n) := by
  exact family_power_refinement_of_line B C D hm hbase
    (typed_family_line_refinement B C D hm hbase) n

lemma compTest_comparison {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G) (n : ℕ) :
    powerComparison (compTest B C) n =
      composeComparison (baseMap S T B.scalar) (baseMap T R C.scalar)
        (baseMap S R (compTest B C).scalar) (by simp only [compTest_scalar, baseMap, CommRingCat.ofHom_comp, Spec.map_comp])
        (power E n) (power F n) (HodgePower R W n)
        (tensorComparison (baseMap S T B.scalar) (hodge E) (hodge F) (familyIso B) n)
        (powerComparison C n) := by
  exact family_comparison_refinement B C (compTest B C) rfl
    (by simp only [compTest_scalar, baseMap, CommRingCat.ofHom_comp, Spec.map_comp]) n

#print axioms compTest_comparison


lemma compTest_section {S T R : Type} [CommRing S] [CommRing T] [CommRing R]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    {W : WeierstrassCurve R} {G : Law R W}
    (C : ArithmeticThetaOpenHodgeR0180.Test T F R W G) (n : ℕ)
    (d : Γ(power E n, ⊤)) :
    pullSection C n (powerTransport (baseMap S T B.scalar) (hodge E) (hodge F)
      (familyIso B) n d) = pullSection (compTest B C) n d := by
  change transportSection (baseMap T R C.scalar) _ _ _
    (transportSection (baseMap S T B.scalar) _ _ _ d) =
      transportSection (baseMap S R (compTest B C).scalar) _ _
        (powerComparison (compTest B C) n) d
  rw [compTest_comparison,
    ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.transportSection_comp_eq]

/-- Intrinsic initial tensors agree under every actual family comparison for
which the target admits the accepted normal Weierstrass atlas. -/
lemma family_discriminant_naturality {S T : Type} [CommRing S] [CommRing T]
    {E : EllipticFamily S} {F : EllipticFamily T} (B : FamilyMap E F)
    (A : Atlas T F) (d : Γ(power E 24, ⊤)) (e : Γ(power F 24, ⊤))
    (hd : IsD2 E d) (he : IsD2 F e) :
    powerTransport (baseMap S T B.scalar) (hodge E) (hodge F)
      (familyIso B) 24 d = e := by
  apply sections_ext_cover (fun i => Base (A.chart i).ring)
    (fun i => baseMap T (A.chart i).ring (A.chart i).comparison.scalar)
    (fun i => (A.chart i).openImmersion) A.covers
  intro i
  let C := A.chart i
  have hgeom := relative_curve_geometry C.ring C.equation
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.1
  obtain ⟨g, hg⟩ := normalized_exists C.ring C.equation C.law C.originLaw
    5 (by norm_num) (by norm_num)
  have huniq := relative_initial_hodge_section C.ring C.equation C.law C.originLaw
    5 (by norm_num) (by norm_num) g hg
  have hlocal : pullSection (compTest B C.comparison) 24 d =
      pullSection C.comparison 24 e :=
    huniq.unique
      ⟨hd.2 C.ring C.equation C.law C.originLaw (compTest B C.comparison) g hg,
        pullSection_frame (compTest B C.comparison) 24 d hd.1⟩
      ⟨he.2 C.ring C.equation C.law C.originLaw C.comparison g hg,
        pullSection_frame C.comparison 24 e he.1⟩
  have hlocal' := (compTest_section B C.comparison 24 d).trans hlocal
  apply (ConcreteCategory.bijective_of_isIso ((powerComparison C.comparison 24).hom.app
    (baseMap T C.ring C.comparison.scalar ⁻¹ᵁ ⊤))).1
  simpa only [pullSection, res_refl] using hlocal'


#print axioms family_discriminant_naturality

lemma one_section {S : Type} [CommRing S] (E : EllipticFamily S)
    {T : Scheme} (t : T ⟶ Base S) :
    (E.law.one t).val = t ≫ zero E := by
  exact (congrArg Subtype.val
    (E.law.one_natural (𝟙 _) t t (Category.comp_id t))).symm

lemma family_nsmul_comp {S T : Type} [CommRing S] [CommRing T]
    (E : EllipticFamily S) (F : EllipticFamily T) (ρ : S →+* T)
    (f : F.curve ⟶ E.curve) (hc : IsPullback f F.projection E.projection (baseMap S T ρ))
    (hm : ∀ {U : Scheme} (t : U ⟶ Base T) (x y : SchemeHomOver t F.projection),
      (F.law.mul t x y).val ≫ f =
      (E.law.mul (t ≫ baseMap S T ρ)
        ⟨x.val ≫ f, by rw [Category.assoc, hc.w, ← Category.assoc, x.property]⟩
        ⟨y.val ≫ f, by rw [Category.assoc, hc.w, ← Category.assoc, y.property]⟩).val)
    (hz : zero F ≫ f = baseMap S T ρ ≫ zero E) (n : ℕ) :
    F.law.schemeNsmul n ≫ f = f ≫ E.law.schemeNsmul n := by
  have hn {U : Scheme} (t : U ⟶ Base T) (x : SchemeHomOver t F.projection) (m : ℕ) :
      (F.law.nsmul t m x).val ≫ f =
      (E.law.nsmul (t ≫ baseMap S T ρ) m
        ⟨x.val ≫ f, by rw [Category.assoc, hc.w, ← Category.assoc, x.property]⟩).val := by
    induction m with
    | zero =>
      change (F.law.one t).val ≫ f = (E.law.one (t ≫ baseMap S T ρ)).val
      rw [one_section, Category.assoc, hz, ← Category.assoc, one_section]
    | succ m ih =>
      rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, hm,
        GoodReductionJacobian.RelativeGroupLaw.nsmul_succ]
      congr 2
      exact Subtype.ext ih
  have hnat := congrArg Subtype.val (E.law.nsmul_natural E.projection
    (F.projection ≫ baseMap S T ρ) f hc.w n GoodReductionJacobian.RelativeGroupLaw.idPoint)
  rw [GoodReductionJacobian.RelativeGroupLaw.schemeNsmul, hn]
  simpa only [GoodReductionJacobian.RelativeGroupLaw.schemeNsmul,
    GoodReductionJacobian.schemeHomOverComp, Category.id_comp, Category.comp_id] using hnat.symm

/-- Classifying maps preserve all multiplication maps, not just the marked points. -/
def classifierFamilyMap {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : LevelData k L) (F : Family (Base R))
    (σ : Base R ⟶ Base k) (M : FullLevel F L)
    (b : Base R ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve)
    (h : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b f) :
    FamilyMap D.atlas.descent.family (affineFamily F) := by
  let ρ : D.atlas.quotient.ring →+* R := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have hρ : baseMap _ _ ρ = b ≫ D.quotient.inclusion := Spec.map_preimage _
  have hc : IsPullback f F.p D.atlas.descent.family.projection (baseMap _ _ ρ) := by
    rw [hρ]; exact h.2.1
  have hz : zero (affineFamily F) ≫ f =
      baseMap _ _ ρ ≫ zero D.atlas.descent.family := by
    rw [hρ]; exact h.2.2.1
  refine ⟨ρ, f, hc, hz, ?_⟩
  intro n
  apply family_nsmul_comp D.atlas.descent.family (affineFamily F) ρ f hc _ hz n
  intro T t x y
  have hm := h.2.2.2.2.2
  rw [← hρ] at hm
  exact (hm T t x y _ _ rfl rfl).symm


lemma compose_inclusion {X Y Z : Scheme} (j : Y ⟶ X) (b : Z ⟶ Y) (r : Z ⟶ X)
    (hr : r = b ≫ j) (H : X.Modules) (P : Z.Modules)
    (f : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj H) ≅ P)
    (η : (Scheme.Modules.pullback r).obj H ≅ P)
    (hf : f.hom = (Scheme.Modules.pullbackComp b j).hom.app H ≫
      (pullbackEqIso hr.symm H).hom ≫ η.hom) :
    composeComparison j b r hr H ((Scheme.Modules.pullback j).obj H) P
      (Iso.refl _) f = η := by
  subst r
  apply Iso.ext
  simp [composeComparison, pullbackEqIso, hf]

lemma compose_normalized {X Y Z : Scheme} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : X.Modules) (N : Y.Modules) (P Q : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (g : (Scheme.Modules.pullback (q ≫ p)).obj M ≅ P) (δ : P ≅ Q)
    (h : (Scheme.Modules.pullback q).map e.hom ≫ f.hom =
      (Scheme.Modules.pullbackComp q p).hom.app M ≫ g.hom) :
    composeComparison p q (q ≫ p) rfl M N Q e (f ≪≫ δ) = g ≪≫ δ := by
  apply Iso.ext
  dsimp only [composeComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [pullbackEqIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rw [← Category.assoc ((Scheme.Modules.pullback q).map e.hom), h]
  simp [Category.assoc]

lemma powerTransport_inclusion {X Y Z : Scheme} (j : Y ⟶ X) (b : Z ⟶ Y)
    (r : Z ⟶ X) (hr : r = b ≫ j) (H : X.Modules) (P : Z.Modules)
    (hH : Scheme.Modules.IsInvertible H)
    (e : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj H) ≅ P)
    (η : (Scheme.Modules.pullback r).obj H ≅ P)
    (he : e.hom = (Scheme.Modules.pullbackComp b j).hom.app H ≫
      (pullbackEqIso hr.symm H).hom ≫ η.hom)
    (n : ℕ) (s : Γ(tensorPower X H n, ⊤)) :
    powerTransport b ((Scheme.Modules.pullback j).obj H) P e n
      (transportSection j (tensorPower X H n)
        (tensorPower Y ((Scheme.Modules.pullback j).obj H) n)
        (ArithmeticThetaPullback.pullback_tensorPower_iso Y X j H n) s) =
      powerTransport r H P η n s := by
  have hline := compose_inclusion j b r hr H P e η he
  have ht := ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorComparison_comp_eq
    j b r hr H ((Scheme.Modules.pullback j).obj H) P hH (Iso.refl _) e n
  rw [hline, tensorComparison_refl _ _ hH] at ht
  unfold powerTransport
  rw [← ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.transportSection_comp_eq
    j b r hr, ← ht]

/-- Pulling the ambient intrinsic tensor to the open base and then to a
classified affine family uses precisely the canonical family comparison. -/
lemma classifier_transport {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : LevelData k L) (F : Family (Base R))
    (σ : Base R ⟶ Base k) (M : FullLevel F L)
    (b : Base R ⟶ OpenBase k L D) (f : F.curve ⟶ D.atlas.descent.family.curve)
    (h : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b f)
    (e : (Scheme.Modules.pullback b).obj (weight D) ≅ Cotangent F)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b f e)
    (n : ℕ) (d : Γ(power D.atlas.descent.family n, ⊤)) :
    letI := AffineConormalHodgeNaturality.differential_isIso F
    powerTransport b (weight D) (hodge (affineFamily F))
      (e ≪≫ asIso (affineDifferential F)) n
      (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L n d) =
    powerTransport (baseMap _ _ (classifierFamilyMap D F σ M b f h).scalar)
      (hodge D.atlas.descent.family) (hodge (affineFamily F))
      (familyIso (classifierFamilyMap D F σ M b f h)) n d := by
  letI := AffineConormalHodgeNaturality.differential_isIso F
  let B := classifierFamilyMap D F σ M b f h
  have hρ : baseMap _ _ B.scalar = b ≫ D.quotient.inclusion := Spec.map_preimage _
  have he' : (e ≪≫ asIso (affineDifferential F)).hom =
      (Scheme.Modules.pullbackComp b D.quotient.inclusion).hom.app
        (hodge D.atlas.descent.family) ≫
      (pullbackEqIso hρ.symm (hodge D.atlas.descent.family)).hom ≫ (familyIso B).hom :=
    classifier_differential D F b f B.scalar hρ B.cartesian B.origin_eq e he
  exact powerTransport_inclusion D.quotient.inclusion b (baseMap _ _ B.scalar) hρ
    (hodge D.atlas.descent.family) (hodge (affineFamily F))
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible D.atlas.descent.family)
    (e ≪≫ asIso (affineDifferential F)) (familyIso B) he' n d


lemma powerTransport_comp {X Y Z : Scheme}
    (p : Y ⟶ X) (q : Z ⟶ Y) (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (n : ℕ) (s : Γ(tensorPower X M n, ⊤)) :
    powerTransport q N P f n (powerTransport p M N e n s) =
      powerTransport (q ≫ p) M P
        (composeComparison p q (q ≫ p) rfl M N P e f) n s := by
  unfold powerTransport
  rw [tensorComparison_comp p q M N P hM e f n, transportSection_comp]

#print axioms classifier_differential
#print axioms classifier_transport
#print axioms family_discriminant_naturality
#print axioms compTest_comparison
end OpenDiscriminantConstantNaturality
open OpenDiscriminantConstantNaturality
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180 ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaSchemeLevelR0204 ArithmeticThetaSchemeHodgeR0205
open ArithmeticThetaLevelConstantsR0234 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182
open ArithmeticThetaTensorPower

/-- The intrinsic discriminant is natural under the actual normalized coefficient comparison. -/
theorem open_discriminant_constant_naturality :
∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (L : ℕ), 3 ≤ L → Even L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l L E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) (d : (ArithmeticThetaOpenHodgeR0180.power D.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤)) (e : (ArithmeticThetaOpenHodgeR0180.power E.atlas.descent.family 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaOpenHodgeR0180.IsD2 D.atlas.descent.family d → ArithmeticThetaOpenHodgeR0180.IsD2 E.atlas.descent.family e → ArithmeticThetaArithmeticSectionsR0236.powerTransport C.openMap (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E) C.hodgeMap 24 (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L 24 d) = ArithmeticThetaBoundaryHodgeR0182.pullToOpen l L 24 e := by
  intro k l _ _ _ _ ι L hL heven D E X Y C d e hd he
  obtain ⟨F, M, g, hg⟩ := SchemeFullLevelUniversal.converse E.atlas
    (OpenBase l L E) (openStructure l L E) (𝟙 _) (Category.id_comp _)
  obtain ⟨a, ha⟩ := C.classifies.2 _ _ F M (𝟙 _) g hg
  obtain ⟨el, hel, _⟩ := classifying_cotangent_hodge l L hL heven
    E.atlas E.two E.cover E.quotient _ _ F M (𝟙 _) g hg
  obtain ⟨ek, hek, _⟩ := classifying_cotangent_hodge k L hL heven
    D.atlas D.two D.cover D.quotient _ _ F M ((𝟙 _) ≫ C.openMap) a ha
  let F' := affineFamily F
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas l E.quotient.quotient.ring
    E.quotient.quotient.smooth F'
  obtain ⟨dF, hdF⟩ := global_discriminant_exists_of_atlas F' A
  let BK := classifierFamilyMap D F (openStructure l L E ≫ constants ι)
    M ((𝟙 _) ≫ C.openMap) a ha
  let BL := classifierFamilyMap E F (openStructure l L E) M (𝟙 _) g hg
  have hK := family_discriminant_naturality BK A d dF hd hdF
  have hE := family_discriminant_naturality BL A e dF he hdF
  letI := AffineConormalHodgeNaturality.differential_isIso F
  let δ := asIso (affineDifferential F)
  let eL : (Scheme.Modules.pullback (𝟙 (OpenBase l L E))).obj (weight E) ≅ hodge F' :=
    el ≪≫ δ
  let eK : (Scheme.Modules.pullback ((𝟙 _) ≫ C.openMap)).obj (weight D) ≅ hodge F' :=
    ek ≪≫ δ
  have hn := C.normalized _ _ F M (𝟙 _) g a hg ha el ek hel hek
  have hcomp : composeComparison C.openMap (𝟙 _) ((𝟙 _) ≫ C.openMap) rfl
      (weight D) (weight E) (hodge F') C.hodgeMap eL = eK :=
    compose_normalized C.openMap (𝟙 _) (weight D) (weight E) (Cotangent F)
      (hodge F') C.hodgeMap el ek δ hn
  have hM : Scheme.Modules.IsInvertible (weight D) :=
    Scheme.Modules.IsInvertible.pullback D.quotient.inclusion
      (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible D.atlas.descent.family)
  apply (transportSection_injective (𝟙 (OpenBase l L E))
    (tensorPower _ (weight E) 24) (power F' 24)
    (tensorComparison (𝟙 _) (weight E) (hodge F') eL 24))
  change powerTransport (𝟙 _) (weight E) (hodge F') eL 24
    (powerTransport C.openMap (weight D) (weight E) C.hodgeMap 24
      (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L 24 d)) =
    powerTransport (𝟙 _) (weight E) (hodge F') eL 24
      (ArithmeticThetaBoundaryHodgeR0182.pullToOpen l L 24 e)
  have htrans := powerTransport_comp C.openMap (𝟙 _) (weight D) (weight E)
    (hodge F') hM C.hodgeMap eL 24
    (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L 24 d)
  rw [hcomp] at htrans
  have htK := classifier_transport D F (openStructure l L E ≫ constants ι)
    M ((𝟙 _) ≫ C.openMap) a ha ek hek 24 d
  have htE := classifier_transport E F (openStructure l L E) M (𝟙 _) g hg el hel 24 e
  exact htrans.trans (htK.trans (hK.trans (hE.symm.trans htE.symm)))

#print axioms open_discriminant_constant_naturality
end ArithmeticThetaArithmeticSectionsR0236
