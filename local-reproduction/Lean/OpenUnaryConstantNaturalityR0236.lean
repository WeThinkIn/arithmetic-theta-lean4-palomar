import ArithmeticSectionsDefinitionsR0236

/-! Geometric comparison lemmas for the normalized open unary section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaArithmeticSectionsR0236.OpenUnaryConstantNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
open ArithmeticThetaOpenHodgeR0180
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180
open ArithmeticThetaOpenHodgeR0180.OpenLevelNormalizedHodgePowerR0180
open ArithmeticThetaOpenHodgeR0180.GlobalLevelCyclicQuotientR0180
open ArithmeticThetaBoundaryHodgeR0182.OpenUnaryDesignatedExpansionR0182

/-- The local normalization formula determines its section without assuming
that the section being compared is a frame. -/
lemma normalized_formula_unique {X : Scheme} (H J : X.Modules)
    (hH : Scheme.Modules.IsInvertible H) (f : H ⟶ J) (e w : ℕ)
    (d : Γ(tensorPower X H 24, ⊤)) (r : Γ(X, ⊤))
    (s t : Γ(tensorPower X J w, ⊤))
    (hs : ∀ (U : X.Opens) (η : Γ(H,U)) (a : Γ(X,U)), IsFrame H U η →
      res (tensorPower X H 24) le_top d = a • tensorPowerSection X H 24 U η →
      res (tensorPower X J w) le_top s =
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
          tensorPowerSection X J w U (f.app U η))
    (ht : ∀ (U : X.Opens) (η : Γ(H,U)) (a : Γ(X,U)), IsFrame H U η →
      res (tensorPower X H 24) le_top d = a • tensorPowerSection X H 24 U η →
      res (tensorPower X J w) le_top t =
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
          tensorPowerSection X J w U (f.app U η)) : s = t := by
  apply sections_eq_local
  intro x _
  obtain ⟨U, η, hx, hη⟩ := local_frames H hH x
  obtain ⟨a, ha⟩ := (InitialHodgeSection.tensor_frame H η hη 24 U le_rfl).2
    (res (tensorPower X H 24) le_top d)
  rw [InitialHodgeSection.res_self] at ha
  exact ⟨U, hx, le_top, (hs U η a hη ha.symm).trans (ht U η a hη ha.symm).symm⟩

/-- The actual image of a point through a morphism over a base map. -/
def baseImage {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {E' : EllipticFamily S}
    {b : Base S ⟶ Base R} (j : E'.curve ⟶ E.curve)
    (hj : j ≫ E.projection = E'.projection ≫ b)
    {T : Scheme} (t : T ⟶ Base S) (x : SchemeHomOver t E'.projection) :
    SchemeHomOver (t ≫ b) E.projection :=
  ⟨x.val ≫ j, by rw [Category.assoc, hj, ← Category.assoc, x.property]⟩

/-- Compatibility with the actual group operation on all test schemes. -/
def IsFamilyHom {R S : Type} [CommRing R] [CommRing S]
    (E : EllipticFamily R) (E' : EllipticFamily S)
    {b : Base S ⟶ Base R} (j : E'.curve ⟶ E.curve)
    (hj : j ≫ E.projection = E'.projection ≫ b) : Prop :=
  ∀ (T : Scheme) (t : T ⟶ Base S) (x y : SchemeHomOver t E'.projection),
    baseImage j hj t (E'.law.mul t x y) =
      E.law.mul (t ≫ b) (baseImage j hj t x) (baseImage j hj t y)

/-- A genuine group comparison preserves all multiplication morphisms. -/
lemma familyHom_nsmul {R S : Type} [CommRing R] [CommRing S]
    (E : EllipticFamily R) (F : EllipticFamily S)
    {b : Base S ⟶ Base R} (j : F.curve ⟶ E.curve)
    (hj : j ≫ E.projection = F.projection ≫ b)
    (hhom : IsFamilyHom E F j hj) (hzero : zero F ≫ j = b ≫ zero E) (n : ℕ) :
    F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n := by
  have hone {T : Scheme} (t : T ⟶ Base S) :
      baseImage j hj t (F.law.one t) = E.law.one (t ≫ b) := by
    apply Subtype.ext
    have hF := congrArg Subtype.val (F.law.one_natural (𝟙 _) t t (Category.comp_id _))
    have hE := congrArg Subtype.val
      (E.law.one_natural (𝟙 _) (t ≫ b) (t ≫ b) (Category.comp_id _))
    change t ≫ zero F = (F.law.one t).val at hF
    change (t ≫ b) ≫ zero E = (E.law.one (t ≫ b)).val at hE
    change (F.law.one t).val ≫ j = _
    rw [← hF, Category.assoc, hzero, ← Category.assoc, hE]
  have hn {T : Scheme} (t : T ⟶ Base S) (x : SchemeHomOver t F.projection) (n : ℕ) :
      baseImage j hj t (F.law.nsmul t n x) =
        E.law.nsmul (t ≫ b) n (baseImage j hj t x) := by
    induction n with
    | zero => exact hone t
    | succ n ih => rw [F.law.nsmul_succ, E.law.nsmul_succ, hhom, ih]
  have hh := congrArg Subtype.val
    (hn F.projection GoodReductionJacobian.RelativeGroupLaw.idPoint n)
  change F.law.schemeNsmul n ≫ j = _ at hh
  rw [← comp_nsmul] at hh
  simpa only [baseImage, GoodReductionJacobian.RelativeGroupLaw.idPoint, Category.id_comp] using hh

lemma pointed_nsmul {R : Type} [CommRing R] {E F : EllipticFamily R}
    (f : Pointed R E F) (hf : IsHom f) (n : ℕ) :
    E.law.schemeNsmul n ≫ f.map = f.map ≫ F.law.schemeNsmul n := by
  letI := E.law.pointGroup E.projection
  letI := F.law.pointGroup E.projection
  have hh := (pointHom E f hf E.projection).map_pow
    GoodReductionJacobian.RelativeGroupLaw.idPoint n
  simp only [← nsmul_pow] at hh
  have hv := congrArg Subtype.val hh
  change E.law.schemeNsmul n ≫ f.map =
    (F.law.nsmul E.projection n (imagePoint f E.projection
      GoodReductionJacobian.RelativeGroupLaw.idPoint)).val at hv
  rw [← comp_nsmul] at hv
  simpa only [imagePoint, GoodReductionJacobian.RelativeGroupLaw.idPoint, Category.id_comp] using hv

/-- Quotient targets compare through the actual Cartesian source comparison.
The proof compares the complete split kernel schemes, so no rational-cusp or
finite-extension hypothesis enters. -/
lemma quotient_cartesian_comparison {R S : Type} [CommRing R] [CommRing S]
    (E : EllipticFamily R) (E' : EllipticFamily S) {m : ℕ}
    (P : Cyclic E m) (P' : Cyclic E' m)
    (Q : Quotient R E m P.point) (Q' : Quotient S E' m P'.point)
    (b : Base S ⟶ Base R) (j : E'.curve ⟶ E.curve)
    (hj : IsPullback j E'.projection E.projection b)
    (hhom : IsFamilyHom E E' j hj.w)
    (hzero : zero E' ≫ j = b ≫ zero E)
    (hmultiple : ∀ i : Fin m, multiple E' P' i ≫ j = b ≫ multiple E P i) :
    ∃ q : Q'.target.curve ⟶ Q.target.curve,
      IsPullback q Q'.target.projection Q.target.projection b ∧
      Q'.arrow.map ≫ q = j ≫ Q.arrow.map ∧
      zero Q'.target ≫ q = b ≫ zero Q.target ∧
      ∀ n, Q'.target.law.schemeNsmul n ≫ q = q ≫ Q.target.law.schemeNsmul n := by
  let F := baseChangeFamily Q.target b
  let a := QuotientComparison.baseChangeArrow E Q.target Q.arrow b E'.projection j hj
  have haover : a ≫ F.projection = E'.projection :=
    QuotientComparison.baseChangeArrow_over E Q.target Q.arrow b E'.projection j hj
  have ha0 : zero E' ≫ a = zero F := by
    apply pullback.hom_ext
    · rw [Category.assoc, QuotientComparison.baseChangeArrow_fst,
        ← Category.assoc, hzero, Category.assoc, Q.arrow.zero_eq]
      exact (baseChange_zero Q.target b).symm
    · rw [Category.assoc, haover]
      exact (E'.law.one (𝟙 _)).property.trans (F.law.one (𝟙 _)).property.symm
  let f : Pointed S E' F := ⟨a, haover, ha0⟩
  letI : IsFinite Q.arrow.map := Q.finite
  letI : Etale Q.arrow.map := Q.etale
  letI : Surjective Q.arrow.map := Q.surjective
  have hgeo := QuotientComparison.baseChangeArrow_geometry E Q.target Q.arrow b
    E'.projection j hj Q.degree
  letI : IsFinite f.map := hgeo.1
  letI : Etale f.map := hgeo.2.1
  letI : Surjective f.map := hgeo.2.2.1
  letI : IsFinite Q'.arrow.map := Q'.finite
  letI : Etale Q'.arrow.map := Q'.etale
  letI : Surjective Q'.arrow.map := Q'.surjective
  have hf : IsHom f := by
    intro T t x y
    apply Subtype.ext
    apply pullback.hom_ext
    · change (E'.law.mul t x y).val ≫ a ≫ pullback.fst Q.target.projection b = _
      rw [QuotientComparison.baseChangeArrow_fst, ← Category.assoc]
      have hm := congrArg Subtype.val (hhom T t x y)
      change (E'.law.mul t x y).val ≫ j = _ at hm
      rw [hm]
      have hq := congrArg Subtype.val (Q.hom T (t ≫ b)
        (baseImage j hj.w t x) (baseImage j hj.w t y))
      change _ ≫ Q.arrow.map = _ at hq
      rw [hq]
      change _ = (F.law.mul t (imagePoint f t x) (imagePoint f t y)).val ≫ _
      rw [show F.law = Q.target.law.baseChange b from rfl,
        GoodReductionJacobian.RelativeGroupLaw.baseChange_mul,
        GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      apply congrArg Subtype.val
      congr 1 <;> apply Subtype.ext <;>
        simp only [imagePoint, baseImage, f, a, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase,
          Category.assoc, QuotientComparison.baseChangeArrow_fst]
    · exact (imagePoint f t (E'.law.mul t x y)).property.trans
        (F.law.mul t (imagePoint f t x) (imagePoint f t y)).property.symm
  have hK := QuotientComparison.quotient_split_baseChange E P Q b E'.projection j hj
    (multiple E' P') (multiple_over E' P') hmultiple
  obtain ⟨e, he, heover, hezero⟩ := QuotientComparison.iso_of_split_kernel
    E' Q'.target F Q'.arrow f Q'.hom hf
    (Sigma.desc (multiple E' P')) (Sigma.desc (fun _ : Fin m => 𝟙 (Base S)))
    (QuotientComparison.quotient_split_cartesian E' P' Q') hK
  have hq : Q'.arrow.map ≫ (e.hom ≫ pullback.fst Q.target.projection b) = j ≫ Q.arrow.map := by
    rw [← Category.assoc, he]
    exact QuotientComparison.baseChangeArrow_fst E Q.target Q.arrow b E'.projection j hj
  refine ⟨e.hom ≫ pullback.fst Q.target.projection b, ?_, hq, ?_, ?_⟩
  · have hi : IsPullback e.hom Q'.target.projection F.projection (𝟙 (Base S)) := by
      apply IsPullback.of_horiz_isIso
      exact ⟨by simpa only [Category.comp_id] using heover⟩
    have hp := hi.paste_horiz (IsPullback.of_hasPullback Q.target.projection b)
    simpa only [Category.id_comp] using hp
  · rw [← Category.assoc, hezero]
    exact baseChange_zero Q.target b
  · intro n
    letI : Epi Q'.arrow.map := Flat.epi_of_flat_of_surjective _
    apply (cancel_epi Q'.arrow.map).mp
    rw [← Category.assoc, ← pointed_nsmul Q'.arrow Q'.hom n,
      Category.assoc, hq, ← Category.assoc, familyHom_nsmul E E' j hj.w hhom hzero n,
      Category.assoc, pointed_nsmul Q.arrow Q.hom n, ← Category.assoc, ← hq,
      Category.assoc]


open ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182

/-- The local tensor formula commutes with restriction after arbitrary pullback. -/
lemma transport_tensor_restrict {X Y : Scheme} (b : X ⟶ Y)
    (H : Y.Modules) (J : X.Modules) (E : (Scheme.Modules.pullback b).obj H ≅ J)
    (n : ℕ) (s : Γ(tensorPower Y H n, ⊤)) (U : Y.Opens) (V : X.Opens)
    (η : Γ(H,U)) (a : Γ(Y,U)) (h : V ≤ b ⁻¹ᵁ U)
    (hs : res (tensorPower Y H n) le_top s = a • tensorPowerSection Y H n U η) :
    res (tensorPower X J n) le_top (powerTransport b H J E n s) =
      b.appLE U V h a • tensorPowerSection X J n V
        (res J h (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) := by
  have hh := transportSection_restrict b (tensorPower Y H n) (tensorPower X J n)
    (tensorComparison b H J E n) s U V h
  rw [hs, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    InitialHodgeSection.res_smul, tensorComparison_section] at hh
  rw [show res (tensorPower X J n) h
      (tensorPowerSection X J n (b ⁻¹ᵁ U) (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) =
      tensorPowerSection X J n V (res J h (E.hom.app _ (Scheme.Modules.pullbackLocalSection b η))) from
    tensorPowerSection_restrict X J n _ _ _ _] at hh
  exact hh

/-- The normalization formula on the actual source and target Hodge lines. -/
def NormalizedFormula {X : Scheme} (H J : X.Modules) (f : H ⟶ J) (e w : ℕ)
    (d : Γ(tensorPower X H 24, ⊤)) (r : Γ(X, ⊤))
    (s : Γ(tensorPower X J w, ⊤)) : Prop :=
  ∀ (U : X.Opens) (η : Γ(H,U)) (a : Γ(X,U)), IsFrame H U η →
    res (tensorPower X H 24) le_top d = a • tensorPowerSection X H 24 U η →
    res (tensorPower X J w) le_top s =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e) •
        tensorPowerSection X J w U (f.app U η)

/-- The entire normalized section is natural once the actual discriminant,
scalar, and differential square are identified. No frame assumption on either
normalized section, nonzero scalar, or finiteness assumption on the map is used. -/
lemma normalized_formula_transport {X Y : Scheme} (b : X ⟶ Y)
    (H J : Y.Modules) (H' J' : X.Modules) (hH : Scheme.Modules.IsInvertible H)
    (EH : (Scheme.Modules.pullback b).obj H ≅ H')
    (EJ : (Scheme.Modules.pullback b).obj J ≅ J')
    (f : H ⟶ J) (f' : H' ⟶ J')
    (hcomm : (Scheme.Modules.pullback b).map f ≫ EJ.hom = EH.hom ≫ f')
    (e w : ℕ) (d : Γ(tensorPower Y H 24, ⊤)) (d' : Γ(tensorPower X H' 24, ⊤))
    (r : Γ(Y, ⊤)) (r' : Γ(X, ⊤))
    (s : Γ(tensorPower Y J w, ⊤)) (s' : Γ(tensorPower X J' w, ⊤))
    (hd : powerTransport b H H' EH 24 d = d')
    (hr : b.appLE ⊤ ⊤ (by simp) r = r')
    (hs : NormalizedFormula H J f e w d r s)
    (hs' : NormalizedFormula H' J' f' e w d' r' s') :
    powerTransport b J J' EJ w s = s' := by
  apply sections_eq_local
  intro x _
  obtain ⟨U, η, hx, hη⟩ := local_frames H hH (b x)
  let V := b ⁻¹ᵁ U
  let η' : Γ(H',V) := EH.hom.app V (Scheme.Modules.pullbackLocalSection b η)
  obtain ⟨a, ha⟩ := (InitialHodgeSection.tensor_frame H η hη 24 U le_rfl).2
    (res (tensorPower Y H 24) le_top d)
  rw [InitialHodgeSection.res_self] at ha
  have ha := ha.symm
  have hη' : IsFrame H' V η' := frame_iso EH _ (pullback_frame b H η hη)
  have hd' : res (tensorPower X H' 24) le_top d' =
      b.appLE U V le_rfl a • tensorPowerSection X H' 24 V η' := by
    rw [← hd]
    simpa only [InitialHodgeSection.res_self] using
      transport_tensor_restrict b H H' EH 24 d U V η a le_rfl ha
  have hmap : EJ.hom.app V (Scheme.Modules.pullbackLocalSection b (f.app U η)) =
      f'.app V η' := by
    have hh := congrArg (fun g => g.app V (Scheme.Modules.pullbackLocalSection b η)) hcomm
    change EJ.hom.app V (((Scheme.Modules.pullback b).map f).app V
      (Scheme.Modules.pullbackLocalSection b η)) = f'.app V η' at hh
    rw [← Scheme.Modules.pullbackLocalSection_app] at hh
    exact hh
  have hcoef : b.appLE U V le_rfl
      (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r' := by
    rw [← hr]
    exact (ConcreteCategory.congr_hom
      (b.map_appLE le_rfl (homOfLE (show U ≤ ⊤ from le_top)).op) r).trans
        (ConcreteCategory.congr_hom
          (b.appLE_map (show (⊤ : X.Opens) ≤ b ⁻¹ᵁ ⊤ by simp)
            (homOfLE (show V ≤ ⊤ from le_top)).op) r).symm
  refine ⟨V, hx, le_top, ?_⟩
  have ht := transport_tensor_restrict b J J' EJ w s U V (f.app U η)
    (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a^e)
    le_rfl (hs U η a hη ha)
  rw [map_mul, map_pow, hcoef, InitialHodgeSection.res_self, hmap] at ht
  exact ht.trans (hs' V η' (b.appLE U V le_rfl a) hη' hd').symm

/-- Coefficient extension preserves the exact inverse-power normalization. -/
lemma normalization_scalar {k l R S : Type} [Field k] [Field l]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra l S]
    (ι : k →+* l) (ρ : R →+* S)
    (hρ : ρ.comp (algebraMap k R) = (algebraMap l S).comp ι)
    (m w : ℕ) (v : R) :
    ρ ((algebraMap k R (m : k)⁻¹)^w * v) =
      (algebraMap l S (m : l)⁻¹)^w * ρ v := by
  rw [map_mul, map_pow]
  have hh := DFunLike.congr_fun hρ ((m : k)⁻¹)
  simpa only [RingHom.comp_apply, map_inv₀, map_natCast] using
    congrArg (fun a : S => a^w * ρ v) hh

open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170

/-- Composition of actual pointed Cartesian tests, with the same scalar map. -/
def composeTest {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    {W : WeierstrassCurve T} {G : Law T W} (C : Test S F T W G) :
    Test R E T W G where
  scalar := C.scalar.comp ρ
  map := C.map ≫ j
  cartesian := by
    have hc := C.cartesian.paste_horiz hj
    have hb : baseMap S T C.scalar ≫ baseMap R S ρ = baseMap R T (C.scalar.comp ρ) := by
      unfold baseMap
      rw [← Spec.map_comp]
      rfl
    rw [hb] at hc
    exact hc
  origin_eq := by
    rw [← Category.assoc, C.origin_eq, Category.assoc, hzero, ← Category.assoc]
    congr 1
    simp only [baseMap, ← Spec.map_comp]
    rfl
  nsmul_eq n := by rw [← Category.assoc, C.nsmul_eq, Category.assoc, hn, Category.assoc]

/-- The intrinsic Kato value predicate is natural through a pointed Cartesian
family comparison and the actual transported point. -/
lemma kato_value_base_change {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    (c : ℕ) (P : Base R ⟶ E.curve) (P' : Base S ⟶ F.curve)
    (hP : P' ≫ j = baseMap R S ρ ≫ P)
    (v : R) (hv : IsKatoValue E c P v) : IsKatoValue F c P' (ρ v) := by
  refine ⟨hv.1.map ρ, ?_⟩
  intro T _ _ _ _ _ W _ _ _ _ _ G hG C p hp hpoint g hg
  apply hv.2 T W G hG (composeTest ρ j hj hzero hn C) p hp
  · change p ≫ (C.map ≫ j) = baseMap R T (C.scalar.comp ρ) ≫ P
    rw [← Category.assoc, hpoint, Category.assoc, hP, ← Category.assoc]
    congr 1
    simp only [baseMap, ← Spec.map_comp]
    rfl
  · exact hg

/-- Intrinsic Kato values are unique on an actual Weierstrass atlas.
No torsion or nonvanishing assumption is needed in addition to the value predicate. -/
lemma kato_value_unique_of_atlas {S : Type} [CommRing S]
    (E : EllipticFamily S) (A : Atlas S E) (c : ℕ) (hc : 1 < c)
    (hc6 : Nat.Coprime c 6) (P : Base S ⟶ E.curve)
    (hP : P ≫ E.projection = 𝟙 _) (v w : S)
    (hv : IsKatoValue E c P v) (hw : IsKatoValue E c P w) : v = w := by
  have he (i : Fin A.count) :
      (A.chart i).comparison.scalar v = (A.chart i).comparison.scalar w := by
    let C := A.chart i
    have hgeom := relative_curve_geometry C.ring C.equation
    letI := hgeom.1
    letI := hgeom.2.1
    letI := hgeom.2.2.2.1
    letI := hgeom.2.2.2.2.1
    obtain ⟨g, hg⟩ := GlobalFamilyDiscriminantR0180.normalized_exists
      C.ring C.equation C.law C.originLaw c hc hc6
    let p := GlobalFamilyTorsionValueR0180.testPoint C.comparison P hP
    have hp := GlobalFamilyTorsionValueR0180.testPoint_over C.comparison P hP
    have hpmap := GlobalFamilyTorsionValueR0180.testPoint_map C.comparison P hP
    exact TorsionUnitValue.hasValue_unique C.ring C.equation p g
      (hv.2 C.ring C.equation C.law C.originLaw C.comparison p hp hpmap g hg)
      (hw.2 C.ring C.equation C.law C.originLaw C.comparison p hp hpmap g hg)
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  change scalar S v = scalar S w
  let f (i : Fin A.count) := baseMap S (A.chart i).ring (A.chart i).comparison.scalar
  letI (i : Fin A.count) : IsOpenImmersion (f i) := (A.chart i).openImmersion
  let U (i : Fin A.count) : (Base S).Opens := f i ''ᵁ ⊤
  apply TopCat.Sheaf.eq_of_locally_eq' (Base S).sheaf U ⊤ (fun _ => homOfLE le_top)
    (fun x _ => by
      obtain ⟨i, y, hy⟩ := A.covers x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, trivial, hy⟩)
  intro i
  apply (f i |>.appIso ⊤).commRingCatIsoToRingEquiv.injective
  change (f i |>.appIso ⊤).hom
      ((Base S).presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (scalar S v)) =
    (f i |>.appIso ⊤).hom
      ((Base S).presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (scalar S w))
  rw [GlobalFamilyTorsionValueR0180.image_restrict (f i),
    GlobalFamilyTorsionValueR0180.image_restrict (f i),
    GlobalFamilyTorsionValueR0180.scalar_natural (A.chart i).comparison.scalar v,
    GlobalFamilyTorsionValueR0180.scalar_natural (A.chart i).comparison.scalar w, he i]

/-- The canonical differential comparison for the specified family map. -/
def familyComparison {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E) :
    (Scheme.Modules.pullback (baseMap R S ρ)).obj (hodge E) ≅ hodge F := by
  letI : Algebra R S := ρ.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso E.projection F.projection j hj (zero E) (zero F) hzero

lemma family_power_local {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (n : ℕ) (U : E.curve.Opens) (a : Γ(E.curve,U)) (V : (Base S).Opens)
    (h₁ : V ≤ baseMap R S ρ ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ zero F ⁻¹ᵁ (j ⁻¹ᵁ U)) :
    res (power F n) h₁
      ((tensorComparison (baseMap R S ρ) (hodge E) (hodge F)
        (familyComparison ρ j hj hzero) n).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) (familyLocalPower E n U a))) =
      res (power F n) h₂ (familyLocalPower F n (j ⁻¹ᵁ U) (j.app U a)) := by
  letI : Algebra R S := ρ.toAlgebra
  letI := E.smooth
  unfold familyLocalPower
  rw [tensorComparison_section]
  change (tensorPower (Base S) (hodge F) n).presheaf.map (homOfLE h₁).op
    (tensorPowerSection _ _ n _ _) =
      (tensorPower (Base S) (hodge F) n).presheaf.map (homOfLE h₂).op
        (tensorPowerSection _ _ n _ _)
  rw [tensorPowerSection_restrict, tensorPowerSection_restrict]
  exact congrArg (tensorPowerSection (Base S) (hodge F) n V)
    (pointedDifferentialIso_D E.projection F.projection j hj (zero E) (zero F) hzero U a V h₁ h₂)


#print axioms normalized_formula_unique

/-- Local section formulas determine composition for arbitrary modules and pointed
schemes. Keeping this argument abstract prevents concrete model reduction from
entering the restriction and pullback calculation. -/
lemma comparison_comp_local {B₀ B₁ B₂ X₀ X₁ X₂ : Scheme}
    (z₀ : B₀ ⟶ X₀) (z₁ : B₁ ⟶ X₁) (z₂ : B₂ ⟶ X₂)
    (p : B₁ ⟶ B₀) (q : B₂ ⟶ B₁) (r : B₂ ⟶ B₀) (hr : r = q ≫ p)
    (j : X₁ ⟶ X₀) (k : X₂ ⟶ X₁) (h : X₂ ⟶ X₀) (hm : k ≫ j = h)
    (hp : z₁ ≫ j = p ≫ z₀) (hh : z₂ ≫ h = r ≫ z₀)
    (M : B₀.Modules) (N : B₁.Modules) (P : B₂.Modules)
    (dM : ∀ U : X₀.Opens, Γ(X₀,U) → Γ(M,z₀ ⁻¹ᵁ U))
    (dN : ∀ U : X₁.Opens, Γ(X₁,U) → Γ(N,z₁ ⁻¹ᵁ U))
    (dP : ∀ U : X₂.Opens, Γ(X₂,U) → Γ(P,z₂ ⁻¹ᵁ U))
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P)
    (g : (Scheme.Modules.pullback r).obj M ≅ P)
    (he : ∀ U a V (h₁ : V ≤ p ⁻¹ᵁ (z₀ ⁻¹ᵁ U))
        (h₂ : V ≤ z₁ ⁻¹ᵁ (j ⁻¹ᵁ U)),
      res N h₁ (e.hom.app _ (Scheme.Modules.pullbackLocalSection p (dM U a))) =
        res N h₂ (dN _ (j.app U a)))
    (hf : ∀ U a V (h₁ : V ≤ q ⁻¹ᵁ (z₁ ⁻¹ᵁ U))
        (h₂ : V ≤ z₂ ⁻¹ᵁ (k ⁻¹ᵁ U)),
      res P h₁ (f.hom.app _ (Scheme.Modules.pullbackLocalSection q (dN U a))) =
        res P h₂ (dP _ (k.app U a)))
    (hg : ∀ U a V (h₁ : V ≤ r ⁻¹ᵁ (z₀ ⁻¹ᵁ U))
        (h₂ : V ≤ z₂ ⁻¹ᵁ (h ⁻¹ᵁ U)),
      res P h₁ (g.hom.app _ (Scheme.Modules.pullbackLocalSection r (dM U a))) =
        res P h₂ (dP _ (h.app U a)))
    (U : X₀.Opens) (a : Γ(X₀,U)) :
    g.hom.app _ (Scheme.Modules.pullbackLocalSection r (dM U a)) =
      (composeComparison p q r hr M N P e f).hom.app _
        (Scheme.Modules.pullbackLocalSection r (dM U a)) := by
  subst h
  let V := r ⁻¹ᵁ (z₀ ⁻¹ᵁ U)
  have hV : V ≤ q ⁻¹ᵁ (p ⁻¹ᵁ (z₀ ⁻¹ᵁ U)) := by
    intro y hy
    change (q ≫ p) y ∈ z₀ ⁻¹ᵁ U
    rw [← hr]
    exact hy
  have hN : p ⁻¹ᵁ (z₀ ⁻¹ᵁ U) ≤ z₁ ⁻¹ᵁ (j ⁻¹ᵁ U) := by
    intro y hy
    change (z₁ ≫ j) y ∈ U
    rw [hp]
    exact hy
  have hP : V ≤ z₂ ⁻¹ᵁ (k ⁻¹ᵁ (j ⁻¹ᵁ U)) := by
    intro y hy
    change (z₂ ≫ (k ≫ j)) y ∈ U
    rw [hh]
    exact hy
  have hleft := hg U a V le_rfl hP
  have hcomp := composeComparison_section p q r hr M N P e f
    (z₀ ⁻¹ᵁ U) (dM U a) V le_rfl hV
  have hinner := he U a (p ⁻¹ᵁ (z₀ ⁻¹ᵁ U)) le_rfl hN
  rw [res_refl] at hinner
  rw [hinner, ← InitialSectionNaturality.pullback_res, ← hom_res,
    InitialHodgeSection.res_res] at hcomp
  rw [hf (j ⁻¹ᵁ U) (j.app U a) V (fun y hy => hN (hV hy)) hP] at hcomp
  have hv := ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality.section_comp
    z₂ P dP k j U a V hP hP
  rw [← hv] at hcomp
  simpa only [res_refl] using hleft.trans hcomp.symm

/-- Local frames upgrade the abstract composition formula to equality of the
specified pullback isomorphisms. -/
lemma comparison_eq_of_local {B X Y : Scheme} (z : B ⟶ X) (r : Y ⟶ B)
    (M : B.Modules) (P : Y.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(M,z ⁻¹ᵁ U))
    (hframes : ∀ x : B, ∃ (U : X.Opens) (a : Γ(X,U)),
      z x ∈ U ∧ IsFrame M (z ⁻¹ᵁ U) (d U a))
    (e f : (Scheme.Modules.pullback r).obj M ≅ P)
    (he : ∀ U a, e.hom.app _ (Scheme.Modules.pullbackLocalSection r (d U a)) =
      f.hom.app _ (Scheme.Modules.pullbackLocalSection r (d U a))) : e = f := by
  apply Iso.ext
  apply hom_ext_frames
  intro x
  obtain ⟨U, a, hx, ha⟩ := hframes (r x)
  exact ⟨r ⁻¹ᵁ (z ⁻¹ᵁ U), Scheme.Modules.pullbackLocalSection r (d U a),
    hx, pullback_frame r M (d U a) ha, he U a⟩

#print axioms comparison_comp_local
#print axioms comparison_eq_of_local

set_option maxHeartbeats 200000 in
lemma family_power_frames {R : Type} [CommRing R] (E : EllipticFamily R)
    (n : ℕ) (x : Base R) : ∃ (U : E.curve.Opens) (a : Γ(E.curve,U)),
      zero E x ∈ U ∧ IsFrame (power E n) (zero E ⁻¹ᵁ U) (familyLocalPower E n U a) := by
  letI := E.smooth
  obtain ⟨U, a, hx, hf⟩ := exists_exact_differential_frame E.projection (zero E x)
  refine ⟨U, a, hx, ?_⟩
  apply tensorPower_frame
  exact pullback_frame (zero E) E.projection.kaehler _ hf

#print axioms family_power_frames

/-- Actual local differential along the specified family identity. -/
def familyLocalDifferential {R : Type} [CommRing R] (E : EllipticFamily R)
    (U : E.curve.Opens) (a : Γ(E.curve,U)) : Γ(hodge E, zero E ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection (zero E)
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD E.projection U a)

lemma family_differential_frames {R : Type} [CommRing R] (E : EllipticFamily R)
    (x : Base R) : ∃ (U : E.curve.Opens) (a : Γ(E.curve,U)),
      zero E x ∈ U ∧ IsFrame (hodge E) (zero E ⁻¹ᵁ U) (familyLocalDifferential E U a) := by
  letI := E.smooth
  obtain ⟨U, a, hx, hf⟩ := exists_exact_differential_frame E.projection (zero E x)
  exact ⟨U, a, hx, pullback_frame (zero E) E.projection.kaehler _ hf⟩

lemma family_differential_local {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (U : E.curve.Opens) (a : Γ(E.curve,U)) (V : (Base S).Opens)
    (h₁ : V ≤ baseMap R S ρ ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ zero F ⁻¹ᵁ (j ⁻¹ᵁ U)) :
    res (hodge F) h₁ ((familyComparison ρ j hj hzero).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) (familyLocalDifferential E U a))) =
      res (hodge F) h₂ (familyLocalDifferential F (j ⁻¹ᵁ U) (j.app U a)) := by
  letI : Algebra R S := ρ.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso_D E.projection F.projection j hj (zero E) (zero F) hzero U a V h₁ h₂

lemma test_differential_local {R T : Type} [CommRing R] [CommRing T]
    {E : EllipticFamily R} {W : WeierstrassCurve T} {G : Law T W}
    (C : Test R E T W G)
    (U : E.curve.Opens) (a : Γ(E.curve,U)) (V : (Base T).Opens)
    (h₁ : V ≤ baseMap R T C.scalar ⁻¹ᵁ (zero E ⁻¹ᵁ U))
    (h₂ : V ≤ origin T W ⁻¹ᵁ (C.map ⁻¹ᵁ U)) :
    res (Hodge T W) h₁ ((comparison C).hom.app _
      (Scheme.Modules.pullbackLocalSection (baseMap R T C.scalar) (familyLocalDifferential E U a))) =
      res (Hodge T W) h₂ (localDifferential T W (C.map ⁻¹ᵁ U) (C.map.app U a)) := by
  letI : Algebra R T := C.scalar.toAlgebra
  letI := E.smooth
  exact pointedDifferentialIso_D E.projection (structureMap T W) C.map C.cartesian
    (zero E) (origin T W) C.origin_eq U a V h₁ h₂

/-- Proof-free statement preflight for the precise weight-one composition. -/
def FamilyComparisonStatement {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    {W : WeierstrassCurve T} {G : Law T W}
    (C : Test S F T W G) (D : Test R E T W G)
    (_hmap : C.map ≫ j = D.map)
    (hbase : baseMap R T D.scalar = baseMap S T C.scalar ≫ baseMap R S ρ) : Prop :=
    comparison D = composeComparison (baseMap R S ρ) (baseMap S T C.scalar)
      (baseMap R T D.scalar) hbase (hodge E) (hodge F) (Hodge T W)
      (familyComparison ρ j hj hzero) (comparison C)

#print axioms family_differential_frames
#print axioms family_differential_local
#print axioms test_differential_local
#print axioms FamilyComparisonStatement

/-- Local differentials with the scheme and its pointed section kept as parameters. -/
def pointedLocalDifferential {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Base R) (z : Base R ⟶ X) (U : X.Opens) (a : Γ(X,U)) :
    Γ((Scheme.Modules.pullback z).obj f.kaehler, z ⁻¹ᵁ U) :=
  Scheme.Modules.pullbackLocalSection z
    (ArithmeticThetaCompactifiedDifferentialR0145.relativeD f U a)

lemma pointed_differential_frames {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Base R) [SmoothOfRelativeDimension 1 f] (z : Base R ⟶ X)
    (x : Base R) : ∃ (U : X.Opens) (a : Γ(X,U)), z x ∈ U ∧
      IsFrame ((Scheme.Modules.pullback z).obj f.kaehler) (z ⁻¹ᵁ U)
        (pointedLocalDifferential f z U a) := by
  obtain ⟨U, a, hx, hf⟩ := exists_exact_differential_frame f (z x)
  exact ⟨U, a, hx, pullback_frame z f.kaehler _ hf⟩

/-- Typed canonical comparison retaining the exact scalar, curve and point maps. -/
def canonicalComparison {R S : Type} [CommRing R] [CommRing S]
    (ρ : R →+* S) {X Y : Scheme} (f : X ⟶ Base R) (g : Y ⟶ Base S)
    [SmoothOfRelativeDimension 1 f] (j : Y ⟶ X)
    (hj : IsPullback j g f (baseMap R S ρ))
    (x : Base R ⟶ X) (y : Base S ⟶ Y) (hz : y ≫ j = baseMap R S ρ ≫ x) :
    (Scheme.Modules.pullback (baseMap R S ρ)).obj ((Scheme.Modules.pullback x).obj f.kaehler) ≅
      (Scheme.Modules.pullback y).obj g.kaehler := by
  letI : Algebra R S := ρ.toAlgebra
  exact pointedDifferentialIso f g j hj x y hz

lemma canonicalComparison_local {R S : Type} [CommRing R] [CommRing S]
    (ρ : R →+* S) {X Y : Scheme} (f : X ⟶ Base R) (g : Y ⟶ Base S)
    [SmoothOfRelativeDimension 1 f] (j : Y ⟶ X)
    (hj : IsPullback j g f (baseMap R S ρ))
    (x : Base R ⟶ X) (y : Base S ⟶ Y) (hz : y ≫ j = baseMap R S ρ ≫ x)
    (U : X.Opens) (a : Γ(X,U)) (V : (Base S).Opens)
    (h₁ : V ≤ baseMap R S ρ ⁻¹ᵁ (x ⁻¹ᵁ U)) (h₂ : V ≤ y ⁻¹ᵁ (j ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback y).obj g.kaehler) h₁
      ((canonicalComparison ρ f g j hj x y hz).hom.app _
        (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) (pointedLocalDifferential f x U a))) =
      res ((Scheme.Modules.pullback y).obj g.kaehler) h₂
        (pointedLocalDifferential g y (j ⁻¹ᵁ U) (j.app U a)) := by
  letI : Algebra R S := ρ.toAlgebra
  exact pointedDifferentialIso_D f g j hj x y hz U a V h₁ h₂

/-- Canonical pointed differentials compose before choosing a curve presentation. -/
lemma canonicalComparison_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (ρ : R →+* S) (σ : S →+* T) (τ : R →+* T)
    {X Y Z : Scheme} (f : X ⟶ Base R) (g : Y ⟶ Base S) (h : Z ⟶ Base T)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (j : Y ⟶ X) (k : Z ⟶ Y) (v : Z ⟶ X)
    (hj : IsPullback j g f (baseMap R S ρ))
    (hk : IsPullback k h g (baseMap S T σ))
    (hv : IsPullback v h f (baseMap R T τ))
    (x : Base R ⟶ X) (y : Base S ⟶ Y) (z : Base T ⟶ Z)
    (hzj : y ≫ j = baseMap R S ρ ≫ x)
    (hzk : z ≫ k = baseMap S T σ ≫ y)
    (hzv : z ≫ v = baseMap R T τ ≫ x)
    (hm : k ≫ j = v) (hb : baseMap R T τ = baseMap S T σ ≫ baseMap R S ρ) :
    canonicalComparison τ f h v hv x z hzv =
      composeComparison (baseMap R S ρ) (baseMap S T σ) (baseMap R T τ) hb
        ((Scheme.Modules.pullback x).obj f.kaehler)
        ((Scheme.Modules.pullback y).obj g.kaehler)
        ((Scheme.Modules.pullback z).obj h.kaehler)
        (canonicalComparison ρ f g j hj x y hzj) (canonicalComparison σ g h k hk y z hzk) := by
  apply comparison_eq_of_local x (baseMap R T τ)
    ((Scheme.Modules.pullback x).obj f.kaehler) ((Scheme.Modules.pullback z).obj h.kaehler)
    (pointedLocalDifferential f x) (pointed_differential_frames f x)
  exact comparison_comp_local x y z (baseMap R S ρ) (baseMap S T σ)
    (baseMap R T τ) hb j k v hm hzj hzv
    ((Scheme.Modules.pullback x).obj f.kaehler)
    ((Scheme.Modules.pullback y).obj g.kaehler)
    ((Scheme.Modules.pullback z).obj h.kaehler)
    (pointedLocalDifferential f x) (pointedLocalDifferential g y) (pointedLocalDifferential h z)
    (canonicalComparison ρ f g j hj x y hzj) (canonicalComparison σ g h k hk y z hzk)
    (canonicalComparison τ f h v hv x z hzv)
    (canonicalComparison_local ρ f g j hj x y hzj)
    (canonicalComparison_local σ g h k hk y z hzk)
    (canonicalComparison_local τ f h v hv x z hzv)

#print axioms canonicalComparison_comp

set_option maxHeartbeats 200000 in
lemma family_differential_composition {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    {W : WeierstrassCurve T} {G : Law T W}
    (C : Test S F T W G) (D : Test R E T W G)
    (hmap : C.map ≫ j = D.map)
    (hbase : baseMap R T D.scalar = baseMap S T C.scalar ≫ baseMap R S ρ) : FamilyComparisonStatement ρ j hj hzero C D hmap hbase := by
  letI := E.smooth
  letI := F.smooth
  exact canonicalComparison_comp ρ C.scalar D.scalar E.projection F.projection
    (structureMap T W) j C.map D.map hj C.cartesian D.cartesian
    (zero E) (zero F) (origin T W) hzero C.origin_eq D.origin_eq hmap hbase

#print axioms family_differential_composition

lemma family_power_composition {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    {W : WeierstrassCurve T} {G : Law T W}
    (C : Test S F T W G) (D : Test R E T W G)
    (hmap : C.map ≫ j = D.map)
    (hbase : baseMap R T D.scalar = baseMap S T C.scalar ≫ baseMap R S ρ)
    (n : ℕ) :
    powerComparison D n =
      composeComparison (baseMap R S ρ) (baseMap S T C.scalar)
        (baseMap R T D.scalar) hbase (power E n) (power F n) (HodgePower T W n)
        (tensorComparison (baseMap R S ρ) (hodge E) (hodge F) (familyComparison ρ j hj hzero) n)
        (powerComparison C n) := by
  have hc := family_differential_composition ρ j hj hzero C D hmap hbase
  change comparison D = _ at hc
  unfold powerComparison
  rw [hc]
  exact ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorComparison_comp_eq
    (baseMap R S ρ) (baseMap S T C.scalar) (baseMap R T D.scalar) hbase
    (hodge E) (hodge F) (Hodge T W)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible E)
    (familyComparison ρ j hj hzero) (comparison C) n

#print axioms family_power_composition

lemma family_power_test {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    {W : WeierstrassCurve T} {G : Law T W} (C : Test S F T W G)
    (n : ℕ) (d : Γ(power E n, ⊤)) :
    pullSection C n (powerTransport (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hzero) n d) =
      pullSection (composeTest ρ j hj hzero hn C) n d := by
  have hbase : baseMap R T (C.scalar.comp ρ) = baseMap S T C.scalar ≫ baseMap R S ρ := by
    unfold baseMap
    rw [← Spec.map_comp]
    rfl
  have he : powerComparison (composeTest ρ j hj hzero hn C) n =
      composeComparison (baseMap R S ρ) (baseMap S T C.scalar)
        (baseMap R T (C.scalar.comp ρ)) hbase (power E n) (power F n) (HodgePower T W n)
        (tensorComparison (baseMap R S ρ) (hodge E) (hodge F)
          (familyComparison ρ j hj hzero) n) (powerComparison C n) :=
    family_power_composition ρ j hj hzero C (composeTest ρ j hj hzero hn C) rfl hbase n
  change transportSection (baseMap S T C.scalar) (power F n) (HodgePower T W n)
      (powerComparison C n)
      (transportSection (baseMap R S ρ) (power E n) (power F n)
        (tensorComparison (baseMap R S ρ) (hodge E) (hodge F)
          (familyComparison ρ j hj hzero) n) d) =
    transportSection (baseMap R T (C.scalar.comp ρ)) (power E n) (HodgePower T W n)
      (powerComparison (composeTest ρ j hj hzero hn C) n) d
  rw [he]
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.transportSection_comp_eq
    (baseMap R S ρ) (baseMap S T C.scalar) (baseMap R T (C.scalar.comp ρ)) hbase
    (power E n) (power F n) (HodgePower T W n)
    (tensorComparison (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hzero) n) (powerComparison C n) d).symm


#print axioms family_power_test

/-- Intrinsic D2 commutes with actual pointed Cartesian coefficient change. -/
lemma discriminant_base_change {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    (d : Γ(power E 24, ⊤)) (hd : IsD2 E d) :
    IsD2 F (powerTransport (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hzero) 24 d) := by
  constructor
  · exact frame_restrict _ (by simp) _
      (frame_iso (tensorComparison (baseMap R S ρ) (hodge E) (hodge F)
        (familyComparison ρ j hj hzero) 24) _ (pullback_frame _ _ d hd.1))
  · intro T _ _ _ _ _ W _ _ _ _ _ G hG C g hg
    rw [family_power_test ρ j hj hzero hn C]
    exact hd.2 T W G hG (composeTest ρ j hj hzero hn C) g hg

#print axioms discriminant_base_change

open ArithmeticThetaRelativeIsogenyHodgeR0172.PointedHodgeFunctoriality

lemma pointed_section_map_congr {X Y B : Scheme} (z : B ⟶ X) (P : B.Modules)
    (d : ∀ U : X.Opens, Γ(X,U) → Γ(P,z ⁻¹ᵁ U))
    (f g : X ⟶ Y) (he : f = g) (U : Y.Opens) (a : Γ(Y,U)) (V : B.Opens)
    (hf : V ≤ z ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : V ≤ z ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    res P hf (d _ (f.app U a)) = res P hg (d _ (g.app U a)) := by
  subst g
  rfl

lemma pointMap_local {R : Type} [CommRing R] {X Y : Scheme}
    (f : X ⟶ Base R) (g : Y ⟶ Base R) (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (p : Base R ⟶ X) (q : Base R ⟶ Y) (hpq : p ≫ φ = q)
    (U : Y.Opens) (a : Γ(Y,U)) (V : (Base R).Opens)
    (h₁ : V ≤ q ⁻¹ᵁ U) (h₂ : V ≤ p ⁻¹ᵁ (φ ⁻¹ᵁ U)) :
    res ((Scheme.Modules.pullback p).obj f.kaehler) h₁
      ((PeriodDifferential.pointMap f g φ hφ p q hpq).app _ (pointedLocalDifferential g q U a)) =
    res ((Scheme.Modules.pullback p).obj f.kaehler) h₂
      (pointedLocalDifferential f p (φ ⁻¹ᵁ U) (φ.app U a)) := by
  exact pointed_D g f φ (by simpa using hφ) q p hpq.symm U a V h₁ h₂

/-- The full differential square over arbitrary rings, checked on local frames.
The source and target schemes and all four geometric maps remain parameters. -/
lemma canonicalComparison_square {R S : Type} [CommRing R] [CommRing S]
    (ρ : R →+* S) {X Y X' Y' : Scheme}
    (f : X ⟶ Base R) (g : Y ⟶ Base R) (f' : X' ⟶ Base S) (g' : Y' ⟶ Base S)
    [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 g]
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : IsPullback a f' f (baseMap R S ρ))
    (hb : IsPullback b g' g (baseMap R S ρ))
    (p : Base R ⟶ X) (q : Base R ⟶ Y) (p' : Base S ⟶ X') (q' : Base S ⟶ Y')
    (hpa : p' ≫ a = baseMap R S ρ ≫ p) (hqb : q' ≫ b = baseMap R S ρ ≫ q)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (hpq : p ≫ φ = q)
    (ψ : X' ⟶ Y') (hψ : ψ ≫ g' = f') (hpq' : p' ≫ ψ = q')
    (hsq : a ≫ φ = ψ ≫ b) :
    (Scheme.Modules.pullback (baseMap R S ρ)).map (PeriodDifferential.pointMap f g φ hφ p q hpq) ≫
        (canonicalComparison ρ f f' a ha p p' hpa).hom =
      (canonicalComparison ρ g g' b hb q q' hqb).hom ≫
        PeriodDifferential.pointMap f' g' ψ hψ p' q' hpq' := by
  apply hom_ext_frames
  intro x
  obtain ⟨U, t, hx, ht⟩ := pointed_differential_frames g q (baseMap R S ρ x)
  let V := baseMap R S ρ ⁻¹ᵁ (q ⁻¹ᵁ U)
  have hpre : q ⁻¹ᵁ U ≤ p ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    intro y hy
    change (p ≫ φ) y ∈ U
    rw [hpq]
    exact hy
  have hA : V ≤ baseMap R S ρ ⁻¹ᵁ (p ⁻¹ᵁ (φ ⁻¹ᵁ U)) := fun y hy => hpre hy
  have hB : V ≤ q' ⁻¹ᵁ (b ⁻¹ᵁ U) := by
    intro y hy
    change (q' ≫ b) y ∈ U
    rw [hqb]
    exact hy
  have hL : V ≤ p' ⁻¹ᵁ (a ⁻¹ᵁ (φ ⁻¹ᵁ U)) := by
    intro y hy
    change ((p' ≫ a) ≫ φ) y ∈ U
    rw [hpa, Category.assoc, hpq]
    exact hy
  have hR : V ≤ p' ⁻¹ᵁ (ψ ⁻¹ᵁ (b ⁻¹ᵁ U)) := by
    intro y hy
    change (p' ≫ ψ) y ∈ b ⁻¹ᵁ U
    rw [hpq']
    exact hB hy
  refine ⟨V, Scheme.Modules.pullbackLocalSection (baseMap R S ρ)
    (pointedLocalDifferential g q U t), hx,
    pullback_frame (baseMap R S ρ) _ _ ht, ?_⟩
  change (canonicalComparison ρ f f' a ha p p' hpa).hom.app V
      (((Scheme.Modules.pullback (baseMap R S ρ)).map
        (PeriodDifferential.pointMap f g φ hφ p q hpq)).app V
        (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) (pointedLocalDifferential g q U t))) =
    (PeriodDifferential.pointMap f' g' ψ hψ p' q' hpq').app V
      ((canonicalComparison ρ g g' b hb q q' hqb).hom.app V
        (Scheme.Modules.pullbackLocalSection (baseMap R S ρ) (pointedLocalDifferential g q U t)))
  rw [← Scheme.Modules.pullbackLocalSection_app]
  have hd := pointMap_local f g φ hφ p q hpq U t (q ⁻¹ᵁ U) le_rfl hpre
  rw [res_refl] at hd
  rw [hd, ← InitialSectionNaturality.pullback_res, ← hom_res]
  rw [canonicalComparison_local ρ f f' a ha p p' hpa (φ ⁻¹ᵁ U) (φ.app U t) V hA hL]
  have hr := canonicalComparison_local ρ g g' b hb q q' hqb U t V le_rfl hB
  rw [res_refl] at hr
  rw [hr, ← hom_res, pointMap_local f' g' ψ hψ p' q' hpq' (b ⁻¹ᵁ U) (b.app U t) V hB hR]
  exact (section_comp p' ((Scheme.Modules.pullback p').obj f'.kaehler)
    (pointedLocalDifferential f' p') a φ U t V hL hL).symm.trans
      ((pointed_section_map_congr p' ((Scheme.Modules.pullback p').obj f'.kaehler)
        (pointedLocalDifferential f' p') (a ≫ φ) (ψ ≫ b) hsq U t V hL hR).trans
          (section_comp p' ((Scheme.Modules.pullback p').obj f'.kaehler)
            (pointedLocalDifferential f' p') ψ b U t V hR hR))

#print axioms canonicalComparison_square

/-- The actual family Hodge maps commute with the two Cartesian comparisons.
No field or connectedness hypothesis is imposed on either coefficient ring. -/
lemma family_hodge_square {R S : Type} [CommRing R] [CommRing S]
    {E F : EllipticFamily R} {E' F' : EllipticFamily S}
    (ρ : R →+* S) (j : E'.curve ⟶ E.curve) (q : F'.curve ⟶ F.curve)
    (hj : IsPullback j E'.projection E.projection (baseMap R S ρ))
    (hq : IsPullback q F'.projection F.projection (baseMap R S ρ))
    (hzj : zero E' ≫ j = baseMap R S ρ ≫ zero E)
    (hzq : zero F' ≫ q = baseMap R S ρ ≫ zero F)
    (φ : Pointed R E F) (ψ : Pointed S E' F')
    (hsq : j ≫ φ.map = ψ.map ≫ q) :
    (Scheme.Modules.pullback (baseMap R S ρ)).map (familyHodgeMap φ) ≫
        (familyComparison ρ j hj hzj).hom =
      (familyComparison ρ q hq hzq).hom ≫ familyHodgeMap ψ := by
  letI := E.smooth
  letI := F.smooth
  exact canonicalComparison_square ρ E.projection F.projection E'.projection F'.projection
    j q hj hq (zero E) (zero F) (zero E') (zero F') hzj hzq
    φ.map φ.over_eq φ.zero_eq ψ.map ψ.over_eq ψ.zero_eq hsq

/-- The two actual intrinsic discriminants agree through the specified map,
with uniqueness detected on a genuine atlas of the target family. -/
lemma discriminant_transport_eq {R S : Type} [CommRing R] [CommRing S]
    {E : EllipticFamily R} {F : EllipticFamily S}
    (ρ : R →+* S) (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hn : ∀ n, F.law.schemeNsmul n ≫ j = j ≫ E.law.schemeNsmul n)
    (A : Atlas S F) (d : Γ(power E 24, ⊤)) (d' : Γ(power F 24, ⊤))
    (hd : IsD2 E d) (hd' : IsD2 F d') :
    powerTransport (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hzero) 24 d = d' :=
  isD2_unique_of_atlas F A _ d' (discriminant_base_change ρ j hj hzero hn d hd) hd'

#print axioms family_hodge_square
#print axioms discriminant_transport_eq

/-- The affine version of the same scheme family, with its exact group law. -/
abbrev ellipticFamily {R : Type} [CommRing R]
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R)) : EllipticFamily R where
  curve := F.curve
  projection := F.p
  law :=
    { mul := F.law.mul, one := F.law.one, inv := F.law.inv
      mul_assoc := F.law.mul_assoc, one_mul := F.law.one_mul
      mul_one := F.law.mul_one, inv_mul_cancel := F.law.inv_mul_cancel
      mul_natural := F.law.mul_natural }
  commutative := F.law.mul_comm
  proper := F.proper
  smooth := F.dimension
  connected := F.connected

lemma multiple_ellipticFamily {R : Type} [CommRing R]
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    {T : Scheme} (t : T ⟶ Base R) (n : ℕ) (x : SchemeHomOver t F.p) :
    ArithmeticThetaSchemeLevelR0204.multiple F t n x = (ellipticFamily F).law.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F.law.mul t (ArithmeticThetaSchemeLevelR0204.multiple F t n x) x =
      F.law.mul t ((ellipticFamily F).law.nsmul t n x) x
    rw [ih]

/-- The same ordered full marking in the affine-family interface. -/
def familyLevel {R : Type} [CommRing R]
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R)) {L : ℕ}
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L) : FamilyLevel R (ellipticFamily F) L where
  x := M.x
  y := M.y
  killed_x := by
    exact (comp_nsmul (ellipticFamily F) (𝟙 _) M.x L).trans
      (congrArg Subtype.val ((multiple_ellipticFamily F (𝟙 _) L M.x).symm.trans M.killed_x))
  killed_y := by
    exact (comp_nsmul (ellipticFamily F) (𝟙 _) M.y L).trans
      (congrArg Subtype.val ((multiple_ellipticFamily F (𝟙 _) L M.y).symm.trans M.killed_y))
  avoids := by
    intro i j hij
    simpa only [multiple_ellipticFamily F, ArithmeticThetaLocalWeierstrassR0203.Family.zero] using M.avoids i j hij

/-- A classifier preserves the actual affine family group law. -/
lemma classifier_familyHom {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L)
    (σ : Base R ⟶ Base k)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (f : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b f) :
    IsFamilyHom D.atlas.descent.family (ellipticFamily F) f hc.2.1.w := by
  intro T t x y
  apply Subtype.ext
  exact (hc.2.2.2.2.2 T t x y (baseImage f hc.2.1.w t x)
    (baseImage f hc.2.1.w t y) rfl rfl).symm

/-- Both coefficient models classify one and the same fully marked source on
    the target open base, retaining their actual family maps. -/
lemma common_classifiers {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]
    {L : ℕ} (ι : k →+* l)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L)
    (f : ArithmeticThetaLevelCompactificationR0179.OpenBase l L E ⟶
      ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (hf : ArithmeticThetaLevelConstantsR0234.RespectsClassifiers ι D E f) :
    ∃ (F : ArithmeticThetaLocalWeierstrassR0203.Family
        (ArithmeticThetaLevelCompactificationR0179.OpenBase l L E))
      (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L)
      (g : F.curve ⟶ E.atlas.descent.family.curve)
      (a : F.curve ⟶ D.atlas.descent.family.curve),
      ArithmeticThetaLevelConstantsR0234.Classifies E
        (ArithmeticThetaLevelCompactificationR0179.openStructure l L E) F M (𝟙 _) g ∧
      ArithmeticThetaLevelConstantsR0234.Classifies D
        (ArithmeticThetaLevelCompactificationR0179.openStructure l L E ≫
          ArithmeticThetaLevelConstantsR0234.constants ι) F M ((𝟙 _) ≫ f) a := by
  obtain ⟨F, M, g, hg⟩ := ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.converse
    E.atlas (B := E.two) (C := E.cover) (Q := E.quotient)
    (ArithmeticThetaLevelCompactificationR0179.OpenBase l L E)
    (ArithmeticThetaLevelCompactificationR0179.openStructure l L E) (𝟙 _) (Category.id_comp _)
  obtain ⟨a, ha⟩ := hf.2 _ (ArithmeticThetaLevelCompactificationR0179.openStructure l L E)
    F M (𝟙 _) g hg
  exact ⟨F, M, g, a, hg, ha⟩

/-- Both ordered-coordinate combinations transport through the actual classifier. -/
lemma classifier_coordinates {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L) (σ : Base R ⟶ Base k)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (f : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b f) (u v : ℕ) :
    ((ellipticFamily F).law.mul (𝟙 _)
      ((ellipticFamily F).law.nsmul (𝟙 _) u M.x)
      ((ellipticFamily F).law.nsmul (𝟙 _) v M.y)).val ≫ f =
    (b ≫ D.quotient.inclusion) ≫ (D.atlas.descent.family.law.mul (𝟙 _)
      (D.atlas.descent.family.law.nsmul (𝟙 _) u D.atlas.marking.x)
      (D.atlas.descent.family.law.nsmul (𝟙 _) v D.atlas.marking.y)).val := by
  let U := ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily L D.atlas
  have hx := ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp U F
    (b ≫ D.quotient.inclusion) f hc.2.2.1 hc.2.2.2.2.2
    M.x D.atlas.marking.x hc.2.2.2.1 u
  have hy := ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp U F
    (b ≫ D.quotient.inclusion) f hc.2.2.1 hc.2.2.2.2.2
    M.y D.atlas.marking.y hc.2.2.2.2.1 v
  have h := ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.mul_comp U F
    (b ≫ D.quotient.inclusion) f hc.2.2.2.2.2 _ _ _ _ hx hy
  dsimp only [U] at h
  simp only [ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.multiple_eq,
    multiple_ellipticFamily F] at h
  exact h

lemma classifier_multiple_x {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L) (σ : Base R ⟶ Base k)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (f : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b f) (n : ℕ) :
    ((ellipticFamily F).law.nsmul (𝟙 _) n M.x).val ≫ f =
      (b ≫ D.quotient.inclusion) ≫
        (D.atlas.descent.family.law.nsmul (𝟙 _) n D.atlas.marking.x).val := by
  have h := ArithmeticThetaSchemeLevelR0204.CartesianFullMarking.multiple_comp
    (ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier.universalFamily L D.atlas) F
    (b ≫ D.quotient.inclusion) f hc.2.2.1 hc.2.2.2.2.2
    M.x D.atlas.marking.x hc.2.2.2.1 n
  simp only [ArithmeticThetaSchemeLevelR0204.SchemeFullLevelUniversal.multiple_eq,
    multiple_ellipticFamily F] at h
  exact h

#print axioms classifier_coordinates
#print axioms classifier_multiple_x

abbrev familyKernel {R : Type} [CommRing R] (E : EllipticFamily R) {L : ℕ}
    (M : FamilyLevel R E L) (m : ℕ) : Base R ⟶ E.curve :=
  (E.law.nsmul (𝟙 _) (L/m) M.x).val

abbrev familyLift {R : Type} [CommRing R] (E : EllipticFamily R) {L : ℕ}
    (M : FamilyLevel R E L) (m N a b : ℕ) : Base R ⟶ E.curve :=
  (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*N)*b) M.x)
    (E.law.nsmul (𝟙 _) (L/N*a) M.y)).val

/-- The actual unary construction on a specified fully marked affine family.
Every predicate concerns the constructed quotient, point, scalar and Hodge line. -/
structure FamilyPower (k : Type) [Field k] {R : Type} [CommRing R] [Algebra k R]
    (E : EllipticFamily R) {L : ℕ} (M : FamilyLevel R E L) (m N : ℕ) (a b : Fin N) where
  quotient : Quotient R E m (familyKernel E M m)
  discriminant : Γ(power quotient.target 24, ⊤)
  intrinsic : IsD2 quotient.target discriminant
  value : R
  value_spec : IsKatoValue quotient.target (1+12*N)
    (familyLift E M m N a.val b.val ≫ quotient.arrow.map) value
  section_ : Γ(power E (ArithmeticThetaCompactUnaryR0183.weight N), ⊤)
  normalized : NormalizedFormula (hodge quotient.target) (hodge E) (familyHodgeMap quotient.arrow)
    (ArithmeticThetaCompactUnaryR0183.dExponent N) (ArithmeticThetaCompactUnaryR0183.weight N)
    discriminant
    (scalar R ((algebraMap k R (m : k)⁻¹)^(ArithmeticThetaCompactUnaryR0183.weight N) * value)) section_

/-- The given OpenPower is retained verbatim in the general affine interface. -/
def ofOpenPower (k : Type) [Field k] [CharZero k] (m N : ℕ)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N))
    (a b : Fin N) (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) :
    FamilyPower k D.atlas.descent.family D.atlas.marking m N a b where
  quotient := A.quotient
  discriminant := A.discriminant
  intrinsic := A.intrinsic
  value := A.value
  value_spec := A.value_spec
  section_ := A.section_
  normalized := A.normalized

/-- Construction on the common smooth affine base, with the literal scalar
normalization and actual full ordered torsion point. -/
lemma family_power_exists (k : Type) [Field k] [CharZero k]
    (R : Type) [CommRing R] [Algebra k R]
    (hR : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k R))))
    (E : EllipticFamily R) {L : ℕ} (M : FamilyLevel R E L) (hL : 0 < L)
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (heven : Even N) (hmNL : m*N ∣ L)
    (a b : Fin N) (hab : a.val ≠ 0 ∨ b.val ≠ 0) :
    Nonempty (FamilyPower k E M m N a b) := by
  obtain ⟨A⟩ := elliptic_family_weierstrass_atlas k R hR E
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m N) hmNL
  obtain ⟨P, hP⟩ := cyclic_of_level E hL M m hm hmL
  have hQ : Nonempty (Quotient R E m (familyKernel E M m)) := by
    simpa only [hP] using quotient_nonempty E A hm P
  obtain ⟨Q⟩ := hQ
  obtain ⟨d, hd, _⟩ := global_family_discriminant k R hR Q.target
  have hl := level_lift_conditions E hL M m N hm hN hmNL a b hab
  have hp : familyLift E M m N a.val b.val ≫ E.projection = 𝟙 _ :=
    (E.law.mul (𝟙 _) (E.law.nsmul (𝟙 _) (L/(m*N)*b.val) M.x)
      (E.law.nsmul (𝟙 _) (L/N*a.val) M.y)).property
  have hpoint := quotient_lift E hm P (familyKernel E M m) hP Q N
    (familyLift E M m N a.val b.val) hp
    (by simpa only [hP, familyKernel, familyLift] using hl.1)
    (by simpa only [hP, familyKernel, familyLift] using hl.2)
  have hc : 1 < 1+12*N := by omega
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    simpa [← Nat.mul_assoc] using
      (Nat.coprime_add_mul_left_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  have hcN : Nat.Coprime (1+12*N) N :=
    (Nat.coprime_add_mul_right_left 1 N 12).mpr (Nat.coprime_one_left N)
  obtain ⟨v, hv, _⟩ := global_family_torsion_value k R hR Q.target (1+12*N) N
    hc hc6 hN hcN (familyLift E M m N a.val b.val ≫ Q.arrow.map)
    (by rw [Category.assoc, Q.arrow.over_eq]; exact hp) hpoint.1 hpoint.2
  letI := Q.etale
  letI : IsIso (familyHodgeMap Q.arrow) := family_hodge_isIso Q.arrow
  let w := ArithmeticThetaCompactUnaryR0183.weight N
  let r := scalar R ((algebraMap k R (m : k)⁻¹)^w * v)
  have hmu : IsUnit (algebraMap k R (m : k)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))).map _
  have hr : IsUnit r := ((hmu.pow w).mul hv.1).map
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨s, hs, _⟩ := normalized_section (hodge Q.target) (hodge E)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible Q.target) (familyHodgeMap Q.arrow)
    (ArithmeticThetaCompactUnaryR0183.dExponent N) w (exponents N heven).2 d hd.1 r hr
  exact ⟨⟨Q, d, hd, v, hv, s, hs.2⟩⟩

#print axioms ofOpenPower
#print axioms family_power_exists

/-- Naturality of the actual unary construction under a pointed Cartesian
family map preserving the specified cyclic generator and lifted point. -/
lemma family_power_naturality {k l R S : Type} [Field k] [Field l]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra l S]
    (ι : k →+* l) (ρ : R →+* S)
    (hρ : ρ.comp (algebraMap k R) = (algebraMap l S).comp ι)
    (E : EllipticFamily R) (F : EllipticFamily S) {L : ℕ}
    (M : FamilyLevel R E L) (M' : FamilyLevel S F L)
    (hL : 0 < L) (m N : ℕ) (hm : 0 < m) (hmL : m ∣ L) (hN : 0 < N)
    (a b : Fin N) (A : FamilyPower k E M m N a b) (B : FamilyPower l F M' m N a b)
    (j : F.curve ⟶ E.curve)
    (hj : IsPullback j F.projection E.projection (baseMap R S ρ))
    (hhom : IsFamilyHom E F j hj.w)
    (hzero : zero F ≫ j = baseMap R S ρ ≫ zero E)
    (hkernel : familyKernel F M' m ≫ j = baseMap R S ρ ≫ familyKernel E M m)
    (hlift : familyLift F M' m N a.val b.val ≫ j =
      baseMap R S ρ ≫ familyLift E M m N a.val b.val)
    (atlas : Atlas S B.quotient.target) :
    powerTransport (baseMap R S ρ) (hodge E) (hodge F)
      (familyComparison ρ j hj hzero) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ =
      B.section_ := by
  obtain ⟨⟨p, hp, hpk, hpd⟩, he⟩ := cyclic_of_level E hL M m hm hmL
  change p = familyKernel E M m at he
  subst p
  let P : Cyclic E m := ⟨familyKernel E M m, hp, hpk, hpd⟩
  obtain ⟨⟨p', hp', hpk', hpd'⟩, he'⟩ := cyclic_of_level F hL M' m hm hmL
  change p' = familyKernel F M' m at he'
  subst p'
  let P' : Cyclic F m := ⟨familyKernel F M' m, hp', hpk', hpd'⟩
  have hmultiple (i : Fin m) : multiple F P' i ≫ j = baseMap R S ρ ≫ multiple E P i := by
    change (familyKernel F M' m ≫ F.law.schemeNsmul i.val) ≫ j =
      baseMap R S ρ ≫ (familyKernel E M m ≫ E.law.schemeNsmul i.val)
    rw [Category.assoc, familyHom_nsmul E F j hj.w hhom hzero i.val,
      ← Category.assoc, hkernel, Category.assoc]
  obtain ⟨q, hq, harrow, hzq, hnq⟩ := quotient_cartesian_comparison E F P P'
    A.quotient B.quotient (baseMap R S ρ) j hj hhom hzero hmultiple
  have hpoint : (familyLift F M' m N a.val b.val ≫ B.quotient.arrow.map) ≫ q =
      baseMap R S ρ ≫ (familyLift E M m N a.val b.val ≫ A.quotient.arrow.map) := by
    rw [Category.assoc, harrow, ← Category.assoc, hlift, Category.assoc]
  have hpOver : (familyLift F M' m N a.val b.val ≫ B.quotient.arrow.map) ≫
      B.quotient.target.projection = 𝟙 _ := by
    rw [Category.assoc, B.quotient.arrow.over_eq]
    exact (F.law.mul (𝟙 _) (F.law.nsmul (𝟙 _) (L/(m*N)*b.val) M'.x)
      (F.law.nsmul (𝟙 _) (L/N*a.val) M'.y)).property
  have hc : 1 < 1+12*N := by omega
  have hc6 : Nat.Coprime (1+12*N) 6 := by
    simpa [← Nat.mul_assoc] using
      (Nat.coprime_add_mul_left_left 1 6 (2*N)).mpr (Nat.coprime_one_left 6)
  have hvalue : ρ A.value = B.value :=
    kato_value_unique_of_atlas B.quotient.target atlas (1+12*N) hc hc6
      (familyLift F M' m N a.val b.val ≫ B.quotient.arrow.map) hpOver (ρ A.value) B.value
      (kato_value_base_change ρ q hq hzq hnq (1+12*N)
        (familyLift E M m N a.val b.val ≫ A.quotient.arrow.map)
        (familyLift F M' m N a.val b.val ≫ B.quotient.arrow.map)
        hpoint A.value A.value_spec) B.value_spec
  have hd := discriminant_transport_eq ρ q hq hzq hnq atlas A.discriminant B.discriminant
    A.intrinsic B.intrinsic
  have hr : (baseMap R S ρ).appLE ⊤ ⊤ (by simp)
      (scalar R ((algebraMap k R (m : k)⁻¹)^(ArithmeticThetaCompactUnaryR0183.weight N) * A.value)) =
    scalar S ((algebraMap l S (m : l)⁻¹)^(ArithmeticThetaCompactUnaryR0183.weight N) * B.value) := by
    change (baseMap R S ρ).appTop
      (scalar R ((algebraMap k R (m : k)⁻¹)^(ArithmeticThetaCompactUnaryR0183.weight N) * A.value)) = _
    rw [GlobalFamilyTorsionValueR0180.scalar_natural,
      normalization_scalar ι ρ hρ, hvalue]
  exact normalized_formula_transport (baseMap R S ρ)
    (hodge A.quotient.target) (hodge E) (hodge B.quotient.target) (hodge F)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible A.quotient.target)
    (familyComparison ρ q hq hzq) (familyComparison ρ j hj hzero)
    (familyHodgeMap A.quotient.arrow) (familyHodgeMap B.quotient.arrow)
    (family_hodge_square ρ j q hj hq hzero hzq A.quotient.arrow B.quotient.arrow harrow.symm)
    (ArithmeticThetaCompactUnaryR0183.dExponent N) (ArithmeticThetaCompactUnaryR0183.weight N)
    A.discriminant B.discriminant _ _ A.section_ B.section_ hd hr A.normalized B.normalized

#print axioms family_power_naturality

open ArithmeticThetaSchemeHodgeR0205

/-- The canonical affine differential comparison with an explicitly equal
presentation of its actual base map. -/
def affineHodgeOver {R S : Type} [CommRing R] [CommRing S]
    (E : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base S))
    (ρ : R →+* S) (r : Base S ⟶ Base R) (hr : r = baseMap R S ρ)
    (j : F.curve ⟶ E.curve) (hc : IsPullback j F.p E.p r)
    (hz : F.zero ≫ j = r ≫ E.zero) :
    (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback E.zero).obj E.p.kaehler) ≅
      (Scheme.Modules.pullback F.zero).obj F.p.kaehler :=
  pullbackEqIso hr _ ≪≫ affineHodgeComparison E F ρ j
    (by change IsPullback j F.p E.p (baseMap R S ρ); rw [← hr]; exact hc)
    (by change F.zero ≫ j = baseMap R S ρ ≫ E.zero; rw [← hr]; exact hz)

lemma affine_conormal_over {R S : Type} [CommRing R] [CommRing S]
    (E : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base S))
    (ρ : R →+* S) (r : Base S ⟶ Base R) (hr : r = baseMap R S ρ)
    (j : F.curve ⟶ E.curve) (hc : IsPullback j F.p E.p r)
    (hz : F.zero ≫ j = r ≫ E.zero)
    (i : (Scheme.Modules.pullback j).obj E.zero.ker.module ≅ F.zero.ker.module)
    (hi : IdealCompatible E F j i) :
    (Scheme.Modules.pullback r).map (affineDifferential E) ≫
        (affineHodgeOver E F ρ r hr j hc hz).hom =
      (cotangentComparison E F r j hz i).hom ≫ affineDifferential F := by
  subst r
  simpa [affineHodgeOver, pullbackEqIso, baseMap] using
    (affine_conormal_hodge_naturality R S E F ρ j hc hz).2.2 i hi

/-- Cancellation of an invertible conormal normalization through the standard
pullback associator, with all modules kept independent. -/
lemma normalized_hodge_square {X Y Z : Scheme} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M N : X.Modules) (K H : Z.Modules) (d : M ⟶ N) [IsIso d]
    (e : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj N) ⟶ K)
    (c : (Scheme.Modules.pullback (q ≫ p)).obj M ⟶ K) (t : K ⟶ H)
    (f : (Scheme.Modules.pullback (q ≫ p)).obj N ⟶ H)
    (he : (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback p).map d) ≫ e =
      ((Scheme.Modules.pullbackComp q p).app M).hom ≫ c)
    (hn : (Scheme.Modules.pullback (q ≫ p)).map d ≫ f = c ≫ t) :
    e ≫ t = ((Scheme.Modules.pullbackComp q p).app N).hom ≫ f := by
  apply (cancel_epi ((Scheme.Modules.pullback q).map ((Scheme.Modules.pullback p).map d))).mp
  rw [← Category.assoc, he, Category.assoc, ← hn, ← Category.assoc]
  exact congrArg (fun v => v ≫ f) (((Scheme.Modules.pullbackComp q p).hom.naturality d).symm)

/-- The normalized classifier's cotangent map gives precisely the canonical
whole Hodge comparison, with no scalar ambiguity. -/
lemma classifier_differential_hom {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L) (σ : Base R ⟶ Base k)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (j : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b j)
    (ρ : D.atlas.quotient.ring →+* R)
    (hρ : baseMap D.atlas.quotient.ring R ρ = b ≫ D.quotient.inclusion)
    (e : (Scheme.Modules.pullback b).obj (ArithmeticThetaLevelConstantsR0234.weight D) ≅ Cotangent F)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b j e) :
    e.hom ≫ affineDifferential F =
      ((Scheme.Modules.pullbackComp b D.quotient.inclusion).app (hodge D.atlas.descent.family)).hom ≫
        (affineHodgeOver (universalFamily k L D.atlas) F ρ (b ≫ D.quotient.inclusion)
          hρ.symm j hc.2.1 hc.2.2.1).hom := by
  obtain ⟨hz, i, hi, hn⟩ := he
  let U := universalFamily k L D.atlas
  have hnatur := affine_conormal_over U F ρ (b ≫ D.quotient.inclusion) hρ.symm
    j hc.2.1 hz i hi
  letI : IsIso (affineDifferential U) := AffineConormalHodgeNaturality.differential_isIso U
  exact normalized_hodge_square D.quotient.inclusion b
    (Cotangent U) (hodge D.atlas.descent.family) (Cotangent F) (hodge (ellipticFamily F))
    (affineDifferential U) e.hom (cotangentComparison U F (b ≫ D.quotient.inclusion) j hz i).hom
    (affineDifferential F) (affineHodgeOver U F ρ (b ≫ D.quotient.inclusion) hρ.symm j hc.2.1 hz).hom
    hn hnatur

lemma composeComparison_of_normalization {X Y Z : Scheme}
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) (hr : r = q ≫ p)
    (M : X.Modules) (P : Z.Modules)
    (e : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M) ≅ P)
    (f : (Scheme.Modules.pullback r).obj M ≅ P)
    (he : e.hom = ((Scheme.Modules.pullbackComp q p).app M).hom ≫
      (pullbackEqIso hr.symm M).hom ≫ f.hom) :
    composeComparison p q r hr M ((Scheme.Modules.pullback p).obj M) P (Iso.refl _) e = f := by
  subst r
  apply Iso.ext
  simp [composeComparison, pullbackEqIso, he, Category.assoc]

/-- Classifier compatibility gives the scalar square for the specific map of
atlas rings, including an arbitrary coefficient-field embedding. -/
lemma classifier_scalar_eq {k l R : Type} [Field k] [CharZero k] [Field l] [CommRing R]
    [Algebra l R] {L : ℕ} (ι : k →+* l)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (j : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D
      (Spec.map (CommRingCat.ofHom (algebraMap l R)) ≫ ArithmeticThetaLevelConstantsR0234.constants ι)
      F M b j)
    (ρ : D.atlas.quotient.ring →+* R)
    (hρ : baseMap D.atlas.quotient.ring R ρ = b ≫ D.quotient.inclusion) :
    ρ.comp (algebraMap k D.atlas.quotient.ring) = (algebraMap l R).comp ι := by
  change (CommRingCat.ofHom (ρ.comp (algebraMap k D.atlas.quotient.ring))).hom =
    (CommRingCat.ofHom ((algebraMap l R).comp ι)).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  simp only [CommRingCat.ofHom_comp, Spec.map_comp]
  change baseMap D.atlas.quotient.ring R ρ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k D.atlas.quotient.ring)) = _
  rw [hρ, Category.assoc, D.quotient.over_eq]
  exact hc.1

/-- The classifier identification followed by the actual conormal derivative. -/
def classifierLine {R : Type} [CommRing R] {X : Scheme}
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    {b : Base R ⟶ X} {M : X.Modules}
    (e : (Scheme.Modules.pullback b).obj M ≅ Cotangent F) :
    (Scheme.Modules.pullback b).obj M ≅ hodge (ellipticFamily F) := by
  letI : IsIso (affineDifferential F) := AffineConormalHodgeNaturality.differential_isIso F
  exact e ≪≫ asIso (affineDifferential F)

lemma classifier_total_comparison {k R : Type} [Field k] [CharZero k] [CommRing R]
    {L : ℕ} (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L)
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F L) (σ : Base R ⟶ Base k)
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D)
    (j : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D σ F M b j)
    (ρ : D.atlas.quotient.ring →+* R)
    (hρ : baseMap D.atlas.quotient.ring R ρ = b ≫ D.quotient.inclusion)
    (hj : IsPullback j F.p D.atlas.descent.family.projection (baseMap _ _ ρ))
    (hz : F.zero ≫ j = baseMap _ _ ρ ≫ zero D.atlas.descent.family)
    (e : (Scheme.Modules.pullback b).obj (ArithmeticThetaLevelConstantsR0234.weight D) ≅ Cotangent F)
    (he : ClassifierHodge k L D.atlas D.two D.cover D.quotient F b j e) :
    composeComparison D.quotient.inclusion b (baseMap _ _ ρ) hρ
      (hodge D.atlas.descent.family) (ArithmeticThetaLevelConstantsR0234.weight D)
      (hodge (ellipticFamily F)) (Iso.refl _) (classifierLine F e) =
      familyComparison ρ j hj hz := by
  apply composeComparison_of_normalization
  have hh := classifier_differential_hom D F M σ b j hc ρ hρ e he
  change e.hom ≫ affineDifferential F = _
  change e.hom ≫ affineDifferential F =
    ((Scheme.Modules.pullbackComp b D.quotient.inclusion).app (hodge D.atlas.descent.family)).hom ≫
      ((pullbackEqIso hρ.symm (hodge D.atlas.descent.family)) ≪≫
        familyComparison (E := D.atlas.descent.family) (F := ellipticFamily F) ρ j hj hz).hom at hh
  exact hh

lemma powerTransport_comp {X Y Z : Scheme} (p : Y ⟶ X) (q : Z ⟶ Y)
    (r : Z ⟶ X) (hr : r = q ≫ p) (M : X.Modules) (N : Y.Modules) (P : Z.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ P) (n : ℕ)
    (s : Γ(tensorPower X M n, ⊤)) :
    powerTransport r M P (composeComparison p q r hr M N P e f) n s =
      powerTransport q N P f n (powerTransport p M N e n s) := by
  unfold powerTransport
  rw [ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.tensorComparison_comp_eq
    p q r hr M N P hM,
    ArithmeticThetaBoundaryHodgeR0182.CompactDiscriminantSectionR0182.transportSection_comp_eq]

lemma pullToOpen_transport (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (n : ℕ)
    (s : Γ(power D.atlas.descent.family n, ⊤)) :
    ArithmeticThetaBoundaryHodgeR0182.pullToOpen k L n s =
      powerTransport D.quotient.inclusion (hodge D.atlas.descent.family)
        (ArithmeticThetaLevelConstantsR0234.weight D) (Iso.refl _) n s := by
  unfold powerTransport
  have ht := ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.tensorComparison_refl
    D.quotient.inclusion (hodge D.atlas.descent.family)
    (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible D.atlas.descent.family) n
  exact congrArg (fun e =>
    ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection
      D.quotient.inclusion _ _ e s) ht.symm

/-- Each classified open construction agrees with the actual common-family
construction through its normalized Hodge identification. -/
lemma classified_power_transport {k l R : Type} [Field k] [CharZero k]
    [Field l] [CharZero l] [CommRing R] [Algebra l R]
    (ι : k →+* l) (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hL : 0 < ArithmeticThetaCompactUnaryR0183.level N)
    (hmL : m ∣ ArithmeticThetaCompactUnaryR0183.level N)
    (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N))
    (F : ArithmeticThetaLocalWeierstrassR0203.Family (Base R))
    (M : ArithmeticThetaSchemeLevelR0204.FullLevel F (ArithmeticThetaCompactUnaryR0183.level N))
    (b : Base R ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k (ArithmeticThetaCompactUnaryR0183.level N) D)
    (j : F.curve ⟶ D.atlas.descent.family.curve)
    (hc : ArithmeticThetaLevelConstantsR0234.Classifies D
      (Spec.map (CommRingCat.ofHom (algebraMap l R)) ≫ ArithmeticThetaLevelConstantsR0234.constants ι)
      F M b j)
    (e : (Scheme.Modules.pullback b).obj (ArithmeticThetaLevelConstantsR0234.weight D) ≅ Cotangent F)
    (he : ClassifierHodge k (ArithmeticThetaCompactUnaryR0183.level N)
      D.atlas D.two D.cover D.quotient F b j e)
    (a c : Fin N) (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a c)
    (B : FamilyPower l (ellipticFamily F) (familyLevel F M) m N a c)
    (atlas : Atlas R B.quotient.target) :
    powerTransport b (ArithmeticThetaLevelConstantsR0234.weight D) (hodge (ellipticFamily F))
      (classifierLine F e) (ArithmeticThetaCompactUnaryR0183.weight N)
      (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N)
        (ArithmeticThetaCompactUnaryR0183.weight N) A.section_) = B.section_ := by
  let ρ : D.atlas.quotient.ring →+* R := (Spec.preimage (b ≫ D.quotient.inclusion)).hom
  have hρ : baseMap _ _ ρ = b ≫ D.quotient.inclusion := Spec.map_preimage _
  have hj : IsPullback j F.p D.atlas.descent.family.projection (baseMap _ _ ρ) := by
    rw [hρ]; exact hc.2.1
  have hz : F.zero ≫ j = baseMap _ _ ρ ≫ zero D.atlas.descent.family := by
    rw [hρ]; exact hc.2.2.1
  have hh : IsFamilyHom D.atlas.descent.family (ellipticFamily F) j hj.w := by
    simpa only [hρ] using classifier_familyHom D F M _ b j hc
  have hk : familyKernel (ellipticFamily F) (familyLevel F M) m ≫ j =
      baseMap _ _ ρ ≫ familyKernel D.atlas.descent.family D.atlas.marking m := by
    rw [hρ]; exact classifier_multiple_x D F M _ b j hc _
  have hl : familyLift (ellipticFamily F) (familyLevel F M) m N a.val c.val ≫ j =
      baseMap _ _ ρ ≫ familyLift D.atlas.descent.family D.atlas.marking m N a.val c.val := by
    rw [hρ]; exact classifier_coordinates D F M _ b j hc _ _
  have hn := family_power_naturality ι ρ (classifier_scalar_eq ι D F M b j hc ρ hρ)
    D.atlas.descent.family (ellipticFamily F) D.atlas.marking (familyLevel F M)
    hL m N hm hmL hN a c (ofOpenPower k m N D a c A) B j hj hh hz hk hl atlas
  rw [pullToOpen_transport,
    ← powerTransport_comp D.quotient.inclusion b (baseMap _ _ ρ) hρ _ _ _
      (EllipticFamilyWeierstrassAtlasR0180.hodge_invertible D.atlas.descent.family),
    classifier_total_comparison D F M _ b j hc ρ hρ hj hz e he]
  exact hn

/-- A normalized comparison remains normalized after a fixed actual
invertible derivative; this calculation uses independent module parameters. -/
lemma composeComparison_postcompose {X Y Z : Scheme} (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : X.Modules) (N : Y.Modules) (K P : Z.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (f : (Scheme.Modules.pullback q).obj N ≅ K)
    (g : (Scheme.Modules.pullback (q ≫ p)).obj M ≅ K)
    (d : K ≅ P)
    (he : (Scheme.Modules.pullback q).map e.hom ≫ f.hom =
      ((Scheme.Modules.pullbackComp q p).app M).hom ≫ g.hom) :
    composeComparison p q (q ≫ p) rfl M N P e (f ≪≫ d) = g ≪≫ d := by
  apply Iso.ext
  simp only [composeComparison, pullbackEqIso, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc ((Scheme.Modules.pullback q).map e.hom), he]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Naturality of the normalized unary power through the specified coefficient
comparison, proved on one actual common fully marked family. -/
theorem _root_.ArithmeticThetaArithmeticSectionsR0236.open_unary_constant_naturality :
    ∀ (k l : Type) [Field k] [CharZero k] [Field l] [CharZero l] (ι : k →+* l) (m N : ℕ), 0 < m → Even m → 0 < N → Even N → m ∣ N → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (Y : ArithmeticThetaLevelCompactificationR0179.Compactification l (ArithmeticThetaCompactUnaryR0183.level N) E) (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k (ArithmeticThetaCompactUnaryR0183.level N) ι D E X Y) (a b : Fin N), (a.val ≠ 0 ∨ b.val ≠ 0) → ∀ (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (A' : ArithmeticThetaCompactUnaryR0183.OpenPower l m N E a b), ArithmeticThetaArithmeticSectionsR0236.powerTransport C.openMap (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E) C.hodgeMap (ArithmeticThetaCompactUnaryR0183.weight N) (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_) = ArithmeticThetaBoundaryHodgeR0182.pullToOpen l (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A'.section_ := by
  intro k l _ _ _ _ ι m N hm hmeven hN hNeven hmN D E X Y C a b hab A A'
  have hL : 3 ≤ ArithmeticThetaCompactUnaryR0183.level N := by
    have := Nat.one_le_pow 2 N hN
    dsimp [ArithmeticThetaCompactUnaryR0183.level]
    omega
  have hLeven : Even (ArithmeticThetaCompactUnaryR0183.level N) :=
    ⟨12*N^2, by dsimp [ArithmeticThetaCompactUnaryR0183.level]; omega⟩
  have hmNL : m*N ∣ ArithmeticThetaCompactUnaryR0183.level N :=
    (period_parameters m N hm hN hmN).2.2.2
  have hmL : m ∣ ArithmeticThetaCompactUnaryR0183.level N :=
    dvd_trans (dvd_mul_right m N) hmNL
  obtain ⟨F, M, g, j, hg, hj⟩ := common_classifiers ι D E C.openMap C.classifies
  let R := E.quotient.quotient.ring
  obtain ⟨B⟩ := family_power_exists l R E.quotient.quotient.smooth
    (ellipticFamily F) (familyLevel F M) (by omega) m N hm hN hNeven hmNL a b hab
  obtain ⟨atlas⟩ := elliptic_family_weierstrass_atlas l R E.quotient.quotient.smooth B.quotient.target
  obtain ⟨el, hel, _⟩ := classifying_cotangent_hodge l _ hL hLeven
    E.atlas E.two E.cover E.quotient _
    (ArithmeticThetaLevelCompactificationR0179.openStructure l _ E) F M (𝟙 _) g hg
  obtain ⟨ek, hek, _⟩ := classifying_cotangent_hodge k _ hL hLeven
    D.atlas D.two D.cover D.quotient _
    (ArithmeticThetaLevelCompactificationR0179.openStructure l _ E ≫
      ArithmeticThetaLevelConstantsR0234.constants ι) F M ((𝟙 _) ≫ C.openMap) j hj
  have hk := classified_power_transport ι m N hm hN (by omega) hmL
    D F M ((𝟙 _) ≫ C.openMap) j hj ek hek a b A B atlas
  have hid : ArithmeticThetaLevelConstantsR0234.constants (RingHom.id l) = 𝟙 (Base l) := by
    change Spec.map (𝟙 (CommRingCat.of l)) = _
    exact Spec.map_id _
  have hg' : ArithmeticThetaLevelConstantsR0234.Classifies E
      (Spec.map (CommRingCat.ofHom (algebraMap l R)) ≫
        ArithmeticThetaLevelConstantsR0234.constants (RingHom.id l)) F M (𝟙 _) g := by
    simpa only [hid, Category.comp_id, ArithmeticThetaLevelCompactificationR0179.openStructure] using hg
  have hl := classified_power_transport (RingHom.id l) m N hm hN (by omega) hmL
    E F M (𝟙 _) g hg' el hel a b A' B atlas
  have hn := C.normalized _ (ArithmeticThetaLevelCompactificationR0179.openStructure l _ E)
    F M (𝟙 _) g j hg hj el ek hel hek
  letI : IsIso (affineDifferential F) := AffineConormalHodgeNaturality.differential_isIso F
  have hcomp := composeComparison_postcompose C.openMap (𝟙 _)
    (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E)
    (Cotangent F) (hodge (ellipticFamily F)) C.hodgeMap el ek (asIso (affineDifferential F)) hn
  change composeComparison C.openMap (𝟙 _) ((𝟙 _) ≫ C.openMap) rfl
    (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E)
    (hodge (ellipticFamily F)) C.hodgeMap (classifierLine F el) = classifierLine F ek at hcomp
  apply ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection_injective
    (𝟙 _) _ _ (tensorComparison (𝟙 _) (ArithmeticThetaLevelConstantsR0234.weight E)
      (hodge (ellipticFamily F)) (classifierLine F el) (ArithmeticThetaCompactUnaryR0183.weight N))
  change powerTransport (𝟙 _) _ _ (classifierLine F el) _
    (powerTransport C.openMap _ _ C.hodgeMap _ _) =
      powerTransport (𝟙 _) _ _ (classifierLine F el) _ _
  have hMD : Scheme.Modules.IsInvertible (ArithmeticThetaLevelConstantsR0234.weight D) :=
    ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.openHodge_invertible
      k (ArithmeticThetaCompactUnaryR0183.level N) D
  have ht := powerTransport_comp C.openMap (𝟙 _) ((𝟙 _) ≫ C.openMap) rfl
    (ArithmeticThetaLevelConstantsR0234.weight D) (ArithmeticThetaLevelConstantsR0234.weight E)
    (hodge (ellipticFamily F)) hMD C.hodgeMap (classifierLine F el)
    (ArithmeticThetaCompactUnaryR0183.weight N)
    (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N)
      (ArithmeticThetaCompactUnaryR0183.weight N) A.section_)
  have ht' := congrArg (fun e => powerTransport ((𝟙 _) ≫ C.openMap)
    (ArithmeticThetaLevelConstantsR0234.weight D) (hodge (ellipticFamily F)) e
    (ArithmeticThetaCompactUnaryR0183.weight N)
    (ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N)
      (ArithmeticThetaCompactUnaryR0183.weight N) A.section_)) hcomp
  exact ht.symm.trans (ht'.trans (hk.trans hl.symm))

#print axioms ArithmeticThetaArithmeticSectionsR0236.open_unary_constant_naturality

#print axioms composeComparison_postcompose
#print axioms classifier_total_comparison
#print axioms powerTransport_comp
#print axioms pullToOpen_transport
#print axioms classified_power_transport

#print axioms affine_conormal_over
#print axioms classifier_differential_hom
#print axioms composeComparison_of_normalization
#print axioms classifier_scalar_eq

#print axioms familyLevel
#print axioms classifier_familyHom
#print axioms common_classifiers

#print axioms familyHom_nsmul

#print axioms pointed_nsmul

#print axioms quotient_cartesian_comparison

#print axioms transport_tensor_restrict

#print axioms normalized_formula_transport

#print axioms normalization_scalar

#print axioms kato_value_base_change

#print axioms kato_value_unique_of_atlas

#print axioms family_power_local

end ArithmeticThetaArithmeticSectionsR0236.OpenUnaryConstantNaturality
