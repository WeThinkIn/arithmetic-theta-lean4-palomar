import MultiplierKeyDefinitionsR0217
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one

/-! Construction of the inverse-character multiplier on the actual marking cover.
The implementation helpers stay in the namespace of this module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
open Opposite TopologicalSpace
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaSchemeLevelR0204 ArithmeticThetaFourTorsion
open ArithmeticThetaRelativeDiscriminantR0171 (IsFrame)

lemma phase_four {R : Type*} [CommRing R] (z : R) (hz : z ^ 2 = -1) :
    z ^ 4 = 1 := by
  calc
    z ^ 4 = (z ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hz]; ring

/-- The exponent used in the frozen frame rule is the inverse character,
without any reducedness, connectedness or field hypothesis on the ring. -/
lemma inverse_character_mul {R : Type*} [CommRing R] (z : R)
    (hz : z ^ 2 = -1) (n : ℕ) : z ^ (3 * n) * z ^ n = 1 := by
  rw [← pow_add, show 3 * n + n = 4 * n by omega, pow_mul, phase_four z hz,
    one_pow]

/-- The inverse character is multiplicative, with the same exponent convention
as the frozen multiplier predicate. -/
lemma inverse_character_product {R : Type*} [CommRing R] (z : R)
    (hz : z ^ 2 = -1) (A B : EvenGroup) :
    z ^ (3 * (characterExponent (A.val * B.val)).val) =
      z ^ (3 * (characterExponent A.val).val) *
        z ^ (3 * (characterExponent B.val).val) := by
  rw [(finite_character_laws.2.2.2.2.2.2 A.val B.val A.property B.property).2,
    ZMod.val_add, ← pow_add]
  apply pow_eq_pow_of_modEq (n := 4) _ (phase_four z hz)
  change (3 * (((characterExponent A.val).val + (characterExponent B.val).val) % 4)) % 4 =
    (3 * (characterExponent A.val).val + 3 * (characterExponent B.val).val) % 4
  simp only [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_add]

/-- The open fibers of a locally constant marking transition. -/
def fiberOpen {T : Scheme.{u}} {I : Type*} (g : LocallyConstant T I) (i : I) : T.Opens :=
  ⟨{t | g t = i}, g.isLocallyConstant.isOpen_fiber i⟩

lemma fiberOpen_cover {T : Scheme.{u}} {I : Type*} (g : LocallyConstant T I) :
    (⨆ i, fiberOpen g i) = ⊤ := by
  apply top_unique
  intro t _
  exact Opens.mem_iSup.mpr ⟨g t, rfl⟩

/-- Gluing along the open fibers constructs an actual regular function. No
identification of sections with scalar-valued point functions is used. -/
lemma existsUnique_piecewise {T : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (v : I → Γ(T, ⊤)) :
    ∃! s : Γ(T, ⊤), ∀ i : I,
      T.presheaf.map (homOfLE (show fiberOpen g i ≤ ⊤ from le_top)).op s =
      T.presheaf.map (homOfLE (show fiberOpen g i ≤ ⊤ from le_top)).op (v i) := by
  apply TopCat.Sheaf.existsUnique_gluing' T.sheaf (fiberOpen g) ⊤
    (fun _ => homOfLE le_top) (fiberOpen_cover g).ge
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hempty : fiberOpen g i ⊓ fiberOpen g j = ⊥ := by
      apply bot_unique
      intro t ht
      exact (hij (ht.1.symm.trans ht.2)).elim
    haveI := CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hempty)
    exact Subsingleton.elim _ _

def piecewise {T : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (v : I → Γ(T, ⊤)) : Γ(T, ⊤) :=
  (existsUnique_piecewise g v).choose

lemma piecewise_spec {T : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (v : I → Γ(T, ⊤)) (i : I) :
    T.presheaf.map (homOfLE (show fiberOpen g i ≤ ⊤ from le_top)).op (piecewise g v) =
      T.presheaf.map (homOfLE (show fiberOpen g i ≤ ⊤ from le_top)).op (v i) :=
  (existsUnique_piecewise g v).choose_spec.1 i

lemma piecewise_germ {T : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (v : I → Γ(T, ⊤)) (t : T) :
    T.presheaf.germ ⊤ t trivial (piecewise g v) =
      T.presheaf.germ ⊤ t trivial (v (g t)) := by
  have H := congrArg (fun s => T.presheaf.germ (fiberOpen g (g t)) t
    (show t ∈ fiberOpen g (g t) from rfl) s) (piecewise_spec g v (g t))
  simpa only [TopCat.Presheaf.germ_res_apply] using H

/-- Piecewise sections commute with arbitrary scheme pullback; this is equality
in local rings, not equality after passing to residue fields. -/
lemma piecewise_precomp {T V : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (v : I → Γ(T, ⊤)) (f : V ⟶ T) :
    f.appTop (piecewise g v) = piecewise (g.comap f.base.hom) (fun i => f.appTop (v i)) := by
  apply TopCat.Presheaf.section_ext V.sheaf ⊤
  intro x hx
  change V.presheaf.germ ⊤ x trivial (f.appTop (piecewise g v)) =
    V.presheaf.germ ⊤ x trivial (piecewise (g.comap f.base.hom) (fun i => f.appTop (v i)))
  rw [piecewise_germ]
  change V.presheaf.germ ⊤ x hx (f.app ⊤ (piecewise g v)) =
    V.presheaf.germ ⊤ x hx (f.app ⊤ (v (g (f x))))
  exact (f.germ_stalkMap_apply ⊤ x trivial (piecewise g v)).symm.trans
    ((congrArg (fun s => f.stalkMap x s) (piecewise_germ g v (f x))).trans
      (f.germ_stalkMap_apply ⊤ x trivial (v (g (f x)))))

lemma piecewise_const {T : Scheme.{u}} {I : Type*}
    (g : LocallyConstant T I) (s : Γ(T, ⊤)) : piecewise g (fun _ => s) = s := by
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro t ht
  exact piecewise_germ g (fun _ => s) t

lemma piecewise_const_index {T : Scheme.{u}} {I : Type*}
    (i : I) (v : I → Γ(T, ⊤)) : piecewise (LocallyConstant.const T i) v = v i := by
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro t ht
  exact piecewise_germ (LocallyConstant.const T i) v t

/-- The actual regular inverse-character function associated to a locally
constant marking transition. -/
def inverseScalar {T : Scheme.{u}} (w : Γ(T, ⊤)) (g : LocallyConstant T EvenGroup) : Γ(T, ⊤) :=
  piecewise g (fun A => w ^ (3 * (characterExponent A.val).val))

lemma inverseScalar_germ {T : Scheme.{u}} (w : Γ(T, ⊤))
    (g : LocallyConstant T EvenGroup) (t : T) :
    T.presheaf.germ ⊤ t trivial (inverseScalar w g) =
      T.presheaf.germ ⊤ t trivial (w ^ (3 * (characterExponent (g t).val).val)) :=
  piecewise_germ g _ t

lemma inverseScalar_precomp {T V : Scheme.{u}} (w : Γ(T, ⊤))
    (g : LocallyConstant T EvenGroup) (f : V ⟶ T) :
    f.appTop (inverseScalar w g) = inverseScalar (f.appTop w) (g.comap f.base.hom) := by
  simp only [inverseScalar, piecewise_precomp, map_pow]

lemma inverseScalar_isUnit {T : Scheme.{u}} (w : Γ(T, ⊤)) (hw : w ^ 2 = -1)
    (g : LocallyConstant T EvenGroup) : IsUnit (inverseScalar w g) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨piecewise g (fun A => w ^ (characterExponent A.val).val), ?_⟩
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro t ht
  change T.presheaf.germ ⊤ t trivial
    (inverseScalar w g * piecewise g (fun A => w ^ (characterExponent A.val).val)) =
      T.presheaf.germ ⊤ t trivial 1
  rw [map_mul, inverseScalar_germ, piecewise_germ, ← map_mul, inverse_character_mul w hw]

/-- Multiplication by an actual global regular section, as a sheaf morphism. -/
abbrev restrictScalar {T : Scheme.{u}} (r : Γ(T, ⊤)) (U : T.Opens) : Γ(T, U) :=
  T.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r

def scalarEnd {T : Scheme.{u}} (r : Γ(T, ⊤)) (M : T.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toLinearMap Γ(T, U.unop) Γ(M, U.unop)
          (restrictScalar r U.unop)).toAddMonoidHom
      naturality := by
        intro U V i
        ext s
        change restrictScalar r V.unop •
          (show Γ(M, V.unop) from M.presheaf.map i (show Γ(M, U.unop) from s)) =
          (show Γ(M, V.unop) from M.presheaf.map i
            (restrictScalar r U.unop • (show Γ(M, U.unop) from s)))
        unfold restrictScalar
        rw [show i = i.unop.op from rfl, Scheme.Modules.map_smul,
          ← CategoryTheory.comp_apply, ← T.presheaf.map_comp]
        rfl }
    (fun U a s => by
      change restrictScalar r U.unop •
          ((show Γ(T, U.unop) from a) • (show Γ(M, U.unop) from s)) =
        (show Γ(T, U.unop) from a) •
          (restrictScalar r U.unop • (show Γ(M, U.unop) from s))
      exact smul_comm _ _ _)⟩

lemma scalarEnd_app {T : Scheme.{u}} (r : Γ(T, ⊤)) (M : T.Modules)
    (U : T.Opens) (s : Γ(M, U)) :
    (scalarEnd r M).app U s = restrictScalar r U • s := rfl

lemma unit_frame (T : Scheme.{u}) : IsFrame (𝟙_ T.Modules) ⊤ (1 : Γ(T, ⊤)) := by
  intro U hU
  change Function.Bijective (fun a : Γ(T, U) =>
    a * T.presheaf.map (homOfLE hU).op (1 : Γ(T, ⊤)))
  simp only [map_one, mul_one]
  exact ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

/-- A frame determines a sheaf map on every open, including the empty open. -/
lemma hom_ext_of_frame {T : Scheme.{u}} {L K : T.Modules}
    (m : Γ(L, ⊤)) (hm : IsFrame L ⊤ m) (f g : L ⟶ K)
    (h : f.app ⊤ m = g.app ⊤ m) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  obtain ⟨a, rfl⟩ := (hm U le_top).2 s
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  rw [← ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.hom_res,
    ← ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.hom_res, h]


/-- A global frame trivializes the entire sheaf, using all open restrictions. -/
lemma exists_frame_iso {X : Scheme.{u}} (M : X.Modules)
    (m : Γ(M, ⊤)) (hm : IsFrame M ⊤ m) :
    ∃ e : (𝟙_ X.Modules) ≅ M, e.hom.app ⊤ (1 : Γ(X, ⊤)) = m := by
  let f := ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.fromSection M m
  haveI : IsIso f := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr (fun U => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hm U le_top)
  refine ⟨asIso f, ?_⟩
  change (1 : Γ(X, ⊤)) • M.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op m = m
  simp

/-- The isomorphism between framed sheaves is unique before descent. -/
lemma existsUnique_frame_iso {X : Scheme.{u}} (M N : X.Modules)
    (m : Γ(M, ⊤)) (n : Γ(N, ⊤)) (hm : IsFrame M ⊤ m) (hn : IsFrame N ⊤ n) :
    ∃! e : M ≅ N, e.hom.app ⊤ m = n := by
  obtain ⟨eM, heM⟩ := exists_frame_iso M m hm
  obtain ⟨eN, heN⟩ := exists_frame_iso N n hn
  have h : (eM.symm ≪≫ eN).hom.app ⊤ m = n := by
    rw [← heM]
    change (eM.hom ≫ eM.inv ≫ eN.hom).app ⊤ (1 : Γ(X, ⊤)) = n
    simpa only [Iso.hom_inv_id_assoc] using heN
  refine ⟨eM.symm ≪≫ eN, h, ?_⟩
  intro e he
  apply Iso.ext
  exact hom_ext_of_frame m hm e.hom (eM.symm ≪≫ eN).hom (he.trans h.symm)

/-- A scalar equation of sheaf maps determines the corresponding frame rule. -/
lemma scalar_frame_transfer {X : Scheme.{u}} {M N : X.Modules}
    (β : M ≅ N) (φ : M ⟶ N) (r : Γ(X, ⊤))
    (m t : Γ(M, ⊤)) (v : Γ(N, ⊤))
    (hβ : β.hom = φ ≫ scalarEnd r N)
    (hφ : φ.app ⊤ t = v) (hm : β.hom.app ⊤ m = v) : t = r • m := by
  apply (ConcreteCategory.bijective_of_isIso (β.hom.app ⊤)).1
  rw [Scheme.Modules.Hom.app_smul, hm, hβ]
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, scalarEnd_app, hφ]
  have hr : restrictScalar r ⊤ = r :=
    ConcreteCategory.congr_hom (X.presheaf.map_id (op ⊤)) r
  rw [hr]


/-- Equality of global module sections is detected on a covering family of
actual open subschemes. -/
lemma section_ext_open_pullback {X : Scheme.{u}} (M : X.Modules) (s t : Γ(M, ⊤))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ArithmeticThetaPullback.pullbackGlobalSection U.ι M s =
        ArithmeticThetaPullback.pullbackGlobalSection U.ι M t) : s = t := by
  choose U hx hU using h
  have hc : (⊤ : X.Opens) ≤ ⨆ x, U x := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨M.presheaf, M.isSheaf⟩
    U ⊤ (fun _ => homOfLE le_top) hc
  intro x
  apply (Scheme.Modules.bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff M (U x)).1.1
  have H := congrArg (fun s =>
    ((Scheme.Modules.pullback (U x).ι).obj M).presheaf.map
      (homOfLE (show (U x).ι ⁻¹ᵁ U x ≤ (U x).ι ⁻¹ᵁ ⊤ from fun _ _ => trivial)).op s) (hU x)
  exact (Scheme.Modules.map_homOfLE_pullbackLocalSection (U x).ι le_top s).symm.trans
    (H.trans (Scheme.Modules.map_homOfLE_pullbackLocalSection (U x).ι le_top t))


/-- A framed source allows sheaf morphisms to be checked after local open
pullbacks, with no reducedness assumption. -/
lemma hom_ext_local_pullback {X : Scheme.{u}} {M N : X.Modules}
    (m : Γ(M, ⊤)) (hm : IsFrame M ⊤ m) (f g : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.pullback U.ι).map f = (Scheme.Modules.pullback U.ι).map g) : f = g := by
  apply hom_ext_of_frame m hm
  apply section_ext_open_pullback
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  refine ⟨U, hx, ?_⟩
  change Scheme.Modules.pullbackLocalSection U.ι (f.app ⊤ m) =
    Scheme.Modules.pullbackLocalSection U.ι (g.app ⊤ m)
  rw [Scheme.Modules.pullbackLocalSection_app, Scheme.Modules.pullbackLocalSection_app, hU]

namespace Transport
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2

abbrev FF := ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)

lemma scalar_naturality {X : Scheme.{u}} (r : Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N) :
    scalarEnd r M ≫ f = f ≫ scalarEnd r N := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact Scheme.Modules.Hom.app_smul f _ s

lemma scalar_conjugate {X : Scheme.{u}} (r : Γ(X, ⊤)) {M N : X.Modules} (e : M ≅ N) :
    e.inv ≫ scalarEnd r M ≫ e.hom = scalarEnd r N := by
  rw [scalar_naturality, Iso.inv_hom_id_assoc]

lemma scalar_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map (scalarEnd r M) =
      scalarEnd (f.appTop r) ((Scheme.Modules.pullback f).obj M) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact pullback_map_sectionScalar f r (scalarEnd_app r M) U s

lemma scalar_pullHom {X Y Z : Scheme.{u}} (q : Y ⟶ Z) (M : Z.Modules)
    (r : Γ(Y, ⊤)) (f : X ⟶ Y) (p : X ⟶ Z) (hp : f ≫ q = p) :
    pullHom (F := FF) (M₁ := M) (M₂ := M) (f₁ := q) (f₂ := q)
      (scalarEnd r ((Scheme.Modules.pullback q).obj M)) f p p hp hp =
        scalarEnd (f.appTop r) ((Scheme.Modules.pullback p).obj M) := by
  rw [pullHom_eq₂, scalar_pullback]
  exact scalar_conjugate (f.appTop r)
    ((Scheme.Modules.pullbackComp f q).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M)

set_option maxHeartbeats 1000000
/-- Pulling a complete descent equation along any map into the overlap gives
an equation of actual sheaf maps in one consistent pullback presentation. -/
lemma datum_pull {X Y P T : Scheme.{u}} (q : X ⟶ Y) (p₁ p₂ : P ⟶ X)
    (hp : p₁ ≫ q = p₂ ≫ q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (r : Γ(P, ⊤))
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
      (scalarEnd r _ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M =
          (Scheme.Modules.pullback (p₂ ≫ q)).obj M by rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N =
          (Scheme.Modules.pullback (p₂ ≫ q)).obj N by rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫
        (Scheme.Modules.pullback p₂).map β.hom)
    (s : T ⟶ P) (p : T ⟶ Y) (hs : s ≫ (p₁ ≫ q) = p) :
    pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
      β.hom (s ≫ p₂) p p (by rw [Category.assoc, ← hp, hs])
        (by rw [Category.assoc, ← hp, hs]) =
      pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
        β.hom (s ≫ p₁) p p (by rw [Category.assoc, hs]) (by rw [Category.assoc, hs]) ≫
          scalarEnd (s.appTop r) ((Scheme.Modules.pullback p).obj M) := by
  have H := datum_eq q p₁ p₂ hp (scalarEnd r _) β hβ
  have H' := congrArg (fun f => pullHom (F := FF) (M₁ := N) (M₂ := M)
    (f₁ := p₁ ≫ q) (f₂ := p₁ ≫ q) f s p p hs hs) H
  have hc : (Scheme.Modules.pullbackComp p₁ q).inv.app M ≫
      scalarEnd r ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M)) ≫
      (Scheme.Modules.pullbackComp p₁ q).hom.app M =
      scalarEnd r ((Scheme.Modules.pullback (p₁ ≫ q)).obj M) :=
    scalar_conjugate r ((Scheme.Modules.pullbackComp p₁ q).app M)
  rw [hc] at H'
  rw [Gen.pullHom_comp FF _ _ s p p p hs hs hs] at H'
  rw [scalar_pullHom (p₁ ≫ q) M r s p hs] at H'
  have hleft :
      pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := p₁ ≫ q) (f₂ := p₁ ≫ q)
          (pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
            β.hom p₂ (p₁ ≫ q) (p₁ ≫ q) hp.symm hp.symm)
          s p p hs hs =
        pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
          β.hom (s ≫ p₂) p p
          (by rw [Category.assoc, ← hp, hs]) (by rw [Category.assoc, ← hp, hs]) := by
    exact pullHom_pullHom (F := FF) (φ := β.hom) (g := p₂)
      (gf₁ := p₁ ≫ q) (gf₂ := p₁ ≫ q) (g' := s) (g'f₁ := p) (g'f₂ := p)
      (hgf₁ := hp.symm) (hgf₂ := hp.symm) (hg'f₁ := hs) (hg'f₂ := hs)
  have hright :
      pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := p₁ ≫ q) (f₂ := p₁ ≫ q)
          (pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
            β.hom p₁ (p₁ ≫ q) (p₁ ≫ q) rfl rfl)
          s p p hs hs =
        pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := q) (f₂ := q)
          β.hom (s ≫ p₁) p p
          (by rw [Category.assoc, hs]) (by rw [Category.assoc, hs]) := by
    exact pullHom_pullHom (F := FF) (φ := β.hom) (g := p₁)
      (gf₁ := p₁ ≫ q) (gf₂ := p₁ ≫ q) (g' := s) (g'f₁ := p) (g'f₂ := p)
      (hgf₁ := rfl) (hgf₂ := rfl) (hg'f₁ := hs) (hg'f₂ := hs)
  rw [hleft, hright] at H'
  exact H'
set_option maxHeartbeats 200000

/-- Naturality of the actual pullback-composition frame transport under an
arbitrary morphism of pulled-back modules. -/
lemma pullHom_overPull {S X : Scheme.{u}} (π : X ⟶ S)
    {N M : S.Modules} (q : X ⟶ X) (hq : q ≫ π = π)
    (β : (Scheme.Modules.pullback π).obj N ⟶ (Scheme.Modules.pullback π).obj M)
    (m : Γ((Scheme.Modules.pullback π).obj N, ⊤)) :
    (pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := π) (f₂ := π)
      β q π π hq hq).app ⊤
        (((Scheme.Modules.pullbackComp q π).app N ≪≫
          (Scheme.Modules.pullbackCongr hq).app N).hom.app ⊤
          (ArithmeticThetaPullback.pullbackGlobalSection q ((Scheme.Modules.pullback π).obj N) m)) =
      ((Scheme.Modules.pullbackComp q π).app M ≪≫
        (Scheme.Modules.pullbackCongr hq).app M).hom.app ⊤
          (ArithmeticThetaPullback.pullbackGlobalSection q ((Scheme.Modules.pullback π).obj M)
            (β.app ⊤ m)) := by
  let eN := (Scheme.Modules.pullbackComp q π).app N ≪≫
    (Scheme.Modules.pullbackCongr hq).app N
  let eM := (Scheme.Modules.pullbackComp q π).app M ≪≫
    (Scheme.Modules.pullbackCongr hq).app M
  have hmap : eN.hom ≫
      pullHom (F := FF) (M₁ := N) (M₂ := M) (f₁ := π) (f₂ := π) β q π π hq hq =
      (Scheme.Modules.pullback q).map β ≫ eM.hom := by
    rw [pullHom_eq₂]
    simp only [eN, eM, Iso.trans_hom, Iso.app_hom, Category.assoc,
      Iso.hom_inv_id_app_assoc]
  have H := congrArg (fun f => f.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection q ((Scheme.Modules.pullback π).obj N) m)) hmap
  change _ = eM.hom.app ⊤ _
  rw [show (ArithmeticThetaPullback.pullbackGlobalSection q ((Scheme.Modules.pullback π).obj M)
    (β.app ⊤ m)) = ((Scheme.Modules.pullback q).map β).app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection q ((Scheme.Modules.pullback π).obj N) m) from
        Scheme.Modules.pullbackLocalSection_app q β m]
  exact H

lemma congr_global {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).app M).hom.app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection f M s) =
        ArithmeticThetaPullback.pullbackGlobalSection g M s := by
  subst g
  rfl

lemma comp_global {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app M).hom.app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection f _
        (ArithmeticThetaPullback.pullbackGlobalSection g M s)) =
      ArithmeticThetaPullback.pullbackGlobalSection (f ≫ g) M s :=
  ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackComp_hom_section f g M ⊤ s

lemma unit_inv_one {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)) =
      ArithmeticThetaPullback.pullbackGlobalSection f (𝟙_ Y.Modules) (1 : Γ(Y, ⊤)) := by
  have H := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
    f ⊤ (1 : Γ(Y, ⊤))
  rw [map_one] at H
  have H' := congrArg (fun s => (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ s) H
  change ((Scheme.Modules.pullbackUnitIso f).hom ≫
    (Scheme.Modules.pullbackUnitIso f).inv).app ⊤
      (ArithmeticThetaPullback.pullbackGlobalSection f (𝟙_ Y.Modules) (1 : Γ(Y, ⊤))) =
        (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)) at H'
  rw [Iso.hom_inv_id] at H'
  exact H'.symm

lemma over_unit {X Y : Scheme.{u}} (π : X ⟶ Y) (q : X ⟶ X) (hq : q ≫ π = π) :
    ((Scheme.Modules.pullbackComp q π).app (𝟙_ Y.Modules) ≪≫
      (Scheme.Modules.pullbackCongr hq).app (𝟙_ Y.Modules)).hom.app ⊤
        (ArithmeticThetaPullback.pullbackGlobalSection q _
          ((Scheme.Modules.pullbackUnitIso π).inv.app ⊤ (1 : Γ(X, ⊤)))) =
      (Scheme.Modules.pullbackUnitIso π).inv.app ⊤ (1 : Γ(X, ⊤)) := by
  rw [unit_inv_one]
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [comp_global, congr_global]


lemma pullHom_map_eq {X Y Z : Scheme.{u}} (π : X ⟶ Y) {L K : Y.Modules}
    (f g : (Scheme.Modules.pullback π).obj L ⟶ (Scheme.Modules.pullback π).obj K)
    (a : Z ⟶ X) (p : Z ⟶ Y) (ha : a ≫ π = p)
    (h : pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π)
        f a p p ha ha =
      pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π) g a p p ha ha) :
    (Scheme.Modules.pullback a).map f = (Scheme.Modules.pullback a).map g := by
  let eL := (Scheme.Modules.pullbackComp a π).app L ≪≫ (Scheme.Modules.pullbackCongr ha).app L
  let eK := (Scheme.Modules.pullbackComp a π).app K ≪≫ (Scheme.Modules.pullbackCongr ha).app K
  have H := congrArg (fun v => eL.hom ≫ v ≫ eK.inv) h
  simpa only [pullHom_eq₂, eL, eK, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id] using H

lemma pullHom_action_eq {X Y T : Scheme.{u}} (π : X ⟶ Y) {L K : Y.Modules}
    (η : (Scheme.Modules.pullback π).obj L ⟶ (Scheme.Modules.pullback π).obj K)
    (q : X ⟶ X) (hq : q ≫ π = π)
    (hη : pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π)
      η q π π hq hq = η)
    (a : T ⟶ X) (p : T ⟶ Y) (ha : a ≫ π = p) :
    pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π)
      η (a ≫ q) p p (by rw [Category.assoc, hq, ha]) (by rw [Category.assoc, hq, ha]) =
    pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π)
      η a p p ha ha := by
  have H := congrArg (fun v =>
    pullHom (F := FF) (M₁ := L) (M₂ := K) (f₁ := π) (f₂ := π) v a p p ha ha) hη
  rw [pullHom_pullHom] at H
  exact H

end Transport

variable {S : Scheme.{u}} (E : Family S)
variable (k : Type u) [Field k] [CharZero k] (σ : S ⟶ Base k)
variable (P : EvenPoint E) (z : Γ(S, ⊤)) (D : Cover E)
variable (hD : RepresentsEven E P z D)

include k σ P z hD

/-- The representing functor separates arbitrary parameter morphisms by the
actual two marking sections, not merely by their geometric points. -/
lemma parameter_ext {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (hx : a ≫ D.marking.x.val ≫ D.comparison = b ≫ D.marking.x.val ≫ D.comparison)
    (hy : a ≫ D.marking.y.val ≫ D.comparison = b ≫ D.marking.y.val ≫ D.comparison) :
    a = b := by
  let c := a ≫ D.projection
  obtain ⟨F, f, hpb, hz, hm⟩ := scheme_family_base_change S T E c
  have hF : Cartesian E F c f := ⟨hpb, hz, hm⟩
  obtain ⟨M, h, hM, hf⟩ := EvenMarkingSubcover.marking_over_parameter E k σ D F c f hF a rfl
  have hmatch : Matches E P z F M c f := by
    have H := EvenMarkingSubcover.matches_pullback E P z D.family F D.marking M
      D.projection D.comparison a h hM hD.1
    simpa only [hf] using H
  have hMx : M.x.val ≫ f = a ≫ D.marking.x.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hM.2.2.2.1, Category.assoc]
  have hMy : M.y.val ≫ f = a ≫ D.marking.y.val ≫ D.comparison := by
    rw [← hf, ← Category.assoc, hM.2.2.2.2, Category.assoc]
  obtain ⟨l, hl, hlf⟩ := SchemeFourCover.marked_factor E k σ D.family F
    D.projection D.comparison D.cartesian c f hF b hab.symm D.marking M
    (hMx.trans hx) (hMy.trans hy)
  exact congrArg Subtype.val ((hD.2 T F M c f hF hmatch).unique
    (y₁ := ⟨a, rfl⟩) (y₂ := ⟨b, hab.symm⟩) ⟨h, hM, hf⟩ ⟨l, hl, hlf⟩)

/-- The locally constant marking comparison is an equality of actual action
maps locally on every test scheme. This supplies the full-overlap bridge. -/
lemma locallyRelated_action {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (g : LocallyConstant T EvenGroup) (hg : LocallyRelated E D a b g)
    (q : ∀ A : EvenGroup, D.space ≅ D.space)
    (hq : ∀ A : EvenGroup, Acts E D A.val (q A)) :
    ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      (∀ v : T, v ∈ U → g v = g t) ∧ U.ι ≫ b = U.ι ≫ a ≫ (q (g t)).hom := by
  intro t
  obtain ⟨U, ht, hU, hx, hy⟩ := hg t
  refine ⟨U, ht, hU, parameter_ext E k σ P z D hD _ _ ?_ ?_ ?_⟩
  · simp only [Category.assoc, (hq (g t)).1, hab]
  · simpa only [Category.assoc, (hq (g t)).2.1] using hx
  · simpa only [Category.assoc, (hq (g t)).2.2] using hy

/-- Chosen representatives of the unique actual action automorphisms. -/
def action (A : EvenGroup) : D.space ≅ D.space :=
  (EvenCoverRightAction.iso_exists E k σ P z D hD A).choose

lemma action_spec (A : EvenGroup) : Acts E D A.val (action E k σ P z D hD A) :=
  (EvenCoverRightAction.iso_exists E k σ P z D hD A).choose_spec.1

omit k σ P z hD in
lemma action_locallyRelated {T : Scheme.{u}} (a b : T ⟶ D.space)
    (g : LocallyConstant T EvenGroup)
    (q : ∀ A : EvenGroup, D.space ≅ D.space)
    (hq : ∀ A : EvenGroup, Acts E D A.val (q A))
    (hg : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      (∀ v : T, v ∈ U → g v = g t) ∧ U.ι ≫ b = U.ι ≫ a ≫ (q (g t)).hom) :
    LocallyRelated E D a b g := by
  intro t
  obtain ⟨U, ht, hU, he⟩ := hg t
  refine ⟨U, ht, hU, ?_, ?_⟩
  · rw [← Category.assoc, he]
    simp only [Category.assoc, (hq (g t)).2.1]
  · rw [← Category.assoc, he]
    simp only [Category.assoc, (hq (g t)).2.2]

/-- Local marking transitions are stable under arbitrary scheme maps. -/
lemma locallyRelated_precomp {T V : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (g : LocallyConstant T EvenGroup) (hg : LocallyRelated E D a b g)
    (f : V ⟶ T) :
    LocallyRelated E D (f ≫ a) (f ≫ b) (g.comap f.base.hom) := by
  apply action_locallyRelated E D _ _ _ (action E k σ P z D hD)
    (action_spec E k σ P z D hD)
  intro v
  obtain ⟨U, hv, hU, he⟩ := locallyRelated_action E k σ P z D hD a b hab g hg
    (action E k σ P z D hD) (action_spec E k σ P z D hD) (f v)
  refine ⟨f ⁻¹ᵁ U, hv, fun w hw => hU (f w) hw, ?_⟩
  change (f ⁻¹ᵁ U).ι ≫ (f ≫ b) =
    (f ⁻¹ᵁ U).ι ≫ (f ≫ a) ≫ (action E k σ P z D hD (g (f v))).hom
  have H := congrArg (fun j => (f ∣_ U) ≫ j) he
  simpa only [← Category.assoc, morphismRestrict_ι] using H

/-- The unique full-overlap transition, on arbitrary scheme-valued tests. -/
def transition {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) : LocallyConstant T EvenGroup :=
  (EvenCoverTorsor.simple_transitivity E k σ P z D hD T a b hab).choose

lemma transition_spec {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) :
    LocallyRelated E D a b (transition E k σ P z D hD a b hab) :=
  (EvenCoverTorsor.simple_transitivity E k σ P z D hD T a b hab).choose_spec.1

lemma transition_unique {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (g : LocallyConstant T EvenGroup) (hg : LocallyRelated E D a b g) :
    g = transition E k σ P z D hD a b hab :=
  (EvenCoverTorsor.simple_transitivity E k σ P z D hD T a b hab).choose_spec.2 g hg

lemma transition_precomp {T V : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) (f : V ⟶ T) :
    transition E k σ P z D hD (f ≫ a) (f ≫ b)
      (by simpa only [Category.assoc] using congrArg (fun j => f ≫ j) hab) =
    (transition E k σ P z D hD a b hab).comap f.base.hom := by
  symm
  apply transition_unique
  exact locallyRelated_precomp E k σ P z D hD a b hab _
    (transition_spec E k σ P z D hD a b hab) f

omit k σ P z hD E D in
def evenProduct (A B : EvenGroup) : EvenGroup :=
  ⟨A.val * B.val, (finite_character_laws.2.2.2.2.2.2 A.val B.val A.property B.property).1⟩

omit k σ P z hD E D in
def localProduct {T : Scheme.{u}} (g h : LocallyConstant T EvenGroup) :
    LocallyConstant T EvenGroup :=
  ⟨fun t => evenProduct (g t) (h t), g.isLocallyConstant.comp₂ h.isLocallyConstant evenProduct⟩

lemma action_product (A B : EvenGroup) :
    (action E k σ P z D hD A).hom ≫ (action E k σ P z D hD B).hom =
      (action E k σ P z D hD (evenProduct A B)).hom := by
  apply EvenCoverRightAction.maps_unique E k σ P z D hD (A.val * B.val)
  · exact EvenCoverRightAction.maps_mul E k σ D A.val B.val A.property.1 B.property.1
      _ _ (action_spec E k σ P z D hD A) (action_spec E k σ P z D hD B)
  · exact action_spec E k σ P z D hD (evenProduct A B)

lemma locallyRelated_product {T : Scheme.{u}} (a b c : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (hbc : b ≫ D.projection = c ≫ D.projection)
    (g h : LocallyConstant T EvenGroup) (hg : LocallyRelated E D a b g)
    (hh : LocallyRelated E D b c h) : LocallyRelated E D a c (localProduct g h) := by
  apply action_locallyRelated E D _ _ _ (action E k σ P z D hD)
    (action_spec E k σ P z D hD)
  intro t
  obtain ⟨U, htU, hU, heU⟩ := locallyRelated_action E k σ P z D hD a b hab g hg
    (action E k σ P z D hD) (action_spec E k σ P z D hD) t
  obtain ⟨V, htV, hV, heV⟩ := locallyRelated_action E k σ P z D hD b c hbc h hh
    (action E k σ P z D hD) (action_spec E k σ P z D hD) t
  refine ⟨U ⊓ V, ⟨htU, htV⟩, ?_, ?_⟩
  · intro v hv
    change evenProduct (g v) (h v) = evenProduct (g t) (h t)
    rw [hU v hv.1, hV v hv.2]
  · have eU := congrArg (fun j => T.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ j) heU
    have eV := congrArg (fun j => T.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ j) heV
    simp only [← Category.assoc, Scheme.homOfLE_ι] at eU eV
    change (U ⊓ V).ι ≫ c = (U ⊓ V).ι ≫ a ≫
      (action E k σ P z D hD (evenProduct (g t) (h t))).hom
    rw [eV, eU]
    simp only [Category.assoc, action_product]

/-- The cocycle equation holds as a locally constant function on every scheme,
including nonreduced and disconnected triple overlaps. -/
lemma transition_product {T : Scheme.{u}} (a b c : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (hbc : b ≫ D.projection = c ≫ D.projection) :
    transition E k σ P z D hD a c (hab.trans hbc) =
      localProduct (transition E k σ P z D hD a b hab)
        (transition E k σ P z D hD b c hbc) := by
  symm
  apply transition_unique
  exact locallyRelated_product E k σ P z D hD a b c hab hbc _ _
    (transition_spec E k σ P z D hD a b hab)
    (transition_spec E k σ P z D hD b c hbc)

omit k σ P z hD E D in
lemma inverseScalar_product {T : Scheme.{u}} (w : Γ(T, ⊤)) (hw : w ^ 2 = -1)
    (g h : LocallyConstant T EvenGroup) :
    inverseScalar w (localProduct g h) = inverseScalar w g * inverseScalar w h := by
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro t ht
  change T.presheaf.germ ⊤ t trivial (inverseScalar w (localProduct g h)) =
    T.presheaf.germ ⊤ t trivial (inverseScalar w g * inverseScalar w h)
  rw [map_mul, inverseScalar_germ, inverseScalar_germ, inverseScalar_germ, ← map_mul]
  exact congrArg (fun s => T.presheaf.germ ⊤ t trivial s)
    (inverse_character_product w hw (g t) (h t))

/-- The regular inverse-character scalar on an arbitrary overlap. -/
def transitionScalar {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) : Γ(T, ⊤) :=
  inverseScalar ((a ≫ D.projection).appTop z) (transition E k σ P z D hD a b hab)

lemma transitionScalar_precomp {T V : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection) (f : V ⟶ T) :
    f.appTop (transitionScalar E k σ P z D hD a b hab) =
      transitionScalar E k σ P z D hD (f ≫ a) (f ≫ b)
        (by simpa only [Category.assoc] using congrArg (fun j => f ≫ j) hab) := by
  unfold transitionScalar
  rw [transition_precomp E k σ P z D hD a b hab f, inverseScalar_precomp]
  simp only [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

lemma transitionScalar_product (hz : z ^ 2 = -1) {T : Scheme.{u}} (a b c : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (hbc : b ≫ D.projection = c ≫ D.projection) :
    transitionScalar E k σ P z D hD a c (hab.trans hbc) =
      transitionScalar E k σ P z D hD a b hab * transitionScalar E k σ P z D hD b c hbc := by
  have hw : ((a ≫ D.projection).appTop z) ^ 2 = -1 := by
    rw [← map_pow, hz, map_neg, map_one]
  unfold transitionScalar
  rw [transition_product E k σ P z D hD a b c hab hbc]
  rw [inverseScalar_product _ hw, hab]

lemma transition_action {T : Scheme.{u}} (a : T ⟶ D.space)
    (A : EvenGroup) (q : D.space ≅ D.space) (hq : Acts E D A.val q) :
    transition E k σ P z D hD a (a ≫ q.hom)
      (by rw [Category.assoc, hq.1]) = LocallyConstant.const T A := by
  symm
  apply transition_unique
  apply action_locallyRelated E D _ _ _ (action E k σ P z D hD)
    (action_spec E k σ P z D hD)
  intro t
  refine ⟨⊤, trivial, fun _ _ => rfl, ?_⟩
  have he : q = action E k σ P z D hD A :=
    (EvenCoverRightAction.iso_exists E k σ P z D hD A).choose_spec.2 q hq
  subst q
  rfl

lemma transition_self {T : Scheme.{u}} (a : T ⟶ D.space) :
    transition E k σ P z D hD a a rfl =
      LocallyConstant.const T (⟨1, EvenCoverRightAction.one_even⟩ : EvenGroup) := by
  simpa only [Iso.refl_hom, Category.comp_id] using
    transition_action E k σ P z D hD a ⟨1, EvenCoverRightAction.one_even⟩
      (Iso.refl D.space) (EvenCoverRightAction.maps_one E k σ D)

/-- The scalar on the graph of each actual right action has exactly the
inverse exponent required by the contract. -/
lemma transitionScalar_action {T : Scheme.{u}} (a : T ⟶ D.space)
    (A : EvenGroup) (q : D.space ≅ D.space) (hq : Acts E D A.val q) :
    transitionScalar E k σ P z D hD a (a ≫ q.hom)
      (by rw [Category.assoc, hq.1]) =
        (a ≫ D.projection).appTop (z ^ (3 * (characterExponent A.val).val)) := by
  unfold transitionScalar
  rw [transition_action E k σ P z D hD a A q hq]
  simp only [inverseScalar, piecewise_const_index, map_pow]

lemma transitionScalar_self {T : Scheme.{u}} (a : T ⟶ D.space) :
    transitionScalar E k σ P z D hD a a rfl = 1 := by
  unfold transitionScalar
  rw [transition_self E k σ P z D hD a]
  simp only [inverseScalar, piecewise_const_index, finite_character_laws.2.2.2.1,
    ZMod.val_zero, mul_zero, pow_zero]

/-- Diagonal normalization of the regular Cech transition. -/
lemma transitionScalar_diagonal {T : Scheme.{u}} (a b : T ⟶ D.space)
    (hab : a ≫ D.projection = b ≫ D.projection)
    (δ : D.space ⟶ T) (hδ₁ : δ ≫ a = 𝟙 D.space) (hδ₂ : δ ≫ b = 𝟙 D.space) :
    δ.appTop (transitionScalar E k σ P z D hD a b hab) = 1 := by
  rw [transitionScalar_precomp E k σ P z D hD a b hab δ]
  simp only [hδ₁, hδ₂]
  exact transitionScalar_self E k σ P z D hD (𝟙 D.space)

/-- The scalar Cech cocycle, stated for actual maps of schemes. -/
lemma transitionScalar_cocycle (hz : z ^ 2 = -1) {T W : Scheme.{u}}
    (p₁ p₂ : T ⟶ D.space) (hp : p₁ ≫ D.projection = p₂ ≫ D.projection)
    (a b c : W ⟶ T) (hab : a ≫ p₂ = b ≫ p₁)
    (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂) :
    a.appTop (transitionScalar E k σ P z D hD p₁ p₂ hp) *
      b.appTop (transitionScalar E k σ P z D hD p₁ p₂ hp) =
        c.appTop (transitionScalar E k σ P z D hD p₁ p₂ hp) := by
  rw [transitionScalar_precomp E k σ P z D hD p₁ p₂ hp a,
    transitionScalar_precomp E k σ P z D hD p₁ p₂ hp b,
    transitionScalar_precomp E k σ P z D hD p₁ p₂ hp c]
  have h₁ : (a ≫ p₁) ≫ D.projection = (a ≫ p₂) ≫ D.projection := by
    simpa only [Category.assoc] using congrArg (fun j => a ≫ j) hp
  have h₂ : (a ≫ p₂) ≫ D.projection = (b ≫ p₂) ≫ D.projection := by
    rw [hab]
    simpa only [Category.assoc] using congrArg (fun j => b ≫ j) hp
  have H := (transitionScalar_product E k σ P z D hD hz
    (a ≫ p₁) (a ≫ p₂) (b ≫ p₂) h₁ h₂).symm
  simpa only [hab, hca, hcb] using H

/-- The actual Cech pair scheme of the already accepted marking cover. -/
abbrev overlap : Scheme.{u} := pullback D.projection D.projection

abbrev first : overlap E D ⟶ D.space := pullback.fst D.projection D.projection
abbrev second : overlap E D ⟶ D.space := pullback.snd D.projection D.projection

def diagonal : D.space ⟶ overlap E D := pullback.lift (𝟙 _) (𝟙 _) (by simp)

abbrev tripleOverlap : Scheme.{u} := pullback (second E D) (first E D)
abbrev firstPair : tripleOverlap E D ⟶ overlap E D := pullback.fst (second E D) (first E D)
abbrev secondPair : tripleOverlap E D ⟶ overlap E D := pullback.snd (second E D) (first E D)

def outerPair : tripleOverlap E D ⟶ overlap E D :=
  pullback.lift (firstPair E D ≫ first E D) (secondPair E D ≫ second E D) (by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, pullback.condition])

/-- Coordinate descent maps point from the first trivialization to the second.
Their scalar is the reciprocal of the frame transition, hence the reversed
arguments here. This is the source's isomorphism-to-standard convention. -/
def descentScalar : Γ(overlap E D, ⊤) :=
  transitionScalar E k σ P z D hD (second E D) (first E D) pullback.condition.symm

def canonicalComparison (M : S.Modules) :
    (Scheme.Modules.pullback (first E D)).obj ((Scheme.Modules.pullback D.projection).obj M) ⟶
      (Scheme.Modules.pullback (second E D)).obj ((Scheme.Modules.pullback D.projection).obj M) :=
  (Scheme.Modules.pullbackComp (first E D) D.projection).hom.app M ≫
    eqToHom (by rw [show first E D ≫ D.projection = second E D ≫ D.projection from
      pullback.condition]) ≫
    (Scheme.Modules.pullbackComp (second E D) D.projection).inv.app M

def descentMap (M : S.Modules) :
    (Scheme.Modules.pullback (first E D)).obj ((Scheme.Modules.pullback D.projection).obj M) ⟶
      (Scheme.Modules.pullback (second E D)).obj ((Scheme.Modules.pullback D.projection).obj M) :=
  scalarEnd (descentScalar E k σ P z D hD) _ ≫ canonicalComparison E D M

/-- Effective descent of the actual equivariant trivial line on the marking
cover, with its complete compatibility equation on the pair scheme. -/
lemma exists_descended_line (hz : z ^ 2 = -1) :
    ∃ (L : S.Modules) (_ : Scheme.Modules.IsInvertible L)
      (β : (Scheme.Modules.pullback D.projection).obj L ≅
        (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)),
      (Scheme.Modules.pullback (first E D)).map β.hom ≫ descentMap E k σ P z D hD (𝟙_ S.Modules) =
        canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map β.hom := by
  obtain ⟨hf, het, hs, _⟩ := EvenCoverTorsor.geometry E k σ P z hz D hD
  letI := hf
  letI := het
  letI := hs
  have hd₁ : diagonal E D ≫ first E D = 𝟙 D.space := pullback.lift_fst _ _ _
  have hd₂ : diagonal E D ≫ second E D = 𝟙 D.space := pullback.lift_snd _ _ _
  have hc₁ : outerPair E D ≫ first E D = firstPair E D ≫ first E D := pullback.lift_fst _ _ _
  have hc₂ : outerPair E D ≫ second E D = secondPair E D ≫ second E D := pullback.lift_snd _ _ _
  have hu₁ : (diagonal E D).appTop (descentScalar E k σ P z D hD) = 1 :=
    transitionScalar_diagonal E k σ P z D hD _ _ _ _ hd₂ hd₁
  have hu₂ : (firstPair E D).appTop (descentScalar E k σ P z D hD) *
      (secondPair E D).appTop (descentScalar E k σ P z D hD) =
        (outerPair E D).appTop (descentScalar E k σ P z D hD) := by
    have H := transitionScalar_cocycle E k σ P z D hD hz
      (second E D) (first E D) pullback.condition.symm
      (secondPair E D) (firstPair E D) (outerPair E D) pullback.condition.symm hc₂ hc₁
    exact (mul_comm _ _).trans H
  have H := DescentCharacter.pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
    D.projection (first E D) (second E D) pullback.condition
    (diagonal E D) hd₁ hd₂ (firstPair E D) (secondPair E D) pullback.condition
    (outerPair E D) hc₁ hc₂ (𝟙_ S.Modules) (descentScalar E k σ P z D hD) hu₁ hu₂
    (scalarEnd (descentScalar E k σ P z D hD) _) (scalarEnd_app _ _)
  exact DescentCharacter.exists_isInvertible_iso_comp_eq_of_cocycle D.projection
    (first E D) (second E D) (IsPullback.of_hasPullback _ _)
    (diagonal E D) hd₁ hd₂ (firstPair E D) (secondPair E D) (IsPullback.of_hasPullback _ _)
    (outerPair E D) hc₁ hc₂ (Scheme.Modules.isInvertible_unit S)
    (descentMap E k σ P z D hD (𝟙_ S.Modules)) H.1 H.2

omit k σ P z hD in
/-- The level frame is obtained from the actual descended trivialization. -/
def levelFrame {L : S.Modules}
    (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)) :
    Γ((Scheme.Modules.pullback D.projection).obj L, ⊤) :=
  (β ≪≫ Scheme.Modules.pullbackUnitIso D.projection).inv.app ⊤ (1 : Γ(D.space, ⊤))

omit k σ P z hD in
lemma levelFrame_isFrame {L : S.Modules}
    (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)) :
    IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ (levelFrame E D β) :=
  ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
    (β ≪≫ Scheme.Modules.pullbackUnitIso D.projection).symm _ (unit_frame D.space)

/-- The effective descent output includes an all-open generating level frame.
The separate action calculation and global uniqueness are still required for
the frozen multiplier theorem. -/
lemma exists_descended_frame (hz : z ^ 2 = -1) :
    ∃ (L : S.Modules) (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)),
      Scheme.Modules.IsInvertible L ∧
      IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ (levelFrame E D β) ∧
      (Scheme.Modules.pullback (first E D)).map β.hom ≫ descentMap E k σ P z D hD (𝟙_ S.Modules) =
        canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map β.hom := by
  obtain ⟨L, hL, β, hβ⟩ := exists_descended_line E k σ P z D hD hz
  exact ⟨L, β, hL, levelFrame_isFrame E D β, hβ⟩

/-- Full faithfulness for compatible line isomorphisms on this particular
marking cover. Compatibility is on the complete pair scheme. -/
lemma descend_compatible_iso (hz : z ^ 2 = -1) (L K : S.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hK : Scheme.Modules.IsInvertible K)
    (η : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj K)
    (hη : (Scheme.Modules.pullback (first E D)).map η.hom ≫ canonicalComparison E D K =
      canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map η.hom) :
    ∃! e : L ≅ K, (Scheme.Modules.pullback D.projection).mapIso e = η := by
  obtain ⟨hf, het, hs, _⟩ := EvenCoverTorsor.geometry E k σ P z hz D hD
  letI := hf
  letI := het
  letI := hs
  exact P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one.KcDescAlong.existsUnique_of_comm
    D.projection (first E D) (second E D) (IsPullback.of_hasPullback _ _) hL hK η hη


open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- Restrict the complete descent equation to the graph with projections q,id.
The reversed transition in the descent datum then has the frame's exponent. -/
lemma descended_graph {L : S.Modules}
    (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules))
    (hβ : (Scheme.Modules.pullback (first E D)).map β.hom ≫
      descentMap E k σ P z D hD (𝟙_ S.Modules) =
        canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map β.hom)
    (A : EvenGroup) (q : D.space ≅ D.space) (hq : Acts E D A.val q) :
    β.hom = pullHom (F := Transport.FF) (M₁ := L) (M₂ := 𝟙_ S.Modules)
      (f₁ := D.projection) (f₂ := D.projection) β.hom q.hom
        D.projection D.projection hq.1 hq.1 ≫
      scalarEnd (D.projection.appTop (z ^ (3 * (characterExponent A.val).val)))
        ((Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)) := by
  let g : D.space ⟶ overlap E D :=
    pullback.lift q.hom (𝟙 _) (by simpa only [Category.id_comp] using hq.1)
  have hg₁ : g ≫ first E D = q.hom := pullback.lift_fst _ _ _
  have hg₂ : g ≫ second E D = 𝟙 D.space := pullback.lift_snd _ _ _
  have hgp : g ≫ (first E D ≫ D.projection) = D.projection := by
    rw [← Category.assoc, hg₁, hq.1]
  have H := Transport.datum_pull D.projection (first E D) (second E D)
    pullback.condition β (descentScalar E k σ P z D hD) hβ g D.projection hgp
  have hs : g.appTop (descentScalar E k σ P z D hD) =
      D.projection.appTop (z ^ (3 * (characterExponent A.val).val)) := by
    unfold descentScalar
    rw [transitionScalar_precomp]
    simp only [hg₂, hg₁]
    simpa only [Category.id_comp] using
      transitionScalar_action E k σ P z D hD (𝟙 D.space) A q hq
  simpa only [hg₁, hg₂, pullHom_id, hs] using H

omit k σ P z hD in
lemma levelFrame_beta {L : S.Modules}
    (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules)) :
    β.hom.app ⊤ (levelFrame E D β) =
      (Scheme.Modules.pullbackUnitIso D.projection).inv.app ⊤ (1 : Γ(D.space, ⊤)) := by
  change (((Scheme.Modules.pullbackUnitIso D.projection).inv ≫ β.inv) ≫ β.hom).app ⊤
    (1 : Γ(D.space, ⊤)) = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
lemma levelFrame_action {L : S.Modules}
    (β : (Scheme.Modules.pullback D.projection).obj L ≅
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules))
    (hβ : (Scheme.Modules.pullback (first E D)).map β.hom ≫
      descentMap E k σ P z D hD (𝟙_ S.Modules) =
        canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map β.hom)
    (A : EvenGroup) (q : D.space ≅ D.space) (hq : Acts E D A.val q) :
    overPull E D L q.hom hq.1 (levelFrame E D β) =
      D.projection.appTop (z ^ (3 * (characterExponent A.val).val)) • levelFrame E D β := by
  let φ : (Scheme.Modules.pullback D.projection).obj L ⟶
      (Scheme.Modules.pullback D.projection).obj (𝟙_ S.Modules) :=
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := 𝟙_ S.Modules)
      (f₁ := D.projection) (f₂ := D.projection) β.hom q.hom
        D.projection D.projection hq.1 hq.1
  have hn := Transport.pullHom_overPull D.projection q.hom hq.1 β.hom (levelFrame E D β)
  rw [levelFrame_beta, Transport.over_unit] at hn
  exact scalar_frame_transfer β φ
    (D.projection.appTop (z ^ (3 * (characterExponent A.val).val)))
    (levelFrame E D β) (overPull E D L q.hom hq.1 (levelFrame E D β))
    ((Scheme.Modules.pullbackUnitIso D.projection).inv.app ⊤ (1 : Γ(D.space, ⊤)))
    (descended_graph E k σ P z D hD β hβ A q hq) hn (levelFrame_beta E D β)

/-- Existence with every conjunct of the frozen multiplier predicate. -/
lemma exists_multiplier (hz : z ^ 2 = -1) :
    ∃ (L : S.Modules) (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤)),
      Multiplier E D z L m := by
  obtain ⟨L, hL, β, hβ⟩ := exists_descended_line E k σ P z D hD hz
  exact ⟨L, levelFrame E D β, hL, levelFrame_isFrame E D β,
    levelFrame_action E k σ P z D hD β hβ⟩


omit k σ P z hD in
lemma overPull_frame {L : S.Modules} (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (hm : IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ m)
    (q : D.space ⟶ D.space) (hq : q ≫ D.projection = D.projection) :
    IsFrame ((Scheme.Modules.pullback D.projection).obj L) ⊤ (overPull E D L q hq m) := by
  exact ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
    ((Scheme.Modules.pullbackComp q D.projection).app L ≪≫
      (Scheme.Modules.pullbackCongr hq).app L) _
    (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame q _ m hm)

omit k σ P hD in
lemma frameIso_action {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤))
    (hm : Multiplier E D z L m) (hn : Multiplier E D z K n)
    (η : (Scheme.Modules.pullback D.projection).obj L ≅ (Scheme.Modules.pullback D.projection).obj K)
    (hη : η.hom.app ⊤ m = n)
    (A : EvenGroup) (q : D.space ≅ D.space) (hq : Acts E D A.val q) :
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom q.hom
        D.projection D.projection hq.1 hq.1 = η.hom := by
  apply hom_ext_of_frame (overPull E D L q.hom hq.1 m)
    (overPull_frame E D m hm.2.1 q.hom hq.1)
  have H := Transport.pullHom_overPull D.projection q.hom hq.1 η.hom m
  rw [hη] at H
  calc
    _ = overPull E D K q.hom hq.1 n := H
    _ = D.projection.appTop (z ^ (3 * (characterExponent A.val).val)) • n := hn.2.2 A q hq
    _ = η.hom.app ⊤ (D.projection.appTop (z ^ (3 * (characterExponent A.val).val)) • m) := by
      rw [Scheme.Modules.Hom.app_smul, hη]
    _ = η.hom.app ⊤ (overPull E D L q.hom hq.1 m) :=
      congrArg (η.hom.app ⊤) (hm.2.2 A q hq).symm


lemma frameIso_pair_eq {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤))
    (hm : Multiplier E D z L m) (hn : Multiplier E D z K n)
    (η : (Scheme.Modules.pullback D.projection).obj L ≅ (Scheme.Modules.pullback D.projection).obj K)
    (hη : η.hom.app ⊤ m = n) :
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom (first E D)
        (first E D ≫ D.projection) (first E D ≫ D.projection) rfl rfl =
    pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
      (f₁ := D.projection) (f₂ := D.projection) η.hom (second E D)
        (first E D ≫ D.projection) (first E D ≫ D.projection)
          pullback.condition.symm pullback.condition.symm := by
  let p := first E D ≫ D.projection
  let v := ((Scheme.Modules.pullbackComp (first E D) D.projection).app L).hom.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (first E D) _ m)
  have hv : IsFrame ((Scheme.Modules.pullback p).obj L) ⊤ v :=
    ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180.frame_iso
      ((Scheme.Modules.pullbackComp (first E D) D.projection).app L) _
      (ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullback_frame (first E D) _ m hm.2.1)
  apply hom_ext_local_pullback v hv
  intro x
  obtain ⟨U, hx, _, he⟩ := locallyRelated_action E k σ P z D hD
    (first E D) (second E D) pullback.condition _
    (transition_spec E k σ P z D hD (first E D) (second E D) pullback.condition)
    (action E k σ P z D hD) (action_spec E k σ P z D hD) x
  let A := transition E k σ P z D hD (first E D) (second E D) pullback.condition x
  let q := action E k σ P z D hD A
  have hq : Acts E D A.val q := action_spec E k σ P z D hD A
  have he' : U.ι ≫ second E D = (U.ι ≫ first E D) ≫ q.hom := by
    simpa only [Category.assoc] using he
  refine ⟨U, hx, ?_⟩
  apply Transport.pullHom_map_eq p _ _ U.ι (U.ι ≫ p) rfl
  have H := Transport.pullHom_action_eq D.projection η.hom q.hom hq.1
    (frameIso_action E z D m n hm hn η hη A q hq)
    (U.ι ≫ first E D) (U.ι ≫ p) (Category.assoc _ _ _)
  rw [pullHom_pullHom (F := Transport.FF) η.hom (first E D) p p U.ι
    (U.ι ≫ p) (U.ι ≫ p) rfl rfl rfl rfl,
    pullHom_pullHom (F := Transport.FF) η.hom (second E D) p p U.ι
      (U.ι ≫ p) (U.ι ≫ p) pullback.condition.symm pullback.condition.symm rfl rfl]
  apply H.symm.trans
  exact P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2.Gen.pullHom_congr
    Transport.FF η.hom ((U.ι ≫ first E D) ≫ q.hom) (U.ι ≫ second E D) he'.symm
      (U.ι ≫ p) (U.ι ≫ p) _ _ _ _

omit k σ P z hD in
/-- Equality in the common pullback presentation gives the original, complete
Cech compatibility equation. -/
lemma compatible_of_pair_eq {L K : S.Modules}
    (η : (Scheme.Modules.pullback D.projection).obj L ≅ (Scheme.Modules.pullback D.projection).obj K)
    (hη :
      pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
        (f₁ := D.projection) (f₂ := D.projection) η.hom (first E D)
          (first E D ≫ D.projection) (first E D ≫ D.projection) rfl rfl =
      pullHom (F := Transport.FF) (M₁ := L) (M₂ := K)
        (f₁ := D.projection) (f₂ := D.projection) η.hom (second E D)
          (first E D ≫ D.projection) (first E D ≫ D.projection)
            pullback.condition.symm pullback.condition.symm) :
    (Scheme.Modules.pullback (first E D)).map η.hom ≫ canonicalComparison E D K =
      canonicalComparison E D L ≫ (Scheme.Modules.pullback (second E D)).map η.hom := by
  have H := congrArg (fun f =>
    (Scheme.Modules.pullbackComp (first E D) D.projection).hom.app L ≫ f ≫
      (Scheme.Modules.pullbackCongr (show first E D ≫ D.projection =
        second E D ≫ D.projection from pullback.condition)).hom.app K ≫
      (Scheme.Modules.pullbackComp (second E D) D.projection).inv.app K) hη
  simpa only [P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2.pullHom_eq₂, P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2.pullbackCongr_hom_app,
    P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.C7G2.pullbackCongr_inv_app', eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    eqToHom_trans, eqToHom_trans_assoc, Functor.comp_obj, canonicalComparison] using H

lemma multiplier_unique (hz : z ^ 2 = -1) {L K : S.Modules}
    (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤))
    (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤))
    (hm : Multiplier E D z L m) (hn : Multiplier E D z K n) :
    ∃! e : L ≅ K, PreservesFrame E D m n e := by
  obtain ⟨η, hη, _⟩ := existsUnique_frame_iso _ _ m n hm.2.1 hn.2.1
  have hc := compatible_of_pair_eq E D η
    (frameIso_pair_eq E k σ P z D hD m n hm hn η hη)
  obtain ⟨e, he, hu⟩ := descend_compatible_iso E k σ P z D hD hz L K hm.1 hn.1 η hc
  refine ⟨e, ?_, ?_⟩
  · have He := congrArg (fun j => j.hom.app ⊤ m) he
    exact He.trans hη
  · intro e' he'
    apply hu e'
    apply Iso.ext
    exact hom_ext_of_frame m hm.2.1 _ _ (he'.trans hη.symm)


#print axioms frameIso_pair_eq
#print axioms compatible_of_pair_eq
#print axioms frameIso_action
#print axioms hom_ext_local_pullback
#print axioms exists_multiplier
#print axioms existsUnique_frame_iso
#print axioms multiplier_unique

#print axioms levelFrame_action
#print axioms Transport.pullHom_overPull
#print axioms Transport.over_unit
#print axioms Transport.datum_pull
#print axioms descend_compatible_iso
#print axioms exists_descended_frame
#print axioms hom_ext_of_frame
#print axioms exists_descended_line
#print axioms transitionScalar_cocycle
#print axioms transitionScalar_diagonal
#print axioms transitionScalar_action
#print axioms transitionScalar_product
#print axioms transitionScalar_precomp
#print axioms inverseScalar_isUnit

#print axioms transition_product
#print axioms transition_precomp
#print axioms parameter_ext
#print axioms locallyRelated_action
#print axioms inverse_character_mul
end ArithmeticThetaMultiplierKeyR0217.InverseCharacterMultiplier

namespace ArithmeticThetaMultiplierKeyR0217
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite TopologicalSpace
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216

theorem inverse_character_multiplier
    (k : Type u) [Field k] [CharZero k]
    (S : Scheme.{u}) (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k)
    (E : ArithmeticThetaLocalWeierstrassR0203.Family S)
    (P : ArithmeticThetaEvenMarkingTorsorR0216.EvenPoint E)
    (z : Γ(S, ⊤)) (hz : z ^ 2 = -1)
    (D : ArithmeticThetaEvenMarkingTorsorR0216.Cover E)
    (hD : ArithmeticThetaEvenMarkingTorsorR0216.RepresentsEven E P z D) :
    ∃ (L : S.Modules) (m : Γ((Scheme.Modules.pullback D.projection).obj L, ⊤)),
      Multiplier E D z L m ∧
      (∀ (K : S.Modules) (n : Γ((Scheme.Modules.pullback D.projection).obj K, ⊤)),
        Multiplier E D z K n →
          ∃! e : L ≅ K, PreservesFrame E D m n e) := by
  obtain ⟨L, m, hm⟩ :=
    InverseCharacterMultiplier.exists_multiplier E k σ P z D hD hz
  refine ⟨L, m, hm, ?_⟩
  intro K n hn
  exact InverseCharacterMultiplier.multiplier_unique E k σ P z D hD hz m n hm hn
end ArithmeticThetaMultiplierKeyR0217

#print axioms ArithmeticThetaMultiplierKeyR0217.inverse_character_multiplier
