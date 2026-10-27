import CoverComparisonDefinitions

/-!
# Square-compatible isomorphisms

Functorial tensor laws for the concrete square-isomorphism functor.
-/
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaGlobalization
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace ArithmeticThetaCoverComparison

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

lemma sheafTensorMap_id (X : Scheme.{u}) (H J : X.Modules) :
    sheafTensorMap X (𝟙 H) (𝟙 J) = 𝟙 (sheafTensor X H J) := by
  unfold sheafTensorMap
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 H.val) ⊗ₘ (𝟙 J.val)) = _
  rw [id_tensorHom_id, CategoryTheory.Functor.map_id]
  rfl

lemma sheafTensorMap_comp (X : Scheme.{u}) {H H' H'' J J' J'' : X.Modules}
    (a : H ⟶ H') (b : H' ⟶ H'') (c : J ⟶ J') (d : J' ⟶ J'') :
    sheafTensorMap X (a ≫ b) (c ≫ d) =
      sheafTensorMap X a c ≫ sheafTensorMap X b d := by
  unfold sheafTensorMap
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((a.val ≫ b.val) ⊗ₘ (c.val ≫ d.val)) = _
  rw [← tensorHom_comp_tensorHom, Functor.map_comp]

@[simp] lemma tensorPowerMap_id (X : Scheme.{u}) (H : X.Modules) (n : ℕ) :
    tensorPowerMap (𝟙 H) n = 𝟙 (tensorPower X H n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorPowerMap, ih, sheafTensorMap_id, tensorPower]

lemma tensorPowerMap_comp {X : Scheme.{u}} {H J K : X.Modules}
    (a : H ⟶ J) (b : J ⟶ K) (n : ℕ) :
    tensorPowerMap (a ≫ b) n = tensorPowerMap a n ≫ tensorPowerMap b n := by
  induction n with
  | zero => simp [tensorPowerMap]
  | succ n ih =>
    simp only [tensorPowerMap, ih, sheafTensorMap_comp]

/-- The actual tensor power functor transports an isomorphism. -/
def tensorPowerIso {X : Scheme.{u}} {H J : X.Modules} (e : H ≅ J) (n : ℕ) :
    tensorPower X H n ≅ tensorPower X J n where
  hom := tensorPowerMap e.hom n
  inv := tensorPowerMap e.inv n
  hom_inv_id := by rw [← tensorPowerMap_comp, e.hom_inv_id, tensorPowerMap_id]
  inv_hom_id := by rw [← tensorPowerMap_comp, e.inv_hom_id, tensorPowerMap_id]

/-- Tensor powers of local sections commute with the actual induced morphism. -/
lemma tensorPowerMap_section {X : Scheme.{u}} {H J : X.Modules}
    (a : H ⟶ J) (n : ℕ) (U : X.Opens) (s : Γ(H, U)) :
    (tensorPowerMap a n).app U (tensorPowerSection X H n U s) =
      tensorPowerSection X J n U (a.app U s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorPowerMap, tensorPowerSection]
    erw [sheafTensorMap_section]
    rw [ih]

open ArithmeticThetaLineRoot

/-- The scalar of a sheaf morphism in two actual local frames. -/
def frameHomCoordinate {X : Scheme.{u}} {H J : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (a : H ⟶ J)
    (V : X.Opens) (hVU : V ≤ U) : Γ(X, V) :=
  (d.equiv V hVU).symm (a.app V (e.equiv V hVU 1))

lemma frameHomCoordinate_apply {X : Scheme.{u}} {H J : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (a : H ⟶ J)
    (V : X.Opens) (hVU : V ≤ U) (r : Γ(X, V)) :
    a.app V (e.equiv V hVU r) =
      d.equiv V hVU (r * frameHomCoordinate e d a V hVU) := by
  have he : e.equiv V hVU r = r • e.equiv V hVU 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  change a.val.app (op V) (e.equiv V hVU r) = _
  rw [he, map_smul, ← smul_eq_mul, map_smul]
  simp only [frameHomCoordinate, LinearEquiv.apply_symm_apply]
  rfl

lemma frameHomCoordinate_comp {X : Scheme.{u}} {H J K : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (c : LocalFrame X K U)
    (a : H ⟶ J) (b : J ⟶ K) (V : X.Opens) (hVU : V ≤ U) :
    frameHomCoordinate e c (a ≫ b) V hVU =
      frameHomCoordinate e d a V hVU * frameHomCoordinate d c b V hVU := by
  unfold frameHomCoordinate
  change (c.equiv V hVU).symm (b.app V (a.app V (e.equiv V hVU 1))) = _
  rw [frameHomCoordinate_apply e d a, one_mul, frameHomCoordinate_apply d c b]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp] lemma frameHomCoordinate_id {X : Scheme.{u}} {H : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (V : X.Opens) (hVU : V ≤ U) :
    frameHomCoordinate e e (𝟙 H) V hVU = 1 := by
  exact (e.equiv V hVU).symm_apply_apply 1

/-- Frame coefficients restrict through the actual structure-sheaf restriction. -/
lemma frameHomCoordinate_restrict {X : Scheme.{u}} {H J : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (a : H ⟶ J)
    (V Z : X.Opens) (hZV : Z ≤ V) (hVU : V ≤ U) :
    frameHomCoordinate e d a Z (hZV.trans hVU) =
      X.presheaf.map (homOfLE hZV).op (frameHomCoordinate e d a V hVU) := by
  unfold frameHomCoordinate
  rw [← ArithmeticThetaGlobalization.frame_coordinate_restrict d V Z hZV hVU]
  congr 1
  change a.val.app (op Z) _ = J.val.map (homOfLE hZV).op (a.val.app (op V) _)
  rw [← PresheafOfModules.naturality_apply]
  congr 1
  change e.equiv Z (hZV.trans hVU) 1 =
    H.presheaf.map (homOfLE hZV).op (e.equiv V hVU 1)
  simpa using (e.naturality V Z hZV hVU 1).symm

/-- An actual isomorphism has an invertible coefficient in any two local frames. -/
lemma frameHomCoordinate_isUnit {X : Scheme.{u}} {H J : X.Modules} {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (a : H ≅ J)
    (V : X.Opens) (hVU : V ≤ U) :
    IsUnit (frameHomCoordinate e d a.hom V hVU) := by
  apply IsUnit.of_mul_eq_one (frameHomCoordinate d e a.inv V hVU)
  rw [← frameHomCoordinate_comp, a.hom_inv_id, frameHomCoordinate_id]

/-- The induced tensor-power morphism raises the frame scalar to that power. -/
lemma frameHomCoordinate_tensorPowerMap {X : Scheme.{u}} {H J : X.Modules}
    {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (a : H ⟶ J) (n : ℕ) (V : X.Opens) (hVU : V ≤ U) :
    frameHomCoordinate (tensorPowerFrame X H U e n) (tensorPowerFrame X J U d n)
      (tensorPowerMap a n) V hVU = (frameHomCoordinate e d a V hVU) ^ n := by
  unfold frameHomCoordinate
  have hf : (tensorPowerFrame X H U e n).equiv V hVU 1 =
      tensorPowerSection X H n V (e.equiv V hVU 1) := by
    simpa only [one_pow] using (tensorPowerSection_frame X H U e n V hVU 1).symm
  rw [hf, tensorPowerMap_section, frameHomCoordinate_apply e d a, one_mul,
    tensorPowerSection_frame]
  simp only [LinearEquiv.symm_apply_apply]

/-- In genuine local frames the compatibility equation is the quadratic root equation. -/
lemma square_compatibility_coordinate {X : Scheme.{u}} {H J W : X.Modules}
    {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (c : LocalFrame X W U) (a : tensorPower X H 2 ≅ W)
    (b : tensorPower X J 2 ≅ W) (w : H ≅ J)
    (hw : tensorPowerMap w.hom 2 ≫ b.hom = a.hom)
    (V : X.Opens) (hVU : V ≤ U) :
    frameHomCoordinate e d w.hom V hVU ^ 2 *
      frameHomCoordinate (tensorPowerFrame X J U d 2) c b.hom V hVU =
      frameHomCoordinate (tensorPowerFrame X H U e 2) c a.hom V hVU := by
  have h := congrArg (fun k =>
    frameHomCoordinate (tensorPowerFrame X H U e 2) c k V hVU) hw
  rw [frameHomCoordinate_comp, frameHomCoordinate_tensorPowerMap] at h
  exact h


namespace HomLine
variable (X : Scheme.{u}) (H J : X.Modules)

/-- Raw families of linear maps on subopens. -/
abbrev Entry (U : X.Opens) (V : {V : X.Opens // V ≤ U}) :=
  Γ(H, V.val) →ₗ[Γ(X, V.val)] Γ(J, V.val)

instance (U : X.Opens) (V : {V : X.Opens // V ≤ U}) :
    AddCommGroup (Entry X H J U V) := inferInstanceAs (AddCommGroup (_ →ₗ[_] _))

instance (priority := 50) (U : X.Opens) (V : {V : X.Opens // V ≤ U}) :
    Module Γ(X, U) (Entry X H J U V) :=
  Module.compHom (Γ(H, V.val) →ₗ[Γ(X, V.val)] Γ(J, V.val))
    (X.presheaf.map (homOfLE V.property).op).hom

/-- Naturality equations cut out a module of actual local sheaf morphisms. -/
def compatibleMaps (U : X.Opens) :
    Submodule Γ(X, U) (∀ V : {V : X.Opens // V ≤ U}, Entry X H J U V) where
  carrier := {a | ∀ (V Z : {V : X.Opens // V ≤ U}) (h : Z.val ≤ V.val)
    (s : Γ(H, V.val)),
    a Z (H.presheaf.map (homOfLE h).op s) =
      J.presheaf.map (homOfLE h).op (a V s)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb V Z h s
    change a Z (H.presheaf.map _ s) + b Z (H.presheaf.map _ s) = _
    simpa only [Pi.add_apply, LinearMap.add_apply, map_add] using congrArg₂ (· + ·) (ha V Z h s) (hb V Z h s)
  smul_mem' := by
    intro r a ha V Z h s
    change X.presheaf.map (homOfLE Z.property).op r • a Z (H.presheaf.map _ s) =
      J.val.map (homOfLE h).op
        (X.presheaf.map (homOfLE V.property).op r • a V s)
    rw [ha, J.val.map_smul]
    congr 1
    change X.presheaf.map (homOfLE Z.property).op r =
      X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE V.property).op r)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- Restrict a compatible family to a smaller open. -/
def restrict (U V : X.Opens) (hVU : V ≤ U) :
    compatibleMaps X H J U →ₛₗ[(X.presheaf.map (homOfLE hVU).op).hom]
      compatibleMaps X H J V where
  toFun a := ⟨fun Z => a.val ⟨Z.val, Z.property.trans hVU⟩, by
    intro Z W h s
    exact a.property ⟨Z.val, Z.property.trans hVU⟩ ⟨W.val, W.property.trans hVU⟩ h s⟩
  map_add' a b := rfl
  map_smul' r a := by
    apply Subtype.ext
    funext Z
    apply LinearMap.ext
    intro s
    change X.presheaf.map (homOfLE (Z.property.trans hVU)).op r • a.val ⟨Z.val, Z.property.trans hVU⟩ s =
      X.presheaf.map (homOfLE Z.property).op
        (X.presheaf.map (homOfLE hVU).op r) • a.val ⟨Z.val, Z.property.trans hVU⟩ s
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- The module presheaf of local morphisms between the supplied sheaves. -/
def homPresheaf : X.PresheafOfModules where
  obj U := ModuleCat.of Γ(X, U.unop) (compatibleMaps X H J U.unop)
  map {U V} h := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map h).hom).obj
      (ModuleCat.of Γ(X, V.unop) (compatibleMaps X H J V.unop)))
    { toFun := restrict X H J U.unop V.unop h.unop.le
      map_add' := (restrict X H J U.unop V.unop h.unop.le).map_add
      map_smul' r a := (restrict X H J U.unop V.unop h.unop.le).map_smulₛₗ r a }
  map_id U := by ext a; rfl
  map_comp f g := by ext a; rfl

open ArithmeticThetaLineRoot ArithmeticThetaGlobalization

/-- A pair of local bases identifies each family with a single scalar. -/
def fromCoordinate {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (r : Γ(X, V)) : compatibleMaps X H J V :=
  ⟨fun Z => X.presheaf.map (homOfLE Z.property).op r •
    ((d.equiv Z.val (Z.property.trans hVU)).toLinearMap.comp
      (e.equiv Z.val (Z.property.trans hVU)).symm.toLinearMap), by
    intro Z W h s
    change X.presheaf.map (homOfLE W.property).op r •
      d.equiv W.val _ ((e.equiv W.val _).symm (H.presheaf.map (homOfLE h).op s)) =
      J.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE Z.property).op r • d.equiv Z.val _ ((e.equiv Z.val _).symm s))
    rw [J.map_smul, frame_coordinate_restrict e Z.val W.val h (Z.property.trans hVU),
      d.naturality]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl⟩

def toCoordinate {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (a : compatibleMaps X H J V) : Γ(X, V) :=
  (d.equiv V hVU).symm (a.val ⟨V, le_rfl⟩ (e.equiv V hVU 1))

lemma fromCoordinate_apply {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (r : Γ(X, V))
    (Z : {Z : X.Opens // Z ≤ V}) (s : Γ(H, Z.val)) :
    (fromCoordinate X H J e d V hVU r).val Z s =
      X.presheaf.map (homOfLE Z.property).op r •
        d.equiv Z.val (Z.property.trans hVU) ((e.equiv Z.val (Z.property.trans hVU)).symm s) := rfl

lemma toCoordinate_fromCoordinate {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (r : Γ(X, V)) :
    toCoordinate X H J e d V hVU (fromCoordinate X H J e d V hVU r) = r := by
  unfold toCoordinate
  rw [fromCoordinate_apply]
  simp only [LinearEquiv.symm_apply_apply, homOfLE_refl, op_id, Functor.map_id,
    ConcreteCategory.id_apply, map_smul, smul_eq_mul, mul_one]
  simp

lemma fromCoordinate_toCoordinate {U : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (a : compatibleMaps X H J V) :
    fromCoordinate X H J e d V hVU (toCoordinate X H J e d V hVU a) = a := by
  apply Subtype.ext
  funext Z
  apply LinearMap.ext
  intro s
  rw [fromCoordinate_apply]
  unfold toCoordinate
  rw [← frame_coordinate_restrict d V Z.val Z.property hVU,
    ← a.property ⟨V, le_rfl⟩ Z Z.property]
  have he : H.presheaf.map (homOfLE Z.property).op (e.equiv V hVU 1) =
      e.equiv Z.val (Z.property.trans hVU) 1 := by
    simpa using e.naturality V Z.val Z.property hVU 1
  rw [he]
  let r := (e.equiv Z.val (Z.property.trans hVU)).symm s
  have hs : s = r • e.equiv Z.val (Z.property.trans hVU) 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (e.equiv Z.val _).apply_symm_apply s |>.symm
  change (d.equiv Z.val _).symm (a.val Z (e.equiv Z.val _ 1)) •
    d.equiv Z.val _ r = a.val Z s
  rw [hs, map_smul, ← map_smul, smul_eq_mul, mul_comm, ← smul_eq_mul,
    map_smul, LinearEquiv.apply_symm_apply]



/-- The actual sheaf obtained by sheafifying compatible local linear maps. -/
def homLine (X : Scheme.{u}) (H J : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (HomLine.homPresheaf X H J)

variable {X : Scheme.{u}} {H J : X.Modules} {U : X.Opens}

open ArithmeticThetaSheafTensor

def fromCoordinateLinear (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) :
    Γ(X,V) →ₗ[Γ(X,V)] compatibleMaps X H J V where
  toFun r := fromCoordinate X H J e d V hVU r
  map_add' r s := by
    apply Subtype.ext; funext Z; apply LinearMap.ext; intro t
    dsimp [fromCoordinate]
    rw [map_add, add_smul]
  map_smul' r s := by
    apply Subtype.ext; funext Z; apply LinearMap.ext; intro t
    dsimp [fromCoordinate]
    rw [map_mul]
    simp only [smul_eq_mul, mul_smul]
    rfl

def coordinateIso (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) :
    Γ(X,V) ≃ₗ[Γ(X,V)] compatibleMaps X H J V :=
  LinearEquiv.ofBijective (fromCoordinateLinear e d V hVU)
    ⟨Function.LeftInverse.injective (toCoordinate_fromCoordinate X H J e d V hVU),
      Function.RightInverse.surjective (fromCoordinate_toCoordinate X H J e d V hVU)⟩

lemma fromCoordinate_restrict (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V Z : X.Opens) (hZV : Z ≤ V) (hVU : V ≤ U) (r : Γ(X,V)) :
    restrict X H J V Z hZV (fromCoordinate X H J e d V hVU r) =
      fromCoordinate X H J e d Z (hZV.trans hVU)
        (X.presheaf.map (homOfLE hZV).op r) := by
  apply Subtype.ext
  funext Q
  apply LinearMap.ext
  intro s
  dsimp [restrict, fromCoordinate]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def homFramePreIso (e : LocalFrame X H U) (d : LocalFrame X J U) :
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val ≅
      (presheafOver X U).obj (homPresheaf X H J) :=
  PresheafOfModules.isoMk
    (fun V => (coordinateIso e d V.unop.left V.unop.hom.le).toModuleIso)
    (fun {V Z} g => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      exact (fromCoordinate_restrict e d V.unop.left Z.unop.left
        g.unop.left.le V.unop.hom.le r).symm)

def homUnitMap : homPresheaf X H J ⟶ (homLine X H J).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

def localHomTrivializationHom (e : LocalFrame X H U) (d : LocalFrame X J U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.over (homLine X H J) U :=
  ⟨(homFramePreIso e d).hom ≫ (presheafOver X U).map homUnitMap⟩

lemma localHomTrivializationHom_isIso (e : LocalFrame X H U) (d : LocalFrame X J U) :
    IsIso (localHomTrivializationHom e d) := by
  let G := Opens.grothendieckTopology X
  let η := CategoryTheory.toSheafify G (homPresheaf X H J).presheaf
  let e' := (PresheafOfModules.toPresheaf _).mapIso (homFramePreIso e d)
  let ηU := Functor.whiskerLeft (Over.forget U).op η
  have hinj : Presheaf.IsLocallyInjective (G.over U) ηU :=
    Presheaf.isLocallyInjective_whisker (G.over U) G (Over.forget U) η
  have hsurj : Presheaf.IsLocallySurjective (G.over U) ηU :=
    Presheaf.isLocallySurjective_whisker (G.over U) G (Over.forget U) η
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (X.ringCatSheaf.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective (G.over U) (e'.hom ≫ ηU)
    infer_instance
  · change Presheaf.IsLocallySurjective (G.over U) (e'.hom ≫ ηU)
    infer_instance

def localHomTrivialization (e : LocalFrame X H U) (d : LocalFrame X J U) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      SheafOfModules.over (homLine X H J) U :=
  have := localHomTrivializationHom_isIso e d
  asIso (localHomTrivializationHom e d)

def homFrame (e : LocalFrame X H U) (d : LocalFrame X J U) :
    LocalFrame X (homLine X H J) U :=
  localFrameOfIso X (homLine X H J) U (localHomTrivialization e d)

lemma homLine_isLineBundle
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J) :
    ArithmeticThetaNormalizedSections.IsLineBundle X (homLine X H J) := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hH x
  obtain ⟨V, hxV, ⟨d⟩⟩ := hJ x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨localHomTrivialization
    (restrictFrame (localFrameOfIso X H U e) (U ⊓ V) inf_le_left)
    (restrictFrame (localFrameOfIso X J V d) (U ⊓ V) inf_le_right)⟩⟩


variable {X : Scheme.{u}} {H J : X.Modules} {U U' : X.Opens}

lemma homFrame_apply (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (r : Γ(X,V)) :
    (homFrame e d).equiv V hVU r =
      homUnitMap.app (op V) (fromCoordinate X H J e d V hVU r) := rfl

lemma coordinateIso_symm_apply (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (a : compatibleMaps X H J V) :
    (coordinateIso e d V hVU).symm a = toCoordinate X H J e d V hVU a := by
  apply (coordinateIso e d V hVU).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (fromCoordinate_toCoordinate X H J e d V hVU a).symm

lemma homFrame_coordinate (e : LocalFrame X H U) (d : LocalFrame X J U)
    (V : X.Opens) (hVU : V ≤ U) (a : compatibleMaps X H J V) :
    ((homFrame e d).equiv V hVU).symm (homUnitMap.app (op V) a) =
      toCoordinate X H J e d V hVU a := by
  apply ((homFrame e d).equiv V hVU).injective
  rw [LinearEquiv.apply_symm_apply, homFrame_apply, fromCoordinate_toCoordinate]

lemma homFrame_transition (e : LocalFrame X H U) (d : LocalFrame X J U)
    (e' : LocalFrame X H U') (d' : LocalFrame X J U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition ((homFrame e d).equiv V hVU) ((homFrame e' d').equiv V hVU') *
      transition (e.equiv V hVU) (e'.equiv V hVU') =
      transition (d.equiv V hVU) (d'.equiv V hVU') := by
  unfold transition
  rw [homFrame_apply, homFrame_coordinate]
  unfold toCoordinate
  rw [fromCoordinate_apply]
  simp only [homOfLE_refl, op_id, Functor.map_id, map_one, one_smul]
  have he : (e'.equiv V hVU').symm (e.equiv V hVU 1) *
      (e.equiv V hVU).symm (e'.equiv V hVU' 1) = 1 := by
    exact (transitionUnit (e'.equiv V hVU') (e.equiv V hVU)).val_inv
  let q := (e'.equiv V hVU').symm (e.equiv V hVU 1)
  have hd : (d.equiv V hVU).symm (d'.equiv V hVU' q) =
      q * (d.equiv V hVU).symm (d'.equiv V hVU' 1) := by
    rw [show d'.equiv V hVU' q = q • d'.equiv V hVU' 1 by
      rw [← map_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  change (d.equiv V hVU).symm (d'.equiv V hVU' q) * _ = _
  rw [hd, mul_right_comm, he, one_mul]

variable {X : Scheme.{u}} {H J : X.Modules}

abbrev res (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(M,U)) : Γ(M,V) :=
  M.presheaf.map (homOfLE h).op s
@[simp] lemma res_res (M : X.Modules) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V)
    (s : Γ(M,U)) : res M k (res M h s) = res M (k.trans h) s := by
  dsimp [res]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma compatibleMaps_naturality {U V W : X.Opens}
    (a : compatibleMaps X H J U) (hVU : V ≤ U) (hWV : W ≤ V)
    (s : Γ(H,V)) :
    res J hWV (a.val ⟨V,hVU⟩ s) =
      a.val ⟨W,hWV.trans hVU⟩ (res H hWV s) :=
  (a.property ⟨V,hVU⟩ ⟨W,hWV.trans hVU⟩ hWV s).symm

lemma compatibleMaps_glue {ι : Type v} (U : ι → X.Opens) (T : X.Opens)
    (hUT : ∀ i, U i ≤ T) (hc : T ≤ iSup U) (a : ∀ i, compatibleMaps X H J (U i))
    (ha : ∀ i j, restrict X H J (U i) (U i ⊓ U j) inf_le_left (a i) =
      restrict X H J (U j) (U i ⊓ U j) inf_le_right (a j)) :
    ∃! b : compatibleMaps X H J T, ∀ i, restrict X H J T (U i) (hUT i) b = a i := by
  classical
  have cover (V : X.Opens) (hVT : V ≤ T) : V ≤ iSup (fun i => V ⊓ U i) := by
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hc (hVT hx))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  have agree (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
      (a i).val ⟨V, hi⟩ = (a j).val ⟨V, hj⟩ := by
    exact congrArg (fun b : compatibleMaps X H J (U i ⊓ U j) =>
      b.val ⟨V, le_inf hi hj⟩) (ha i j)
  have hex (V : X.Opens) (hVT : V ≤ T) (s : Γ(H,V)) : ∃! t : Γ(J,V),
      ∀ i, res J (inf_le_left : V ⊓ U i ≤ V) t =
        (a i).val ⟨V ⊓ U i, inf_le_right⟩ (res H inf_le_left s) := by
    apply TopCat.Sheaf.existsUnique_gluing' ⟨J.presheaf, J.isSheaf⟩
      (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (cover V hVT)
    intro i j
    change res J inf_le_left ((a i).val ⟨V ⊓ U i, inf_le_right⟩ (res H inf_le_left s)) =
      res J inf_le_right ((a j).val ⟨V ⊓ U j, inf_le_right⟩ (res H inf_le_left s))
    rw [compatibleMaps_naturality (a i) inf_le_right inf_le_left,
      compatibleMaps_naturality (a j) inf_le_right inf_le_right]
    change (a i).val ⟨(V ⊓ U i) ⊓ (V ⊓ U j), inf_le_left.trans inf_le_right⟩
      (res H inf_le_left (res H inf_le_left s)) =
      (a j).val ⟨(V ⊓ U i) ⊓ (V ⊓ U j), inf_le_right.trans inf_le_right⟩
      (res H inf_le_right (res H inf_le_left s))
    rw [res_res, res_res, agree i j _ (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right)]
  choose q hq hqu using hex
  have hq' (V W : X.Opens) (hVT : V ≤ T) (i : ι)
      (hWV : W ≤ V) (hWU : W ≤ U i) (s : Γ(H,V)) :
      res J hWV (q V hVT s) = (a i).val ⟨W, hWU⟩ (res H hWV s) := by
    have h := congrArg (res J (le_inf hWV hWU)) (hq V hVT s i)
    rw [res_res, compatibleMaps_naturality (a i) inf_le_right (le_inf hWV hWU)] at h
    exact h.trans (by congr 1; exact res_res H _ _ s)
  have extJ (V : X.Opens) (hVT : V ≤ T) (s t : Γ(J,V))
      (h : ∀ i, res J (inf_le_left : V ⊓ U i ≤ V) s = res J inf_le_left t) : s = t :=
    TopCat.Sheaf.eq_of_locally_eq' ⟨J.presheaf, J.isSheaf⟩
      (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (cover V hVT) s t h
  let ql (V : X.Opens) (hVT : V ≤ T) : Γ(H,V) →ₗ[Γ(X,V)] Γ(J,V) :=
    { toFun := q V hVT
      map_add' := by
        intro s t
        apply extJ V hVT
        intro i
        simp only [hq, res, map_add]
      map_smul' := by
        intro r s
        apply extJ V hVT
        intro i
        simp only [hq, res, Scheme.Modules.map_smul, LinearMap.map_smulₛₗ, RingHom.id_apply] }
  have hn (V W : X.Opens) (hVT : V ≤ T) (hWV : W ≤ V) (s : Γ(H,V)) :
      res J hWV (ql V hVT s) = ql W (hWV.trans hVT) (res H hWV s) := by
    apply extJ W (hWV.trans hVT)
    intro i
    change res J inf_le_left (res J hWV (q V hVT s)) =
      res J inf_le_left (q W (hWV.trans hVT) (res H hWV s))
    rw [res_res, hq' V (W ⊓ U i) hVT i (inf_le_left.trans hWV) inf_le_right, hq, res_res]
  let b : compatibleMaps X H J T :=
    ⟨fun V => ql V.val V.property, fun V W h s => (hn V.val W.val V.property h s).symm⟩
  have hb : ∀ i, restrict X H J T (U i) (hUT i) b = a i := by
    intro i
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro s
    have h := hq' V.val V.val (V.property.trans (hUT i)) i le_rfl V.property s
    change q V.val (V.property.trans (hUT i)) s = (a i).val V s
    simpa [res] using h
  refine ⟨b, hb, ?_⟩
  intro c hc
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro s
  apply extJ V.val V.property
  intro i
  change res J inf_le_left (c.val V s) = res J inf_le_left (b.val V s)
  rw [compatibleMaps_naturality c V.property inf_le_left,
    compatibleMaps_naturality b V.property inf_le_left]
  have h := congrArg (fun z : compatibleMaps X H J (U i) =>
    z.val ⟨V.val ⊓ U i, inf_le_right⟩) ((hc i).trans (hb i).symm)
  exact congrArg (fun l : Γ(H, V.val ⊓ U i) →ₗ[Γ(X, V.val ⊓ U i)] Γ(J, V.val ⊓ U i) =>
    l (res H inf_le_left s)) h

lemma homPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (homPresheaf X H J).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U a ha
  exact compatibleMaps_glue U (iSup U) (le_iSup U) le_rfl a ha

variable {X : Scheme.{u}} {H J : X.Modules}

instance homUnitMap_isIso : IsIso (homUnitMap (X := X) (H := H) (J := J)) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)]
  exact CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology X) homPresheaf_isSheaf

def rawHomSheaf : X.Modules := ⟨homPresheaf X H J, homPresheaf_isSheaf⟩

def rawHomIso : rawHomSheaf (X := X) (H := H) (J := J) ≅ homLine X H J :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (asIso homUnitMap)

def ofHom (a : H ⟶ J) (U : X.Opens) : compatibleMaps X H J U :=
  ⟨fun V => (a.val.app (op V.val)).hom, fun V Z h s =>
    PresheafOfModules.naturality_apply a.val (homOfLE h).op s⟩

def toHom (a : compatibleMaps X H J ⊤) : H ⟶ J :=
  { val :=
    { app := fun V => ModuleCat.ofHom (a.val ⟨V.unop, le_top⟩)
      naturality := by
        intro V Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact a.property ⟨V.unop,le_top⟩ ⟨Z.unop,le_top⟩ f.unop.le s } }

@[simp] lemma toHom_ofHom (a : H ⟶ J) : toHom (ofHom a ⊤) = a := rfl
@[simp] lemma ofHom_toHom (a : compatibleMaps X H J ⊤) : ofHom (toHom a) ⊤ = a := rfl

def sectionEquivHom : Γ(homLine X H J, ⊤) ≃ (H ⟶ J) :=
  ((Iso.toLinearEquiv ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
    (rawHomIso (X := X) (H := H) (J := J)))).symm.toEquiv).trans
    { toFun := toHom
      invFun := fun a => ofHom a ⊤
      left_inv := ofHom_toHom
      right_inv := toHom_ofHom }

@[simp] lemma sectionEquivHom_symm (a : H ⟶ J) :
    sectionEquivHom.symm a = homUnitMap.app (op ⊤) (ofHom a ⊤) := rfl

lemma ofHom_restrict (a : H ⟶ J) (U V : X.Opens) (h : V ≤ U) :
    restrict X H J U V h (ofHom a U) = ofHom a V := rfl

lemma sectionEquivHom_coordinate {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (s : Γ(homLine X H J, ⊤))
    (V : X.Opens) (hVU : V ≤ U) :
    ((homFrame e d).equiv V hVU).symm
      ((homLine X H J).presheaf.map (homOfLE le_top).op s) =
      frameHomCoordinate e d (sectionEquivHom s) V hVU := by
  obtain ⟨a, rfl⟩ := sectionEquivHom.symm.surjective s
  rw [Equiv.apply_symm_apply, sectionEquivHom_symm]
  erw [← PresheafOfModules.naturality_apply homUnitMap (homOfLE le_top).op]
  rw [homFrame_coordinate]
  rfl

end HomLine

lemma frameHomCoordinate_change {X : Scheme.{u}} {H J : X.Modules}
    {U U' : X.Opens} (e : LocalFrame X H U) (d : LocalFrame X J U)
    (e' : LocalFrame X H U') (d' : LocalFrame X J U') (a : H ⟶ J)
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition (d.equiv V hVU) (d'.equiv V hVU') * frameHomCoordinate e' d' a V hVU' =
      transition (e.equiv V hVU) (e'.equiv V hVU') * frameHomCoordinate e d a V hVU := by
  apply (d.equiv V hVU).injective
  rw [← transition_apply, frameHomCoordinate, LinearEquiv.apply_symm_apply]
  rw [transition_apply (e.equiv V hVU) (e'.equiv V hVU') 1,
    mul_one, frameHomCoordinate_apply]

lemma frameHomCoordinate_ext {X : Scheme.{u}} {H J : X.Modules}
    {ι : Type v} (U : ι → X.Opens) (hcover : (⊤ : X.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame X H (U i)) (d : ∀ i, LocalFrame X J (U i))
    {a b : H ⟶ J} (hab : ∀ i V (hV : V ≤ U i),
      frameHomCoordinate (e i) (d i) a V hV = frameHomCoordinate (e i) (d i) b V hV) :
    a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hc : V.unop ≤ iSup (fun i => V.unop ⊓ U i) := by
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨J.presheaf, J.isSheaf⟩
    (fun i => V.unop ⊓ U i) V.unop (fun _ => homOfLE inf_le_left) hc
  intro i
  erw [← PresheafOfModules.naturality_apply a.val,
      ← PresheafOfModules.naturality_apply b.val]
  obtain ⟨r, hr⟩ := ((e i).equiv (V.unop ⊓ U i) inf_le_right).surjective
      (H.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op s)
  change a.app (V.unop ⊓ U i) _ = b.app (V.unop ⊓ U i) _
  erw [← hr, frameHomCoordinate_apply (e i) (d i) a,
      frameHomCoordinate_apply (e i) (d i) b, hab]

namespace HomLine
variable {X : Scheme.{u}} {H J : X.Modules}

lemma fromCoordinate_one_agree {U U' : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U)
    (e' : LocalFrame X H U') (d' : LocalFrame X J U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U')
    (ht : ∀ Z (hZ : Z ≤ V),
      transition (e.equiv Z (hZ.trans hVU)) (e'.equiv Z (hZ.trans hVU')) =
      transition (d.equiv Z (hZ.trans hVU)) (d'.equiv Z (hZ.trans hVU'))) :
    fromCoordinate X H J e d V hVU 1 = fromCoordinate X H J e' d' V hVU' 1 := by
  apply Subtype.ext
  funext Z
  apply LinearMap.ext
  intro s
  rw [fromCoordinate_apply, fromCoordinate_apply]
  simp only [map_one, one_smul]
  obtain ⟨r, rfl⟩ := (e'.equiv Z.val (Z.property.trans hVU')).surjective s
  rw [LinearEquiv.symm_apply_apply,
    transition_apply (e.equiv Z.val (Z.property.trans hVU)) (e'.equiv Z.val (Z.property.trans hVU')) r,
    LinearEquiv.symm_apply_apply, ht Z.val Z.property,
    ← transition_apply]

variable {ι : Type v} (U : ι → X.Opens) (hcover : (⊤ : X.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame X H (U i)) (d : ∀ i, LocalFrame X J (U i))
    (ht : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      transition ((e i).equiv V hi) ((e j).equiv V hj) =
        transition ((d i).equiv V hi) ((d j).equiv V hj))

include hcover ht

lemma exists_frameMap : ∃ a : H ⟶ J, ∀ i V (hV : V ≤ U i) r,
    a.app V ((e i).equiv V hV r) = (d i).equiv V hV r := by
  obtain ⟨b, hb, _⟩ := compatibleMaps_glue U ⊤ (fun _ => le_top) hcover
    (fun i => fromCoordinate X H J (e i) (d i) (U i) le_rfl 1) (by
      intro i j
      rw [fromCoordinate_restrict, fromCoordinate_restrict, map_one, map_one]
      apply fromCoordinate_one_agree
      intro Z hZ
      exact ht i j Z (hZ.trans inf_le_left) (hZ.trans inf_le_right))
  refine ⟨toHom b, ?_⟩
  intro i V hV r
  have h := congrArg (fun z : compatibleMaps X H J (U i) => z.val ⟨V, hV⟩) (hb i)
  change b.val ⟨V, le_top⟩ = (fromCoordinate X H J (e i) (d i) (U i) le_rfl 1).val ⟨V, hV⟩ at h
  change b.val ⟨V, le_top⟩ ((e i).equiv V hV r) = _
  rw [h, fromCoordinate_apply]
  simp only [map_one, one_smul, LinearEquiv.symm_apply_apply]

def frameMap : H ⟶ J := (exists_frameMap U hcover e d ht).choose

lemma frameMap_apply (i : ι) (V : X.Opens) (hV : V ≤ U i) (r : Γ(X,V)) :
    (frameMap U hcover e d ht).app V ((e i).equiv V hV r) = (d i).equiv V hV r :=
  (exists_frameMap U hcover e d ht).choose_spec i V hV r

lemma frameMap_coordinate (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    frameHomCoordinate (e i) (d i) (frameMap U hcover e d ht) V hV = 1 := by
  unfold frameHomCoordinate
  rw [frameMap_apply, LinearEquiv.symm_apply_apply]

def frameIso : H ≅ J where
  hom := frameMap U hcover e d ht
  inv := frameMap U hcover d e (fun i j V hi hj => (ht i j V hi hj).symm)
  hom_inv_id := by
    apply frameHomCoordinate_ext U hcover e e
    intro i V hV
    rw [frameHomCoordinate_comp (e i) (d i) (e i),
      frameMap_coordinate, frameMap_coordinate, frameHomCoordinate_id, mul_one]
  inv_hom_id := by
    apply frameHomCoordinate_ext U hcover d d
    intro i V hV
    rw [frameHomCoordinate_comp (d i) (e i) (d i),
      frameMap_coordinate, frameMap_coordinate, frameHomCoordinate_id, mul_one]

end HomLine

namespace HomLine
variable {X : Scheme.{u}} {H J : X.Modules} {U U' : X.Opens}

lemma tensorPowerFrame_transition_value (e : LocalFrame X H U) (e' : LocalFrame X H U')
    (n : ℕ) (V : X.Opens) (hV : V ≤ U) (hV' : V ≤ U') :
    transition ((tensorPowerFrame X H U e n).equiv V hV)
      ((tensorPowerFrame X H U' e' n).equiv V hV') =
      transition (e.equiv V hV) (e'.equiv V hV') ^ n :=
  congrArg (fun z : Γ(X,V)ˣ => (z : Γ(X,V)))
    (tensorPowerFrame_transition X H U U' e e' n V hV hV')

lemma homTensorPower_transition (e : LocalFrame X H U) (d : LocalFrame X J U)
    (e' : LocalFrame X H U') (d' : LocalFrame X J U') (n : ℕ)
    (V : X.Opens) (hV : V ≤ U) (hV' : V ≤ U') :
    transition ((tensorPowerFrame X (homLine X H J) U (homFrame e d) n).equiv V hV)
      ((tensorPowerFrame X (homLine X H J) U' (homFrame e' d') n).equiv V hV') =
    transition ((homFrame (tensorPowerFrame X H U e n) (tensorPowerFrame X J U d n)).equiv V hV)
      ((homFrame (tensorPowerFrame X H U' e' n) (tensorPowerFrame X J U' d' n)).equiv V hV') := by
  rw [tensorPowerFrame_transition_value]
  apply ((transitionUnit (e.equiv V hV) (e'.equiv V hV')).isUnit.pow n).mul_right_cancel
  change _ * (transition (e.equiv V hV) (e'.equiv V hV')) ^ n =
    _ * (transition (e.equiv V hV) (e'.equiv V hV')) ^ n
  rw [← mul_pow, homFrame_transition]
  have h := homFrame_transition (tensorPowerFrame X H U e n) (tensorPowerFrame X J U d n)
    (tensorPowerFrame X H U' e' n) (tensorPowerFrame X J U' d' n) V hV hV'
  rw [tensorPowerFrame_transition_value, tensorPowerFrame_transition_value] at h
  exact h.symm
end HomLine

namespace HomLine

structure PairFrames (X : Scheme.{u}) (H J : X.Modules) where
  opens : X → X.Opens
  mem : ∀ x, x ∈ opens x
  left : ∀ x, LocalFrame X H (opens x)
  right : ∀ x, LocalFrame X J (opens x)

variable {X : Scheme.{u}} {H J : X.Modules}

def pairFrames (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J) : PairFrames X H J := by
  classical
  choose U hxU E using hH
  choose V hxV D using hJ
  exact ⟨fun x => U x ⊓ V x, fun x => ⟨hxU x, hxV x⟩,
    fun x => restrictFrame (localFrameOfIso X H (U x) (E x).some) _ inf_le_left,
    fun x => restrictFrame (localFrameOfIso X J (V x) (D x).some) _ inf_le_right⟩

lemma PairFrames.covers (C : PairFrames X H J) : (⊤ : X.Opens) ≤ iSup C.opens := by
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, C.mem x⟩

def homTensorPowerIso (C : PairFrames X H J) (n : ℕ) :
    tensorPower X (homLine X H J) n ≅ homLine X (tensorPower X H n) (tensorPower X J n) :=
  frameIso C.opens C.covers
    (fun i => tensorPowerFrame X (homLine X H J) (C.opens i) (homFrame (C.left i) (C.right i)) n)
    (fun i => homFrame (tensorPowerFrame X H (C.opens i) (C.left i) n)
      (tensorPowerFrame X J (C.opens i) (C.right i) n))
    (fun i j V hi hj => homTensorPower_transition (C.left i) (C.right i)
      (C.left j) (C.right j) n V hi hj)

lemma homTensorPowerIso_apply (C : PairFrames X H J) (n : ℕ)
    (i : X) (V : X.Opens) (hV : V ≤ C.opens i) (r : Γ(X,V)) :
    (homTensorPowerIso C n).hom.app V
      ((tensorPowerFrame X (homLine X H J) (C.opens i)
        (homFrame (C.left i) (C.right i)) n).equiv V hV r) =
      (homFrame (tensorPowerFrame X H (C.opens i) (C.left i) n)
        (tensorPowerFrame X J (C.opens i) (C.right i) n)).equiv V hV r :=
  frameMap_apply C.opens C.covers _ _
    (fun i j V hi hj => homTensorPower_transition (C.left i) (C.right i)
      (C.left j) (C.right j) n V hi hj) i V hV r

lemma homTensorPowerIso_section (C : PairFrames X H J) (n : ℕ)
    (s : Γ(homLine X H J, ⊤)) :
    sectionEquivHom ((homTensorPowerIso C n).hom.app ⊤
      (tensorPowerSection X (homLine X H J) n ⊤ s)) =
      tensorPowerMap (sectionEquivHom s) n := by
  apply frameHomCoordinate_ext C.opens C.covers
    (fun i => tensorPowerFrame X H (C.opens i) (C.left i) n)
    (fun i => tensorPowerFrame X J (C.opens i) (C.right i) n)
  intro i V hV
  rw [← sectionEquivHom_coordinate, frameHomCoordinate_tensorPowerMap,
    ← sectionEquivHom_coordinate (C.left i) (C.right i) s V hV]
  erw [← PresheafOfModules.naturality_apply (homTensorPowerIso C n).hom.val]
  erw [tensorPowerSection_restrict]
  let r := ((homFrame (C.left i) (C.right i)).equiv V hV).symm
    ((homLine X H J).presheaf.map (homOfLE le_top).op s)
  have hs : (homLine X H J).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s =
      (homFrame (C.left i) (C.right i)).equiv V hV r :=
    (LinearEquiv.apply_symm_apply _ _).symm
  rw [hs, tensorPowerSection_frame]
  erw [homTensorPowerIso_apply]
  simp only [LinearEquiv.symm_apply_apply]
lemma homTensorPowerIso_inv_apply (C : PairFrames X H J) (n : ℕ)
    (i : X) (V : X.Opens) (hV : V ≤ C.opens i) (r : Γ(X,V)) :
    (homTensorPowerIso C n).inv.app V
      ((homFrame (tensorPowerFrame X H (C.opens i) (C.left i) n)
        (tensorPowerFrame X J (C.opens i) (C.right i) n)).equiv V hV r) =
      (tensorPowerFrame X (homLine X H J) (C.opens i)
        (homFrame (C.left i) (C.right i)) n).equiv V hV r :=
  frameMap_apply C.opens C.covers _ _
    (fun i j V hi hj => (homTensorPower_transition (C.left i) (C.right i)
      (C.left j) (C.right j) n V hi hj).symm) i V hV r

lemma homTensorPowerIso_inv_coordinate (C : PairFrames X H J) (n : ℕ)
    (t : Γ(homLine X (tensorPower X H n) (tensorPower X J n), ⊤))
    (i : X) (V : X.Opens) (hV : V ≤ C.opens i) :
    ((tensorPowerFrame X (homLine X H J) (C.opens i)
        (homFrame (C.left i) (C.right i)) n).equiv V hV).symm
      ((tensorPower X (homLine X H J) n).presheaf.map (homOfLE le_top).op
        ((homTensorPowerIso C n).inv.app ⊤ t)) =
      ((homFrame (tensorPowerFrame X H (C.opens i) (C.left i) n)
        (tensorPowerFrame X J (C.opens i) (C.right i) n)).equiv V hV).symm
          ((homLine X (tensorPower X H n) (tensorPower X J n)).presheaf.map (homOfLE le_top).op t) := by
  erw [← PresheafOfModules.naturality_apply (homTensorPowerIso C n).inv.val]
  obtain ⟨r, hr⟩ := ((homFrame (tensorPowerFrame X H (C.opens i) (C.left i) n)
    (tensorPowerFrame X J (C.opens i) (C.right i) n)).equiv V hV).surjective
      ((homLine X (tensorPower X H n) (tensorPower X J n)).presheaf.map (homOfLE le_top).op t)
  erw [← hr, homTensorPowerIso_inv_apply]
  simp only [LinearEquiv.symm_apply_apply]

variable {W : X.Modules}

def comparisonSection (C : PairFrames X H J)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    Γ(tensorPower X (homLine X H J) 2, ⊤) :=
  (homTensorPowerIso C 2).inv.app ⊤ (sectionEquivHom.symm (a.hom ≫ b.inv))

lemma comparisonSection_generating (C : PairFrames X H J)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    ArithmeticThetaRootTorsor.IsGeneratingSection X
      (tensorPower X (homLine X H J) 2) (comparisonSection C a b) := by
  intro x
  refine ⟨C.opens x, C.mem x,
    tensorPowerFrame X (homLine X H J) (C.opens x) (homFrame (C.left x) (C.right x)) 2, ?_⟩
  unfold comparisonSection
  rw [homTensorPowerIso_inv_coordinate, sectionEquivHom_coordinate, Equiv.apply_symm_apply]
  exact frameHomCoordinate_isUnit (tensorPowerFrame X H (C.opens x) (C.left x) 2)
    (tensorPowerFrame X J (C.opens x) (C.right x) 2) (a ≪≫ b.symm) _ le_rfl

lemma comparisonSection_image (C : PairFrames X H J)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    (homTensorPowerIso C 2).hom.app ⊤ (comparisonSection C a b) =
      sectionEquivHom.symm (a.hom ≫ b.inv) := by
  have h := congrArg (fun k => k.app ⊤) (homTensorPowerIso C 2).inv_hom_id
  exact ConcreteCategory.congr_hom h (sectionEquivHom.symm (a.hom ≫ b.inv))

lemma comparisonSection_eq_iff (C : PairFrames X H J)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (s : Γ(homLine X H J, ⊤)) :
    tensorPowerSection X (homLine X H J) 2 ⊤ s = comparisonSection C a b ↔
      tensorPowerMap (sectionEquivHom s) 2 ≫ b.hom = a.hom := by
  let E := Iso.toLinearEquiv ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
    (homTensorPowerIso C 2))
  have hinj : Function.Injective (fun t : Γ(tensorPower X (homLine X H J) 2, ⊤) =>
      (homTensorPowerIso C 2).hom.app ⊤ t) := E.injective
  rw [← hinj.eq_iff, comparisonSection_image, ← sectionEquivHom.injective.eq_iff,
    homTensorPowerIso_section, Equiv.apply_symm_apply]
  rw [← cancel_mono b.hom, Category.assoc, b.inv_hom_id, Category.comp_id]

/-- The actual geometric root cover for the comparison section. -/
theorem comparison_root_cover
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J)
    (h2 : IsUnit (2 : Γ(X, ⊤)))
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    ∃ (T : Scheme.{u}) (p : T ⟶ X)
      (s : Γ((Scheme.Modules.pullback p).obj (homLine X H J), ⊤)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧ (∀ x, Scheme.Hom.finrank p x = 2) ∧
      ArithmeticThetaRootTorsor.IsGeneratingSection T
        ((Scheme.Modules.pullback p).obj (homLine X H J)) s ∧
      tensorPowerSection T ((Scheme.Modules.pullback p).obj (homLine X H J)) 2 ⊤ s =
        ArithmeticThetaNormalizedSections.pullbackPowerSection p (homLine X H J) 2
          (comparisonSection (pairFrames hH hJ) a b) ∧
      ∀ (S : Scheme.{u}) (f : S ⟶ X)
        (w : ArithmeticThetaRootTorsor.RootSections (homLine X H J) 2
          (comparisonSection (pairFrames hH hJ) a b) f),
        ∃! g : {g : S ⟶ T // g ≫ p = f},
          ArithmeticThetaRootTorsor.pullbackSectionOver p f (homLine X H J) g s = w.val := by
  exact global_root_torsor X (homLine X H J) (homLine_isLineBundle hH hJ) 2
    (by decide) h2 (comparisonSection (pairFrames hH hJ) a b)
    (comparisonSection_generating (pairFrames hH hJ) a b)

end HomLine

variable {X : Scheme.{u}} {H J : X.Modules}

lemma frameHomCoordinate_bijective {U : X.Opens}
    (e : LocalFrame X H U) (d : LocalFrame X J U) (a : H ⟶ J)
    (V : X.Opens) (hV : V ≤ U) (ha : IsUnit (frameHomCoordinate e d a V hV)) :
    Function.Bijective (a.app V) := by
  constructor
  · intro s t h
    obtain ⟨r, rfl⟩ := (e.equiv V hV).surjective s
    obtain ⟨q, rfl⟩ := (e.equiv V hV).surjective t
    rw [frameHomCoordinate_apply e d a, frameHomCoordinate_apply e d a] at h
    exact congrArg (e.equiv V hV) (ha.mul_right_cancel ((d.equiv V hV).injective h))
  · intro t
    obtain ⟨c, hc⟩ := ha
    refine ⟨e.equiv V hV ((d.equiv V hV).symm t * (↑c⁻¹ : Γ(X,V))), ?_⟩
    rw [frameHomCoordinate_apply, ← hc, mul_assoc, Units.inv_mul, mul_one,
      LinearEquiv.apply_symm_apply]

lemma isIso_of_locally_bijective (a : H ⟶ J)
    (ha : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ V : X.Opens, V ≤ U → Function.Bijective (a.app V)) : IsIso a := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · constructor
    intro V s t h x hx
    obtain ⟨U, hxU, hb⟩ := ha x
    refine ⟨V.unop ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
    apply (hb (V.unop ⊓ U) inf_le_right).injective
    change a.val.app (op (V.unop ⊓ U)) (H.val.map (homOfLE inf_le_left).op s) =
      a.val.app (op (V.unop ⊓ U)) (H.val.map (homOfLE inf_le_left).op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg (J.val.map (homOfLE inf_le_left).op) h
  · constructor
    intro V s x hx
    obtain ⟨U, hxU, hb⟩ := ha x
    refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
    exact (hb (V ⊓ U) inf_le_right).surjective (J.presheaf.map (homOfLE inf_le_left).op s)

lemma isIso_of_unit_frame_coordinates (a : H ⟶ J)
    (ha : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (e : LocalFrame X H U) (d : LocalFrame X J U),
      IsUnit (frameHomCoordinate e d a U le_rfl)) : IsIso a := by
  apply isIso_of_locally_bijective a
  intro x
  obtain ⟨U, hx, e, d, hu⟩ := ha x
  refine ⟨U, hx, fun V hV => frameHomCoordinate_bijective e d a V hV ?_⟩
  rw [frameHomCoordinate_restrict e d a U V hV le_rfl]
  exact hu.map (X.presheaf.map (homOfLE hV).op).hom


open ArithmeticThetaNormalizedSections
variable {X : Scheme.{u}} {H J W : X.Modules}

lemma square_morphism_isIso (hH : IsLineBundle X H) (hJ : IsLineBundle X J)
    (hW : IsLineBundle X W) (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (w : H ⟶ J) (hw : tensorPowerMap w 2 ≫ b.hom = a.hom) : IsIso w := by
  apply isIso_of_unit_frame_coordinates w
  intro x
  obtain ⟨U, hxU, ⟨E⟩⟩ := hH x
  obtain ⟨V, hxV, ⟨D⟩⟩ := hJ x
  obtain ⟨Z, hxZ, ⟨F⟩⟩ := hW x
  let O := (U ⊓ V) ⊓ Z
  let e := restrictFrame (localFrameOfIso X H U E) O (inf_le_left.trans inf_le_left)
  let d := restrictFrame (localFrameOfIso X J V D) O (inf_le_left.trans inf_le_right)
  let c := restrictFrame (localFrameOfIso X W Z F) O inf_le_right
  refine ⟨O, ⟨⟨hxU,hxV⟩,hxZ⟩, e, d, ?_⟩
  have h := congrArg (fun k => frameHomCoordinate (tensorPowerFrame X H O e 2) c k O le_rfl) hw
  rw [frameHomCoordinate_comp, frameHomCoordinate_tensorPowerMap] at h
  have hu := frameHomCoordinate_isUnit (tensorPowerFrame X H O e 2) c a O le_rfl
  rw [← h] at hu
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (isUnit_of_mul_isUnit_left hu)

namespace HomLine
variable {X : Scheme.{u}} {H J W : X.Modules}

/-- Over the base itself, roots of the constructed section are exactly genuine
square-compatible line isomorphisms. -/
def comparisonRootsEquiv
    (hH : ArithmeticThetaNormalizedSections.IsLineBundle X H)
    (hJ : ArithmeticThetaNormalizedSections.IsLineBundle X J)
    (hW : ArithmeticThetaNormalizedSections.IsLineBundle X W)
    (C : PairFrames X H J) (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    {s : Γ(homLine X H J, ⊤) // tensorPowerSection X (homLine X H J) 2 ⊤ s = comparisonSection C a b} ≃
      {e : H ≅ J // tensorPowerMap e.hom 2 ≫ b.hom = a.hom} where
  toFun s := by
    have hw := (comparisonSection_eq_iff C a b s.val).mp s.property
    have := square_morphism_isIso hH hJ hW a b (sectionEquivHom s.val) hw
    exact ⟨asIso (sectionEquivHom s.val), hw⟩
  invFun e := ⟨sectionEquivHom.symm e.val.hom, (comparisonSection_eq_iff C a b _).mpr
    (by simpa only [Equiv.apply_symm_apply] using e.property)⟩
  left_inv s := by
    apply Subtype.ext
    exact sectionEquivHom.symm_apply_apply s.val
  right_inv e := by
    apply Subtype.ext
    apply Iso.ext
    exact sectionEquivHom.apply_symm_apply e.val.hom
end HomLine

namespace HomLine
variable {X S : Scheme.{u}} {H : X.Modules} {U U' : X.Opens}

def pulledFrame (f : S ⟶ X) (e : LocalFrame X H U) :
    LocalFrame S ((Scheme.Modules.pullback f).obj H) (f ⁻¹ᵁ U) :=
  (exists_pullbackFrame S X f H U e).choose

lemma pulledFrame_compatible (f : S ⟶ X) (e : LocalFrame X H U) :
    FramePullbackCompatible f H U e (pulledFrame f e) :=
  (exists_pullbackFrame S X f H U e).choose_spec

lemma frameTransition_restrict (e : LocalFrame X H U) (d : LocalFrame X H U')
    (V Z : X.Opens) (hZV : Z ≤ V) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition (e.equiv Z (hZV.trans hVU)) (d.equiv Z (hZV.trans hVU')) =
      X.presheaf.map (homOfLE hZV).op (transition (e.equiv V hVU) (d.equiv V hVU')) := by
  unfold transition
  rw [← frame_coordinate_restrict e V Z hZV hVU]
  congr 1
  simpa using (d.naturality V Z hZV hVU' 1).symm

lemma pulledFrame_transition (f : S ⟶ X) (e : LocalFrame X H U) (d : LocalFrame X H U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U') :
    transition ((pulledFrame f e).equiv (f ⁻¹ᵁ V) (f.preimage_mono hVU))
      ((pulledFrame f d).equiv (f ⁻¹ᵁ V) (f.preimage_mono hVU')) =
      f.app V (transition (e.equiv V hVU) (d.equiv V hVU')) := by
  apply ((pulledFrame f e).equiv (f ⁻¹ᵁ V) (f.preimage_mono hVU)).injective
  simp only [transition, LinearEquiv.apply_symm_apply]
  rw [← pulledFrame_compatible f e V hVU, LinearEquiv.apply_symm_apply,
    pulledFrame_compatible f d V hVU', map_one (f.app V).hom]

lemma pulledFrame_transition_subopen (f : S ⟶ X)
    (e : LocalFrame X H U) (d : LocalFrame X H U')
    (V : X.Opens) (hVU : V ≤ U) (hVU' : V ≤ U')
    (Z : S.Opens) (hZ : Z ≤ f ⁻¹ᵁ V) :
    transition ((pulledFrame f e).equiv Z (hZ.trans (f.preimage_mono hVU)))
      ((pulledFrame f d).equiv Z (hZ.trans (f.preimage_mono hVU'))) =
    S.presheaf.map (homOfLE hZ).op
      (f.app V (transition (e.equiv V hVU) (d.equiv V hVU'))) := by
  rw [frameTransition_restrict (pulledFrame f e) (pulledFrame f d)
    (f ⁻¹ᵁ V) Z hZ (f.preimage_mono hVU) (f.preimage_mono hVU'),
    pulledFrame_transition]
variable {J : X.Modules}

lemma homPullback_transition (f : S ⟶ X)
    (e : LocalFrame X H U) (d : LocalFrame X J U)
    (e' : LocalFrame X H U') (d' : LocalFrame X J U')
    (Z : S.Opens) (hZU : Z ≤ f ⁻¹ᵁ U) (hZU' : Z ≤ f ⁻¹ᵁ U') :
    transition ((pulledFrame f (homFrame e d)).equiv Z hZU)
      ((pulledFrame f (homFrame e' d')).equiv Z hZU') =
    transition ((homFrame (pulledFrame f e) (pulledFrame f d)).equiv Z hZU)
      ((homFrame (pulledFrame f e') (pulledFrame f d')).equiv Z hZU') := by
  have hZ : Z ≤ f ⁻¹ᵁ (U ⊓ U') := le_inf hZU hZU'
  apply (transitionUnit ((pulledFrame f e).equiv Z hZU)
    ((pulledFrame f e').equiv Z hZU')).isUnit.mul_right_cancel
  change _ * transition ((pulledFrame f e).equiv Z hZU)
      ((pulledFrame f e').equiv Z hZU') =
    _ * transition ((pulledFrame f e).equiv Z hZU) ((pulledFrame f e').equiv Z hZU')
  rw [homFrame_transition]
  rw [pulledFrame_transition_subopen f (homFrame e d) (homFrame e' d')
      (U ⊓ U') inf_le_left inf_le_right Z hZ,
    pulledFrame_transition_subopen f e e' (U ⊓ U') inf_le_left inf_le_right Z hZ,
    pulledFrame_transition_subopen f d d' (U ⊓ U') inf_le_left inf_le_right Z hZ,
    ← map_mul, ← map_mul, homFrame_transition]

def pullbackHomFrames (C : PairFrames X H J) (f : S ⟶ X) :
    PairFrames S ((Scheme.Modules.pullback f).obj (homLine X H J))
      (homLine S ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj J)) where
  opens y := f ⁻¹ᵁ C.opens (f y)
  mem y := C.mem (f y)
  left y := pulledFrame f (homFrame (C.left (f y)) (C.right (f y)))
  right y := homFrame (pulledFrame f (C.left (f y))) (pulledFrame f (C.right (f y)))

def homPullbackIso (C : PairFrames X H J) (f : S ⟶ X) :
    (Scheme.Modules.pullback f).obj (homLine X H J) ≅
      homLine S ((Scheme.Modules.pullback f).obj H) ((Scheme.Modules.pullback f).obj J) :=
  frameIso (pullbackHomFrames C f).opens (pullbackHomFrames C f).covers
    (pullbackHomFrames C f).left (pullbackHomFrames C f).right
    (fun i j V hi hj => homPullback_transition f (C.left (f i)) (C.right (f i))
      (C.left (f j)) (C.right (f j)) V hi hj)

lemma homPullbackIso_apply (C : PairFrames X H J) (f : S ⟶ X)
    (i : S) (V : S.Opens) (hV : V ≤ f ⁻¹ᵁ C.opens (f i)) (r : Γ(S,V)) :
    (homPullbackIso C f).hom.app V
      ((pulledFrame f (homFrame (C.left (f i)) (C.right (f i)))).equiv V hV r) =
      (homFrame (pulledFrame f (C.left (f i))) (pulledFrame f (C.right (f i)))).equiv V hV r :=
  frameMap_apply (pullbackHomFrames C f).opens (pullbackHomFrames C f).covers _ _
    (fun i j V hi hj => homPullback_transition f (C.left (f i)) (C.right (f i))
      (C.left (f j)) (C.right (f j)) V hi hj) i V hV r

def pullbackSectionEquivHom (C : PairFrames X H J) (f : S ⟶ X) :
    Γ((Scheme.Modules.pullback f).obj (homLine X H J), ⊤) ≃
      ((Scheme.Modules.pullback f).obj H ⟶ (Scheme.Modules.pullback f).obj J) :=
  (Iso.toLinearEquiv ((SheafOfModules.evaluation S.ringCatSheaf (op ⊤)).mapIso
    (homPullbackIso C f))).toEquiv.trans sectionEquivHom

lemma pullbackSectionEquivHom_coordinate (C : PairFrames X H J) (f : S ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj (homLine X H J), ⊤))
    (i : S) (V : S.Opens) (hV : V ≤ f ⁻¹ᵁ C.opens (f i)) :
    frameHomCoordinate (pulledFrame f (C.left (f i))) (pulledFrame f (C.right (f i)))
      (pullbackSectionEquivHom C f s) V hV =
      ((pulledFrame f (homFrame (C.left (f i)) (C.right (f i)))).equiv V hV).symm
        (((Scheme.Modules.pullback f).obj (homLine X H J)).presheaf.map (homOfLE le_top).op s) := by
  change frameHomCoordinate _ _ (sectionEquivHom ((homPullbackIso C f).hom.app ⊤ s)) V hV = _
  rw [← sectionEquivHom_coordinate]
  erw [← PresheafOfModules.naturality_apply (homPullbackIso C f).hom.val]
  obtain ⟨r, hr⟩ := ((pulledFrame f (homFrame (C.left (f i)) (C.right (f i)))).equiv V hV).surjective
    (((Scheme.Modules.pullback f).obj (homLine X H J)).presheaf.map (homOfLE le_top).op s)
  erw [← hr, homPullbackIso_apply]
  simp only [LinearEquiv.symm_apply_apply]

end HomLine

namespace HomLine
variable {X S : Scheme.{u}} {H J : X.Modules} {U : X.Opens}

lemma pullbackLocalSection_hom (f : S ⟶ X) (a : H ⟶ J)
    (U : X.Opens) (s : Γ(H,U)) :
    ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U)
      (pullbackLocalSection f H U s) = pullbackLocalSection f J U (a.app U s) := by
  exact (ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k U)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)) s).symm

lemma pullbackHom_frame (f : S ⟶ X) (a : H ⟶ J)
    (e : LocalFrame X H U) (d : LocalFrame X J U) (r : Γ(S,f ⁻¹ᵁ U)) :
    ((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U)
      ((pulledFrame f e).equiv (f ⁻¹ᵁ U) le_rfl r) =
    (pulledFrame f d).equiv (f ⁻¹ᵁ U) le_rfl
      (r * f.app U (frameHomCoordinate e d a U le_rfl)) := by
  have he : (pulledFrame f e).equiv (f ⁻¹ᵁ U) le_rfl r =
      r • pullbackLocalSection f H U (e.equiv U le_rfl 1) := by
    rw [pulledFrame_compatible f e U le_rfl, map_one (f.app U).hom,
      ← map_smul, smul_eq_mul, mul_one]
  rw [he, Scheme.Modules.Hom.app_smul, pullbackLocalSection_hom,
    frameHomCoordinate_apply e d a, one_mul,
    pulledFrame_compatible f d U le_rfl, ← map_smul, smul_eq_mul]

lemma pullbackHom_coordinate (f : S ⟶ X) (a : H ⟶ J)
    (e : LocalFrame X H U) (d : LocalFrame X J U) :
    frameHomCoordinate (pulledFrame f e) (pulledFrame f d)
      ((Scheme.Modules.pullback f).map a) (f ⁻¹ᵁ U) le_rfl =
      f.app U (frameHomCoordinate e d a U le_rfl) := by
  unfold frameHomCoordinate
  rw [pullbackHom_frame, one_mul, LinearEquiv.symm_apply_apply]
  rfl
end HomLine
namespace HomLine
variable {X S : Scheme.{u}} {H J : X.Modules} {U : X.Opens}

def pullbackPowerMap (f : S ⟶ X) {n : ℕ}
    (a : tensorPower X H n ⟶ tensorPower X J n) :
    tensorPower S ((Scheme.Modules.pullback f).obj H) n ⟶
      tensorPower S ((Scheme.Modules.pullback f).obj J) n :=
  (pullback_tensorPower_iso S X f H n).inv ≫
    (Scheme.Modules.pullback f).map a ≫ (pullback_tensorPower_iso S X f J n).hom

lemma pullbackPowerMap_coordinate (f : S ⟶ X) (n : ℕ)
    (a : tensorPower X H n ⟶ tensorPower X J n)
    (e : LocalFrame X H U) (d : LocalFrame X J U) :
    frameHomCoordinate (tensorPowerFrame S ((Scheme.Modules.pullback f).obj H)
      (f ⁻¹ᵁ U) (pulledFrame f e) n)
      (tensorPowerFrame S ((Scheme.Modules.pullback f).obj J)
      (f ⁻¹ᵁ U) (pulledFrame f d) n)
      (pullbackPowerMap f a) (f ⁻¹ᵁ U) le_rfl =
      f.app U (frameHomCoordinate (tensorPowerFrame X H U e n)
        (tensorPowerFrame X J U d n) a U le_rfl) := by
  let E := pullback_tensorPower_iso S X f H n
  let D := pullback_tensorPower_iso S X f J n
  have he := local_power_pullback_frame S X f H U e (pulledFrame f e)
    (pulledFrame_compatible f e) n 1
  rw [map_one (f.app U).hom] at he
  apply ((tensorPowerFrame S ((Scheme.Modules.pullback f).obj J)
    (f ⁻¹ᵁ U) (pulledFrame f d) n).equiv (f ⁻¹ᵁ U) le_rfl).injective
  rw [frameHomCoordinate, LinearEquiv.apply_symm_apply, ← he]
  change D.hom.app (f ⁻¹ᵁ U) (((Scheme.Modules.pullback f).map a).app (f ⁻¹ᵁ U)
    (E.inv.app (f ⁻¹ᵁ U) (E.hom.app (f ⁻¹ᵁ U) _))) = _
  have heinv := ConcreteCategory.congr_hom (congrArg
    (fun k => Scheme.Modules.Hom.app k (f ⁻¹ᵁ U)) E.hom_inv_id)
    (pullbackLocalSection f (tensorPower X H n) U ((tensorPowerFrame X H U e n).equiv U le_rfl 1))
  change E.inv.app (f ⁻¹ᵁ U) (E.hom.app (f ⁻¹ᵁ U) _) = _ at heinv
  change E.inv.app (f ⁻¹ᵁ U) (E.hom.app (f ⁻¹ᵁ U) _) =
    pullbackLocalSection f (tensorPower X H n) U ((tensorPowerFrame X H U e n).equiv U le_rfl 1) at heinv
  rw [heinv, pullbackLocalSection_hom,
    frameHomCoordinate_apply (tensorPowerFrame X H U e n) (tensorPowerFrame X J U d n) a,
    one_mul]
  exact local_power_pullback_frame S X f J U d (pulledFrame f d)
    (pulledFrame_compatible f d) n _

lemma frameHomCoordinate_ext_top {Y : Scheme.{u}} {A B : Y.Modules} {ι : Type u}
    (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame Y A (U i)) (d : ∀ i, LocalFrame Y B (U i))
    {a b : A ⟶ B}
    (h : ∀ i, frameHomCoordinate (e i) (d i) a (U i) le_rfl =
      frameHomCoordinate (e i) (d i) b (U i) le_rfl) : a = b := by
  apply frameHomCoordinate_ext U hU e d
  intro i V hV
  rw [frameHomCoordinate_restrict (e i) (d i) a (U i) V hV le_rfl,
    frameHomCoordinate_restrict (e i) (d i) b (U i) V hV le_rfl, h i]

lemma tensorPowerSection_coordinate {Y : Scheme.{u}} {A : Y.Modules}
    (n : ℕ) (s : Γ(A, ⊤)) (U : Y.Opens) (e : LocalFrame Y A U) :
    sectionCoordinate Y (tensorPower Y A n) U (tensorPowerFrame Y A U e n)
      (tensorPowerSection Y A n ⊤ s) = (sectionCoordinate Y A U e s) ^ n := by
  unfold sectionCoordinate
  rw [tensorPowerSection_restrict]
  obtain ⟨r, hr⟩ := (e.equiv U le_rfl).surjective (A.presheaf.map (homOfLE le_top).op s)
  rw [← hr, tensorPowerSection_frame, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

variable {W : X.Modules}
lemma comparisonSection_coordinate (C : PairFrames X H J)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) (i : X) :
    sectionCoordinate X (tensorPower X (homLine X H J) 2) (C.opens i)
      (tensorPowerFrame X (homLine X H J) (C.opens i) (homFrame (C.left i) (C.right i)) 2)
      (comparisonSection C a b) =
      frameHomCoordinate (tensorPowerFrame X H (C.opens i) (C.left i) 2)
        (tensorPowerFrame X J (C.opens i) (C.right i) 2) (a.hom ≫ b.inv) (C.opens i) le_rfl := by
  unfold sectionCoordinate comparisonSection
  rw [homTensorPowerIso_inv_coordinate, sectionEquivHom_coordinate, Equiv.apply_symm_apply]

lemma pullbackPowerMap_comparison (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    pullbackPowerMap f (a.hom ≫ b.inv) = (pullbackPowerIso f a).hom ≫ (pullbackPowerIso f b).inv := by
  simp [pullbackPowerMap, pullbackPowerIso, Functor.map_comp, Category.assoc]

lemma section_eq_iff_coordinates {Y : Scheme.{u}} {A : Y.Modules} {ι : Type u}
    (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame Y A (U i)) (s t : Γ(A, ⊤)) :
    s = t ↔ ∀ i, sectionCoordinate Y A (U i) (e i) s = sectionCoordinate Y A (U i) (e i) t := by
  constructor
  · rintro rfl i; rfl
  · intro h
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨A.presheaf, A.isSheaf⟩ U ⊤
      (fun _ => homOfLE le_top) hU
    intro i
    exact ((e i).equiv (U i) le_rfl).symm.injective (h i)

lemma hom_eq_iff_coordinates {Y : Scheme.{u}} {A B : Y.Modules} {ι : Type u}
    (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (e : ∀ i, LocalFrame Y A (U i)) (d : ∀ i, LocalFrame Y B (U i))
    (a b : A ⟶ B) : a = b ↔ ∀ i,
      frameHomCoordinate (e i) (d i) a (U i) le_rfl =
      frameHomCoordinate (e i) (d i) b (U i) le_rfl :=
  ⟨fun h i => by rw [h], frameHomCoordinate_ext_top U hU e d⟩

lemma pullback_root_equation_iff_map (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (s : Γ((Scheme.Modules.pullback f).obj (homLine X H J), ⊤)) :
    tensorPowerSection S ((Scheme.Modules.pullback f).obj (homLine X H J)) 2 ⊤ s =
      pullbackPowerSection f (homLine X H J) 2 (comparisonSection C a b) ↔
    tensorPowerMap (pullbackSectionEquivHom C f s) 2 = pullbackPowerMap f (a.hom ≫ b.inv) := by
  rw [section_eq_iff_coordinates (pullbackHomFrames C f).opens (pullbackHomFrames C f).covers
    (fun i => tensorPowerFrame S ((Scheme.Modules.pullback f).obj (homLine X H J))
      (f ⁻¹ᵁ C.opens (f i)) (pulledFrame f (homFrame (C.left (f i)) (C.right (f i)))) 2),
    hom_eq_iff_coordinates (pullbackHomFrames C f).opens (pullbackHomFrames C f).covers
      (fun i => tensorPowerFrame S ((Scheme.Modules.pullback f).obj H)
        (f ⁻¹ᵁ C.opens (f i)) (pulledFrame f (C.left (f i))) 2)
      (fun i => tensorPowerFrame S ((Scheme.Modules.pullback f).obj J)
        (f ⁻¹ᵁ C.opens (f i)) (pulledFrame f (C.right (f i))) 2)]
  apply forall_congr'
  intro i
  dsimp [pullbackHomFrames]
  rw [tensorPowerSection_coordinate,
    pullbackPowerSection_coordinate S X f (homLine X H J) (C.opens (f i))
      (homFrame (C.left (f i)) (C.right (f i)))
      (pulledFrame f (homFrame (C.left (f i)) (C.right (f i))))
      (pulledFrame_compatible f (homFrame (C.left (f i)) (C.right (f i)))),
    comparisonSection_coordinate, frameHomCoordinate_tensorPowerMap,
    pullbackSectionEquivHom_coordinate, pullbackPowerMap_coordinate]
  rfl

lemma pullback_root_equation_iff (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (s : Γ((Scheme.Modules.pullback f).obj (homLine X H J), ⊤)) :
    tensorPowerSection S ((Scheme.Modules.pullback f).obj (homLine X H J)) 2 ⊤ s =
      pullbackPowerSection f (homLine X H J) 2 (comparisonSection C a b) ↔
    tensorPowerMap (pullbackSectionEquivHom C f s) 2 ≫ (pullbackPowerIso f b).hom =
      (pullbackPowerIso f a).hom := by
  rw [pullback_root_equation_iff_map, pullbackPowerMap_comparison,
    ← cancel_mono (pullbackPowerIso f b).hom, Category.assoc,
    (pullbackPowerIso f b).inv_hom_id, Category.comp_id]

end HomLine

namespace HomLine
variable {X S : Scheme.{u}} {H J W : X.Modules}

abbrev rootFamily (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :=
  ArithmeticThetaRootTorsor.RootSections (homLine X H J) 2
    (comparisonSection C a b) f

abbrev squareFamily (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) (f : S ⟶ X) :=
  SquareIsos a b f

lemma rootToSquare_prop (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (w : rootFamily C f a b) :
    tensorPowerMap (pullbackSectionEquivHom C f w.val) 2 ≫ (pullbackPowerIso f b).hom =
      (pullbackPowerIso f a).hom :=
  (pullback_root_equation_iff C f a b w.val).mp w.property

def rootToSquare (hH : IsLineBundle X H) (hJ : IsLineBundle X J) (hW : IsLineBundle X W)
    (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    rootFamily C f a b → squareFamily a b f := fun w => by
  have hi : IsIso (pullbackSectionEquivHom C f w.val) :=
    square_morphism_isIso (pullback_isLineBundle S X f H hH) (pullback_isLineBundle S X f J hJ)
      (pullback_isLineBundle S X f W hW)
      (pullbackPowerIso f a) (pullbackPowerIso f b)
      (pullbackSectionEquivHom C f w.val)
      (rootToSquare_prop C f a b w)
  exact ⟨asIso (pullbackSectionEquivHom C f w.val), rootToSquare_prop C f a b w⟩

def squareToRoot (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    squareFamily a b f → rootFamily C f a b := fun e =>
  ⟨(pullbackSectionEquivHom C f).symm e.val.hom, by
    rw [pullback_root_equation_iff C f a b]
    rw [(pullbackSectionEquivHom C f).apply_symm_apply e.val.hom]
    exact e.property⟩

lemma rootSquare_left (hH : IsLineBundle X H) (hJ : IsLineBundle X J) (hW : IsLineBundle X W)
    (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (w : rootFamily C f a b) : squareToRoot C f a b (rootToSquare hH hJ hW C f a b w) = w := by
  apply Subtype.ext
  change (pullbackSectionEquivHom C f).symm ((pullbackSectionEquivHom C f) w.val) = w.val
  exact (pullbackSectionEquivHom C f).symm_apply_apply w.val

lemma rootSquare_right (hH : IsLineBundle X H) (hJ : IsLineBundle X J) (hW : IsLineBundle X W)
    (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W)
    (e : squareFamily a b f) : rootToSquare hH hJ hW C f a b (squareToRoot C f a b e) = e := by
  dsimp [rootToSquare, squareToRoot]
  apply Subtype.ext
  apply Iso.ext
  change _ = e.val.hom
  exact (pullbackSectionEquivHom C f).apply_symm_apply e.val.hom

def rootSquareEquiv (hH : IsLineBundle X H) (hJ : IsLineBundle X J) (hW : IsLineBundle X W)
    (C : PairFrames X H J) (f : S ⟶ X)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    rootFamily C f a b ≃ squareFamily a b f where
  toFun := rootToSquare hH hJ hW C f a b
  invFun := squareToRoot C f a b
  left_inv := rootSquare_left hH hJ hW C f a b
  right_inv := rootSquare_right hH hJ hW C f a b

end HomLine
namespace HomLine
open ArithmeticThetaRootTorsor
variable {X S T : Scheme.{u}} {M : X.Modules} {U : X.Opens}

lemma pullbackComp_frame_general {S T X : Scheme.{u}} (g : S ⟶ T) (p : T ⟶ X)
    {M : X.Modules} (U : X.Opens) (e : LocalFrame X M U) (a : Γ(T, p ⁻¹ᵁ U)) :
    ((Scheme.Modules.pullbackComp g p).hom.app M).app (g ⁻¹ᵁ (p ⁻¹ᵁ U))
      (pullbackLocalSection g ((Scheme.Modules.pullback p).obj M) (p ⁻¹ᵁ U)
        ((pulledFrame p e).equiv _ le_rfl a)) =
      (pulledFrame (g ≫ p) e).equiv _ le_rfl (g.app (p ⁻¹ᵁ U) a) := by
  have hb : (pulledFrame p e).equiv _ le_rfl a =
      a • pullbackLocalSection p M U (e.equiv U le_rfl 1) := by
    rw [pulledFrame_compatible p e U le_rfl, map_one (p.app U).hom]
    simpa only [smul_eq_mul, mul_one] using ((pulledFrame p e).equiv _ le_rfl).map_smul a 1
  rw [hb, pullbackLocalSection_smul]
  rw [Scheme.Modules.Hom.app_smul, pullbackComp_localSection,
    pulledFrame_compatible (g ≫ p) e U le_rfl, map_one ((g ≫ p).app U).hom]
  simpa only [smul_eq_mul, mul_one] using
    (((pulledFrame (g ≫ p) e).equiv _ le_rfl).map_smul (g.app (p ⁻¹ᵁ U) a) 1).symm

lemma pullbackSectionOver_coordinate_comp
    (g : S ⟶ T) (p : T ⟶ X) (e : LocalFrame X M U)
    (v : Γ((Scheme.Modules.pullback p).obj M, ⊤)) :
    sectionCoordinate S ((Scheme.Modules.pullback (g ≫ p)).obj M) ((g ≫ p) ⁻¹ᵁ U)
      (pulledFrame (g ≫ p) e)
      (pullbackSectionOver p (g ≫ p) M ⟨g, rfl⟩ v) =
      g.app (p ⁻¹ᵁ U) (sectionCoordinate T ((Scheme.Modules.pullback p).obj M)
        (p ⁻¹ᵁ U) (pulledFrame p e) v) := by
  let A := (Scheme.Modules.pullback p).obj M
  let q := (Scheme.Modules.pullbackComp g p).app M
  have hn := PresheafOfModules.naturality_apply q.hom.val
    (homOfLE (show (g ≫ p) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
    (pullbackGlobalSection g A v)
  change q.hom.app _
      (((Scheme.Modules.pullback g).obj A).presheaf.map (homOfLE le_top).op
        (pullbackGlobalSection g A v)) =
    ((Scheme.Modules.pullback (g ≫ p)).obj M).presheaf.map (homOfLE le_top).op
      (q.hom.app ⊤ (pullbackGlobalSection g A v)) at hn
  erw [pullbackGlobalSection_restrict g A (p ⁻¹ᵁ U) v] at hn
  have hv : A.presheaf.map (homOfLE le_top).op v =
      (pulledFrame p e).equiv _ le_rfl
        (sectionCoordinate T A (p ⁻¹ᵁ U) (pulledFrame p e) v) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  rw [hv] at hn
  unfold sectionCoordinate pullbackSectionOver
  change ((pulledFrame (g ≫ p) e).equiv _ le_rfl).symm
    (((Scheme.Modules.pullback (g ≫ p)).obj M).presheaf.map (homOfLE le_top).op
      (q.hom.app ⊤ (pullbackGlobalSection g A v))) = _
  rw [← hn]
  erw [pullbackComp_frame_general g p U e
    (sectionCoordinate T A (p ⁻¹ᵁ U) (pulledFrame p e) v),
    LinearEquiv.symm_apply_apply]
  rfl
end HomLine
namespace HomLine
open ArithmeticThetaRootTorsor
variable {X S T : Scheme.{u}} {H J : X.Modules} {U : X.Opens}
lemma pullbackIsoOver_coordinate_comp (g : S ⟶ T) (p : T ⟶ X)
    (e : LocalFrame X H U) (d : LocalFrame X J U)
    (w : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J) :
    frameHomCoordinate (pulledFrame (g ≫ p) e) (pulledFrame (g ≫ p) d)
      (pullbackIsoOver p (g ≫ p) H J ⟨g,rfl⟩ w).hom ((g ≫ p) ⁻¹ᵁ U) le_rfl =
      g.app (p ⁻¹ᵁ U) (frameHomCoordinate (pulledFrame p e) (pulledFrame p d)
        w.hom (p ⁻¹ᵁ U) le_rfl) := by
  let E := (Scheme.Modules.pullbackComp g p).app H
  let D := (Scheme.Modules.pullbackComp g p).app J
  have he := pullbackComp_frame_general g p U e (1 : Γ(T,p ⁻¹ᵁ U))
  rw [map_one (g.app (p ⁻¹ᵁ U)).hom] at he
  apply ((pulledFrame (g ≫ p) d).equiv ((g ≫ p) ⁻¹ᵁ U) le_rfl).injective
  rw [frameHomCoordinate, LinearEquiv.apply_symm_apply, ← he]
  change D.hom.app _ (((Scheme.Modules.pullback g).map w.hom).app _
    (E.inv.app _ (E.hom.app _ _))) = _
  have hcancel := ConcreteCategory.congr_hom (congrArg
    (fun k => Scheme.Modules.Hom.app k (g ⁻¹ᵁ (p ⁻¹ᵁ U))) E.hom_inv_id)
    (pullbackLocalSection g ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
      ((pulledFrame p e).equiv (p ⁻¹ᵁ U) le_rfl 1))
  change E.inv.app _ (E.hom.app _ _) =
    pullbackLocalSection g ((Scheme.Modules.pullback p).obj H) (p ⁻¹ᵁ U)
      ((pulledFrame p e).equiv (p ⁻¹ᵁ U) le_rfl 1) at hcancel
  erw [hcancel]
  erw [pullbackLocalSection_hom g w.hom (p ⁻¹ᵁ U)
    ((pulledFrame p e).equiv (p ⁻¹ᵁ U) le_rfl 1),
    frameHomCoordinate_apply (pulledFrame p e) (pulledFrame p d), one_mul]
  exact pullbackComp_frame_general g p U d _

lemma pullbackSectionEquivHom_comp (C : PairFrames X H J)
    (g : S ⟶ T) (p : T ⟶ X)
    (v : Γ((Scheme.Modules.pullback p).obj (homLine X H J), ⊤))
    (w : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J)
    (hw : w.hom = pullbackSectionEquivHom C p v) :
    pullbackSectionEquivHom C (g ≫ p)
      (pullbackSectionOver p (g ≫ p) (homLine X H J) ⟨g,rfl⟩ v) =
      (pullbackIsoOver p (g ≫ p) H J ⟨g,rfl⟩ w).hom := by
  apply frameHomCoordinate_ext_top (pullbackHomFrames C (g ≫ p)).opens
    (pullbackHomFrames C (g ≫ p)).covers
    (fun i => pulledFrame (g ≫ p) (C.left ((g ≫ p) i)))
    (fun i => pulledFrame (g ≫ p) (C.right ((g ≫ p) i)))
  intro i
  dsimp only [pullbackHomFrames]
  rw [pullbackSectionEquivHom_coordinate, pullbackIsoOver_coordinate_comp, hw]
  change sectionCoordinate S _ ((g ≫ p) ⁻¹ᵁ C.opens ((g ≫ p) i))
    (pulledFrame (g ≫ p) (homFrame (C.left ((g ≫ p) i)) (C.right ((g ≫ p) i)))) _ = _
  rw [pullbackSectionOver_coordinate_comp]
  congr 1
  exact (pullbackSectionEquivHom_coordinate C p v (g i)
    (p ⁻¹ᵁ C.opens (p (g i))) le_rfl).symm

lemma pullbackSectionEquivHom_over (C : PairFrames X H J)
    (p : T ⟶ X) (f : S ⟶ X) (g : {g : S ⟶ T // g ≫ p = f})
    (v : Γ((Scheme.Modules.pullback p).obj (homLine X H J), ⊤))
    (w : (Scheme.Modules.pullback p).obj H ≅ (Scheme.Modules.pullback p).obj J)
    (hw : w.hom = pullbackSectionEquivHom C p v) :
    pullbackSectionEquivHom C f (pullbackSectionOver p f (homLine X H J) g v) =
      (pullbackIsoOver p f H J g w).hom := by
  rcases g with ⟨g,hg⟩
  subst f
  exact pullbackSectionEquivHom_comp C g p v w hw
end HomLine

open HomLine ArithmeticThetaRootTorsor

theorem square_isomorphism_torsor
    (X : Scheme.{u}) (h2 : IsUnit (2 : Γ(X, ⊤)))
    (H J W : X.Modules)
    (hH : IsLineBundle X H) (hJ : IsLineBundle X J) (hW : IsLineBundle X W)
    (a : tensorPower X H 2 ≅ W) (b : tensorPower X J 2 ≅ W) :
    ∃ (T : Scheme.{u}) (p : T ⟶ X) (e : SquareIsos a b p),
      IsFinite p ∧ Etale p ∧ Surjective p ∧ (∀ x : X, Scheme.Hom.finrank p x = 2) ∧
      ∀ (S : Scheme.{u}) (f : S ⟶ X) (w : SquareIsos a b f),
        ∃! g : {g : S ⟶ T // g ≫ p = f},
          pullbackIsoOver p f H J g e.val = w.val := by
  let C : PairFrames X H J := pairFrames hH hJ
  obtain ⟨T, p, s, hfinite, hetale, hsurj, hdegree, hgen, heq, huniv⟩ :=
    comparison_root_cover hH hJ h2 a b
  let rs : HomLine.rootFamily C p a b := ⟨s, heq⟩
  let e : SquareIsos a b p := rootToSquare hH hJ hW C p a b rs
  refine ⟨T, p, e, hfinite, hetale, hsurj, hdegree, ?_⟩
  intro S f w
  let rw : HomLine.rootFamily C f a b := squareToRoot C f a b w
  obtain ⟨g, hg, hgu⟩ := huniv S f rw
  have hew : pullbackIsoOver p f H J g e.val = w.val := by
    have hcomp := pullbackSectionEquivHom_over C p f g s e.val (by rfl)
    have hsec : pullbackSectionEquivHom C f
        (pullbackSectionOver p f (homLine X H J) g s) =
        pullbackSectionEquivHom C f rw.val := by
      exact congrArg (pullbackSectionEquivHom C f) hg
    have hroot : pullbackSectionEquivHom C f rw.val = w.val.hom := by
      dsimp [rw, squareToRoot]
      exact (pullbackSectionEquivHom C f).apply_symm_apply w.val.hom
    apply Iso.ext
    exact hcomp.symm.trans (hsec.trans hroot)
  refine ⟨g, hew, ?_⟩
  intro g' hg'
  apply hgu
  have hcomp := pullbackSectionEquivHom_over C p f g' s e.val (by rfl)
  have hsec : pullbackSectionEquivHom C f
      (pullbackSectionOver p f (homLine X H J) g' s) = w.val.hom := by
    exact hcomp.trans (congrArg Iso.hom hg')
  apply (pullbackSectionEquivHom C f).injective
  have hroot : pullbackSectionEquivHom C f rw.val = w.val.hom := by
    dsimp [rw, squareToRoot]
    exact (pullbackSectionEquivHom C f).apply_symm_apply w.val.hom
  exact hsec.trans hroot.symm

end ArithmeticThetaCoverComparison
