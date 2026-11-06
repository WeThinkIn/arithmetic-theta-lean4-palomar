import SchemeFullLevelThetaMarkingR0259
import SchemeSymmetricSignsR0259

/-! The actual pushforward theta sheaf, its invariant subsheaf, and canonical
geometric maps. Only definitions; all claimed properties are new obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeSchrodingerR0261
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeThetaMarkingR0259
open scoped TensorProduct

local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {S : Scheme.{u}} (E : Family S)
abbrev V (m : ℕ) : S.Modules := (Scheme.Modules.pushforward E.p).obj (thetaLine E m)

/-- An action is characterized on every open by the actual sheaf lift and
pullback of sections. The commuting equation fixes the restriction transport. -/
def IsAction (m : ℕ) (f : E.curve ⟶ E.curve) (α : Lift E m f)
    (A : End (V E m)) : Prop :=
  ∃ h : f ≫ E.p = E.p, ∀ (U : S.Opens) (w : Γ(thetaLine E m, E.p ⁻¹ᵁ U)),
    α.hom.app (f ⁻¹ᵁ (E.p ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection f w) =
      (thetaLine E m).presheaf.map
        (eqToHom (congrArg (fun g : E.curve ⟶ S => g ⁻¹ᵁ U) h)).op (A.app U w)

/-- Finite projectivity and rank are asserted for the actual sheaf on every
affine test, with the structural scalar action. -/
def BundleRank (W : S.Modules) (m : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] (b : Base R ⟶ S),
    let L := (Scheme.Modules.pullback b).obj W
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (𝟙 (Base R)) L ⊤
    ArithmeticThetaRelativeSchrodingerR0257.FiniteProjectiveRank R Γ(L, ⊤) m

/-- The canonical proper-base-change morphism is the adjoint of the pulled-back
counit, with exactly the Cartesian square's maps. -/
def baseChangeMap (m : ℕ) {T : Scheme.{u}} (b : T ⟶ S) :
    (Scheme.Modules.pullback b).obj (V E m) ⟶
      (Scheme.Modules.pushforward (pullback.snd E.p b)).obj
        ((Scheme.Modules.pullback (pullback.fst E.p b)).obj (thetaLine E m)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd E.p b)).homEquiv _ _
    (((Scheme.Modules.pullbackComp (pullback.snd E.p b) b).app (V E m)).hom ≫
      ((Scheme.Modules.pullbackCongr (pullback.condition (f := E.p) (g := b)).symm).app (V E m)).hom ≫
      ((Scheme.Modules.pullbackComp (pullback.fst E.p b) E.p).app (V E m)).inv ≫
      (Scheme.Modules.pullback (pullback.fst E.p b)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m)))

abbrev fixed {W : S.Modules} (A : End W) : S.Modules := kernel (A - 1)
abbrev fixedι {W : S.Modules} (A : End W) : fixed A ⟶ W := kernel.ι (A - 1)
abbrev copies (W : S.Modules) (m : ℕ) : S.Modules := biproduct (fun _ : Fin m => W)

/-- This is the actual structural unit action on the pushforward sheaf. -/
def unitAction (W : S.Modules) (c : Γ(S, ⊤)ˣ) : End W :=
  (P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulIso c W).hom

def Relations (m : ℕ) {W : S.Modules} (A B : End W) (c : Γ(S, ⊤)ˣ) : Prop :=
  A ^ m = 1 ∧ B ^ m = 1 ∧ A * B = unitAction W c * (B * A)

/-- The isomorphism is specified by each orbit inclusion, and by both standard
operators. It does not choose a global generator of the invariant line. -/
def Orbit (m : ℕ) {W : S.Modules} (A B : End W) (c : Γ(S, ⊤)ˣ) : Prop :=
  ∃ e : copies (fixed A) m ≅ W,
    (∀ i : Fin m, biproduct.ι (fun _ : Fin m => fixed A) i ≫ e.hom = fixedι A ≫ (B ^ i.val)) ∧
    (∀ i : Fin m, fixedι A ≫ (B ^ i.val) ≫ A = fixedι A ≫ (B ^ i.val) ≫ unitAction W (c ^ i.val)) ∧
    (∀ i : Fin m, fixedι A ≫ (B ^ i.val) ≫ B = fixedι A ≫ (B ^ ((i.val + 1) % m)))

/-- Canonical invariant-line base change, including nonflat base morphisms. -/
def FixedNatural {W : S.Modules} (A : End W) : Prop :=
  ∀ (T : Scheme.{u}) (b : T ⟶ S),
    ∃ e : (Scheme.Modules.pullback b).obj (fixed A) ≅ fixed ((Scheme.Modules.pullback b).map A),
      e.hom ≫ fixedι ((Scheme.Modules.pullback b).map A) = (Scheme.Modules.pullback b).map (fixedι A)

/-- Evaluation at the actual identity is the pullback of the adjunction counit. -/
def evaluation (m : ℕ) : V E m ⟶ (Scheme.Modules.pullback E.zero).obj (thetaLine E m) :=
  ((Scheme.Modules.pullbackId S).app (V E m)).inv ≫
    ((Scheme.Modules.pullbackCongr (E.law.one (𝟙 S)).property).app (V E m)).inv ≫
    ((Scheme.Modules.pullbackComp E.zero E.p).app (V E m)).inv ≫
    (Scheme.Modules.pullback E.zero).map
      ((Scheme.Modules.pullbackPushforwardAdjunction E.p).counit.app (thetaLine E m))

/-- Components are actual maps between the one common invariant line and the
one identity-fibre line. Equivalently they are sections of their Hom line. -/
def component (m : ℕ) (A B : End (V E m)) (i : Fin m) :
    fixed A ⟶ (Scheme.Modules.pullback E.zero).obj (thetaLine E m) :=
  fixedι A ≫ (B ^ i.val) ≫ evaluation E m

def commonValueLine (m : ℕ) (A : End (V E m)) : S.Modules :=
  tensorObj (Scheme.Modules.dual (fixed A))
    ((Scheme.Modules.pullback E.zero).obj (thetaLine E m))

/-- An unconditional geometric consumer: normalized lifts and the canonical
pushforward representation are constructed from the actual full level. -/
def Comparison (m : ℕ) (M : FullLevel E (2*m)) : Prop :=
  ∃ (ι : Lift E m (inverse E))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y))
    (c : Γ(S, ⊤)ˣ) (A B : End (V E m)),
    NormalizedInversion E m ι ∧
    MidpointNormalized E m M.x ι α ∧ Symmetric E m M.x ι α ∧
    MidpointNormalized E m M.y ι β ∧ Symmetric E m M.y ι β ∧
    Commutator E m M.x M.y α β c ∧ PrimitiveUnit (S := S) m c ∧
    IsAction E m (translation E M.x) α A ∧ IsAction E m (translation E M.y) β B ∧
    Relations m A B c ∧ BundleRank (V E m) m ∧
    Scheme.Modules.IsInvertible (fixed A) ∧ Orbit m A B c ∧ FixedNatural A ∧
    Scheme.Modules.IsInvertible (commonValueLine E m A) ∧ Epi (evaluation E m) ∧
    ∃ e : copies (fixed A) m ≅ V E m,
      (∀ i : Fin m, biproduct.ι (fun _ : Fin m => fixed A) i ≫ e.hom = fixedι A ≫ (B ^ i.val)) ∧
      (∀ i : Fin m, biproduct.ι (fun _ : Fin m => fixed A) i ≫ e.hom ≫ evaluation E m = component E m A B i)

end ArithmeticThetaSchemeSchrodingerR0261
