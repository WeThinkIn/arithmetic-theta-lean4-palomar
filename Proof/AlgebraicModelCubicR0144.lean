module

public import FiniteChartSplitCubicR0144
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public section

/-! Algebraization of the literal split cubic through faithful completion. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u
namespace ArithmeticThetaCubicModelR0144
namespace AlgebraicModelCubicR0144
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136 (baseScheme MarkedLift)
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaAlgebraicCoordinatesR0143.CoordinateMarkedEvaluationR0143
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136

lemma scaled_cubic {R : Type*} [CommRing R] (x y h c d : R) (e : Fin 3 → R)
    (hc : y^2 = ∏ j : Fin 3, (x - e j * h^2)) :
    (d*y)^2 * (c*h^2)^3 =
      (∏ j : Fin 3, (c*x - e j * (c*h^2))) * (d*h^3)^2 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hc ⊢
  linear_combination c^3 * d^2 * h^6 * hc

lemma frame_value {S : Scheme.{u}} {L : S.Modules}
    (f : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶ L) [IsIso f]
    (q : L ⟶ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (v : Γ(S, ⊤)) (hv : f ≫ q = fromSection (SheafOfModules.unit S.ringCatSheaf : S.Modules) v)
    (U : S.Opens) (a : Γ(L, U)) :
    q.app U a = (show Γ(S, U) from (Scheme.Modules.Hom.app (inv f) U) a) *
      S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op v := by
  have he : q = inv f ≫ fromSection (SheafOfModules.unit S.ringCatSheaf : S.Modules) v := by rw [← hv, IsIso.inv_hom_id_assoc]
  rw [he]
  exact fromSection_apply (SheafOfModules.unit S.ringCatSheaf : S.Modules) v U ((Scheme.Modules.Hom.app (inv f) U) a)

open MonoidalCategory
attribute [local instance] Scheme.Modules.pullback_monoidal

def dualMul {S : Scheme.{u}} {L P : S.Modules}
    (φ : L ⟶ (𝟙_ S.Modules)) (ψ : P ⟶ (𝟙_ S.Modules)) :
    L ⊗ P ⟶ (𝟙_ S.Modules) := (φ ⊗ₘ ψ) ≫ (λ_ (𝟙_ S.Modules)).hom

lemma dualMul_app {S : Scheme.{u}} {L P : S.Modules}
    (φ : L ⟶ (𝟙_ S.Modules)) (ψ : P ⟶ (𝟙_ S.Modules))
    (U : S.Opens) (a : Γ(L, U)) (b : Γ(P, U)) :
    (dualMul φ ψ).app U (Scheme.Modules.tensorSections a b) =
      (show Γ(S, U) from φ.app U a) * (show Γ(S, U) from ψ.app U b) := by
  change (λ_ (𝟙_ S.Modules)).hom.val.app (Opposite.op U)
    ((φ ⊗ₘ ψ).val.app (Opposite.op U) (Scheme.Modules.tensorSections a b)) = _
  erw [← Scheme.Modules.tmulSection_eq_tensorSections,
    SheafOfModules.tensorHom_val_app_tmulSection,
    SheafOfModules.leftUnitor_hom_val_app_tmulSection]
  rfl

lemma unitPullback_monoidal {S Z : Scheme.{u}} (f : S ⟶ Z) :
    unitPullback f = (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).inv := by
  have h := congrArg Iso.hom (Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso f)
  exact h.symm

lemma pull_dualMul {S Z : Scheme.{u}} (f : S ⟶ Z) {L P : Z.Modules}
    (φ : L ⟶ (𝟙_ Z.Modules)) (ψ : P ⟶ (𝟙_ Z.Modules)) :
    (Scheme.Modules.pullbackTensorObjIso f L P).inv ≫ pulledInclusion f (dualMul φ ψ) =
      dualMul (pulledInclusion f φ) (pulledInclusion f ψ) := by
  simp only [dualMul, pulledInclusion, Functor.map_comp, Category.assoc,
    Scheme.Modules.pullbackTensorObjIso, Iso.symm_inv, Functor.Monoidal.μIso_hom]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [unitPullback_monoidal]
  erw [Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc]
  erw [Functor.Monoidal.μ_δ_assoc]
  simp only [Functor.Monoidal.εIso_inv, ← leftUnitor_naturality]
  erw [← MonoidalCategory.tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc]
  rfl

lemma pull_dualMul_eq {S Z : Scheme.{u}} (f : S ⟶ Z) {L P : Z.Modules}
    (φ : L ⟶ (𝟙_ Z.Modules)) (ψ : P ⟶ (𝟙_ Z.Modules)) :
    pulledInclusion f (dualMul φ ψ) =
      (Scheme.Modules.pullbackTensorObjIso f L P).hom ≫
        dualMul (pulledInclusion f φ) (pulledInclusion f ψ) := by
  rw [← pull_dualMul f φ ψ, Iso.hom_inv_id_assoc]

lemma dualMul_precomp {S : Scheme.{u}} {L P L' P' : S.Modules}
    (a : L' ⟶ L) (b : P' ⟶ P)
    (φ : L ⟶ (𝟙_ S.Modules)) (ψ : P ⟶ (𝟙_ S.Modules)) :
    dualMul (a ≫ φ) (b ≫ ψ) = (a ⊗ₘ b) ≫ dualMul φ ψ := by
  unfold dualMul
  rw [← tensorHom_comp_tensorHom, Category.assoc]

def pairFrame {S : Scheme.{u}} {L P : S.Modules}
    (a : (𝟙_ S.Modules) ⟶ L) (b : (𝟙_ S.Modules) ⟶ P) :
    (𝟙_ S.Modules) ⟶ L ⊗ P := (λ_ (𝟙_ S.Modules)).inv ≫ (a ⊗ₘ b)

instance pairFrame_isIso {S : Scheme.{u}} {L P : S.Modules}
    (a : (𝟙_ S.Modules) ⟶ L) (b : (𝟙_ S.Modules) ⟶ P) [IsIso a] [IsIso b] :
    IsIso (pairFrame a b) := by unfold pairFrame; infer_instance

lemma pairFrame_eval {S : Scheme.{u}} {L P : S.Modules}
    (a : (𝟙_ S.Modules) ⟶ L) (b : (𝟙_ S.Modules) ⟶ P)
    (φ : L ⟶ (𝟙_ S.Modules)) (ψ : P ⟶ (𝟙_ S.Modules))
    (v w : Γ(S, ⊤))
    (hv : a ≫ φ = fromSection (𝟙_ S.Modules) v)
    (hw : b ≫ ψ = fromSection (𝟙_ S.Modules) w) :
    pairFrame a b ≫ dualMul φ ψ = fromSection (𝟙_ S.Modules) (v*w) := by
  rw [pairFrame, Category.assoc, ← dualMul_precomp, hv, hw]
  apply unit_hom_ext
  change (dualMul (fromSection (𝟙_ S.Modules) v) (fromSection (𝟙_ S.Modules) w)).app ⊤
    ((λ_ (𝟙_ S.Modules)).inv.val.app (Opposite.op ⊤) (1 : Γ(S, ⊤))) = _
  erw [SheafOfModules.leftUnitor_inv_val_app]
  erw [Scheme.Modules.tmulSection_eq_tensorSections, dualMul_app]
  simp [fromSection_apply]

def fiveSource {S : Scheme.{u}} (L P : S.Modules) : S.Modules :=
  (L ⊗ (L ⊗ L)) ⊗ (P ⊗ P)

def dualFive {S : Scheme.{u}} {L P : S.Modules}
    (a b c : L ⟶ (𝟙_ S.Modules)) (d e : P ⟶ (𝟙_ S.Modules)) :
    fiveSource L P ⟶ (𝟙_ S.Modules) := dualMul (dualMul a (dualMul b c)) (dualMul d e)

def fiveFrame {S : Scheme.{u}} {L P : S.Modules}
    (a : (𝟙_ S.Modules) ⟶ L) (b : (𝟙_ S.Modules) ⟶ P) :
    (𝟙_ S.Modules) ⟶ fiveSource L P :=
  pairFrame (pairFrame a (pairFrame a a)) (pairFrame b b)

instance fiveFrame_isIso {S : Scheme.{u}} {L P : S.Modules}
    (a : (𝟙_ S.Modules) ⟶ L) (b : (𝟙_ S.Modules) ⟶ P) [IsIso a] [IsIso b] :
    IsIso (fiveFrame a b) := by unfold fiveFrame; infer_instance

lemma fiveFrame_eval {S : Scheme.{u}} {L P : S.Modules}
    (f : (𝟙_ S.Modules) ⟶ L) (g : (𝟙_ S.Modules) ⟶ P)
    (a b c : L ⟶ (𝟙_ S.Modules)) (d e : P ⟶ (𝟙_ S.Modules))
    (av bv cv dv ev : Γ(S, ⊤))
    (ha : f ≫ a = fromSection (𝟙_ S.Modules) av)
    (hb : f ≫ b = fromSection (𝟙_ S.Modules) bv)
    (hc : f ≫ c = fromSection (𝟙_ S.Modules) cv)
    (hd : g ≫ d = fromSection (𝟙_ S.Modules) dv)
    (he : g ≫ e = fromSection (𝟙_ S.Modules) ev) :
    fiveFrame f g ≫ dualFive a b c d e =
      fromSection (𝟙_ S.Modules) ((av*(bv*cv))*(dv*ev)) :=
  pairFrame_eval _ _ _ _ _ _
    (pairFrame_eval _ _ _ _ _ _ ha (pairFrame_eval _ _ _ _ _ _ hb hc))
    (pairFrame_eval _ _ _ _ _ _ hd he)

lemma fiveFrame_cubic {S : Scheme.{u}} {L P : S.Modules}
    (f : (𝟙_ S.Modules) ⟶ L) (g : (𝟙_ S.Modules) ⟶ P) [IsIso f] [IsIso g]
    (a : L ⟶ (𝟙_ S.Modules)) (b : P ⟶ (𝟙_ S.Modules))
    (q : Fin 3 → (L ⟶ (𝟙_ S.Modules))) (y : P ⟶ (𝟙_ S.Modules))
    {R : Type*} [CommRing R] (ρ : R →+* Γ(S,⊤))
    (h x z : R) (e : Fin 3 → R)
    (ha : f ≫ a = fromSection (𝟙_ S.Modules) (ρ (h^2)))
    (hb : g ≫ b = fromSection (𝟙_ S.Modules) (ρ (h^3)))
    (hq : ∀ j, f ≫ q j = fromSection (𝟙_ S.Modules) (ρ (x-e j*h^2)))
    (hy : g ≫ y = fromSection (𝟙_ S.Modules) (ρ z))
    (hc : z^2 = ∏ j : Fin 3, (x-e j*h^2)) :
    dualFive a a a y y = dualFive (q 0) (q 1) (q 2) b b := by
  apply (cancel_epi (fiveFrame f g)).mp
  rw [fiveFrame_eval f g _ _ _ _ _ _ _ _ _ _ ha ha ha hy hy,
    fiveFrame_eval f g _ _ _ _ _ _ _ _ _ _ (hq 0) (hq 1) (hq 2) hb hb]
  have hv : (ρ (h^2) * (ρ (h^2) * ρ (h^2))) * (ρ z * ρ z) =
      (ρ (x-e 0*h^2) * (ρ (x-e 1*h^2) * ρ (x-e 2*h^2))) *
        (ρ (h^3) * ρ (h^3)) := by
    have hh := congrArg ρ hc
    simp only [map_pow, map_sub, map_mul, Fin.prod_univ_three] at hh ⊢
    linear_combination (ρ h)^6 * hh
  exact congrArg (fromSection (𝟙_ S.Modules)) hv

def fivePullIso {S Z : Scheme.{u}} (f : S ⟶ Z) (L P : Z.Modules) :
    (Scheme.Modules.pullback f).obj (fiveSource L P) ≅
      fiveSource ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj P) :=
  Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
    ((Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
      (Iso.refl _ ⊗ᵢ Scheme.Modules.pullbackTensorObjIso f L L)) ⊗ᵢ
      Scheme.Modules.pullbackTensorObjIso f P P)

lemma pull_dualFive {S Z : Scheme.{u}} (f : S ⟶ Z) {L P : Z.Modules}
    (a b c : L ⟶ (𝟙_ Z.Modules)) (d e : P ⟶ (𝟙_ Z.Modules)) :
    pulledInclusion f (dualFive a b c d e) =
      (fivePullIso f L P).hom ≫ dualFive (pulledInclusion f a)
        (pulledInclusion f b) (pulledInclusion f c) (pulledInclusion f d) (pulledInclusion f e) := by
  simp only [dualFive, pull_dualMul_eq, fivePullIso, Iso.trans_hom,
    tensorIso_hom, Iso.refl_hom, Category.assoc]
  have hh := dualMul_precomp (𝟙 _) (Scheme.Modules.pullbackTensorObjIso f L L).hom
    (pulledInclusion f a) (dualMul (pulledInclusion f b) (pulledInclusion f c))
  simp only [Category.id_comp] at hh
  rw [hh, dualMul_precomp]
  have hh' := dualMul_precomp
    (𝟙 _ ⊗ₘ (Scheme.Modules.pullbackTensorObjIso f L L).hom) (𝟙 _)
    (dualMul (pulledInclusion f a) (dualMul (pulledInclusion f b) (pulledInclusion f c)))
    (dualMul (pulledInclusion f d) (pulledInclusion f e))
  simp only [Category.id_comp] at hh'
  rw [hh']
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

lemma dualFive_app {S : Scheme.{u}} {L P : S.Modules}
    (a b c : L ⟶ (𝟙_ S.Modules)) (d e : P ⟶ (𝟙_ S.Modules))
    (U : S.Opens) (x : Γ(L, U)) (y : Γ(P, U)) :
    (dualFive a b c d e).app U
      (Scheme.Modules.tensorSections
        (Scheme.Modules.tensorSections x (Scheme.Modules.tensorSections x x))
        (Scheme.Modules.tensorSections y y)) =
      ((show Γ(S,U) from a.app U x) *
        ((show Γ(S,U) from b.app U x) * (show Γ(S,U) from c.app U x))) *
      ((show Γ(S,U) from d.app U y) * (show Γ(S,U) from e.app U y)) := by
  unfold dualFive
  erw [dualMul_app, dualMul_app, dualMul_app, dualMul_app]

def shift {S : Scheme.{u}} {L : S.Modules}
    (φ j : L ⟶ (𝟙_ S.Modules)) (v : Γ(S, ⊤)) : L ⟶ (𝟙_ S.Modules) :=
  φ - j ≫ fromSection (𝟙_ S.Modules) v

lemma shift_app {S : Scheme.{u}} {L : S.Modules}
    (φ j : L ⟶ (𝟙_ S.Modules)) (v : Γ(S, ⊤)) (U : S.Opens) (x : Γ(L,U)) :
    (shift φ j v).app U x = (show Γ(S,U) from φ.app U x) -
      S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op v *
        (show Γ(S,U) from j.app U x) := by
  change (show Γ(S,U) from φ.app U x) -
    (show Γ(S,U) from (fromSection (𝟙_ S.Modules) v).app U (j.app U x)) = _
  rw [fromSection_apply]
  change _ - (_ * _) = _
  rw [mul_comm]
  rfl

lemma frame_shift {S : Scheme.{u}} {L : S.Modules}
    (f : (𝟙_ S.Modules) ⟶ L) (φ j : L ⟶ (𝟙_ S.Modules))
    (x h v : Γ(S, ⊤))
    (hx : f ≫ φ = fromSection (𝟙_ S.Modules) x)
    (hh : f ≫ j = fromSection (𝟙_ S.Modules) h) :
    f ≫ shift φ j v = fromSection (𝟙_ S.Modules) (x-v*h) := by
  rw [shift, Preadditive.comp_sub, ← Category.assoc, hx, hh]
  apply unit_hom_ext
  change (fromSection (𝟙_ S.Modules) x).app ⊤ (1 : Γ(S,⊤)) -
    (fromSection (𝟙_ S.Modules) v).app ⊤
      ((fromSection (𝟙_ S.Modules) h).app ⊤ (1 : Γ(S,⊤))) = _
  simp [fromSection_apply, mul_comm]

lemma pull_shift {S Z : Scheme.{u}} (f : S ⟶ Z) {L : Z.Modules}
    (φ j : L ⟶ (𝟙_ Z.Modules)) (v : Γ(Z, ⊤)) :
    pulledInclusion f (shift φ j v) =
      shift (pulledInclusion f φ) (pulledInclusion f j) (f.appTop v) := by
  simp only [shift, pulledInclusion, Functor.map_sub, Preadditive.sub_comp,
    Functor.map_comp, Category.assoc]
  erw [pullback_multiplication]
  rfl

lemma five_equality_local {S : Scheme.{u}} {L P : S.Modules}
    (X j₂ : L ⟶ (𝟙_ S.Modules)) (Y j₃ : P ⟶ (𝟙_ S.Modules))
    (v : Fin 3 → Γ(S,⊤))
    (heq : dualFive j₂ j₂ j₂ Y Y =
      dualFive (shift X j₂ (v 0)) (shift X j₂ (v 1)) (shift X j₂ (v 2)) j₃ j₃)
    (U : S.Opens) (a : Γ(L,U)) (b : Γ(P,U)) :
    (show Γ(S,U) from Y.app U b)^2 * (show Γ(S,U) from j₂.app U a)^3 =
      (∏ j : Fin 3, ((show Γ(S,U) from X.app U a) -
        S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (v j) *
        (show Γ(S,U) from j₂.app U a))) * (show Γ(S,U) from j₃.app U b)^2 := by
  have hh := congrArg (fun φ : fiveSource L P ⟶ (𝟙_ S.Modules) =>
    φ.app U (Scheme.Modules.tensorSections
      (Scheme.Modules.tensorSections a (Scheme.Modules.tensorSections a a))
      (Scheme.Modules.tensorSections b b))) heq
  erw [dualFive_app, dualFive_app] at hh
  erw [shift_app X j₂ (v 0) U a, shift_app X j₂ (v 1) U a,
    shift_app X j₂ (v 2) U a] at hh
  let xx : Γ(S,U) := X.app U a
  let yy : Γ(S,U) := Y.app U b
  let ja : Γ(S,U) := j₂.app U a
  let jb : Γ(S,U) := j₃.app U b
  let vv (j : Fin 3) : Γ(S,U) :=
    S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (v j)
  have hh' : (ja*(ja*ja))*(yy*yy) =
      ((xx-vv 0*ja)*((xx-vv 1*ja)*(xx-vv 2*ja)))*(jb*jb) := hh
  change yy^2 * ja^3 = (∏ j : Fin 3, (xx-vv j*ja))*jb^2
  rw [Fin.prod_univ_three]
  linear_combination hh' 

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- Faithfulness on arbitrary invertible source modules over the actual model. -/
lemma model_hom_ext (M : Model k T) (hM : IsModel k T M)
    (L : M.X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (φ ψ : L ⟶ (SheafOfModules.unit M.X.ringCatSheaf : M.X.Modules))
    (h : ∀ n, pulledInclusion (M.inclusion n) φ = pulledInclusion (M.inclusion n) ψ) :
    φ = ψ := by
  letI : IsProper M.p := hM.1
  have hu := pullback_dual_completion
    (Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) M.p
    (fun n => (T.atlas n).X) M.inclusion (fun n => (T.atlas n).p)
    (fun n => hM.2.2.1 n)
    (fun n => T.transition n (n+1) (Nat.le_succ n))
    (fun n => hM.2.2.2 n (n+1) (Nat.le_succ n)) L hL
    (fun n => pulledInclusion (M.inclusion n) ψ)
    (fun n => compIso_inclusion _ _ _ _ L ψ)
  exact hu.unique h (fun _ => rfl)

lemma model_chart_hom_ext (M : Model k T) (hM : IsModel k T M)
    (L : M.X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (φ ψ : L ⟶ (𝟙_ M.X.Modules))
    (h : ∀ n i, pulledInclusion (chartMap k M n i) φ =
      pulledInclusion (chartMap k M n i) ψ) : φ = ψ := by
  apply model_hom_ext k M hM L hL φ ψ
  intro n
  apply ArithmeticThetaPositiveLineR0134.GlobalPositiveSectionRealizationR0134.hom_ext_pullback_cover
    (fun _ : Fin r => specA k n) (T.atlas n).chart (T.atlas n).chart_open (T.atlas n).covers
  intro i
  letI := unitPullback_isIso ((T.atlas n).chart i)
  apply (cancel_mono (unitPullback ((T.atlas n).chart i))).mp
  change pulledInclusion ((T.atlas n).chart i) (pulledInclusion (M.inclusion n) φ) = _
  change pulledInclusion ((T.atlas n).chart i) (pulledInclusion (M.inclusion n) φ) =
    pulledInclusion ((T.atlas n).chart i) (pulledInclusion (M.inclusion n) ψ)
  erw [← pulledInclusion_comp, ← pulledInclusion_comp]
  exact congrArg (fun q => (Scheme.Modules.pullbackComp ((T.atlas n).chart i)
    (M.inclusion n)).hom.app L ≫ q) (h n i)

lemma chart_scalar (M : Model k T) (hM : IsModel k T M) (n : ℕ) (i : Fin r)
    (g : PowerSeries k) :
    (chartMap k M n i).appTop
      (M.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g)) =
    (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
      (base k n (trunc (PowerSeries k) PowerSeries.X n g)) := by
  have ho : chartMap k M n i ≫ M.p = structureMap k n ≫ baseInclusion k n := by
    rw [chartMap, Category.assoc, (hM.2.2.1 n).w, ← Category.assoc, (T.atlas n).chart_over]
  change (chartMap k M n i ≫ M.p).appTop _ = _
  rw [ho, Scheme.Hom.comp_appTop]
  change (structureMap k n).appTop ((baseInclusion k n).appTop _) = _
  rw [show (baseInclusion k n).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g) =
    (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv
      (trunc (PowerSeries k) PowerSeries.X n g) from base_value k n g]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (base k n))) _).symm

/-- The finite-chart equality holds for arbitrary local sections of the two
pulled-back ideal powers, not only for their canonical generators. -/
lemma chart_local_cubic (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (n : ℕ) (i : Fin r) (U : (specA k n).Opens)
    (a : Γ((Scheme.Modules.pullback (chartMap k M n i)).obj (powerModule k M s 2), U))
    (b : Γ((Scheme.Modules.pullback (chartMap k M n i)).obj (powerModule k M s 3), U)) :
    let ρ : A k n →+* Γ(specA k n, U) :=
      ((specA k n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
    let ja : Γ(specA k n, U) :=
      (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^2))).app U a
    let jb : Γ(specA k n, U) :=
      (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^3))).app U b
    (show Γ(specA k n, U) from (pulledInclusion (chartMap k M n i) Y).app U b)^2 * ja^3 =
      (∏ j : Fin 3, ((show Γ(specA k n, U) from
        (pulledInclusion (chartMap k M n i) X).app U a) - ρ (rootAt k r n j) * ja)) * jb^2 := by
  dsimp only
  let f₂ := chartFrame k h3 M hM s hs 2 n i
  let f₃ := chartFrame k h3 M hM s hs 3 n i
  let ρ : A k n →+* Γ(specA k n, U) :=
    ((specA k n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
  have hx := frame_value f₂ (pulledInclusion (chartMap k M n i) X) _
    (chartFrame_value k h3 M hM s hs false X hX n i) U a
  have hy := frame_value f₃ (pulledInclusion (chartMap k M n i) Y) _
    (chartFrame_value k h3 M hM s hs true Y hY n i) U b
  have ha := frame_value f₂ (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^2))) _
    (chartFrame_inclusion k h3 M hM s hs 2 n i) U a
  have hb := frame_value f₃ (pulledInclusion (chartMap k M n i) (idealInclusion (s.ker^3))) _
    (chartFrame_inclusion k h3 M hM s hs 3 n i) U b
  erw [hx, hy, ha, hb]
  change (_ * ρ (numerator k true r n i))^2 * (_ * ρ (equation k r n i ^ 2))^3 =
    (∏ j : Fin 3, (_ * ρ (numerator k false r n i) -
      ρ (rootAt k r n j) * (_ * ρ (equation k r n i ^ 2)))) *
      (_ * ρ (equation k r n i ^ 3))^2
  simp only [map_pow]
  apply scaled_cubic
  simpa only [map_pow, map_prod, map_sub, map_mul] using
    congrArg ρ (finite_chart_split_cubic k r h3 he n i)

lemma model_chart_cubic (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (n : ℕ) (i : Fin r) :
    let j₂ := idealInclusion (s.ker^2)
    let j₃ := idealInclusion (s.ker^3)
    let v (j : Fin 3) : Γ(M.X,⊤) := M.p.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (rootSeries k r j))
    let q (j : Fin 3) := shift X j₂ (v j)
    pulledInclusion (chartMap k M n i) (dualFive j₂ j₂ j₂ Y Y) =
      pulledInclusion (chartMap k M n i) (dualFive (q 0) (q 1) (q 2) j₃ j₃) := by
  let L := powerModule k M s 2
  let P := powerModule k M s 3
  let j₂ : L ⟶ (𝟙_ M.X.Modules) := idealInclusion (s.ker^2)
  let j₃ : P ⟶ (𝟙_ M.X.Modules) := idealInclusion (s.ker^3)
  let v (j : Fin 3) : Γ(M.X,⊤) := M.p.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (rootSeries k r j))
  let q (j : Fin 3) := shift X j₂ (v j)
  change pulledInclusion (chartMap k M n i) (dualFive j₂ j₂ j₂ Y Y) =
    pulledInclusion (chartMap k M n i) (dualFive (q 0) (q 1) (q 2) j₃ j₃)
  rw [pull_dualFive, pull_dualFive]
  congr 1
  let f := chartMap k M n i
  let f₂ := chartFrame k h3 M hM s hs 2 n i
  let f₃ := chartFrame k h3 M hM s hs 3 n i
  letI : IsIso f₂ := chartFrame_isIso k h3 M hM s hs 2 n i
  letI : IsIso f₃ := chartFrame_isIso k h3 M hM s hs 3 n i
  letI : IsIso (fiveFrame f₂ f₃) := fiveFrame_isIso f₂ f₃
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv.hom
  have hj₂ := chartFrame_inclusion k h3 M hM s hs 2 n i
  have hj₃ := chartFrame_inclusion k h3 M hM s hs 3 n i
  have hx := chartFrame_value k h3 M hM s hs false X hX n i
  have hy := chartFrame_value k h3 M hM s hs true Y hY n i
  have hq (j : Fin 3) : f₂ ≫ pulledInclusion f (q j) =
      fromSection (𝟙_ (specA k n).Modules)
        (ρ (numerator k false r n i - rootAt k r n j * equation k r n i^2)) := by
    dsimp only [q]
    rw [pull_shift, show f.appTop (v j) = ρ (rootAt k r n j) from
      chart_scalar k M hM n i (rootSeries k r j)]
    rw [frame_shift f₂ _ _ _ _ _ hx hj₂]
    simp only [map_sub, map_mul]
    rfl
  exact fiveFrame_cubic (S := specA k n)
    (L := (Scheme.Modules.pullback f).obj L) (P := (Scheme.Modules.pullback f).obj P)
    f₂ f₃ (pulledInclusion f j₂) (pulledInclusion f j₃)
    (fun j => pulledInclusion f (q j)) (pulledInclusion f Y) ρ (equation k r n i)
    (numerator k false r n i) (numerator k true r n i) (rootAt k r n)
    hj₂ hj₃ hq hy (finite_chart_split_cubic k r h3 he n i)

lemma model_cubic_proof (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ModelCubic k M s X Y := by
  let L := powerModule k M s 2
  let P := powerModule k M s 3
  let j₂ : L ⟶ (𝟙_ M.X.Modules) := idealInclusion (s.ker^2)
  let j₃ : P ⟶ (𝟙_ M.X.Modules) := idealInclusion (s.ker^3)
  let v (j : Fin 3) : Γ(M.X,⊤) :=
    M.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv (rootSeries k r j))
  let q (j : Fin 3) := shift X j₂ (v j)
  have hL := (ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs 2).isInvertible_module
  have hP := (ArithmeticThetaIdentitySectionsR0138.AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs 3).isInvertible_module
  have heq : dualFive j₂ j₂ j₂ Y Y = dualFive (q 0) (q 1) (q 2) j₃ j₃ := by
    apply model_chart_hom_ext k M hM (fiveSource L P)
      (hL.tensor_monoidalV2 (hL.tensor_monoidalV2 hL) |>.tensor_monoidalV2
        (hP.tensor_monoidalV2 hP))
    intro n i
    exact model_chart_cubic k h3 he M hM s hs X Y hX hY n i
  intro U a b
  exact five_equality_local X j₂ Y j₃ v heq U a b

end AlgebraicModelCubicR0144
end ArithmeticThetaCubicModelR0144

namespace ArithmeticThetaCubicModelR0144

theorem algebraic_model_cubic :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ArithmeticThetaCubicModelR0144.ModelCubic k M s X Y := by
  intro k _ _ r hr h3 T he M hM s hs X Y hX hY
  exact AlgebraicModelCubicR0144.model_cubic_proof k h3 he M hM s hs X Y hX hY

end ArithmeticThetaCubicModelR0144
#print axioms ArithmeticThetaCubicModelR0144.algebraic_model_cubic
