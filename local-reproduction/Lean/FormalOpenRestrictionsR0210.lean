import FormalCoverDefinitionsR0210

open AlgebraicGeometry CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace ArithmeticThetaFormalCoverR0210
namespace FormalOpenRestrictions

variable (k : Type u) [Field k] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of (PowerSeries k)))

/-- Restriction on the actual nth thickening. -/
def stageMap (U V : X.Opens) (h : V ≤ U) (n : ℕ) :
    StageSections k X f U n →+* StageSections k X f V n :=
  ((stage k X f n).presheaf.map
    (homOfLE ((inclusion k X f n).preimage_mono h)).op).hom

lemma stageMap_transition (U V : X.Opens) (h : V ≤ U) (m n : ℕ)
    (e : ideal k X f ^ n ≤ ideal k X f ^ m) (a : StageSections k X f U n) :
    transition k X f V m n e (stageMap k X f U V h n a) =
      stageMap k X f U V h m (transition k X f U m n e a) := by
  change (((stage k X f n).presheaf.map _ ≫
    (Scheme.IdealSheafData.inclusion e).appLE _ _ _) a) =
    (((Scheme.IdealSheafData.inclusion e).appLE _ _ _ ≫
      (stage k X f m).presheaf.map _) a)
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- Restriction of compatible sections, formed component by component. -/
def map (U V : X.Opens) (h : V ≤ U) :
    FormalRing k X f U →+* FormalRing k X f V where
  toFun a := ⟨fun n => stageMap k X f U V h n (a.val n), by
    intro m n e
    rw [stageMap_transition, a.property m n e]⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' a b := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_mul' a b := by apply Subtype.ext; funext n; exact map_mul _ _ _

lemma map_ofSection (U V : X.Opens) (h : V ≤ U) (a : Γ(X, U)) :
    map k X f U V h (ofSection k X f U a) =
      ofSection k X f V ((X.presheaf.map (homOfLE h).op) a) := by
  apply Subtype.ext
  funext n
  exact (congrArg (fun g : Γ(X, U) ⟶ StageSections k X f V n => g a)
    ((inclusion k X f n).naturality (homOfLE h).op)).symm

lemma map_scalar (U V : X.Opens) (h : V ≤ U) (r : PowerSeries k) :
    map k X f U V h (scalar k X f U r) = scalar k X f V r := by
  change map k X f U V h (ofSection k X f U _) = ofSection k X f V _
  rw [map_ofSection]
  congr 1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f V
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom f h).commutes r

lemma map_parameter (U V : X.Opens) (h : V ≤ U) :
    map k X f U V h (parameter k X f U) = parameter k X f V :=
  map_scalar k X f U V h PowerSeries.X

/-- The parameter becomes a unit, so the actual restriction extends uniquely. -/
def genericMap (U V : X.Opens) (h : V ≤ U) :
    GenericRing k X f U →+* GenericRing k X f V :=
  IsLocalization.Away.lift (parameter k X f U)
    (g := (localize k X f V).comp (map k X f U V h)) (by
      change IsUnit (localize k X f V (map k X f U V h (parameter k X f U)))
      rw [map_parameter]
      exact IsLocalization.Away.algebraMap_isUnit (parameter k X f V))

lemma genericMap_extends (U V : X.Opens) (h : V ≤ U) (a : FormalRing k X f U) :
    genericMap k X f U V h (localize k X f U a) =
      localize k X f V (map k X f U V h a) :=
  IsLocalization.Away.lift_eq _ _ _

def restrictions : Restrictions k X f where
  map := map k X f
  component := by intros; rfl
  genericMap := genericMap k X f
  generic_extends := genericMap_extends k X f

lemma unique (σ ρ : Restrictions k X f) : σ = ρ := by
  have hm : σ.map = ρ.map := by
    funext U V h
    apply RingHom.ext
    intro a
    apply Subtype.ext
    funext n
    exact (σ.component U V h a n).trans (ρ.component U V h a n).symm
  have hg : σ.genericMap = ρ.genericMap := by
    funext U V h
    apply IsLocalization.ringHom_ext (Submonoid.powers (parameter k X f U))
    apply RingHom.ext
    intro a
    change σ.genericMap U V h (localize k X f U a) =
      ρ.genericMap U V h (localize k X f U a)
    rw [σ.generic_extends, ρ.generic_extends, hm]
  cases σ
  cases ρ
  cases hm
  cases hg
  rfl

end FormalOpenRestrictions

/-- The unique restriction system on actual formal sections and their generic localizations. -/
theorem formal_open_restrictions (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of (PowerSeries k))) :
    ∃ ρ : Restrictions k X f, ∀ σ : Restrictions k X f, σ = ρ :=
  ⟨FormalOpenRestrictions.restrictions k X f,
    fun σ => FormalOpenRestrictions.unique k X f σ _⟩

end ArithmeticThetaFormalCoverR0210

#print axioms ArithmeticThetaFormalCoverR0210.formal_open_restrictions
